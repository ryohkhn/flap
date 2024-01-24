(** This module implements a compiler from Hobix to Fopix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Hobix
module S = Source.AST
module Target = Fopix
module T = Target.AST

(**

   The translation from Hobix to Fopix turns anonymous
   lambda-abstractions into toplevel functions and applications into
   function calls. In other words, it translates a high-level language
   (like OCaml) into a first order language (like C).

   To do so, we follow the closure conversion technique.

   The idea is to make explicit the construction of closures, which
   represent functions as first-class objects. A closure is a block
   that contains a code pointer to a toplevel function [f] followed by all
   the values needed to execute the body of [f]. For instance, consider
   the following OCaml code:

   let f =
     let x = 6 * 7 in
     let z = x + 1 in
     fun y -> x + y * z

   The values needed to execute the function "fun y -> x + y * z" are
   its free variables "x" and "z". The same program with explicit usage
   of closure can be written like this:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]

   (in an imaginary OCaml in which arrays are untyped.)

   Once closures are explicited, there are no more anonymous functions!

   But, wait, how to we call such a function? Let us see that on an
   example:

   let f = ... (* As in the previous example *)
   let u = f 0

   The application "f 0" must be turned into an expression in which
   "f" is a closure and the call to "f" is replaced to a call to "g"
   with the proper arguments. The argument "y" of "g" is known from
   the application: it is "0". Now, where is "env"? Easy! It is the
   closure itself! We get:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]
   let u = f[0] 0 f

   (Remark: Did you notice that this form of "auto-application" is
   very similar to the way "this" is defined in object-oriented
   programming languages?)

*)

(**
   Helpers functions.
*)

let error pos msg =
  Error.error "compilation" pos msg

let make_fresh_variable =
  let r = ref 0 in
  fun () -> incr r; T.Id (Printf.sprintf "_%d" !r)

let make_fresh_function_identifier =
  let r = ref 0 in
  fun () -> incr r; T.FunId (Printf.sprintf "_%d" !r)

let define e f =
  let x = make_fresh_variable () in
  T.Define (x, e, f x)

let rec defines ds e =
  match ds with
    | [] ->
      e
    | (x, d) :: ds ->
      T.Define (x, d, defines ds e)

let seq a b =
  define a (fun _ -> b)

let rec seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq x (seqs xs)

let define' e f =
  T.Define (T.Id "_", e, f ())

let seq' a b =
  define' a (fun _ -> b)

let rec anonymous_seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq' x (anonymous_seqs xs)

let allocate_block e =
  T.(FunCall (FunId "allocate_block", [e]))

let write_block e i v =
  T.(FunCall (FunId "write_block", [e; i; v]))

let read_block e i =
  T.(FunCall (FunId "read_block", [e; i]))

let lint i =
  T.(Literal (LInt (Int64.of_int i)))

let predefined_fun = ["equal_string"; "equal_char"; "print_string"; "print_int"]

(** [free_variables e] returns the list of free variables that
     occur in [e].*)
let free_variables =
  let module M =
    Set.Make (struct type t = S.identifier let compare = compare end)
  in
  let rec unions f = function
    | [] -> M.empty
    | [s] -> f s
    | s :: xs -> M.union (f s) (unions f xs)
  in
  let rec fvs = function
    | S.Literal _ ->
       M.empty
    | S.Variable x ->
      let Id s = x in
      (* if the variable is an arithmetic operator or a predefined function it's not added to the dictionnary *)
      if List.mem s predefined_fun || FopixInterpreter.is_binary_primitive s then
        M.empty
      else
        M.singleton x
    | S.While (cond, e) ->
      unions fvs [cond; e]
    | S.Define (vd, a) ->
      let sv_list =
        match vd with
        | SimpleValue (id, e) ->
          [(id, e)]
        | RecFunctions (sv_list) ->
          sv_list
      in
      let ids, expressions = List.split sv_list in
      let ids_set = M.of_list ids in
      unions fvs (a::expressions)
      |> M.filter (fun id -> not (M.mem id ids_set))
    | S.ReadBlock (a, b) ->
       unions fvs [a; b]
    | S.Apply (a, b) ->
       unions fvs (a :: b)
    | S.WriteBlock (a, b, c) | S.IfThenElse (a, b, c) ->
       unions fvs [a; b; c]
    | S.AllocateBlock a ->
       fvs a
    | S.Fun (xs, e) ->
      let ids_set = M.of_list xs in
      fvs e
      |> M.filter (fun id -> not (M.mem id ids_set))
    | S.Switch (a, b, c) ->
       let c = match c with None -> [] | Some c -> [c] in
       unions fvs (a :: ExtStd.Array.present_to_list b @ c)
  in
  fun e -> M.elements (fvs e)

(**

    A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
type environment = {
    vars : (HobixAST.identifier, FopixAST.expression) Dict.t;
    externals : (HobixAST.identifier, int) Dict.t;
}

let initial_environment () =
  { vars = Dict.empty; externals = Dict.empty }

let bind_external id n env =
  { env with externals = Dict.insert id n env.externals }

let bind_vars id e env =
  { env with vars = Dict.insert id e env.vars }

let is_external id env =
  Dict.lookup id env.externals <> None

let reset_vars env =
   { env with vars = Dict.empty }

(** Precondition: [is_external id env = true]. *)
let arity_of_external id env =
  match Dict.lookup id env.externals with
    | Some n -> n
    | None -> assert false (* By is_external. *)

(** [translate p env] turns an Hobix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =
  let rec program env defs =
    let env, defs = ExtStd.List.foldmap definition env defs in
    (List.flatten defs, env)

  and definition env = function
    | S.DeclareExtern (id, n) ->
       let env = bind_external id n env in
       (env, [T.ExternalFunction (function_identifier id, n)])
    | S.DefineValue vd ->
       (env, value_definition env vd)

  and local_value_definition env = function
    | S.SimpleValue (x, e) ->
       let fs, e = expression (reset_vars env) e in
       fs, [(identifier x, e)]
    | S.RecFunctions fdefs ->
       let fs, defs = define_recursive_functions fdefs in
       fs, defs

  and value_definition env = function
    | S.SimpleValue (x, e) ->
       let fs, e = expression (reset_vars env) e in
       fs @ [T.DefineValue (identifier x, e)]
    | S.RecFunctions fdefs ->
       let fs, defs = define_recursive_functions fdefs in
       fs @ List.map (fun (x, e) -> T.DefineValue (x, e)) defs

  and define_recursive_functions rdefs =
    List.fold_left (fun (fs, defs) (id, e ) ->
        match e with
        | S.Fun (fun_ids, body) ->
        (* creates the S expression that represents a recursive function to calculate the free variables *)
        let f = S.Define (S.RecFunctions rdefs, S.Fun (fun_ids, body)) in
        let free_vars = free_variables f in
        let t_defs, e = s_anonymous_fun env fun_ids body free_vars in
        fs @ t_defs, defs @ [identifier id, e]
        | _  -> failwith "Parsing error"
      ) ([], []) rdefs

  (** [expression env expression] takes a Source (Hobix) expression and translates it into
      a Target (Fopix) list of functions definitions and a Target (Fopix) expression *)
  and expression env = function
    | S.Literal l ->
      [], T.Literal (literal l)
    | S.While (cond, e) ->
       let cfs, cond = expression env cond in
       let efs, e = expression env e in
       cfs @ efs, T.While (cond, e)
    | S.Variable x ->
      let xc =
        match Dict.lookup x env.vars with
          | None -> T.Variable (identifier x)
          | Some e -> e
      in
      ([], xc)
    | S.Define (vdef, a) ->
      let next_tdefs, te = expression env a in
      (* instead of putting the Fopix expressions at top level,
         we add them to the current expression *)
      let tdefs, local_tdefs = local_value_definition env vdef in
      tdefs @ next_tdefs, defines local_tdefs te
    | S.Apply (a, bs) ->
      let afs, a' = expression env a in
      let bfs, bs' = expressions env bs in
      begin
        match a' with
        (* if the left expression of an apply is an existing variable we call it with his name *)
        | T.Variable (T.Id x) as x' ->
          let e =
            if FopixInterpreter.is_binary_primitive x || List.mem x predefined_fun then
              T.FunCall (T.FunId x, bs')
            else
              T.UnknownFunCall (read_block x' (lint 0), bs' @ [x'])
          in
          afs @ bfs, e
        | _ ->
          let closure_id = make_fresh_variable () in
          let clo_var = T.Variable closure_id in
          let instr = T.UnknownFunCall ((read_block clo_var (lint 0)), bs' @ [clo_var]) in
          afs @ bfs, T.Define (closure_id, a', instr)
      end
    | S.IfThenElse (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs, T.IfThenElse (a, b, c)
    | S.Fun (x, e) as f ->
      let t_def_list, t_e = s_anonymous_fun env x e (free_variables f) in
      t_def_list, t_e
    | S.AllocateBlock a ->
      let afs, a = expression env a in
      (afs, allocate_block a)
    | S.WriteBlock (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs,
      T.FunCall (T.FunId "write_block", [a; b; c])
    | S.ReadBlock (a, b) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      afs @ bfs,
      T.FunCall (T.FunId "read_block", [a; b])
    | S.Switch (a, bs, default) ->
      let afs, a = expression env a in
      let bsfs, bs =
        ExtStd.List.foldmap (fun bs t ->
                    match ExtStd.Option.map (expression env) t with
                    | None -> (bs, None)
                    | Some (bs', t') -> (bs @ bs', Some t')
                  ) [] (Array.to_list bs)
      in
      let dfs, default = match default with
        | None -> [], None
        | Some e -> let bs, e = expression env e in bs, Some e
      in
      afs @ bsfs @ dfs,
      T.Switch (a, Array.of_list bs, default)

  and s_anonymous_fun env ids e free_vars =
    let fun_id = make_fresh_function_identifier () in
    let clo_id = make_fresh_variable () in
    let clo_var = T.Variable clo_id in
    (* self is the closure argument of the Fopix function *)
    let self = T.Id "self" in
    (* allocates a block of the number of free variables and the pointer of code *)
    let block =
      lint (List.length free_vars + 1)
      |> allocate_block
    in
    let (env, _, insts) = List.fold_right (fun id (env, i, insts) ->
        let i' = (lint i) in
        let _, e = expression env (S.Variable id) in
        let inst = write_block clo_var i' e in
        let env = bind_vars id (read_block (T.Variable self) i') env in
        (env, i + 1, inst :: insts)
      ) free_vars (env, 1, [])
    in
    let t_def_list, t_e = expression env e in
    (* creates the new function with it's name, it's arguments and the id of the closure *)
    let ids = List.map identifier ids in
    let t_fun = T.DefineFunction (fun_id, ids @ [self], t_e) in
    (* creates the instruction to write the function pointer name at pos 0 in the block *)
    let fun_pointer_inst = write_block clo_var (lint 0) (T.Literal (T.LFun (fun_id))) in
    (* each write_block is transfromed into an anonymous define since they're never called *)
    (* clo_var needs to be the last element of the define to reference the created closure *)
    let insts = anonymous_seqs (List.rev (clo_var :: insts @ [fun_pointer_inst])) in
    let closure = T.Define (clo_id, block, insts) in
    (* the Hobix expression generates a list of definitions that are inserted before the translated anonymous function  *)
    t_def_list @ [t_fun], closure

  and expressions env = function
    | [] ->
       [], []
    | e :: es ->
       let efs, es = expressions env es in
       let fs, e = expression env e in
       fs @ efs, e :: es

  and literal = function
    | S.LInt x -> T.LInt x
    | S.LString s -> T.LString s
    | S.LChar c -> T.LChar c

  and identifier (S.Id x) = T.Id x

  and function_identifier (S.Id x) = T.FunId x

  in
  program env p
