open Position
open Error
open HopixAST

(** [error pos msg] reports execution error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of Hopix evaluates into a [value].

   The [value] type is not defined here. Instead, it will be defined
   by instantiation of following ['e gvalue] with ['e = environment].
   Why? The value type and the environment type are mutually recursive
   and since we do not want to define them simultaneously, this
   parameterization is a way to describe how the value type will use
   the environment type without an actual definition of this type.

*)
type 'e gvalue =
  | VInt       of Mint.t
  | VChar      of char
  | VString    of string
  | VUnit
  | VTagged    of constructor * 'e gvalue list
  | VTuple     of 'e gvalue list
  | VRecord    of (label * 'e gvalue) list
  | VLocation  of Memory.location
  | VClosure   of 'e * pattern located * expression located
  | VPrimitive of string * ('e gvalue Memory.t -> 'e gvalue -> 'e gvalue)

(** Two values for booleans. *)
let ptrue  = VTagged (KId "True", [])
let pfalse = VTagged (KId "False", [])

(**
    We often need to check that a value has a specific shape.
    To that end, we introduce the following coercions. A
    coercion of type [('a, 'e)] coercion tries to convert an
    Hopix value into a OCaml value of type ['a]. If this conversion
    fails, it returns [None].
*)

type ('a, 'e) coercion = 'e gvalue -> 'a option
let fail = None
let ret x = Some x
let value_as_int      = function VInt x -> ret x | _ -> fail
let value_as_char     = function VChar c -> ret c | _ -> fail
let value_as_string   = function VString s -> ret s | _ -> fail
let value_as_tagged   = function VTagged (k, vs) -> ret (k, vs) | _ -> fail
let value_as_record   = function VRecord fs -> ret fs | _ -> fail
let value_as_location = function VLocation l -> ret l | _ -> fail
let value_as_closure  = function VClosure (e, p, b) -> ret (e, p, b) | _ -> fail
let value_as_primitive = function VPrimitive (p, f) -> ret (p, f) | _ -> fail
let value_as_bool = function
  | VTagged (KId "True", []) -> true
  | VTagged (KId "False", []) -> false
  | _ -> assert false

(**
   It is also very common to have to inject an OCaml value into
   the types of Hopix values. That is the purpose of a wrapper.
 *)
type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x
let bool_as_value b = if b then ptrue else pfalse

(**

  The flap toplevel needs to print the result of evaluations. This is
   especially useful for debugging and testing purpose. Do not modify
   the code of this function since it is used by the testsuite.

*)
let print_value m v =
  (** To avoid to print large (or infinite) values, we stop at depth 5. *)
  let max_depth = 5 in

  let rec print_value d v =
    if d >= max_depth then "..." else
      match v with
        | VInt x ->
          Mint.to_string x
        | VChar c ->
          "'" ^ Char.escaped c ^ "'"
        | VString s ->
          "\"" ^ String.escaped s ^ "\""
        | VUnit ->
          "()"
        | VLocation a ->
          print_array_value d (Memory.dereference m a)
        | VTagged (KId k, []) ->
          k
        | VTagged (KId k, vs) ->
          k ^ print_tuple d vs
        | VTuple (vs) ->
           print_tuple d vs
        | VRecord fs ->
           "{"
           ^ String.concat ", " (
                 List.map (fun (LId f, v) -> f ^ " = " ^ print_value (d + 1) v
           ) fs) ^ "}"
        | VClosure _ ->
          "<fun>"
        | VPrimitive (s, _) ->
          Printf.sprintf "<primitive: %s>" s
    and print_tuple d vs =
      "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
    and print_array_value d block =
      let r = Memory.read block in
      let n = Mint.to_int (Memory.size block) in
      "[ " ^ String.concat ", " (
                 List.(map (fun i -> print_value (d + 1) (r (Mint.of_int i)))
                         (ExtStd.List.range 0 (n - 1))
               )) ^ " ]"
  in
  print_value 0 v

let print_values m vs =
  String.concat "; " (List.map (print_value m) vs)

module Environment : sig
  (** Evaluation environments map identifiers to values. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x v] extends [env] with a binding from [x] to [v]. *)
  val bind    : t -> identifier -> t gvalue -> t

  (** [update pos x env v] modifies the binding of [x] in [env] so
      that [x ↦ v] ∈ [env]. *)
  val update  : Position.t -> identifier -> t -> t gvalue -> unit

  (** [lookup pos x env] returns [v] such that [x ↦ v] ∈ env. *)
  val lookup  : Position.t -> identifier -> t -> t gvalue

  (** [UnboundIdentifier (x, pos)] is raised when [update] or
      [lookup] assume that there is a binding for [x] in [env],
      where there is no such binding. *)
  exception UnboundIdentifier of identifier * Position.t

  (** [last env] returns the latest binding in [env] if it exists. *)
  val last    : t -> (identifier * t gvalue * t) option

  (** [print env] returns a human readable representation of [env]. *)
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e

end

(**
    We have everything we need now to define [value] as an instantiation
    of ['e gvalue] with ['e = Environment.t], as promised.
*)
type value = Environment.t gvalue

(**
   The following higher-order function lifts a function [f] of type
   ['a -> 'b] as a [name]d Hopix primitive function, that is, an
   OCaml function of type [value -> value].
*)
let primitive name ?(error = fun () -> assert false) coercion wrapper f
: value
= VPrimitive (name, fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}

type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    let error m v =
      Printf.eprintf
        "Invalid arguments for `%s': %s\n"
        name (print_value m v);
      assert false (* By typing. *)
    in
    VPrimitive (name, fun m -> function
      | VInt x ->
         VPrimitive (name, fun m -> function
         | VInt y -> out (op x y)
         | v -> error m v)
      | v -> error m v)
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v))
      x l
  in
  (* Define arithmetic binary operators. *)
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Mint.(
    [ ("`+`", add); ("`-`", sub); ("`*`", mul); ("`/`", div) ]
  ) in
  (* Define arithmetic comparison operators. *)
  let cmparith name = intbin name bool_as_value in
  let cmparithops =
    [ ("`=?`", ( = ));
      ("`<?`", ( < ));
      ("`>?`", ( > ));
      ("`>=?`", ( >= ));
      ("`<=?`", ( <= )) ]
  in
  let boolbin name out op =
    VPrimitive (name, fun _ x -> VPrimitive (name, fun _ y ->
        out (op (value_as_bool x) (value_as_bool y))))
  in
  let boolarith name = boolbin name (fun x -> if x then ptrue else pfalse) in
  let boolarithops =
    [ ("`||`", ( || )); ("`&&`", ( && )) ]
  in
  let generic_printer =
    VPrimitive ("print", fun m v ->
      output_string stdout (print_value m v);
      flush stdout;
      VUnit
    )
  in
  let print s =
    output_string stdout s;
    flush stdout;
    VUnit
  in
  let print_int =
    VPrimitive  ("print_int", fun _ -> function
      | VInt x -> print (Mint.to_string x)
      | _ -> assert false (* By typing. *)
    )
  in
  let print_string =
    VPrimitive  ("print_string", fun _ -> function
      | VString x -> print x
      | _ -> assert false (* By typing. *)
    )
  in
  let bind' x w env = Environment.bind env (Id x) w in
  Environment.empty
  |> bind_all binarith binarithops
  |> bind_all cmparith cmparithops
  |> bind_all boolarith boolarithops
  |> bind' "print"        generic_printer
  |> bind' "print_int"    print_int
  |> bind' "print_string" print_string
  |> bind' "true"         ptrue
  |> bind' "false"        pfalse
  |> bind' "nothing"      VUnit

let initial_runtime () = {
  memory      = Memory.create (640 * 1024 (* should be enough. -- B.Gates *));
  environment = primitives;
}

let rec evaluate runtime ast =
  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)

(** [definition pos runtime d] evaluates the new definition [d]
    into a new runtime [runtime']. In the specification, this
    is the judgment:

                        E, M ⊢ dv ⇒ E', M'

*)

and definition runtime d = match d.value with
  | DefineValue vd -> value_definition runtime.environment runtime.memory vd
  | _ -> runtime (* we ignore types *)

and value_definition environment memory = function
  | SimpleValue (id, _, e) ->
    let v = expression' environment memory e in
    { memory = memory; environment = bind_id environment id v }
  | RecFunctions fd_list ->
    let env' = rec_functions environment fd_list in
    { memory = memory; environment = env' }

and rec_functions environment fd_list =
  (* we bind each id of the mutualy recursive functions to a VUnit in the same environment *)
  let environment = List.fold_left (
      fun env (id, _, _) ->
        (bind_id env id VUnit)
    ) environment fd_list
  in
  (* evaluate each FunctionDefinition into their VClosure and associate them to their respective id *)
  let vclosure_list = List.map (
      fun (id, _, FunctionDefinition(p, e)) ->
        (id, VClosure (environment, p, e))
    ) fd_list
  in
  (* finally the modified environment is updated with the value of each closure *)
  let rec update_env environment = function
    | (id, vclosure) :: tl ->
      Environment.update id.position id.value environment vclosure;
      update_env environment tl
    | [] -> environment
  in
  update_env environment vclosure_list

(* returns the extended environment after binding the identifier id to the value v *)
and bind_id env id v =
  Environment.bind env id.value v

and expression' environment memory e =
  expression (position e) environment memory (value e)

(** [expression pos runtime e] evaluates into a value [v] if

                          E, M ⊢ e ⇓ v, M'

   and E = [runtime.environment], M = [runtime.memory].
*)

and expression _ environment memory = function
  | Literal l -> literal (l.value)
  | Variable (x, _) -> var_in_env environment x
  | Tagged (c, _, e_list) -> VTagged (c.value, evaluate_expression_list environment memory e_list)
  | Tuple e_list -> VTuple (evaluate_expression_list environment memory e_list)
  | Record (le_list, _) -> VRecord (evaluate_label_expression_list environment memory le_list)
  | Field (e, l, _) -> evaluate_field environment memory e l
  | Sequence e_list ->
    let v_list = evaluate_expression_list environment memory e_list in
    List.fold_left (fun _ x -> x) (List.hd v_list) v_list
  | Define (vd, e) ->
    let runtime' = value_definition environment memory vd in
    expression' runtime'.environment runtime'.memory e
  | Apply (ef, ea) -> apply environment memory ef ea
  | Ref e ->
    let v = expression' environment memory e in
    VLocation (Memory.allocate memory Mint.one v)
  | Read e -> evaluate_read environment memory e
  | TypeAnnotation _ -> VUnit
  | Assign(e1,e2) -> assign_test environment memory e1 e2
  | Case (e, br) -> case_test environment memory e br
  | IfThenElse (e_cond, e_true, e_false) -> if_then_else environment memory e_cond e_true e_false
  | While(eb, e) -> while_test environment memory eb e
  | For(x, e1, e2, e) -> for_test environment memory x e1 e2 e
  | Fun (FunctionDefinition (p, e)) -> VClosure (environment, p, e)

and literal = function
  | LInt n -> VInt n
  | LChar c -> VChar c
  | LString s -> VString s

and var_in_env environment x =
  Environment.lookup (x.position) (x.value) environment

and evaluate_expression_list environment memory e_list =
  List.map (expression' environment memory) e_list

and evaluate_label_expression_list environment memory le_list =
  List.map (fun (l, e) -> (l.value, expression' environment memory e)) le_list

and evaluate_field environment memory e l =
  let v = expression' environment memory e in
  match v with
  | VRecord lv_list -> List.assoc l.value lv_list
  | _ -> assert false

and apply environment memory ef ea =
  let vf = expression' environment memory ef in
  let va = expression' environment memory ea in
  match vf with
  | VPrimitive (_, f) -> f memory va
  | VClosure (env2, p, e) ->
    (
    match evaluate_pattern env2 p.value va with
    | Some env3 -> expression' env3 memory e
    | None -> failwith "expected a pattern in the function"
  )
  | _ -> failwith "expected a function in the left element of an apply"

and evaluate_read environment memory e =
  match value_as_location (expression' environment memory e) with
  | Some l ->
    let block = Memory.dereference memory l in
    Memory.read block Int64.zero
  | None -> failwith "read error"

and if_then_else environment memory e_cond e_true e_false =
  let v_cond = value_as_bool (expression' environment memory e_cond) in
  if v_cond then
    expression' environment memory e_true
  else
    expression' environment memory e_false

and evaluate_pattern environment pattern e =
  match pattern, e with
  | PVariable id, _ -> Some (bind_id environment id e)
  | PWildcard, _ -> Some (environment)
  | PLiteral l, _ -> match_litteral e l environment
  | PTuple patterns, VTuple values -> match_tuple environment patterns values
  | PRecord(fields, _), VRecord(values) -> match_record environment fields values
  | PTaggedValue(cstr, _, pattern_list), VTagged(cstr1, v) -> match_TV environment cstr pattern_list cstr1 v
  | POr patterns, _ -> match_disjonctions environment patterns e
  | PAnd patterns, _ -> match_conjonctions environment patterns e
  | _ -> None

and match_litteral e l environment =
  match e, l.value with
  | VInt i1, LInt i2 when i1 = i2 -> Some (environment)
  | VString s1, LString s2 when s1 = s2 -> Some (environment)
  | VChar c1, LChar c2 when c1 = c2 -> Some (environment)
  | _ -> None

and match_tuple env ps vs =
  match ps, vs with
  | [], [] -> Some env
  | p :: ps', v :: vs' ->
    (match evaluate_pattern env p.value v with
      | Some updated_env -> match_tuple updated_env ps' vs'
      | None -> None)
  | _ -> None

and match_record environment fields values =
  let evaluate_field env (label_located, pattern) =
    match List.assoc_opt label_located.value values with
    | Some v -> (
        match evaluate_pattern env pattern.value v with
        | Some updated_env -> Some updated_env
        | None -> None  (* La correspondance pour ce champ a échoué *)
        )
    | None -> None  (* Le champ n'est pas présent dans l'enregistrement *)
    in
    (* On passe en revue tous les champs de l'enregistrement *)
    List.fold_left (fun env field -> match env with
      | Some current_env -> evaluate_field current_env field
      | None -> None)
      (Some environment)
      fields

and match_TV environment cstr pattern_list cstr1 v =
 let pos_cstr = cstr.value in
 match pos_cstr, cstr1 with
 | KId _, KId _ when pos_cstr = cstr1 -> match_tuple environment pattern_list v
 | _ -> None

and match_disjonctions env patterns e =
  let rec disjonction_aux env = function
      | [] -> None
      | pattern :: rest ->
        match evaluate_pattern env pattern.value e with
        | Some env' -> Some env'
        | None -> disjonction_aux env rest
  in disjonction_aux env patterns

and match_conjonctions env patterns e =
  let rec evaluate_conjunction env = function
    | [] -> Some env
    | pattern :: rest ->
      match evaluate_pattern env pattern.value e with
      | Some env' -> evaluate_conjunction env' rest
      | None -> None
  in evaluate_conjunction env patterns

and evaluate_branch environment memory caseExpression = function
  | Branch (pattern, pExpr) ->
    match evaluate_pattern environment (pattern.value) caseExpression with
    | Some env' ->
      Some (expression' env' memory pExpr)
    | _ -> None

and case_test environment memory e br =
  let v = expression' environment memory e in
  let result = List.find_map (
      fun branch ->
        evaluate_branch environment memory v (Position.value branch)
    ) br
  in
  match result with
  | Some x -> x
  | None -> failwith "incorrect match"

and while_test environment memory eb e =
  let rec while_aux () =
    if value_as_bool (expression' environment memory eb) then
      (ignore (expression' environment memory e); while_aux())
    else
      VUnit
  in
  while_aux ()

and assign_test environment memory e1 e2 =
  let value = expression' environment memory e2 in
  match value_as_location (expression' environment memory e1) with
  | Some l -> let block = Memory.dereference memory l in
    Memory.write block Int64.zero value;
    VUnit
  | None -> failwith "Erreur"

and incrementation = function
  | VInt x -> VInt (Int64.add x (Int64.one))
  | _ -> assert false

and evalInt environment memory id =
  match value_as_int (expression' environment memory id) with
    | Some x -> x
    | _ -> assert false

and for_test environment memory vlr e1 e2 e =
  let n2 = VInt (evalInt environment memory e2) in
  let rec loop env =
    let n1 = var_in_env env vlr in
    if n1 <= n2 then
      begin
        ignore(expression' env memory e);
        Environment.update vlr.position vlr.value env (incrementation n1);
        loop env
      end
    else
      VUnit
  in loop (bind_id environment vlr (VInt (evalInt environment memory e1)))

(** This function returns the difference between two runtimes. *)
and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

(** This function displays a difference between two runtimes. *)
let print_observable (_ : runtime) observation =
  Environment.print observation.new_memory observation.new_environment
