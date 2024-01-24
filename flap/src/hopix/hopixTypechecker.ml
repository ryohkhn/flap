(** This module implements a bidirectional type checker for Hopix. *)

open HopixAST
open HopixTypes

(** Error messages *)

let check_equal_types pos ~expected ~given =
  if expected <> given
  then
    Printf.sprintf "Type mismatch.\nExpected:\n  %s\nGiven:\n  %s"
      (string_of_aty expected) (string_of_aty given)
    |> type_error pos

(** Linearity-checking code for patterns *)

let rec destruct_function_type_nth n = function
  | ATyArrow (ins, out) when n > 0 ->
     let ins', out = destruct_function_type_nth (n - 1) out in
     (ins :: ins', out)
  | ty ->
     ([], ty)

let rec check_pattern_linearity
  : identifier list -> pattern Position.located -> identifier list
  = fun vars Position.{ value; position; } ->
    match value with
    | PWildcard -> vars
    | PLiteral _ -> vars
    | PVariable id ->
      let x = Position.value id in
      if List.mem x vars then
        type_error position "The variable x has already appeared in this pattern."
      else
        x :: vars
    | PRecord(record_fields, ty_list) ->
      List.fold_left (fun acc (_, pat) ->
        check_pattern_linearity acc pat
      ) vars record_fields
    | PTuple patterns | POr patterns | PAnd patterns ->
      List.fold_left (fun acc pat ->
          check_pattern_linearity acc pat
        ) vars patterns
    | PTypeAnnotation (pat, _) -> check_pattern_linearity vars pat
    | PTaggedValue(_, _, pat) -> List.fold_left (fun acc pat ->
        check_pattern_linearity acc pat
      ) vars pat
    | _ -> failwith "not implemented yet"

(** Type-checking code *)

let result_of_function_type x aty =
  destruct_function_type (Position.position x) aty
  |> fun (_, result) -> result

let check_type_scheme :
  HopixTypes.typing_environment ->
  Position.t ->
  HopixAST.type_scheme ->
  HopixTypes.aty_scheme * HopixTypes.typing_environment
  = fun env pos (ForallTy (ts, ty)) ->
    let ts = List.map Position.value ts in
    let tenv = bind_type_variables pos env ts in
    Scheme (ts, internalize_ty tenv ty), tenv

let synth_literal :
  HopixAST.literal -> HopixTypes.aty
  = fun l ->
    match l with
    | LInt _ -> hint
    | LString _ -> hstring
    | LChar _ -> hchar

let lookup_type_scheme_of_identifier' pos id env =
    try
      lookup_type_scheme_of_identifier pos id env
    with Unbound (pos, bind) ->
      Printf.sprintf "Unbound %s." (string_of_binding bind)
      |> type_error pos

let lookup_type_scheme_of_label' pos label env =
    try
      lookup_type_scheme_of_label pos label env
    with Unbound (pos, bind) ->
      Printf.sprintf "Unbound %s." (string_of_binding bind)
      |> type_error pos

let lookup_type_constructor_of_label' pos label env =
    try
      lookup_type_constructor_of_label pos label env
    with Unbound (pos, bind) ->
      Printf.sprintf "Unbound %s." (string_of_binding bind)
      |> type_error pos

let lookup_type_scheme_of_constructor' pos constr env =
    try
      lookup_type_scheme_of_constructor pos constr env
    with Unbound (pos, bind) ->
      Printf.sprintf "Unbound %s." (string_of_binding bind)
      |> type_error pos

let instantiate_type_scheme' :
  Position.t ->
  HopixTypes.aty_scheme ->
  HopixTypes.aty list ->
  HopixTypes.aty
  = fun pos scheme aty_list ->
    try
      instantiate_type_scheme scheme aty_list
    with
      InvalidInstantiation {expected = exp; given = giv;} ->
      Printf.sprintf "Invalid number of types in instantiation: %d given while %d were expected." giv exp
      |> type_error pos

let synth_variable :
  HopixTypes.typing_environment ->
  HopixAST.identifier Position.located ->
  HopixAST.ty Position.located list option ->
  HopixTypes.aty
  = fun env id ty_list ->
    let scheme = lookup_type_scheme_of_identifier' (Position.position id) (Position.value id) env in
    match ty_list with
    | Some ty_list ->
        let aty_list = List.map (fun ty -> internalize_ty env ty) ty_list in
        instantiate_type_scheme' (Position.position id) scheme aty_list
    | None ->
      let Scheme (tv_list, aty) = scheme in
      if List.length tv_list = 0 then
        aty
      else
        Printf.sprintf "Ill-formed type: anotation of type required for a variable."
        |> type_error (Position.position id)


let make_fresh_name_generator () =
  let r = ref (-1) in
  let mangle () =
    if !r > 26 then
      "a" ^ string_of_int !r
    else
      String.make 1 (Char.(chr (code 'a' + !r)))
  in
  fun () ->
  incr r; TId ("`" ^ mangle ())

let fresh = make_fresh_name_generator ()

let rec check_pattern_linearity_tuple :
  identifier list -> pattern Position.located list -> identifier list
  = fun vars patterns ->
  List.fold_left (fun acc pat -> check_pattern_linearity acc pat) vars patterns

let rec check_pattern :
  HopixTypes.typing_environment ->
  HopixAST.pattern Position.located ->
  HopixTypes.aty ->
  HopixTypes.typing_environment
  = fun env Position.({ value = p; position = pos; } as pat) expected ->
    match p with
    | PLiteral l ->
      let literal_type = synth_literal l.value in
      check_equal_types pos ~expected:expected ~given:literal_type;
      env
    | PWildcard -> env
    | PVariable id ->
      (* (fun (Id s) -> print_string s) (Position.value id); *)
      let scheme = monomorphic_type_scheme expected in
      let res = check_pattern_linearity [] pat in
      bind_value (Position.value id) scheme env;

    | PRecord (record_fields, type_list_opt) ->
    (* record_fields est une liste de champs du motif d'enregistrement *)
    (* type_list_opt est une option de liste de types correspondants aux champs *)
    let type_list =
      match type_list_opt with
      | Some tl -> tl
      | None -> type_error pos "Missing type annotation for record fields."
    in
    (* Séparer les champs et les types pour les utiliser correctement dans List.combine *)
    let field_names, field_patterns = List.split record_fields in
    let _ = check_pattern_linearity_tuple [] field_patterns in
    let field_types, env' = List.fold_left
        (fun (types, env_acc) (field_name, field_pattern) ->
            let field_type, env'' = synth_pattern env_acc field_pattern in
            ((field_name, field_type) :: types, env''))
        ([], env)
        (List.combine field_names field_patterns)
    in
    let record_type = ATyCon (TCon "record", (List.map snd field_types)) in
    check_equal_types pos ~expected:record_type ~given:expected;
    env'

    | PTaggedValue (constructor, type_list_opt, pats) ->
     (* constructor est le constructeur associé au motif étiqueté *)
      (* type_list_opt est une option de liste de types correspondants aux sous-motifs *)
      let constructor_type = lookup_type_scheme_of_constructor' pos (Position.value constructor) env in
      let _ = check_pattern_linearity_tuple [] pats in
      (* Vérifie les sous-motifs et accumule l'environnement *)
      let type_list =
        match type_list_opt with
        | Some tl -> List.map (fun ty -> internalize_ty env ty) tl
        | None -> type_error pos "Missing type annotation for tagged value subpatterns."
      in
   let inst_type = instantiate_type_scheme' pos constructor_type type_list in
   check_equal_types pos ~expected:inst_type ~given:expected;
   (* Vérifie chaque sous-motif avec son type correspondant *)
    List.fold_left2
    (fun env_acc pat' expected_type ->
      check_pattern env_acc pat' expected_type)
    env
    pats
    type_list
    | PTuple p_list ->
      (* destructs the product aty and then checks each pattern associated with it's aty type *)
      destruct_product_type pos expected
      |> let res = check_pattern_linearity_tuple [] p_list in
      List.fold_left2 (fun env p aty ->
          check_pattern env p aty
        ) env p_list
    | POr patterns ->
    let res = check_pattern_linearity_tuple [] patterns in
    List.fold_left
        (fun env_acc pat' -> check_pattern env_acc pat' expected)
        env
        patterns
    | PAnd patterns ->
      let res = check_pattern_linearity_tuple [] patterns in
      List.fold_left
        (fun env_acc pat' -> check_pattern env_acc pat' expected)
        env
        patterns
    | _ ->
      let (aty, env') = synth_pattern env pat in
      check_equal_types pos ~expected:expected ~given:aty;
      env'

and synth_pattern :
  HopixTypes.typing_environment ->
  HopixAST.pattern Position.located ->
  HopixTypes.aty * HopixTypes.typing_environment
  = fun env (Position.{ value = p; position = pos; } as p') ->
    match p with
    | PWildcard -> type_error pos "Error PWildcard"
    | PLiteral l -> (synth_literal (Position.value l), env)
    | PVariable id -> type_error pos "Error PVariable"
    | PTypeAnnotation (p, ty) ->
      let expected_type = internalize_ty env ty in
      let env = check_pattern env p expected_type in
      (expected_type, env)
    | PTaggedValue(constructor, type_list_opt, pats) ->
    (* constructor est le constructeur associé au motif étiqueté *)
      (* type_list_opt est une option de liste de types correspondants aux sous-motifs *)
      let constructor_type = lookup_type_scheme_of_constructor' pos (Position.value constructor) env in
      let inst_type = instantiate_type_scheme' pos constructor_type [] in

      (* Synthétise les types des sous-motifs *)
      let (pat_types, env') = List.fold_left
          (fun (types, env_acc) pat' ->
              let pat_type, env'' = synth_pattern env_acc pat' in
              (pat_type :: types, env''))
          ([], env)
          pats
      in

      (* Vérifie que les types des sous-motifs correspondent à ceux spécifiés dans type_list_opt *)
      let type_list =
        match type_list_opt with
        | Some tl -> List.map (fun ty -> internalize_ty env ty) tl
        | None -> type_error pos "Missing type annotation for tagged value subpatterns."
      in
      List.iter2
          (fun expected_type given_type ->
              check_equal_types pos ~expected:expected_type ~given:given_type)
          type_list
          pat_types;

      (inst_type, env')

    | PRecord(_, _) -> type_error pos "Error PRecord"
    | PTuple pl ->  let tuple_types, env' = List.fold_left
                        (fun (types, env_acc) p' ->
                           let p_type, env'' = synth_pattern env_acc p' in
                           (p_type :: types, env''))
                        ([], env)
                        pl
      in
      (ATyTuple (List.rev tuple_types), env')
    | POr patterns -> type_error pos "Error POr"
    | PAnd patterns -> type_error pos "Error PAnd"
    | _ -> failwith "Error not Patterns"

let rec synth_expression :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env Position.{ value = e; position = pos; } ->
    match e with
    | Literal l ->
      synth_literal l.value
    | Variable (id, ty_list) ->
      synth_variable env id ty_list
    | Tagged (constr, ty_list, e_list) ->
      synth_tagged env constr ty_list e_list
    | Record (le_list, ty_list) ->
      synth_record env le_list ty_list
    | Field (e, label, ty_list) ->
      synth_field env e label ty_list
    | Tuple e_list ->
      synth_tuple env e_list
    | Sequence e_list ->
      synth_sequence env e_list
    | Define (vd, e) ->
      synth_define env vd e
    | Fun (FunctionDefinition (pat, e)) ->
      synth_fun env e pat
    | Apply (e1, e2) ->
      synth_apply env e1 e2
    | Ref e ->
      href (synth_expression env e)
    | Assign (e1, e2) ->
      synth_assign env e1 e2
    | Read e ->
      synth_read env e
    | Case (e, branch_list) ->
      synth_case env e branch_list
    | IfThenElse (e_cond, e_true, e_false) ->
      synth_if_then_else env e_cond e_true e_false
    | TypeAnnotation (e, ty) ->
      synth_annot env e ty
    | While(e_cond, e_body) ->
      synth_while env e_cond e_body
    | For(id, exp1, exp2, exp3) ->
      synth_for env id exp1 exp2 exp3

and check_expression :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixTypes.aty ->
  unit
  = fun env (Position.{ value = e; position = pos; } as exp) expected ->
    match e with
    | Fun (FunctionDefinition (p, e)) ->
      check_fun env e p expected;
    | Define (vd, e) ->
      check_define env vd e expected;
    | Case (e, branch_list) ->
      check_case env e branch_list expected;
    | _ ->
      let aty = synth_expression env exp in
      check_equal_types pos ~expected:expected ~given:aty

and synth_simple_val :
  HopixTypes.typing_environment ->
  HopixAST.identifier Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.typing_environment
  = fun env id e ->
    let scheme =
      synth_expression env e
      |> generalize_type env
    in
    bind_value (Position.value id) scheme env

and check_simple_val :
  HopixTypes.typing_environment ->
  HopixAST.identifier Position.located ->
  HopixAST.type_scheme Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.typing_environment
  = fun env id ts e ->
    let ForallTy(tvl, ty) = Position.value ts in
    let tvl = List.map (fun x -> Position.value x) tvl in
    (* checks that the type_scheme is well formed and
       verify that each aty is not free in the env *)
    let aty = internalize_ty env ty in
    check_expression env e aty;
    let scheme = Scheme (tvl, aty) in
    bind_value (Position.value id) scheme env

and check_rec_functions :
  HopixTypes.typing_environment ->
  HopixAST.function_definition HopixAST.polymorphic_definition list ->
  HopixTypes.typing_environment
  = fun env fd_list ->
    let env =
      List.fold_left (fun env (id, ts, _) ->
          match ts with
          | Some ts ->
            let ForallTy(tvl, ty) = Position.value ts in
            (* each type_variable needs to be bound to the environment *)
            let tvl = List.map (fun x -> Position.value x) tvl in
            (* we bind the type_variable list to a temporary environment
               to be able to internalize the provided type *)
            let env' = bind_type_variables (Position.position ty) env tvl in
            let aty = internalize_ty env' ty in
            let scheme = Scheme (tvl, aty) in
            bind_value (Position.value id) scheme env
          | None ->
            Printf.sprintf "Ill-formed type: type annotation is required for a recursive function."
            |> type_error (Position.position id)
        ) env fd_list
    in
    (* checks that each recursive function is correctly typed and
       bind the type_variable list to the function environment *)
    List.iter (fun (_, ts, FunctionDefinition(p, e)) ->
        match ts with
        | Some ts ->
          let ForallTy(tvl, ty) = Position.value ts in
          let tvl = List.map (fun x -> Position.value x) tvl in
          let env = bind_type_variables (Position.position ty) env tvl in
          let aty = internalize_ty env ty in
          check_fun env e p aty;
        | None -> ()
      ) fd_list;
    env

and check_value_definition :
  HopixTypes.typing_environment ->
  HopixAST.value_definition ->
  HopixTypes.typing_environment
  = fun env def ->
    match def with
    | SimpleValue (x, None, e) -> synth_simple_val env x e
    | SimpleValue (x, Some ts, e) -> check_simple_val env x ts e
    | RecFunctions fd_list -> check_rec_functions env fd_list

and synth_tagged :
  HopixTypes.typing_environment ->
  HopixAST.constructor Position.located ->
  HopixAST.ty Position.located list option ->
  HopixAST.expression Position.located list ->
  HopixTypes.aty
  = fun env constr ty_list e_list ->
    match ty_list with
    | Some ty_list ->
      let scheme = lookup_type_scheme_of_constructor' (Position.position constr) (Position.value constr) env in
      (* We substitute each aty into the env *)
      (* and get the maximally destructed function of the Tagged expression *)
      let aty =
        List.map (fun ty -> internalize_ty env ty) ty_list
        |> instantiate_type_scheme' (Position.position constr) scheme
      in
      let (left, result) = destruct_function_type_maximally (Position.position constr) aty in
      begin
        try
          List.iter2 (fun expected e -> check_expression env e expected) left e_list;
          result
        with _ ->
          (* If the number of expressions doesn't match *)
          (* the number of elements in the constructor we throw an error *)
          let smallest_list = min (List.length e_list) (List.length left) in
          let (_, result) = destruct_function_type_nth smallest_list aty in
          let e = (List.nth e_list (smallest_list - 1)) in
          let aty = synth_expression env e in
          check_equal_types (Position.position e) ~expected:aty ~given:result;
          aty
      end
    | None ->
      Printf.sprintf "Ill-formed type: type annotation is required for a constructor."
      |> type_error (Position.position constr)

and synth_tuple :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located list ->
  HopixTypes.aty
  = fun env e_list ->
    let aty_list = List.map (fun e -> synth_expression env e) e_list in
    ATyTuple aty_list

and synth_sequence :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located list ->
  HopixTypes.aty
  = fun env e_list ->
    match e_list with
    | []  -> hunit
    | [e] -> synth_expression env e
    | e::e_list ->
      check_expression env e hunit;
      synth_sequence env e_list

and synth_define :
  HopixTypes.typing_environment ->
  HopixAST.value_definition ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env vd e' ->
    let env = check_value_definition env vd in
    synth_expression env e'

and check_define :
  HopixTypes.typing_environment ->
  HopixAST.value_definition ->
  HopixAST.expression Position.located ->
  HopixTypes.aty ->
  unit
  = fun env vd e expected ->
    let env = check_value_definition env vd in
    check_expression env e expected;

and synth_fun :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.pattern Position.located ->
  HopixTypes.aty
  = fun env e p ->
    let (t, env') = synth_pattern env p in
    let t' = synth_expression env' e in
    ATyArrow (t, t')

and check_fun :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.pattern Position.located ->
  HopixTypes.aty ->
  unit
  = fun env e p expected ->
    match expected with
    | ATyArrow (t, t') ->
      let env = check_pattern env p t in
      check_expression env e t';
    | _ ->
      Printf.sprintf "Ill-formed type: This expression is not a lambda function."
      |> type_error (Position.position p)

and synth_apply :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env e1 e2 ->
    let e1_aty = synth_expression env e1 in
    match e1_aty with
    | ATyArrow (t1, t2) ->
      check_expression env e2 t1;
      t2
    | _ ->
      Printf.sprintf "This expression has type int which should be a function type."
      |> type_error (Position.position e1)

and synth_assign :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
= fun env e1 e2 ->
    let e1_aty =
      synth_expression env e1
      |> destruct_reference_type (Position.position e1)
    in
    check_expression env e2 e1_aty;
    hunit

and synth_read :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env e ->
    let e_aty = synth_expression env e in
    destruct_reference_type (Position.position e) e_aty

and synth_case :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.branch Position.located list ->
  HopixTypes.aty
  = fun env e branch_list ->
    let t' = synth_expression env e in
    (* Each branch's aty should match the aty of the first branch *)
    let Branch (_, e') = (Position.value (List.hd branch_list)) in
    let first_branch_aty = synth_expression env e' in
    List.iter (fun b ->
        let Branch (p, e) = (Position.value b) in
        let env = check_pattern env p t' in
        check_expression env e first_branch_aty;
    ) branch_list;
    first_branch_aty

and synth_if_then_else :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env e_cond e_true e_false ->
    let aty_cond = synth_expression env e_cond in
    check_equal_types (Position.position e_cond) ~expected:hbool ~given:aty_cond;
    let aty_true = synth_expression env e_cond in
    check_equal_types (Position.position e_true) ~expected:hunit ~given:aty_true;
    let aty_false = synth_expression env e_cond in
    check_equal_types (Position.position e_false) ~expected:hunit ~given:aty_false;
    hunit

and synth_annot :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.ty Position.located->
  HopixTypes.aty
  = fun env e ty ->
    let t = internalize_ty env ty in
    check_expression env e t;
    t

and check_case :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.branch Position.located list ->
  HopixTypes.aty ->
  unit
  = fun env e branch_list expected ->
    let t' = synth_expression env e in
    List.iter (fun b ->
        let Branch (p, e) = (Position.value b) in
        let env = check_pattern env p t' in
        check_expression env e expected;
    ) branch_list

and synth_record :
  HopixTypes.typing_environment ->
  (HopixAST.label Position.located * HopixAST.expression Position.located) list ->
  HopixAST.ty Position.located list option ->
  HopixTypes.aty
  = fun env le_list ty_list ->
    match ty_list with
    | Some ty_list ->
      (* we lookup the first label to get the associated type_constructor in the context *)
      let (label, _) = List.hd le_list in
      let tc, _, label_list =
        lookup_type_constructor_of_label' (Position.position label) (Position.value label) env
      in
      let aty_list = List.map (fun ty -> internalize_ty env ty) ty_list in
      (* we verify that each label associated to the type_constructor is provided *)
      List.iter (fun (l, _) ->
          if (not (List.mem (Position.value l) label_list)) then
            (
             Printf.sprintf "Ill-formed type: one or multiple elements of the record are missing."
             |> type_error (Position.position l)
           )
        ) le_list;
      check_record_expressions env le_list aty_list;
      ATyCon (tc, aty_list)
    | None ->
      let (_, e) = List.hd le_list in
      Printf.sprintf "Ill-formed type: anotation of type required for a variable."
      |> type_error (Position.position e)

and check_record_expressions :
  HopixTypes.typing_environment ->
  (HopixAST.label Position.located * HopixAST.expression Position.located) list ->
  HopixTypes.aty list ->
  unit
  = fun env le_list aty_list ->
    (* we lookup the type_scheme and substitute it by each aty in the env *)
    List.iter (fun (l, e) ->
        let scheme =
          lookup_type_scheme_of_label' (Position.position l) (Position.value l) env
        in
        instantiate_type_scheme' (Position.position l) scheme aty_list
        |> destruct_function_type (Position.position l)
        |> fun (_, right_aty) -> check_expression env e right_aty;
      ) le_list

and synth_field :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.label Position.located ->
  HopixAST.ty Position.located list option ->
  HopixTypes.aty
  = fun env e label ty_list ->
    let aty = synth_expression env e in
    match aty with
    | ATyCon (tc, tc_aty_list) ->
      (* we get the labels associated to the type_constructor *)
      let label_list = lookup_fields_of_type_constructor (Position.position e) tc env in
      let l = Label (Position.value label) in
      (* we verify that the field label is part of TCon labels *)
      if not (List.mem (Position.value label) label_list) then
        Printf.sprintf "Unbound %s." (string_of_binding l)
        |> type_error (Position.position label);
      verify_field_types env e label tc_aty_list ty_list
    | _ ->
      Printf.sprintf "Ill-formed type: the expression should be a constructor."
      |> type_error (Position.position e)

and synth_while :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env e_cond e_body ->
  let aty_cond = synth_expression env e_cond in
  check_equal_types (Position.position e_cond) ~expected:hbool ~given:aty_cond;
  synth_expression env e_body;

and synth_for :
  HopixTypes.typing_environment ->
  HopixAST.identifier Position.located ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixAST.expression Position.located ->
  HopixTypes.aty
  = fun env id e_start e_end e_body ->
  let start_type = synth_expression env e_start in
  check_equal_types (Position.position e_start) ~expected:hint ~given:start_type;
  let end_type = synth_expression env e_end in
  check_equal_types (Position.position e_end) ~expected:hint ~given:end_type;

  (*Ajout de l'id au contexte avec le type hint*)
  let env' = bind_value (Position.value id) (Scheme ([], hint)) env in

  let body_type = synth_expression env' e_body in
  check_equal_types (Position.position e_body) ~expected:hunit ~given:body_type;
  hunit

and verify_field_types :
  HopixTypes.typing_environment ->
  HopixAST.expression Position.located ->
  HopixAST.label Position.located ->
  HopixTypes.aty list ->
  HopixAST.ty Position.located list option ->
  HopixTypes.aty =
  fun env e label tc_aty_list ty_list ->
  let scheme =
    lookup_type_scheme_of_label' (Position.position label) (Position.value label) env
  in
  let Scheme (_, aty) = scheme in
  match ty_list with
  | Some ty_list ->
    let aty_list' = List.map (fun ty -> internalize_ty env ty) ty_list in
    (* we compare the provided type list to the type constructor type list *)
    List.iter2 (fun exp g ->
        check_equal_types (Position.position e) ~expected:exp ~given:g
      ) tc_aty_list aty_list';
    instantiate_type_scheme' (Position.position label) scheme tc_aty_list
    |> result_of_function_type label
  | None ->
    result_of_function_type label aty

let check_definition env = function
  | DefineValue vdef ->
     check_value_definition env vdef

  | DefineType (t, ts, tdef) ->
     let ts = List.map Position.value ts in
     HopixTypes.bind_type_definition (Position.value t) ts tdef env

  | DeclareExtern (x, tys) ->
     let tys, _ = Position.located_pos (check_type_scheme env) tys in
     HopixTypes.bind_value (Position.value x) tys env

let typecheck env program =
  List.fold_left
    (fun env d -> Position.located (check_definition env) d)
    env program

type typing_environment = HopixTypes.typing_environment

let initial_typing_environment = HopixTypes.initial_typing_environment

let print_typing_environment = HopixTypes.string_of_typing_environment
