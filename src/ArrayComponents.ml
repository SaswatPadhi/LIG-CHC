open Core

open Expr
open Utils

let shrink =
  List.dedup_and_stable_sort ~which_to_keep:`First
                             ~compare:(fun (k1,_) (k2,_) -> Value.compare k1 k2)


(* match ghost variables to substitute for forall_var *)
let get_unghosted_expr (expr: string) (subst: string) : string = 
  let regex = Str.regexp "ghost_[^ ]* " in
  Str.global_substitute regex (fun _ -> subst) expr

let equality_symbol: string = "="
let equality = [
  {
    (MakeComponent.binary ~symbol:equality_symbol "equal") with
    codomain = Type.BOOL;
    domain = Type.[ARRAY (TVAR 1, TVAR 2); ARRAY (TVAR 1, TVAR 2)];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> true);
    evaluate = Value.(fun [@warning "-8"]
                      [ Array (a_key_type, a_val_type, a_elems, a_default_val)
                      ; Array (b_key_type, b_val_type, b_elems, b_default_val) ]
                      -> Value.Bool (
                           (Type.equal a_key_type b_key_type) &&
                           (Type.equal a_val_type b_val_type) &&
                           (Value.equal a_default_val b_default_val) &&
                           (List.equal (Tuple.T2.equal ~eq1:Value.equal ~eq2:Value.equal)
                                       (shrink a_elems)
                                       (shrink b_elems))))
  }
]

let reads = equality @ [
  {
    (MakeComponent.binary "select") with
    codomain = Type.TVAR 2;
    domain = Type.[ARRAY (TVAR 1, TVAR 2); TVAR 1];
    check_arg_ASTs = (function
                         | [FCall (comp, [a ; k1 ; _]) ; k2]
                           when String.equal comp.name "store"
                           -> k1 =/= k2
                         | _ -> true);
    evaluate = Value.(fun [@warning "-8"]
                      [Array (_, _, elems, default_val) ; key]
                      -> match List.Assoc.find elems ~equal:Value.equal key with
                         | None -> default_val
                         | Some value -> value)
  }
]

let writes = reads @ [
  {
    MakeComponent.base with
    name = "store";
    codomain = Type.(ARRAY (TVAR 1, TVAR 2));
    domain = Type.[ARRAY (TVAR 1, TVAR 2); TVAR 1; TVAR 2];
    evaluate = Value.(fun [@warning "-8"]
                      [Array (key_type, val_type, elems, default_val) ; key ; value]
                      -> Array (key_type, val_type, (key, value)::elems, default_val));

    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(store " ^ a ^ " " ^ b ^ " " ^ c ^ ")")
  } ;
]

let bounded_int_quantifiers = writes @ [
  {
    MakeComponent.base with
    name = "bounded-int-forall";
    codomain = Type.(BOOL);
    domain = Type.[ARRAY (INT, TVAR 1); INT; INT; BOOL];
    check_arg_ASTs = (function
                           (* TODO: The following check could be made tighter:
                            * We should check that the last arg (the predicate)
                            * uses the array (arg 1) *)
                         | (Var _) :: _ -> true
                         | _ -> false);
    callable_args = [ (4, Expr.ghost_variable_name, INT, BOOL) ];
    evaluate = Value.(fun [@warning "-8"]
                      [Array (INT, INT, elems, default_val) ; (Int lb) ; (Int ub) ; Fun_ (INT, BOOL, pred)]
                      -> let idx_range = List.range ~stride:1 ~start:`inclusive ~stop:`inclusive lb ub
                          in Bool (List.for_all
                               idx_range
                               ~f:(fun key -> match List.Assoc.find elems ~equal:Value.equal (Int key) with
                                              | None -> equal (pred default_val) (Bool true)
                                              | Some value -> equal (pred value) (Bool true))));
    to_string = (fun [@warning "-8"] [arr_name ; lb ; ub ; pred]
                 -> "(forall ((" ^ Expr.ghost_variable_name ^ " Int)) (=> (and " ^ lb ^ " " ^ ub ^ ") " ^ pred ^ "))")
  }
]

let levels = [| equality ; reads ; writes (* *; bounded_int_quantifiers *) |]

let forall = [
  {
    name = "forall";
    codomain = Type.BOOL;
    domain = Type.[INT; INT; GHOST 1];
    check_arg_ASTs = (function
                          | _ -> true);
    evaluate = Value.(fun [@warning "-8"]
                      [ left_bound ; right_bound ; expr ]
                      -> Value.Bool (
                            (* TODO check array bounds *)
                            true
                            (* List.for_all ~f:(fun [@warning "-8"] b -> expr b)) *)
                      ));
    to_string = (fun [@warning "-8"] [left ; right ; array_expr] 
      (* generate randome string for quantified variable __FORALL_VAR_ghost_random_nr *)
      -> begin 
        let forall_var = Utils.get_fresh_var () in
        let unghosted_expr = get_unghosted_expr array_expr forall_var in
        
        "(forall " ^ "((" ^ forall_var ^ "Int))" ^ " (=>" ^ 
          "(and (<= " ^ left ^ " " ^ forall_var ^ ") (<= " ^ forall_var ^ " " ^ right ^ "))" ^
          "( " ^ unghosted_expr ^ ")" ^   
          "))"
        end );
      (* TODO: 
            1. how do I get an expression with a hole in it here?
            2. how do I know which array to use with forall_var as index, and how can I get it given a ghost variable
        *)
  }
]