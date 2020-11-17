open Core

open Expr
open Utils

let shrink =
  List.dedup_and_stable_sort ~which_to_keep:`First
                             ~compare:(fun (k1,_) (k2,_) -> Value.compare k1 k2)

let equality = [
  {
    (MakeComponent.binary ~symbol:"=" "equal") with
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
