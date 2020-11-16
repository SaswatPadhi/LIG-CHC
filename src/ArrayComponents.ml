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

let equality = [
  {
    name = "equal";
    codomain = Type.BOOL;
    domain = Type.[ARRAY (TVAR 1, TVAR 2); ARRAY (TVAR 1, TVAR 2)];
    is_argument_valid = (function
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
                                       (shrink b_elems))));
    to_string = (fun [@warning "-8"] [a ; b] -> "(= " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let reads = [
  {
    name = "select";
    codomain = Type.TVAR 2;
    domain = Type.[ARRAY (TVAR 1, TVAR 2); TVAR 1];
    is_argument_valid = (function
                         | [FCall (comp, [a ; k1 ; _]) ; k2]
                           when String.equal comp.name "store"
                           -> k1 =/= k2
                         | _ -> true);
    evaluate = Value.(fun [@warning "-8"]
                      [Array (_, _, elems, default_val) ; key]
                      -> match List.Assoc.find elems ~equal:Value.equal key with
                         | None -> default_val
                         | Some value -> value);
    to_string = (fun [@warning "-8"] [a ; b] -> "(select " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let writes = [
  {
    name = "store";
    codomain = Type.(ARRAY (TVAR 1, TVAR 2));
    domain = Type.[ARRAY (TVAR 1, TVAR 2); TVAR 1; TVAR 2];
    is_argument_valid = (function
                         | _ -> true);
    evaluate = Value.(fun [@warning "-8"]
                      [Array (key_type, val_type, elems, default_val) ; key ; value]
                      -> Array (key_type, val_type, (key, value)::elems, default_val));
    to_string = (fun [@warning "-8"] [a ; b ; c] -> "(store " ^ a ^ " " ^ b ^ " " ^ c ^ ")");
    global_constraints = (fun _ -> [])
  } 
]

let forall = [
  {
    name = "forall";
    codomain = Type.BOOL;
    domain = Type.[INT; INT; GHOST 1];
    is_argument_valid = (function
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
    global_constraints = (fun _ -> [])
  }
]


let levels = [| equality ; reads ; writes ; forall|]
