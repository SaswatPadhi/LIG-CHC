open Base

open Expr

let all_qf = [
  {
    (MakeComponent.unary "len") with
    codomain = Type.INT;
    domain = Type.[LIST (TVAR 0)];
    check_arg_ASTs = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)] -> Int (List.length l))
  } ;
  {
    (MakeComponent.unary "hd") with
    codomain = Type.TVAR 1;
    domain = Type.[LIST (TVAR 1)];
    check_arg_ASTs = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)] -> List.hd_exn l)
  } ;
  {
    (MakeComponent.unary "tl") with
    codomain = Type.(LIST (TVAR 1));
    domain = Type.[LIST (TVAR 1)];
    check_arg_ASTs = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (t,l)] -> List (t, (List.tl_exn l)))
  }
]

let all = all_qf @ [
  {
    (MakeComponent.unary "all") with
    codomain = Type.BOOL;
    domain = Type.[LIST BOOL];
    check_arg_ASTs = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)]
                      -> Bool (List.for_all l ~f:(fun [@warning "-8"] (Bool b) -> b)))
  } ;
  {
    (MakeComponent.unary "any") with
    codomain = Type.BOOL;
    domain = Type.[LIST BOOL];
    check_arg_ASTs = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)]
                      -> Bool (List.exists l ~f:(fun [@warning "-8"] (Bool b) -> b)))
  }
]

let map_transform_unary (component : component) : component =
  match component.domain with
  | [dom] -> let name = "map-" ^ component.name
              in { (MakeComponent.unary name) with
                   codomain = Type.LIST component.codomain;
                   domain = Type.[LIST dom];
                   check_arg_ASTs = (function _ -> true);
                   evaluate = Value.(fun [@warning "-8"] [ List (_,l) ]
                                     -> List ((Type.LIST component.codomain),
                                              (List.map l ~f:(fun e -> component.evaluate [e]))))
                  }
  | l -> raise (Exceptions.Transformation_Exn (
                  "Cannot transform a " ^ (Int.to_string (List.length l)) ^ "-ary component " ^ component.name))

let all_transformed_int_unary =
  all @ (List.filter_map (BooleanComponents.all @ IntegerComponents.polynomials)
                         ~f:(fun c -> try Some (map_transform_unary c)
                                      with _ -> None))

(* FIXME: We create two map versions of each binary component:
          One that fixes the first argument and another that fixes the second.
          However, these would be equivalent for commutative components;
          so may be keep a `commutative` attribute for each component,
          or, implement a better, more general strategy for component transformation. *)

let map_transform_binary (component : component) : component list =
  match component.domain with
  | [d1 ; d2]
    -> let nameL = "map-fixL-" ^ component.name in
       let nameR = "map-fixR-" ^ component.name
        in [{
              (MakeComponent.binary nameR) with
              codomain = Type.LIST component.codomain;
              domain = Type.[LIST d1 ; d2];
              check_arg_ASTs = (function _ -> true);
              evaluate = Value.(fun [@warning "-8"] [List (_, x) ; y]
                                -> List (component.codomain, (List.map x ~f:(fun e -> component.evaluate [e ; y]))));
              global_constraints = component.global_constraints
            } ;
            {
              (MakeComponent.binary nameL) with
              codomain = Type.LIST component.codomain;
              domain = Type.[d1 ; LIST d2];
              check_arg_ASTs = (function _ -> true);
              evaluate = Value.(fun [@warning "-8"] [x ; List (_, y)]
                                -> List (component.codomain, (List.map y ~f:(fun e -> component.evaluate [x ; e]))));
              global_constraints = component.global_constraints
            }]
  | l -> raise (Exceptions.Transformation_Exn (
                  "Cannot transform a " ^ (Int.to_string (List.length l)) ^
                  "-ary component " ^ component.name))

let all_transformed_int_binary =
  all_transformed_int_unary @
  List.(concat (filter_map (BooleanComponents.all @ IntegerComponents.polynomials)
                           ~f:(fun c -> try Some (map_transform_binary c)
                                        with _ -> None)))

let levels = [| all_qf ; all ; all_transformed_int_unary ; all_transformed_int_binary |]
