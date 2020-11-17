open Base

open Expr

let pos_div x y = (x - (x % y)) / y

let equality = [
  {
    (MakeComponent.binary ~symbol:"=" "int-eq") with
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Bool Int.(x = y))
  }
]

let intervals = equality @ [
   {
    (MakeComponent.binary ~symbol:">=" "int-geq") with
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Bool Int.(x >= y))
  } ;
  {
    (MakeComponent.binary ~symbol:"<=" "int-leq") with
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Bool Int.(x <= y))
  } ;
  {
    (MakeComponent.binary ~symbol:"<" "int-lt") with
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Bool Int.(x < y))
  } ;
  {
    (MakeComponent.binary ~symbol:">" "int-gt") with
    codomain = Type.BOOL;
    domain = Type.[INT; INT];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Bool Int.(x > y))
  }
]

let octagons = intervals @ [
  {
    (MakeComponent.binary ~symbol:"+" "int-add") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [x ; FCall (comp, [_ ; y])]
                                 when String.equal comp.name "int-sub"
                                 -> x =/= y && (x =/= Const (Int 0))
                               | [FCall (comp, [_ ; x]) ; y]
                                 when String.equal comp.name "int-sub"
                                 -> x =/= y && (y =/= Const (Int 0))
                               | [x ; y] -> (x =/= Const (Int 0)) && (y =/= Const (Int 0))
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Int (x + y))
  } ;
  {
    (MakeComponent.binary ~symbol:"-" "int-sub") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [(FCall (comp, [x ; y])) ; z]
                                 when String.equal comp.name "int-add"
                                 -> x =/= z && y =/= z && (z =/= Const (Int 0))
                               | [(FCall (comp, [x ; _])) ; y]
                                 when String.equal comp.name "int-sub"
                                 -> x =/= y && (y =/= Const (Int 0))
                               | [x ; (FCall (comp, [y ; _]))]
                                 when (String.equal comp.name "int-sub" || String.equal comp.name "int-add")
                                 -> x =/= y
                               | [x ; y] -> (x =/= y)
                                         && (x =/= Const (Int 0)) && (y =/= Const (Int 0))
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Int (x - y))
  }
]

let polyhedra = octagons @ [
  {
    (MakeComponent.binary ~symbol:"*" "int-lin-mult") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [x ; y]
                                 -> (x =/= Const (Int 0)) && (x =/= Const (Int 1))
                                 && (y =/= Const (Int 0)) && (y =/= Const (Int 1))
                                 && (is_constant x || is_constant y)
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Int (x * y))
  }
]

let polynomials = polyhedra @ [
  {
    (MakeComponent.binary ~symbol:"*" "int-nonlin-mult") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [x ; y] -> not (is_constant x || is_constant y)
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Int x ; Int y] -> Int (x * y))
  }
]

let peano = polynomials @ [
  {
    (MakeComponent.binary ~symbol:"div" "int-div") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [x ; y] -> x =/= y
                                         && (x =/= Const (Int 0)) && (x =/= Const (Int 1))
                                         && (y =/= Const (Int 0)) && (y =/= Const (Int 1))
                               | _ -> false);
    evaluate = Value.(function [@warning "-8"]
                      [Int x ; Int y] when Int.(y <> 0)
                      -> Int (pos_div x y));
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  } ;
  {
    (MakeComponent.binary ~symbol:"mod" "int-mod") with
    codomain = Type.INT;
    domain = Type.[INT; INT];
    check_arg_ASTs = Value.(function
                               | [x ; y] -> x =/= y
                                         && (x =/= Const (Int 0)) && (x =/= Const (Int 1))
                                         && (y =/= Const (Int 0)) && (y =/= Const (Int 1))
                               | _ -> false);
    evaluate = Value.(function [@warning "-8"]
                      [Int x ; Int y] when Int.(y <> 0)
                      -> Int (x % y));
    global_constraints = (fun [@warning "-8"] [_ ; b] -> ["(not (= 0 " ^ b ^ "))"]);
  }
]

let linear_levels = [| equality ; intervals ; octagons ; polyhedra |]
let non_linear_levels = [| equality ; intervals ; octagons ; polyhedra ; polynomials ; peano |]
