open Base

open Expr

let all = [
  {
    (MakeComponent.unary "not") with
    codomain = Type.BOOL;
    domain = [Type.BOOL];
    check_arg_ASTs = (function
                         | [FCall (comp, _)] when String.equal comp.name "not"
                           -> false
                         | [ e ] -> not (is_constant e)
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Bool x] -> Bool (not x))
  } ;
  {
    (MakeComponent.binary "and") with
    codomain = Type.BOOL;
    domain = Type.[BOOL; BOOL];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x || is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Bool x ; Bool y] -> Bool (x && y))
  } ;
  {
    (MakeComponent.binary "or") with
    codomain = Type.BOOL;
    domain = Type.[BOOL; BOOL];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y) && (not (is_constant x || is_constant y))
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [Bool x ; Bool y] -> Bool (x || y))
  }
]

let levels = [| all |]
