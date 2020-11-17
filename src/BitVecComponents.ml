open Base

open Expr

let is_zero : Expr.t -> bool =
  function Const (Value.BitVec v) -> Bitarray.all_zeros v
         | _ -> false

let is_one : Expr.t -> bool =
  function Const (Value.BitVec v) -> Bitarray.((unsafe_get v 0) && (all_zeros (shiftr v 1)))
         | _ -> false

let equality = [
  {
    (MakeComponent.binary ~symbol:"=" "bv-eq") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.equal (Bitarray.compare v1 v2) 0));
  }
]

let intervals = equality @ [
  {
    (MakeComponent.binary "bvsge") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_negative (Bitarray.signed_compare v1 v2)));
  } ;
  {
    (MakeComponent.binary "bvsle") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_positive (Bitarray.signed_compare v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvsgt") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_positive (Bitarray.signed_compare v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvslt") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_negative (Bitarray.signed_compare v1 v2)))
  }
]

let unsigned_intervals = intervals @ [
  {
    (MakeComponent.binary "bvuge") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_negative (Bitarray.compare v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvule") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_positive (Bitarray.compare v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvugt") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_positive (Bitarray.compare v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvult") with
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_negative (Bitarray.compare v1 v2)))
  }
]

let octagons = unsigned_intervals @ [
  {
    (MakeComponent.binary "bvadd") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = Value.(function
                               | [x ; FCall (comp, [_ ; y])]
                                 when String.equal comp.name "bvsub"
                                 -> x =/= y && (not (is_zero x))
                               | [FCall (comp, [_ ; x]) ; y]
                                 when String.equal comp.name "bvsub"
                                 -> x =/= y && (not (is_zero x))
                               | [x ; y] -> (not (is_zero x)) && (not (is_zero y))
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvadd ~bits:(length v1) v1 v2)))
  } ;
  {
    (MakeComponent.binary "bvsub") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = Value.(function
                               | [(FCall (comp, [x ; y])) ; z]
                                 when String.equal comp.name "bvadd"
                                 -> x =/= z && y =/= z && (not (is_zero z))
                               | [(FCall (comp, [x ; _])) ; y]
                                 when String.equal comp.name "bvsub"
                                 -> x =/= y && (not (is_zero y))
                               | [x ; (FCall (comp, [y ; _]))]
                                 when (String.equal comp.name "bvsub" || String.equal comp.name "bvadd")
                                 -> x =/= y
                               | [x ; y] -> (x =/= y) && (not (is_zero x)) && (not (is_zero y))
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvsub ~bits:(length v1) v1 v2)))
  }
]

let bitwise = octagons @ [
  {
    (MakeComponent.unary "bvnot") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1)];
    check_arg_ASTs = (function
                         | [FCall (comp, _)] when String.equal comp.name "bvnot"
                           -> false
                         | [ _ ] -> true
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v] -> BitVec (Bitarray.bw_not v))
  } ;
  {
    (MakeComponent.binary "bvand") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.bw_and v1 v2))
  } ;
  {
    (MakeComponent.binary "bvor") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.bw_or v1 v2))
  }
]

let polyhedra = bitwise @ [
  {
    (MakeComponent.binary "bvmul") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = (function
                          | [x ; y]
                            -> (is_constant x || is_constant y)
                            && (not (is_zero x)) && (not (is_one x))
                            && (not (is_zero y)) && (not (is_one y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvmul ~bits:(length v1) v1 v2)))
  }
]

let polynomials = polyhedra @ [
  {
    (MakeComponent.binary ~symbol:"bvmul" "bv-nonlin-mul") with
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    check_arg_ASTs = Value.(function
                               | [x ; y] -> not (is_constant x || is_constant y)
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvmul ~bits:(length v1) v1 v2)))
  }
]

let peano = polynomials @ [
  (* TODO *)
]

let levels = [| equality ; intervals ; unsigned_intervals ; octagons
              ; bitwise ; polyhedra ; polynomials ; peano |]
