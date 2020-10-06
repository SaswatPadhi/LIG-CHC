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
    name = "bv-eq";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.equal (Bitarray.compare v1 v2) 0));
    to_string = (fun [@warning "-8"] [v1;v2] -> "(= " ^ v1 ^ " " ^ v2 ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let intervals = equality @ [
  {
    name = "bvsge";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_negative (Bitarray.signed_compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvsge " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvsle";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_positive (Bitarray.signed_compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvsle " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvsgt";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_positive (Bitarray.signed_compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvsgt " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvslt";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_negative (Bitarray.signed_compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvslt " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let unsigned_intervals = intervals @ [
  {
    name = "bvuge";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_negative (Bitarray.compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvuge " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvule";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_non_positive (Bitarray.compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvule " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvugt";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_positive (Bitarray.compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvugt " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvult";
    codomain = Type.BOOL;
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y] -> (x =/= y) && (not (is_constant x && is_constant y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> Bool (Int.is_negative (Bitarray.compare v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvult " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let octagons = unsigned_intervals @ [
  {
    name = "bvadd";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = Value.(function
                               | [x ; FCall (comp, [_ ; y])]
                                 when String.equal comp.name "bvsub"
                                 -> x =/= y && (not (is_zero x))
                               | [FCall (comp, [_ ; x]) ; y]
                                 when String.equal comp.name "bvsub"
                                 -> x =/= y && (not (is_zero x))
                               | [x ; y] -> (not (is_zero x)) && (not (is_zero y))
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvadd ~bits:(length v1) v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvadd " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvsub";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = Value.(function
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
                      -> BitVec (Bitarray.(unsafe_same_len_bvsub ~bits:(length v1) v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvsub " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let bitwise = octagons @ [
  {
    name = "bvnot";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1)];
    is_argument_valid = (function
                         | [FCall (comp, _)] when String.equal comp.name "bvnot"
                           -> false
                         | [ _ ] -> true
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v] -> BitVec (Bitarray.bw_not v));
    to_string = (fun [@warning "-8"] [a] -> "(bvnot " ^ a ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvand";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.bw_and v1 v2));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvand " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  } ;
  {
    name = "bvor";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                         | [x ; y] -> (x =/= y)
                         | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.bw_or v1 v2));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvor " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let polyhedra = bitwise @ [
  {
    name = "bvmul";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = (function
                          | [x ; y]
                            -> (is_constant x || is_constant y)
                            && (not (is_zero x)) && (not (is_one x))
                            && (not (is_zero y)) && (not (is_one y))
                          | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvmul ~bits:(length v1) v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvmul " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> []);
  }
]

let polynomials = polyhedra @ [
  {
    name = "bv-nonlin-mul";
    codomain = Type.BITVEC (-1);
    domain = Type.[BITVEC (-1); BITVEC (-1)];
    is_argument_valid = Value.(function
                               | [x ; y] -> not (is_constant x || is_constant y)
                               | _ -> false);
    evaluate = Value.(fun [@warning "-8"] [BitVec v1 ; BitVec v2]
                      -> BitVec (Bitarray.(unsafe_same_len_bvmul ~bits:(length v1) v1 v2)));
    to_string = (fun [@warning "-8"] [a ; b] -> "(bvmul " ^ a ^ " " ^ b ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let peano = polynomials @ [
  (* TODO *)
]

let levels = [| equality ; intervals ; unsigned_intervals ; octagons
              ; bitwise ; polyhedra ; polynomials ; peano |]
