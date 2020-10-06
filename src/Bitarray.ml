open Core
open Exceptions

open Utils

include Bitv
include Core.Comparable.Make (Bitv)

let signed_compare (v1 : t) (v2 : t) : int =
  let l1 = (length v1) - 1 and l2 = (length v2) - 1
   in if (unsafe_get v1 l1) && (not (unsafe_get v2 l2)) then -1
      else if (not (unsafe_get v1 l1)) && (unsafe_get v2 l2) then 1
      else compare v1 v2

let to_string (v : t) : string =
  "#b" ^ (M.to_string v)

let unsafe_set_hex_char (v : t) (i : int) : char -> unit =
  let open Bitv in
  let helper b0 b1 b2 b3 = unsafe_set v (i + 3) b0
                         ; unsafe_set v (i + 2) b1
                         ; unsafe_set v (i + 1) b2
                         ; unsafe_set v i b3
   in function '0' -> helper false false false false
             | '1' -> helper false false false true
             | '2' -> helper false false true false
             | '3' -> helper false false true true
             | '4' -> helper false false false false
             | '5' -> helper false true false true
             | '6' -> helper false true true false
             | '7' -> helper false true true true
             | '8' -> helper true false false false
             | '9' -> helper true false false true
             | 'a' | 'A' -> helper true false true false
             | 'b' | 'B' -> helper true false true true
             | 'c' | 'C' -> helper true true false false
             | 'd' | 'D' -> helper true true false true
             | 'e' | 'E' -> helper true true true false
             | 'f' | 'F' -> helper true true true true
             | _ -> raise Caml.Exit

let of_hex_string (s : string) : t =
  let n = String.length s in
  let v = create (4 * n) false
   in String.iteri s ~f:(fun i -> unsafe_set_hex_char v (4 * (n - 1 - i)))
    ; v

let of_bin_string (s : string) : t =
  M.of_string s

let of_string (s : string) : t =
  try
    of_bin_string (String.chop_prefix_exn ~prefix:"#b" s)
  with _ -> try
    of_hex_string (String.chop_prefix_exn ~prefix:"#x" s)
  with _ -> try
    begin match [@warning "-8"] Sexp.(force_parse s) with
      | Sexp.(List [ Atom "_" ; Atom const ; Atom width ])
        -> let two_big_int = Bigint.of_int 2
           and big_int_const = ref (Bigint.of_string (String.chop_prefix_exn ~prefix:"bv" const))
           and int_width = Int.of_string width
            in let v = create int_width false
               and i = ref (0)
                in while Bigint.(!big_int_const > zero)
                      do (if Int.(!i >= int_width)
                          then raise (Parse_Exn ("Binary constant " ^ const ^
                                                 " is too large for width " ^ width)))
                       ; (if Bigint.((!big_int_const % two_big_int) = one)
                          then unsafe_set v !i true)
                       ; big_int_const := Bigint.(!big_int_const asr 1)
                       ; i := !i + 1
                    done
                 ; v
    end
  with Parse_Exn _ as p -> raise p
     | _ -> raise (Parse_Exn ("Binary constant in unknown format: " ^ s))

let add (v1 : t) (v2 : t) (bits : int) : t =
  let sum = create bits false in
  let carry = ref false 
   in for i = 0 to bits - 1 do
        match (unsafe_get v1 i), (unsafe_get v2 i) with
        | true, true
          -> unsafe_set sum i !carry
           ; carry := true
        | false, true | true, false
          -> unsafe_set sum i (not !carry)
        | false, false
          -> unsafe_set sum i !carry
           ; carry := false
      done
    ; sum

let unsafe_same_len_bvadd ~(bits : int) (v1 : t) (v2 : t) : t =
  let res = create bits false in
  let carry = ref false 
   in for i = 0 to bits - 1 do
        match (unsafe_get v1 i), (unsafe_get v2 i) with
        | true, true
          -> unsafe_set res i !carry
           ; carry := true
        | false, true | true, false
          -> unsafe_set res i (not !carry)
        | false, false
          -> unsafe_set res i !carry
           ; carry := false
      done
    ; res

let unsafe_same_len_bvsub ~(bits : int) (v1 : t) (v2 : t) : t =
  let bvadd = unsafe_same_len_bvadd ~bits in
  let one = create bits false
   in unsafe_set one 0 true
    ; bvadd v1 (bvadd (bw_not v2) one)

let unsafe_same_len_bvmul ~(bits : int) (v1 : t) (v2 : t) : t =
  let bvadd = unsafe_same_len_bvadd ~bits in
  let res = ref (create bits false)
   in for i = 0 to bits - 1 do
        if unsafe_get v1 i
        then res := (bvadd !res (shiftl v2 i))
      done
    ; !res
