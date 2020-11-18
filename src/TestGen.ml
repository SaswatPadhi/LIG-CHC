open Core
open Quickcheck
open Generator

let rec for_type (t : Type.t) : Value.t Generator.t =
  match t with
  | Type.ARRAY (key,value) -> (Int.gen_incl 0 64)
                              >>= fun len -> ((tuple2 (List.gen_with_length len (tuple2 (for_type key) (for_type value))) (for_type value))
                                              >>= fun (arr, def) -> singleton (Value.Array (key, value, arr, def)))
  | Type.BITVEC n -> let bv = Bitarray.create n false in
                     let randarray = Bitarray.fold bv ~init:((singleton bv), 0)
                                       ~f:(fun (sbv, i) _ ->
                                         (sbv >>= fun bitarr -> bool >>= fun b ->
                                                                Bitarray.set bitarr i b; singleton bitarr), i+1) in
                     (match randarray with
                      | sbv, i -> sbv >>= fun bv -> singleton (Value.BitVec bv))
  | Type.BOOL -> bool >>= fun b -> singleton (Value.Bool b)
  | Type.CHAR -> char >>= fun c -> singleton (Value.Char c)
  (* Full range of Int:
  | Type.INT -> Int.gen >>= fun i -> singleton (Value.Int i) *)
  | Type.INT -> (Int.gen_incl (-4096) 4095) >>= fun i -> singleton (Value.Int i)
  | Type.LIST _ | Type.TVAR _
    -> raise (Exceptions.Internal_Exn "Generator not implemented!")
  | Type.STRING -> (Int.gen_incl 0 64)
                   >>= fun len -> (String.gen_with_length len (Char.gen_print)
                                  >>= fun s -> singleton (Value.String s))