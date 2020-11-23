open Core
open Quickcheck
open Generator

module Config = struct
  type t = {
    max_length : int ;
    min_length : int ;
    max_int : int ;
    min_int : int ;
    seed : [`Nondeterministic | `Deterministic of string]
  }

  let default : t = {
    max_length = 32 ;
    min_length = 0 ;
    max_int = 1023 ;
    min_int = -1024 ;
    seed = `Deterministic "SomeRandomSeed"
  }
end

let rec for_type ?(config = Config.default) (t : Type.t) : Value.t Generator.t =
  match t with
  | Type.ARRAY (key,value) -> (Int.gen_incl config.min_length config.max_length)
                              >>= fun len -> ((tuple2 (List.gen_with_length len (tuple2 (for_type ~config key) (for_type ~config value))) (for_type ~config value))
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
  | Type.INT -> (Int.gen_incl config.min_int config.max_int) >>= fun i -> singleton (Value.Int i)
  | Type.LIST _ | Type.TVAR _
    -> raise (Exceptions.Internal_Exn "Generator not implemented!")
  | Type.STRING -> (Int.gen_incl config.min_length config.max_length)
                   >>= fun len -> (String.gen_with_length len (Char.gen_print)
                                  >>= fun s -> singleton (Value.String s))

let list_of_random_values ?(config = Config.default) (length : int) (t : Type.t) : Value.t list =
  Quickcheck.(random_value ~seed:config.seed (Generator.list_with_length length (for_type ~config t)))
