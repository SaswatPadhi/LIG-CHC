open Core_kernel

open Exceptions
open Utils

type desc = string
type 'a feature = 'a -> bool
type 'a with_desc = 'a * desc

type ('a, 'b) _t = {
  arg_names : string list ;
  arg_types : Type.t list ;
  features : 'a feature with_desc list ;
  neg_tests : ('a * (bool list lazy_t)) list ;
  pos_tests : ('a * (bool list lazy_t)) list ;
}

type t = (Value.t list, Value.t) _t

let are_values_equal = List.equal Value.equal

let compute_feature_value (test : 'a) (feature : 'a feature with_desc) : bool =
  try (fst feature) test with _ -> false
  [@@inline always]

let compute_feature_vector (test : 'a) (features : 'a feature with_desc list)
                           : bool list =
  List.map ~f:(compute_feature_value test) features
[@@inline always]

let create ~args ?(features = []) ?(pos_tests = []) ?(neg_tests = []) () : t =
  { features
  ; arg_names = List.map args ~f:fst
  ; arg_types = List.map args ~f:snd
  ; pos_tests = List.map pos_tests ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
  ; neg_tests = List.map neg_tests ~f:(fun t -> (t, lazy (compute_feature_vector t features)))
  }

let has_pos_test ~(job : t) (test : Value.t list) : bool =
  List.exists job.pos_tests ~f:(fun (pt, _) -> are_values_equal pt test)

let has_neg_test ~(job : t) (test : Value.t list) : bool =
  List.exists job.neg_tests ~f:(fun (nt, _) -> are_values_equal nt test)

let add_pos_test ~(job : t) (test : Value.t list) : t =
  if has_pos_test ~job test
  then raise (Duplicate_Test ("New POS test (" ^ (String.concat ~sep:"," job.arg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ "), already exists in POS set!"))
  else if has_neg_test ~job test
  then raise (Ambiguous_Test ("New POS test (" ^ (String.concat ~sep:"," job.arg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))
  else { job with
         pos_tests = (test, lazy (compute_feature_vector test job.features))
                  :: job.pos_tests
       }

let add_neg_test ~(job : t) (test : Value.t list) : t =
  if has_neg_test ~job test
  then raise (Duplicate_Test ("New NEG test (" ^ (String.concat ~sep:"," job.arg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in NEG set!"))
  else if has_pos_test ~job test
  then raise (Ambiguous_Test ("New NEG test (" ^ (String.concat ~sep:"," job.arg_names)
                             ^ ") = (" ^ (List.to_string_map ~sep:"," ~f:Value.to_string test)
                             ^ ") already exists in POS set!"))
  else { job with
         neg_tests = (test, lazy (compute_feature_vector test job.features))
                  :: job.neg_tests
       }

let add_feature ~(job : t) (feature : 'a feature with_desc) : t =
  let add_to_fv (t, old_fv) =
    (t, lazy ((compute_feature_value t feature) :: (Lazy.force old_fv)))
  in { job with
       features = feature :: job.features ;
       pos_tests = List.map job.pos_tests ~f:add_to_fv ;
       neg_tests = List.map job.neg_tests ~f:add_to_fv ;
     }