open Core

module Array = struct
  include Array

  let to_rev_list_map (a : 'a array) ~(f : 'a -> 'b) : 'b list =
    Array.fold a ~init:[] ~f:(fun acc e -> (f e) :: acc)

  let to_string_map ~(sep : string) (l : 'a array) ~(f : 'a -> string) : string =
    String.concat_array ~sep (map l ~f)

  let to_string_map2 ~(sep : string) (l1 : 'a array) (l2 : 'b array)
                     ~(f : 'a -> 'b -> string) : string =
    String.concat_array ~sep (map2_exn l1 l2 ~f)
end

module Bitv = struct
  include Bitv

  let fold = fold_left

  let foldi = foldi_left

  let compare (v1 : t) (v2 : t) : int =
    let rec helper (i1 : int) (i2 : int) : int =
      if i1 >= 0 && i2 >= 0
      then let b1 = unsafe_get v1 i1 and b2 = unsafe_get v2 i2
            in if Bool.equal b1 b2
               then helper (i1 - 1) (i2 - 1)
               else (if b1 then 1 else -1)
      else if i1 < 0
      then begin
             if i2 < 0 then 0
             else (if unsafe_get v2 i2 then -1 else helper i1 (i2 - 1))
           end
      else (if unsafe_get v1 i1 then 1 else helper (i1 - 1) i2)
     in helper ((length v1) - 1) ((length v2) - 1)

  let sexp_of_t (v : t) : Sexp.t =
    Array.sexp_of_t Bool.sexp_of_t
                    (Array.init (length v) ~f:(unsafe_get v))

  let t_of_sexp (sexp : Sexp.t) : t =
    let array = Array.t_of_sexp Bool.t_of_sexp sexp in
    let v = create (Array.length array) false
     in Array.iteri array ~f:(unsafe_set v)
      ; v
end

module Hashtbl = struct
  include Hashtbl

  let find_default (tbl : ('a, 'b) Hashtbl.t) (key : 'a) ~(default : 'b) : 'b =
    Option.value (Hashtbl.find tbl key) ~default
end

module List = struct
  include List

  let to_string_map ~(sep : string) (l : 'a list) ~(f : 'a -> string) : string =
    String.concat ~sep (List.map l ~f)

  let to_string_mapi ~(sep : string) (l : 'a list) ~(f : int -> 'a -> string) : string =
    String.concat ~sep (mapi ~f l)

  let to_string_map2 ~(sep : string) (l1 : 'a list) (l2 : 'b list)
                     ~(f : 'a -> 'b -> string) : string =
    String.concat ~sep (map2_exn ~f l1 l2)

  let range_map ?(stride = 1) ?(start = `inclusive) ?(stop = `exclusive)
                ~(f : int -> 'a) (start_i : int) (stop_i : int) : 'a list =
    map ~f (range ~stride ~start ~stop start_i stop_i)

  let dedup_and_stable_sort ?(which_to_keep=`Last) ~compare list =
    match list with
    | [] -> []
    | _ -> let equal x x' = compare x x' = 0 in
           let sorted = stable_sort ~compare list
            in remove_consecutive_duplicates ~which_to_keep ~equal sorted
end

module Sexp = struct
  include Sexp

  let force_parse str =
    match parse str with
    | Done (sexp , _) -> sexp
    | _ -> Atom str
end

module String = struct
  include String

  let iteri s ~f =
    ignore
      (fold s ~init:0 ~f:(fun i x -> f i x ; i + 1) : int)
end

let normalize_spaces = Str.(global_replace (regexp "[ \n\r\x0c\t][ \n\r\x0c\t]+") " ")

let get_in_channel = function
  | "-"      -> Stdio.In_channel.stdin
  | filename -> Stdio.In_channel.create filename

let make_user_features feature_strings vars : (string * string) list =
  let feature_strings =
      List.filter_map feature_strings
                      ~f:(fun fs -> let fs = String.strip fs
                                     in match String.is_empty fs with
                                        | true -> None
                                        | _ -> Some fs)
   in begin
     if List.is_empty feature_strings then [] else
     let decl_var (s,t) = "(" ^ s ^ " " ^ (Type.to_string t) ^ ")" in
     let var_decls = List.to_string_map vars ~sep:" " ~f:decl_var in
     let sign = " (" ^ var_decls ^ ") Bool "
      in List.mapi
           feature_strings
           ~f:(fun i fs -> let fname = "f_" ^ (Int.to_string i) in
                           let fdef = "(define-fun " ^ fname ^ sign ^ fs ^ ")"
                            in (fdef, fname))
   end
  
  let forall_numbers_ref: int list ref = ref []

  let rec get_fresh_var () : string = 
    let random_var = Random.int 1000 in 
    if (List.exists !forall_numbers_ref ~f:(fun (i:int) -> i = random_var))
      then get_fresh_var ()
    else 
      let rdms = !forall_numbers_ref in 
      forall_numbers_ref := rdms@[random_var];
      "__FORALL_VAR_" ^ "_" ^ (string_of_int random_var)