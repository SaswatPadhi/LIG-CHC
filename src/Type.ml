open Core

open Exceptions

module T = struct
  type t = ARRAY of (t * t)
         | BITVEC of int
         | BOOL
         | CHAR
         | INT
         | LIST of t
         | STRING
         | TVAR of int
         | GHOST of int
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let rec of_sexp (sexp: Sexp.t) : t =
  let open Sexp in
  match sexp with
    | List [Atom "Array" ; index ; value]
      -> ARRAY ((of_sexp index) , (of_sexp value))
    | List [Atom "_" ; Atom "BitVec" ; Atom width]
      -> BITVEC (Int.of_string width)
    | Atom "Bool"   -> BOOL
    | Atom "Char"   -> CHAR
    | Atom "Int"    -> INT
    | List [Atom "List" ; typ]
      -> LIST (of_sexp typ)
    | Atom "String" -> STRING
    | s -> raise (Parse_Exn ("Could not parse type `" ^ (Sexp.to_string_hum s) ^ "`."))

let rec to_string : t -> string = function
  | ARRAY (k,v) -> "(Array " ^ (to_string k) ^ " " ^ (to_string v) ^ ")"
  | BITVEC w    -> "(_ BitVec " ^ (Int.to_string w) ^ ")"
  | BOOL        -> "Bool"
  | CHAR        -> "Char"
  | STRING      -> "String"
  | INT         -> "Int"
  | LIST t      -> "(List " ^ (to_string t) ^ ")"
  | TVAR n      -> Int.to_string n
  | GHOST n     -> Int.to_string n
    (* TODO: We may want to detect cases when a TVAR should never occur in a type,
             and throw exceptions in those cases *)

module Unification = struct
  (* Adapted from: https://eli.thegreenplace.net/2018/unification/
  *
  * TODO: The algorithm below is simple but not efficient.
  * See: https://eli.thegreenplace.net/2018/unification#efficiency
  *)

type target = TYPE_ of int
            | SIZE_ of int

  let rec substitute_with_exn (env : (target * t) list) = function
    | ARRAY (k_type,v_type)
      -> ARRAY ((substitute_with_exn env k_type), (substitute_with_exn env v_type))
    | BITVEC size_ -> begin
        match List.find env ~f:(fun (id,_) -> match id with SIZE_ e_size_ -> Int.equal e_size_ size_
                                                          | _ -> false) with
        | Some (_,value) -> value
        | _ -> raise (Unification_Exn ("Could not find a binding for " ^ (to_string (BITVEC size_))))
      end
    | LIST el_type      -> LIST (substitute_with_exn env el_type)
    | TVAR type_ -> begin
        match List.find env ~f:(fun (id,_) -> match id with TYPE_ e_type_ -> Int.equal e_type_ type_
                                                          | _ -> false) with
        | Some (_,value) -> value
        | _ -> raise (Unification_Exn ("Could not find a binding for " ^ (to_string (TVAR type_))))
      end
    | t -> t

  let substitute (env : (target * t) list) (t : t) : t option =
    try Some (substitute_with_exn env t) with _ -> None

  let rec resolve_var ?(env = []) = function
    | TYPE_ lhs, TVAR rhs
      -> if Int.equal lhs rhs
         then raise (Unification_Exn "Circular dependency!")
         else begin match List.find env ~f:(fun (e,_) -> match e with TYPE_ e -> Int.equal e rhs
                                                                    | _ -> false) with
                | None -> (TYPE_ lhs, TVAR rhs)
                | Some (_, (TVAR x)) -> resolve_var ~env (TYPE_ lhs, (TVAR x))
                | Some (_, rhs) -> (TYPE_ lhs, rhs)
              end
    | pair -> pair

  let rec of_var ?(env = []) (var : target) (rhs : t) =
    match List.Assoc.find env var ~equal:(fun t_var t_env
                                          -> match t_var, t_env with
                                             | (TYPE_ i1), (TYPE_ i2)
                                             | (SIZE_ i1), (SIZE_ i2) -> Int.equal i1 i2
                                             | _ -> false) with
    | None -> begin
        match rhs with
        | TVAR var_rhs -> begin
            match List.Assoc.find env (TYPE_ var_rhs) ~equal:(fun _ -> function TYPE_ i_var_ -> Int.equal var_rhs i_var_
                                                                              | _ -> false) with
            | None -> List.fold ((var,rhs) :: env) ~init:[]
                                ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs) :: env)) :: acc))
            | Some value -> begin match var with
                              | TYPE_ var -> of_type ~env (TVAR var) value
                              | _ -> raise (Unification_Exn ("A SIZE_ target is bound to TVAR!"))
                            end
          end
        | _ -> List.fold ((var,rhs) :: env) ~init:[]
                         ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs)::env)) :: acc))
      end
    | Some value -> of_type ~env value rhs
  and of_type ?(env = []) (lhs : t) (rhs : t) =
    match lhs, rhs with
    | ARRAY (lhs_key,lhs_value), ARRAY (rhs_key,rhs_value)
      -> let env = env @ (of_type ~env lhs_key rhs_key)
          in (of_type lhs_value rhs_value ~env)
    | BITVEC lhs_width, BITVEC rhs_width
      -> begin match lhs_width, rhs_width with
           | _ when Int.(lhs_width < 0) -> of_var ~env (SIZE_ lhs_width) rhs
           | _ when Int.(rhs_width < 0) -> of_var ~env (SIZE_ rhs_width) lhs
           | _ -> env
         end
    | LIST lhs_type, LIST rhs_type
      -> of_type lhs_type rhs_type ~env
    | TVAR x , _ -> of_var ~env (TYPE_ x) rhs
    | _ , TVAR y -> of_var ~env (TYPE_ y) lhs
    | lhs , rhs -> if equal lhs rhs then env
                   else raise (Unification_Exn "Circular dependency!")

  let rec of_types_exn ?(env = []) (lhs : t list) (rhs : t list) : (target * t) list =
    match lhs , rhs with
    | (x :: tx, y :: ty) -> of_types_exn ~env:(of_type ~env x y) tx ty
    | _ -> env

  let of_types ?(env = []) (t1 : t list) (t2 : t list) : (target * t) list option =
      try Some (of_types_exn t1 t2) with _ -> None
end
