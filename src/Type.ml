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
    (* TODO: We may want to detect cases when a TVAR should never occur in a type,
             and throw exceptions in those cases *)

module Unification = struct
  (* Adapted from: https://eli.thegreenplace.net/2018/unification/
  *
  * TODO: The algorithm below is simple but not efficient.
  * See: https://eli.thegreenplace.net/2018/unification#efficiency
  *)

  let rec substitute_with_exn (env : (int * t) list) = function
    | ARRAY (k_type,v_type)
      -> ARRAY ((substitute_with_exn env k_type), (substitute_with_exn env v_type))
    | LIST el_type      -> LIST (substitute_with_exn env el_type)
    | TVAR name -> begin
        match List.find ~f:(fun (id,_) -> Int.equal id name) env with
        | Some (_,value) -> value
        | _ -> raise (Unification_Exn ("Could not find a binding for " ^ (Int.to_string name)))
      end
    | t -> t

  let substitute (env : (int * t) list) (t : t) : t option =
    try Some (substitute_with_exn env t) with _ -> None

  let rec resolve_var ?(env = []) = function
    | lhs, TVAR rhs -> if Int.equal lhs rhs
                       then raise (Unification_Exn "Circular dependency!")
                       else begin
                         match List.find env ~f:(fun (e,_) -> Int.equal e rhs) with
                         | None -> (lhs, TVAR rhs)
                         | Some (_, (TVAR x)) -> resolve_var ~env (lhs, (TVAR x))
                         | Some (_, rhs) -> (lhs, rhs)
                       end
    | pair -> pair

  let rec of_var ?(env = []) (var : int) (rhs : t) =
    match List.Assoc.find env ~equal:Int.equal var with
    | None -> begin
        match rhs with
        | TVAR var_rhs -> begin
            match List.Assoc.find env ~equal:Int.equal var_rhs with
            | None -> List.fold ((var,rhs) :: env) ~init:[]
                                ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs) :: env)) :: acc))
            | Some value -> of_type ~env (TVAR var) value
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
           | _ when Int.(lhs_width < 0) -> of_var ~env lhs_width rhs
           | _ when Int.(rhs_width < 0) -> of_var ~env rhs_width lhs
           | _ -> env
         end
    | LIST lhs_type, LIST rhs_type
      -> of_type lhs_type rhs_type ~env
    | TVAR x , _ -> of_var ~env x rhs
    | _ , TVAR y -> of_var ~env y lhs
    | lhs , rhs -> if equal lhs rhs then env
                   else raise (Unification_Exn "Circular dependency!")

  let rec of_types_exn ?(env = []) (lhs : t list) (rhs : t list) : (int * t) list =
    match lhs , rhs with
    | (x :: tx, y :: ty) -> of_types_exn ~env:(of_type ~env x y) tx ty
    | _ -> env

  let of_types ?(env = []) (t1 : t list) (t2 : t list) : (int * t) list option =
      try Some (of_types_exn t1 t2) with _ -> None
end