open Core

open Exceptions


let rec flatten : Sexp.t -> Sexp.t = function
  | Atom _ as atom -> atom
  | List [ (Atom "and") ; arg ] | List [ (Atom "or") ; arg ] -> arg
  | List ((Atom "and") :: args)
    -> List ( (Atom "and") :: (List.concat_map args ~f:(fun a -> match flatten a with
                                                                 | List ((Atom "and") :: inner_args)
                                                                   -> inner_args
                                                                 | a -> [a])) )
  | List ((Atom "or") :: args)
    -> List ( (Atom "or") :: (List.concat_map args ~f:(fun a -> match flatten a with
                                                                | List ((Atom "or") :: inner_args)
                                                                  -> inner_args
                                                                | a -> [a])) )
  | List [(Atom "forall") ; (List vars) ; body]
    -> begin match flatten body with
         | List [(Atom "forall") ; (List inner_vars) ; body]
           -> List [(Atom "forall") ; (List (vars @ inner_vars)) ; body]
         | body -> List [(Atom "forall") ; (List vars) ; body]
       end
  | List [(Atom "exists") ; (List vars) ; body]
    -> begin match flatten body with
         | List [(Atom "exists") ; (List inner_vars) ; body]
           -> List [(Atom "exists") ; (List (vars @ inner_vars)) ; body]
         | body -> List [(Atom "exists") ; (List vars) ; body]
       end
  | List l -> List (List.map l ~f:flatten)

let rec bv_to_int ~(width : int) : Sexp.t -> Sexp.t = function
  | List [ (Atom "_") ; (Atom bv) ; (Atom w)] as sexp
    -> if width <> Int.of_string w then raise (Parse_Exn ("Unexpected BitVec width " ^ w ^ "!"))
       else begin match String.chop_prefix bv ~prefix:"bv" with
              | None -> if String.equal bv "BitVec" then (Atom "Int")
                        else raise (Parse_Exn ("Bad subexpression: " ^ (Sexp.to_string_hum sexp) ^ "!"))
              | Some const -> Atom const
            end
  | List [ (Atom "bvneg") ; arg ]
    -> List [ (Atom "-") ; (Atom "0") ; (bv_to_int ~width arg) ]
  | Atom "bvadd" -> Atom "+"
  | Atom "bvsub" -> Atom "-"
  | Atom "bvmul" -> Atom "*"
  | Atom "bvudiv" | Atom "bvsdiv" -> Atom "div"
  | Atom "bvurem" | Atom "bvsrem" | Atom "bvsmod" -> Atom "mod"
  | Atom "bvule" | Atom "bvsle" -> Atom "<="
  | Atom "bvult" | Atom "bvslt" -> Atom "<"
  | Atom "bvuge" | Atom "bvsge" -> Atom ">="
  | Atom "bvugt" | Atom "bvsgt" -> Atom ">"
  | Atom a -> Atom a
  | List l -> List (List.map ~f:(bv_to_int ~width) l)

let replace bindings expr =
  if List.is_empty bindings then expr else
  let open Sexp in
  let table = ref (String.Map.empty)
   in List.iter bindings
                ~f:(function [@warning "-8"]
                    | List [ (Atom key) ; data ]
                      -> table := String.Map.add_exn !table ~key ~data)
    ; let rec helper = function
        | List l -> List (List.map l ~f:helper)
        | Atom atom -> match String.Map.find !table atom with
                       | None      -> Atom atom
                       | Some data -> data
       in helper expr

let rec remove_lets : Sexp.t -> Sexp.t = function
  | Atom _ as atom -> atom
  | List [ (Atom "let") ; List bindings ; body ]
    -> replace bindings (remove_lets body)
  | List l -> List (List.map l ~f:remove_lets)
