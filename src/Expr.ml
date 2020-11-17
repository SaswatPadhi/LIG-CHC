open Base

open Utils
open Exceptions

let ghost_variable_name = "__idx__"

(* FIXME: I think a better design would be to merge the `callable_args`
 * and `domain` fields of the `component` structure,
 * or may be some more general design for high-order functions
 * callable_args : index of callable, name to be bound, domain, codomain
 *)
type component = {
  name : string ;
  codomain : Type.t ;
  domain : Type.t list ;
  check_arg_ASTs : t list -> bool ;
  callable_args : (int * string * Type.t * Type.t) list ;
  evaluate : Value.t list -> Value.t ;
  to_string : string list -> string ;
  global_constraints : string list -> string list ;
} and t =
  | FCall of component * t list
  | Const of Value.t
  | Var of int
  [@@deriving sexp]

module MakeComponent = struct
  let base : component = {
    name = "UNKNOWN" ;
    domain = [] ;
    codomain = Type.TVAR 0 ;
    callable_args = [];
    evaluate = (fun _ -> raise (Internal_Exn "NOT IMPLEMENTED!")) ;
    to_string = (fun _ -> raise (Internal_Exn "NOT IMPLEMENTED!")) ;
    global_constraints = (fun _ -> []);
    check_arg_ASTs = (fun _ -> true) ;
  }

  let binary ?(symbol = "") (name : string) : component = {
    base with
    name ;
    to_string = (fun [@warning "-8"] [a ; b]
                 -> "(" ^ (if String.is_empty symbol then name else symbol) ^ " " ^ a ^ " " ^ b ^ ")") ;
  }

  let unary ?(symbol = "") (name : string) : component = {
    base with
    name ;
    to_string = (fun [@warning "-8"] [ a ]
                 -> "(" ^ (if String.is_empty symbol then name else symbol) ^ " " ^ a ^ ")") ;
  }
end

let rec equal e1 e2 =
  match e1, e2 with
  | Var i1, Var i2 -> i1 = i2
  | Const v1, Const v2 -> Value.equal v1 v2
  | FCall (c1, l1), FCall (c2, l2)
    -> String.equal c1.name c2.name
    && List.fold2_exn l1 l2 ~init:true ~f:(fun acc x y -> acc && (equal x y))
  | _ -> false

let (=/=) = fun x y -> (not (equal x y))

let is_constant expr =
  let rec helper = function
    | Const _ -> ()
    | Var _ -> raise Caml.Exit
    | FCall (_, exprs) -> List.iter ~f:helper exprs
  in try helper expr ; true
     with Caml.Exit -> false

let rec to_string arg_names = function
  | FCall (comp, comp_args) -> comp.to_string (List.map ~f:(to_string arg_names) comp_args)
  | Const v -> Value.to_string v
  | Var i -> arg_names.(i)

let rec to_function = function
  | FCall (comp, comp_args)
    -> let arg_funcs = List.map ~f:to_function comp_args
        in (fun args -> comp.evaluate (List.map arg_funcs ~f:(fun afunc -> afunc args)))
  | Const v -> (fun _ -> v)
  | Var i -> (fun args -> List.nth_exn args i)

let rec get_constraints arg_names = function
  | FCall (comp, comp_args)
    -> List.fold comp_args ~init:(comp.global_constraints (List.map ~f:(to_string arg_names) comp_args))
                 ~f:(fun acc comp_arg -> acc @ (get_constraints arg_names comp_arg))
  | _ -> []

let rec height = function
  | FCall (_, args) -> 1 + (List.fold_left ~f:max ~init:0 (List.map ~f:height args))
  | _ -> 1

let rec size = function
  | FCall (_, args) -> List.fold_left ~f:(+) ~init:1 (List.map ~f:size args)
  | _ -> 1

type synthesized = {
  expr : t ;
  outputs : Value.t array ;
} [@@deriving sexp]

let unify_component (comp : component) (arg_types : Type.t list) : component option =
  let open Type.Unification in
  match of_types arg_types comp.domain with
  | None -> None
  | Some env -> match substitute env comp.codomain with
                | None -> None
                | Some codomain -> let domain = List.map comp.domain ~f:(substitute_with_exn env)
                                    in Some { comp with codomain ; domain }

let apply (comp : component) (args : synthesized list) : synthesized option =
  if (not (comp.check_arg_ASTs (List.map args ~f:(fun arg -> arg.expr)))) then None
  else try
    let select idx = List.map args ~f:(fun arg -> arg.outputs.(idx))
     in Some { expr = FCall (comp, List.map ~f:(fun arg -> arg.expr) args)
             ; outputs = Array.mapi (List.hd_exn args).outputs
                                    ~f:(fun i _ -> comp.evaluate (select i)) }
  with Internal_Exn e -> raise (Internal_Exn e)
     | _ -> None
