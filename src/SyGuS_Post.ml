open Core_kernel
open Sexplib
open Sexplib.Type
open Core

open Exceptions
open SyGuS
open Utils
exception Failure of string

(***
  * This module is used to do postprocessing on parsed input 
  * for inferring universally quantified invariants over arrays. 
  * To do so, we equip each invariant stored as uifunc with a list 
  * of loop counters of type (int * string * string) containing
  * the index of the argument of the loop counter variable to the invariant. 
  * For a single loop we assume this to be the second argument, i.e. position 1 (starting indexing with 0).
  * The second argument stores the lower bound and the third argument contains the upper bound, 
  * i.e. 0 to N for incremental loop counters, or N to i for decremental loop counters. 
***)

type loop_guard = {
  inv_index : int ;
  counter: string ;
  counter_primed : string ;
  guard_expression : string list ;
  is_inc : bool ;  (* true if counter is incremented, false if counter is decremented  *)
}

let rec print_list = function 
[] -> print_string "[]"
| e::l -> print_string e ; print_string " " ; print_list l

let rec print_invlist = function 
[] -> print_string "[]"
| (i, lst)::l -> print_string (string_of_int i); print_string " "; print_list lst ; print_string " " ; print_invlist l

(* for an inductive invariant in head/tail find the counterpart in tail/head *)
let rec find_matching_invariant (index: int) (lst : (int * (string list)) list) : (int * (string list)) = 
    match lst with
    | [] -> raise (Failure "Not counterpart invariant found")
    | h :: t -> 
        match h with 
            | (i, _) ->  if index = i then h else find_matching_invariant index t

(* for (inv a i val ...) return the second argument of inv which is assumed to be the loop counter variable i *)
let find_counter_variable (elem: (int * (string list))) : string =
    match elem with 
        | (_, []) -> raise (Parse_Exn ("No counter variable found in head invariant. ")) 
        | (_, lst) -> begin
                let counter_str = List.nth lst 1 in
                match counter_str with 
                    | Some(counter) -> counter
                    | None -> raise (Parse_Exn ("No counter variable found in head invariant. "))
            end

(* assumes simple loop guards with one inquality without conjunctions or disjunctions *)
(* e.g. i < N, i > N, i != N, i <= N, i >= N  *)
(* INPUT:  e.g. (inv a i val N) (<= i N) (= a1 (ite (= val i) (store a i 0) (store a i i)) *)
let get_loop_guard_expressions (lst: Sexp.t list) : string list list = 
    List.filter_map lst ~f:(function
        | List [(Atom "<") ; (Atom lower) ; (Atom upper)] -> Some(["<"; lower; upper])
        | List [(Atom ">") ; (Atom upper) ; (Atom lower)] -> Some([">"; upper; lower])
        | List [(Atom "<=") ; (Atom lower) ; (Atom upper)] -> Some(["<="; lower; upper])
        | List [(Atom ">=") ; (Atom upper) ; (Atom lower)] -> Some([">="; upper; lower]) 
        | List [(Atom "not") ; List [(Atom "=") ; (Atom left) ; (Atom right)]] -> Some(["not ="; left; right])
        | _ -> None
    )

let str_split (x: string) : string list =
    String.split_on_chars ~on:[ ' ' ; '\t' ; '\n' ; '\r' ] x
    |> List.filter ~f:(fun s -> not (String.equal s "") )


(* string contains *)
let contains (s1:string) (s2: string): bool =
    let re = Str.regexp_string s2 in
    try 
       ignore (Str.search_forward re s1 0); 
       true
    with Not_found_s e -> false 


(* find update expressions for a loop counter i  *)
let [@warning "-8"] get_update (i: string) (a: Sexp.t ): string =
    match a with
         | List [Atom "+" ; Atom left ; Atom right ] -> 
            if (String.equal left i || String.equal right i)  
                then Sexp.to_string_hum a 
            else ""
        | List [Atom "-" ; Atom left ; Atom right ] -> 
            if (String.equal left i || String.equal right i)  
                then Sexp.to_string_hum a 
            else ""
        | List [Atom "+" ; List _ ; Atom right ] -> 
            if (String.equal right i)  
                then Sexp.to_string_hum a
            else ""
        | List [Atom "-" ; List _ ; Atom right ] -> 
            if (String.equal right i)  
                then Sexp.to_string_hum a
            else ""
        | List [Atom "+" ; Atom left ; List _ ] -> 
            if (String.equal left i)  
                then Sexp.to_string_hum a 
            else ""
        | List [Atom "-" ; Atom left ; List _ ] -> 
            if (String.equal left i)  
                then Sexp.to_string_hum a
            else ""
        | List [Atom _ ; _ ] -> ""
        | List [_] -> ""
        | List [] -> ""

        

(* assumes simple loop counter increments or decrements of the form  *)
(* find expressions of the form: + i 1, + 1 i, - i 1, - 1 i,  *)
let [@warning "-8"] rec find_counter_updates (i_tail: string) (i_prime: string) (lst: Sexp.t list) : string list =
    match lst with 
        | h::t -> begin 
            (* Printf.printf "\n find counter updates head:  %s \n" (Sexp.to_string_hum h); *)
            match h with
            | Atom a -> (find_counter_updates i_tail i_prime t)
            | List [Atom "="; Atom i; ops]  -> 
                if String.equal i i_prime 
                    then (get_update i_tail ops)::(find_counter_updates i_tail i_prime t)
                else (find_counter_updates i_tail i_prime t)
            | List [(Atom "="); ops ; Atom i ]  -> 
                if String.equal i i_prime 
                    then (get_update i_tail ops)::(find_counter_updates i_tail i_prime t)
                else (find_counter_updates i_tail i_prime t)
            | List ((Atom _)::ops) -> (find_counter_updates i_tail i_prime ops)@(find_counter_updates i_tail i_prime t)
            | List [_] -> (find_counter_updates i_tail i_prime t)
            end 
        | [] -> [""]



(*  Input: 
    {LoopInvGen.SyGuS.args =
     [("a", LoopInvGen.Type.ARRAY (LoopInvGen.Type.INT, LoopInvGen.Type.INT));
      ("i", LoopInvGen.Type.INT); ("val", LoopInvGen.Type.INT);
      ("N", LoopInvGen.Type.INT);
      ("a1", LoopInvGen.Type.ARRAY (LoopInvGen.Type.INT, LoopInvGen.Type.INT));
      ("i1", LoopInvGen.Type.INT)];
    body =
     "(=> (and (inv a i val N) (<= i N)\n (= a1 (ite (= val i) (store a i 0) (store a i i))) (= i1 (+ i 1)))
      (inv a1 i1 val N))";
    head = [(0, ["a1"; "i1"; "val"; "N"])]; is_ind = true;
    name = "_chc_index__1_"; tail = [(0, ["a"; "i"; "val"; "N"])]}

    Output: args.(1), "0", "i"
 *)
(* takes an inductiveness check and an invariant to find loop guards *)
let find_guard_candidates (constr : chc): loop_guard =
    if not constr.is_ind then
        raise (Failure "Not an inductive invariant found")
    (** assumes the head to only contain invariant since we only take inductive CHCs *)
    ; let counter_head = match constr.head with 
        | fst::_ -> fst
        | _ -> raise (Parse_Exn ("No invariant found in head. ")) 

    (** i1 *)
    in let counter_head_variable : string = find_counter_variable counter_head

    (** 0 since only one invariant *)
    in let invariant_index : int = match counter_head with
        | i, _ -> i

    in let counter_tail = find_matching_invariant invariant_index constr.tail 
    
    (** i *)
    in let counter_tail_variable = find_counter_variable counter_tail

    (* (=> (and (inv a i val N) (<= i N) (= a1 (ite (= val i) (store a i 0) (store a i i))) (= i1 (+ i 1))) (inv a1 i1 val N)) *)
    in let body_sexp : Sexp.t  = Sexp.of_string constr.body 
    in let tail = 
        match body_sexp with 
            | List [ (Atom "=>") ; (Atom t) ; _ ] -> [Sexp.of_string t]
            | List [ (Atom "=>") ; List (Atom ("and") :: conjuncts) ; _ ] -> conjuncts
            | _ -> raise (Failure "CHC Body is not formatted correctly. ") 
    in let guard_cands : string list list = get_loop_guard_expressions tail
    (** pattern match for Some / None *)
    (* in let guard_cands : string list list = match guard_cands with
        | Some x -> x
        | None -> "" *)
    (** check whether the guard expression contains the right counter variable for first and second argument of guard expression *)
    in let [@warning "-8"] guards : string list list = List.filter guard_cands ~f:(fun 
        [_;v1;v2] -> String.equal v1 counter_tail_variable || String.equal v2 counter_tail_variable)
    (** Assumption: only one guard candidate left in single loop scenario *)
    in let guard: string list = List.nth_exn guards 0 in
    (* print_list guard; *)
    (* in let ctrs = List.map guard_cands ~f:(fun c -> str_split c) guard_cands is already a string list) *)
    (* TODO for each counter get the second string which should be the variable that is used in the remaining tail with an increment or decrement *)
    (* in let counter_vars = List.map guards ~f:(match c with [rel;ctr;bound] -> ctr) *) (** old stuff *)
    (* for each such variable look for an expression containing + or - and save it to a tuple of guard expression * boolean (true if increment, false if decrement) *)
    (* filter out guard_cands that don't match with a increment or decrement *)

    (*find increment/decrement expressions*)
    let assignments: string list = List.filter ~f:(fun s -> not (String.equal s "")) 
            (find_counter_updates counter_tail_variable counter_head_variable tail) in
  
    (* print_list assignments; *)

    (** ASSUMPTION: only one expression that increments/decrements the counter in a single loop scenario *)
    let assmnt: string = List.nth_exn assignments 0 in 
    let is_inc = contains assmnt "+" 
    in { inv_index = invariant_index 
        ; counter =  counter_tail_variable 
        ; counter_primed = counter_head_variable 
        ; guard_expression = guard
        ; is_inc = is_inc 
        }
    

 (* TODO let check_guard_candidates (cand : loop_guard) (constr: chc list): (int * string * string) = *)
    (* ( 0, "", "" )  *)

let rec find_init (lst: (int * string list) list) (inv:int) : string =
    match lst with
        | [] -> ""
        | h::t -> match h with 
            | (i, lst) -> if i = inv then List.nth_exn lst 1 else find_init t inv


    
let add_counter (obj : t) : t = 
    let uninterpreted_funcs = obj.uninterpreted_functions in 
    let constraints = obj.constraints in
    let ind_constraints = List.filter ~f:(fun c -> c.is_ind) constraints in
    (** assumes one inductive chc and one invariant *)
    let counter_candidates: loop_guard list = List.map ~f:find_guard_candidates ind_constraints in 
    
    (* TODO countercheck counter_candidates by checking whether the loop guard is actually a loop guard *)
    (* TODO: check queries with Z3 by discharging loop_guard and not negated_loop_guard to be unsat *)
    (* let count = List.map ~f:(fun c -> check_guard_candidates counter_candidates constraints queries) counter_candidates in  *)


    (** take the first loop_guard, assumption: there's only one *)
    (** to generalize do the remaining code of this method for each counter_cand *)
    let counter_cand: loop_guard = match counter_candidates with 
        | h::_ -> h 
        | [] -> raise (Parse_Exn ("No loop counter found. "))
    in 

    (* get ranges *)
    (** assumption: only one initialization chc, since the query is saved in queries, not constraints *)
    (** to generalize check for a tail that doesn't contain the invariant you're currently investigating*)
    let inits: chc list = List.filter ~f:(fun c -> not c.is_ind) constraints 
    in let init = List.nth_exn inits 0
    in let init_head = init.head in
    (* print_invlist init_head; *)
    let counter_init: string = find_init init_head counter_cand.inv_index
    
    in let leftBound = if counter_cand.is_inc then counter_init else counter_cand.counter
    (* assumption: simple loops contain the upper bound in the query, for multiple loops: need to check all chcs containing invariant in tail *)
    (* to generalize let post_conditions = List.filter constraints ~f:(fun c 
            -> (not c.is_ind && contains_inv_in_tail)) in *)
    in let [@warning "-8"] upper = match counter_cand.guard_expression with 
            [_;l;r] -> if String.equal l counter_cand.counter then r else l

    (** assumption: if the counter is incremented the invariant will range from 0 (or initial value) to counter, if decrement it will range from i to N *)
    in let rightBound = if counter_cand.is_inc then counter_cand.counter else upper 

    (** count is the triple of *)
    in let count: (int * string * string) = (1, leftBound, rightBound) in
    (* let count = List.map ~f:(fun c -> (c.inv_index c.counter c.guard_expression)) counter_candidates in  *)
    let ui = uninterpreted_funcs.(0) in
    let ui_updated = {
            args = ui.args ;
            name = ui.name ;
            counters = [count];
            return = ui.return ;
            expressible = ui.expressible ;
    } in 
        Array.set uninterpreted_funcs 0 ui_updated;    (* assumes a single loop invariant *)
        {obj with uninterpreted_functions = uninterpreted_funcs}
    





