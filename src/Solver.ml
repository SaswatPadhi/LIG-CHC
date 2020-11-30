open Core_kernel

open Exceptions
open SyGuS
open Utils

module Config = struct
  type 'a t = {
    _PIE : PIE.Config.t ;

    base_random_seed : string ;
    describe : (('a Job.feature Job.with_desc) CNF.t option) -> Job.desc ;
    max_counterexamples : int ;
    start_with_true : bool ;
    user_features: (string * string) list ;
  }

  let default : 'a t = {
    _PIE = PIE.Config.default ;

    base_random_seed = "LoopInvGen" ;
    describe = PIE.cnf_opt_to_desc ;
    max_counterexamples = 1 ;
    start_with_true = true ;
    user_features = [] ;
  }
end

type candidate = {
  func : SyGuS.func ;
  job : Job.t ;
  solution : string ;
  weakest_solution : string ;
}

type chc_counterex = {
  head_states : (int * (Value.t list)) list ;
  tail_states : (int * (Value.t list)) list ;
}

exception CounterExamples of chc_counterex list

let check_chc ?(scoped = true) ~(z3 : ZProc.t) (c : SyGuS.chc) : bool =
  let db = List.fold c.args ~init:[ "(assert (not " ^ c.body ^ "))" ]
                     ~f:(fun acc v -> (SyGuS.var_declaration v) :: acc)
   in not (ZProc.check_sat z3 ~db ~scoped)

let negate_states expr states : string =
  "(assert (not (and " ^
  List.(to_string_map2 expr states ~sep:" "
                       ~f:(fun (_,terms) (_,vals)
                           -> to_string_map2 terms vals ~sep:" "
                                             ~f:(fun t v -> "(= " ^ t ^ " " ^ (Value.to_string v) ^ " )"))) ^
  ")))"

let negate (chc : SyGuS.chc) (cex : chc_counterex) : string list =
  if List.length chc.head_ui_calls > 0 && List.length chc.tail_ui_calls > 0
  then [ negate_states chc.head_ui_calls cex.head_states ; negate_states chc.tail_ui_calls cex.tail_states ]
  else if List.length chc.head_ui_calls > 0
       then [ negate_states chc.head_ui_calls cex.head_states ]
       else [ negate_states chc.tail_ui_calls cex.tail_states ]


let contains_all (list1: var list) (list2: var list): bool =
  if List.length list1 <> List.length list2 then false 
  else List.fold2_exn ~init:true ~f:(fun a (name1, type1) (name2, type2) -> a && (String.equal name1 name2) && (Type.equal type1 type2)) list1 list2 

let is_equal (list1: var list) (list2: var list): bool = contains_all list1 list2 && contains_all list2 list1

let rec find (uifuncs: SyGuS.func array) (inv_name: string) (inv_args: var list) n =
  let curr = uifuncs.(n) in 
  if (String.equal curr.name inv_name) && (is_equal curr.args inv_args) then n 
  else find uifuncs inv_name inv_args (n+1)

let check ?(config = Config.default) ~(z3 : ZProc.t) (sygus : SyGuS.t) (candidates : candidate array) : unit =
  let uifuncs = sygus.uninterpreted_functions in
  let cands = List.map (Array.to_rev_list_map candidates
            ~f:(fun c -> { c.func with body = c.solution }))  ~f:(fun c -> 
                (* find the index of the corresponding uninterpreted function to replace correct invariant later *)
                let ui_index = find uifuncs c.name c.args 0 in (ui_index, c) 
            ) in
  List.iter (sygus.queries @ sygus.constraints)
            ~f:(fun chc -> 
            List.iter cands
              ~f:(fun (index, cand) ->
                  ZProc.create_scope z3
                         ; if check_chc ~scoped:false ~z3 (SyGuS.replace_inv chc index cand.name cand.body cand.args)
                           then ZProc.close_scope z3
                           else begin
                             Log.debug (lazy ("CHC " ^ chc.name ^ " is violated! Collecting " ^ (Int.to_string config.max_counterexamples) ^ " counterexamples ...")) ;
                             try let counterexamples = List.(
                                   fold (range 0 config.max_counterexamples) ~init:[]
                                        ~f:(fun acc i -> if not (ZProc.check_sat z3 ~db:(if i = 0 then [] else negate chc (hd_exn acc)) ~scoped:false)
                                                         then raise (CounterExamples acc)
                                                         else {
                                                           head_states = List.map chc.head_ui_calls ~f:(fun (i,terms) -> (i, List.map terms ~f:(ZProc.evaluate z3))) ;
                                                           tail_states = List.map chc.tail_ui_calls ~f:(fun (i,terms) -> (i, List.map terms ~f:(ZProc.evaluate z3)))
                                                         } :: acc))
                                  in raise (CounterExamples counterexamples)
                             with CounterExamples counterexamples
                                  -> ZProc.close_scope z3
                                   ; ZProc.close_scope z3
                                   ; raise (CounterExamples counterexamples)
                           end)) 

let rec solve_impl ?(config = Config.default) ~(z3 : ZProc.t) (sygus : SyGuS.t) (candidates : candidate array) : SyGuS.func list =
  try Log.debug (lazy ("Checking validity of CHCs with current candidate interpretations ..."))
    ; check ~config ~z3 sygus candidates
    ; Array.to_rev_list_map candidates ~f:(fun c -> { c.func with body = c.solution })
  with
    | CounterExamples cex_list
      -> let needs_update = ref (Int.Set.empty)
          in List.iter
               cex_list
               ~f:(fun cex -> match List.filter cex.tail_states ~f:(fun (i,ts) -> not (Job.has_pos_test ~job:candidates.(i).job ts)) with
                              | [] -> begin match cex.head_states with
                                        | [] -> raise NoSuchFunction
                                        | [ (h,_) ] -> candidates.(h) <- { candidates.(h) with
                                                                           solution = candidates.(h).weakest_solution
                                                                         ; job = (Job.add_pos_test
                                                                                    ~job:{ candidates.(h).job with neg_tests = [] }
                                                                                    (snd (List.hd_exn cex.head_states)))}
                                        | _ -> raise (Internal_Exn "Impossible case! Multiple atoms in CHC head!")
                                      end
                              | tail_neg_updates
                                -> List.iter tail_neg_updates
                                             ~f:(fun (i,ts) -> candidates.(i) <- { candidates.(i) with
                                                                                   job = Job.add_neg_test candidates.(i).job ts }
                                                             ; needs_update := Int.Set.add !needs_update i ))
           ; Int.Set.iter
               !needs_update
               ~f:(fun i -> Log.debug (lazy ("Updating interpretation of " ^ candidates.(i).func.name))
                          ; candidates.(i) <- { candidates.(i) with
                                                solution = config.describe (fst (
                                                             PIE.learnPreCond candidates.(i).job ~config:config._PIE ~consts:sygus.constants
                                                           ))})
           ; solve_impl ~config ~z3 sygus candidates

let remove_ui_and_negate (ui : func) (query : chc) =
  match Sexp.force_parse query.body with
  | List [ (Atom "not") ; List ((Atom "and") :: conjuncts) ]
    -> let ui_call_args = ref [] in
       let solution_conjuncts =
           List.filter conjuncts ~f:(function List ((Atom func_name) :: call_args)
                                              when String.equal func_name ui.name
                                              -> ui_call_args := call_args
                                               ; List.iter call_args
                                                           ~f:(function Atom _ -> ()
                                                               | _ -> raise (Internal_Exn "CHC in improper format!"))
                                               ; false
                                            | a -> true)
        in if List.is_empty solution_conjuncts
           then "false"
           else begin
             let solution_body =
                 Transform.replace (List.map2_exn !ui_call_args ui.args
                                                  ~f:(fun old_name (new_name,_) : Sexp.t
                                                      -> List [ old_name ; (Atom new_name) ]))
                                   (List [ (Atom "not") ; (List (Atom "and" :: solution_conjuncts)) ]) in
             let solution_body = Sexp.to_string_hum solution_body
              in if List.((length ui.args) = (length query.args))
                 then solution_body
                 else let qvars = List.(filter query.args ~f:(fun (a,_) -> not (mem !ui_call_args (Atom a) ~equal:Sexp.equal)))
                       in "(forall ("
                        ^ (List.to_string_map qvars ~sep:" " ~f:(fun (n,t) -> "(" ^ n ^ " " ^ (Type.to_string t) ^ ")"))
                        ^ ") "
                        ^ solution_body
                        ^ ")"
           end
  | _ -> raise (Internal_Exn "CHC in improper format!")

let solve ?(config = Config.default) ~(zpath : string) (sygus : SyGuS.t) : SyGuS.func list =
  let cands = Array.map sygus.uninterpreted_functions
                        ~f:(fun func -> { job = (Job.create ~args:func.args ())
                                        ; func
                                        ; solution = "true"
                                        ; weakest_solution = "true"
                                        })
   in (if not config.start_with_true then
       List.iter sygus.queries
                 ~f:(fun q -> match q.tail_ui_calls with
                              | [] -> ()
                              | [ (i, _) ] -> let weakest_solution = remove_ui_and_negate sygus.uninterpreted_functions.(i) q
                                               in cands.(i) <- { cands.(i) with
                                                                 weakest_solution
                                                               ; solution = weakest_solution
                                                               }
                              | _ -> raise (Internal_Exn "Non-linear CHC detected!")))
    ; ZProc.process
        ~zpath
        ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic config.base_random_seed)
                                                                    (Generator.small_non_negative_int)))))
        (fun z3 -> SyGuS.setup_z3 sygus z3
                 ; solve_impl ~config ~z3 sygus cands)
