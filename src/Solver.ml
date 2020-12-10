open Core_kernel

open Exceptions
open SyGuS
open Utils

module Config = struct
  type 'a t = {
    _PIE : PIE.Config.t ;

    base_random_seed : string ;
    describe : (('a Job.feature Job.with_desc) CNF.t option) -> Job.desc ;
    max_array_template_size : int ;
    max_counterexamples : int ;
    user_features: (string * string) list ;
  }

  let default : 'a t = {
    _PIE = PIE.Config.default ;

    base_random_seed = "LoopInvGen" ;
    describe = PIE.cnf_opt_to_desc ;
    max_array_template_size = 8 ;
    max_counterexamples = 1 ;
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

exception CounterExample of chc_counterex
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

let negate (chc : SyGuS.chc) (cex : chc_counterex) : string =
  if List.length chc.head_ui_calls > 0 && List.length chc.tail_ui_calls > 0
  then negate_states (chc.head_ui_calls @ chc.tail_ui_calls) (cex.head_states @ cex.tail_states)
  else if List.length chc.head_ui_calls > 0
       then negate_states chc.head_ui_calls cex.head_states
       else negate_states chc.tail_ui_calls cex.tail_states

let grab_counterexample_states ~(z3 : ZProc.t) (chc : chc) : chc_counterex =
  {
    head_states = List.(map chc.head_ui_calls ~f:(fun (i,terms) -> (i, map terms ~f:(ZProc.evaluate z3)))) ;
    tail_states = List.(map chc.tail_ui_calls ~f:(fun (i,terms) -> (i, map terms ~f:(ZProc.evaluate z3))))
  }

let more_counterexamples_exist ?(config = Config.default) ~(z3 : ZProc.t) ~(db : string list) (chc : chc) : chc_counterex option =
  let array_variables = List.filter chc.args ~f:(function (_, Type.ARRAY _) -> true | _ -> false) in
  let exist_more_cexs = ZProc.check_sat z3 ~db ~scoped:false
   in if config.max_array_template_size < 1 || List.is_empty array_variables
      then (if exist_more_cexs then None else Some (grab_counterexample_states ~z3 chc))
      else try
             List.(iter (range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 config.max_array_template_size)
                        ~f:(fun template_size -> Log.debug (lazy ("Restricting arrays to template size " ^ (Int.to_string template_size)))
                                               ; let template_size_range = range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 template_size in
                                                 let template_db = (
                                                       concat_map array_variables
                                                                  ~f:(fun [@warning "-8"] (name, Type.ARRAY (k_type, v_type))
                                                                      -> ("(declare-const _" ^ name ^ "_template_default_var_ " ^ (Type.to_string v_type) ^ ")")
                                                                      :: (concat_map template_size_range
                                                                                     ~f:(fun i -> [ ("(declare-const _" ^ name ^ "_template_k_var_" ^ (Int.to_string i) ^ "_ " ^ (Type.to_string v_type) ^ ")")
                                                                                                  ; ("(declare-const _" ^ name ^ "_template_v_var_" ^ (Int.to_string i) ^ "_ " ^ (Type.to_string v_type) ^ ")") ])))
                                                 ) in let template_constraints = map array_variables
                                                                                  ~f:(fun (v,t) -> "(assert (= " ^ v ^ " "
                                                                                                 ^ (fold template_size_range ~init:("((as const " ^ (Type.to_string t) ^ ") _" ^ v ^ "_template_default_var_)")
                                                                                                                       ~f:(fun acc i -> "(store " ^ acc ^ " _" ^ v ^ "_template_k_var_" ^ (Int.to_string i) ^ "_ _" ^ v ^ "_template_v_var_" ^ (Int.to_string i) ^ "_)"))
                                                                                                 ^ "))")
                                                       in ZProc.create_scope z3
                                                        ; if not (ZProc.check_sat z3 ~db:(template_db @ template_constraints) ~scoped:false)
                                                          then ZProc.close_scope z3
                                                          else begin
                                                            let cex = grab_counterexample_states ~z3 chc
                                                             in ZProc.close_scope z3
                                                              ; raise (CounterExample cex)
                                                          end)) ;
             None
           with CounterExample cex -> Some cex

let check ?(config = Config.default) ~(z3 : ZProc.t) (sygus : SyGuS.t) (candidates : candidate array) : unit =
  ZProc.create_scope z3 ~db:(Array.to_rev_list_map candidates
                                                   ~f:(fun c -> SyGuS.func_definition { c.func with body = c.solution })) ;
  List.iter (sygus.queries @ sygus.constraints)
            ~f:(fun chc -> ZProc.create_scope z3
                         ; if check_chc ~scoped:false ~z3 chc
                           then ZProc.close_scope z3
                           else begin
                             Log.debug (lazy ("CHC " ^ chc.name ^ " is violated! Collecting " ^ (Int.to_string config.max_counterexamples) ^ " counterexamples ...")) ;
                             try let counterexamples = List.(
                                   fold (range 0 config.max_counterexamples) ~init:[]
                                        ~f:(fun acc i -> match more_counterexamples_exist ~config ~z3 ~db:(if i = 0 then [] else [ negate chc (hd_exn acc) ]) chc with
                                                         | None -> raise (CounterExamples acc)
                                                         | Some cex -> cex  :: acc))
                                  in raise (CounterExamples counterexamples)
                             with CounterExamples counterexamples
                                  -> ZProc.close_scope z3
                                   ; ZProc.close_scope z3
                                   ; raise (CounterExamples counterexamples)
                           end) ;
  ZProc.close_scope z3

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
                          ; ZProc.create_scope z3 ~db:(List.map ~f:SyGuS.var_declaration candidates.(i).func.args)
                          ; candidates.(i) <- { candidates.(i) with
                                                solution = config.describe (fst (
                                                             PIE.learnPreCond ~config:config._PIE ~consts:sygus.constants candidates.(i).job
                                                           ))}
                          ; ZProc.close_scope z3)
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
                        ~f:(fun (func, _) -> { job = (Job.create ~args:func.args ())
                                             ; func
                                             ; solution = "false"
                                             ; weakest_solution = "true"
                                             })
   in ZProc.process
        ~zpath
        ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic config.base_random_seed)
                                                                    (Generator.small_non_negative_int)))))
        (fun z3 -> SyGuS.setup_z3 sygus z3
                 ; Array.iteri cands
                              ~f:(fun i cand
                                  -> cands.(i) <- {
                                       cands.(i) with
                                       job = (List.fold (snd sygus.uninterpreted_functions.(i))
                                                        ~init:cands.(i).job
                                                        ~f:(fun job e -> Job.add_feature ~job ((ZProc.build_feature ~z3 (List.map ~f:fst cand.func.args) e), e))) })
                 ; solve_impl ~config ~z3 sygus cands)
