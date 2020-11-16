open Core_kernel

open SyGuS
open Utils

module Config = struct
  type 'a t = {
    _PIE : PIE.Config.t ;

    base_random_seed : string ;
    describe : (('a Job.feature Job.with_desc) CNF.t option) -> Job.desc ;
    max_steps_on_restart : int ;
    model_completion_mode : [ `RandomGeneration | `UsingZ3 ] ;
    user_features: (string * string) list ;
  }

  let default : 'a t = {
    _PIE = PIE.Config.default ;

    base_random_seed = "LoopInvGen" ;
    describe = PIE.cnf_opt_to_desc ;
    max_steps_on_restart = 256 ;
    model_completion_mode = `RandomGeneration ;
    user_features = [] ;
  }
end

type candidate = {
  func : SyGuS.func ;
  solution : string ;
  job : Job.t ;
  counters : (int * string * string) list;
}

type chc_counterex = {
  q_type : [`Query | `Constraint ] ;
  chc : SyGuS.chc ;
  head_states : (int * (Value.t list)) list ;
  tail_states : (int * (Value.t list)) list ;
}

exception CounterExample of chc_counterex

let check_chc ?(scoped = true)
              ~(z3 : ZProc.t)
              (c : SyGuS.chc)
              : bool =
  let db = List.fold c.args ~init:[ "(assert (not " ^ c.body ^ "))" ]
                     ~f:(fun acc v -> (SyGuS.var_declaration v) :: acc)
   in not (ZProc.check_sat z3 ~db ~scoped)

let check ~(z3 : ZProc.t)
          (sygus : SyGuS.t)
          (candidates : candidate array)
          : unit =
  ZProc.create_scope z3 ~db:(Array.to_rev_list_map candidates
                                                   ~f:(fun c -> SyGuS.func_forall_definition { c.func with body = c.solution })) ;
  List.iter sygus.queries
            ~f:(fun chc -> ZProc.create_scope z3
                         ; if check_chc ~scoped:false ~z3 chc then ZProc.close_scope z3
                           else let head_states = []
                                and tail_states = List.map chc.tail ~f:(fun (i,terms) -> (i, List.map terms ~f:(ZProc.evaluate z3)))
                                in ZProc.close_scope z3
                                 ; ZProc.close_scope z3
                                 ; raise (CounterExample { q_type = `Query ; chc ; head_states ; tail_states })) ;
  List.iter sygus.constraints
            ~f:(fun chc -> ZProc.create_scope z3
                         ; if check_chc ~scoped:false ~z3 chc then ZProc.close_scope z3
                           else let head_states = List.map chc.head ~f:(fun (i,terms) -> (i, List.map terms ~f:(ZProc.evaluate z3)))
                                and tail_states = List.map chc.tail ~f:(fun (i,terms) -> (i, List.map terms ~f:(ZProc.evaluate z3)))
                                in ZProc.close_scope z3
                                 ; ZProc.close_scope z3
                                 ; raise (CounterExample { q_type = `Constraint ; chc ; head_states ; tail_states })) ;
  ZProc.close_scope z3

let rec solve_impl ?(config = Config.default)
                   (sygus : SyGuS.t)
                   (candidates : candidate array)
                   (z3 : ZProc.t)
                   : SyGuS.func list =
  try check ~z3 sygus candidates
    ; Array.to_rev_list_map candidates ~f:(fun c -> { c.func with body = c.solution })
  with
    | CounterExample cex
      -> begin
           match List.filter cex.tail_states ~f:(fun (i,ts) -> not (Job.has_pos_test ~job:candidates.(i).job ts)) with
            | [] -> begin match [@warning "-8"] cex.head_states with
                      | [] -> raise Exceptions.NoSuchFunction
                      | [ (h,_) ] -> candidates.(h) <- { candidates.(h) with
                                                         solution = "true"
                                                       ; job = (Job.add_pos_test
                                                                  ~job:{ candidates.(h).job with neg_tests = [] }
                                                                  (snd (List.hd_exn cex.head_states))
                                                               )
                                                       }
                    end
            | tail_neg_updates
              -> List.iter tail_neg_updates
                           ~f:(fun (i,ts) -> let job = Job.add_neg_test candidates.(i).job ts in
                                             let solution = config.describe (fst (
                                                              PIE.learnPreCond job ~config:config._PIE ~consts:sygus.constants
                                                            ))
                                              in candidates.(i) <- { candidates.(i) with solution ; job })
         end
       ; solve_impl ~config sygus candidates z3

let solve ?(config = Config.default)
          ~(zpath : string)
          (sygus : SyGuS.t)
          (candidates : candidate array)
          : SyGuS.func list =
  ZProc.process
    ~zpath
    ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic config.base_random_seed)
                                                                (Generator.small_non_negative_int)))))
    (fun z3 -> SyGuS.setup_z3 sygus z3
             ; solve_impl ~config sygus candidates z3)
