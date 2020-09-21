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
  info : SyGuS.func ;
  solution : string ;
  job : Job.t ;
}

type chc_counterex = {
  q_type : [`Query | `Constraint ] ;
  chc : SyGuS.chc ;
  states : ZProc.model
}

exception CounterExample of chc_counterex

let check_chc ~(z3 : ZProc.t)
              (c : SyGuS.chc)
              : ZProc.model option =
  let db = List.fold c.args ~init:[ "(assert (not " ^ c.body ^ "))" ]
                     ~f:(fun acc v -> (SyGuS.var_declaration v) :: acc)
   in ZProc.get_sat_model z3 ~db ~eval_term:c.body

let check ~(z3 : ZProc.t)
          (sygus : SyGuS.t)
          (candidates : candidate list)
          : unit =
  ZProc.create_scope z3 ~db:(List.map candidates ~f:(fun c -> SyGuS.func_definition { c.info with body = c.solution })) ;
  List.iter sygus.queries
            ~f:(fun q -> match check_chc z3 q with
                         | None -> ()
                         | Some model -> raise (CounterExample { q_type = `Query ; chc = q ; bindings = model })) ;
  List.iter sygus.constraints
            ~f:(fun q -> match check_chc z3 q with
                         | None -> ()
                         | Some model -> raise (CounterExample { q_type = `Constraint ; chc = q ; bindings = model })) ;
  ZProc.close_scope z3

let solve ?(config = Config.default)
          ~(zpath : string)
          (sygus : SyGuS.t)
          (candidates : candidate list)
          : SyGuS.func list =
  ZProc.process
    ~zpath
    ~random_seed:(Some config.base_random_seed)
    (fun z3
     -> []
    )