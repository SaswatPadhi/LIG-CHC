open Core

open LoopInvGen
open LoopInvGen.Solver
open LoopInvGen.Utils

let config_flags =
  let open Command.Let_syntax in
  [%map_open
    let base_random_seed          = flag "base-random-seed"
                                         (optional_with_default Solver.Config.default.base_random_seed string)
                                         ~doc:"STRING seed for the internal PRNG"
    and max_conflict_group_size   = flag "max-conflict-group-size"
                                         (optional_with_default Solver.Config.default._PIE.max_conflict_group_size int)
                                         ~doc:"INTEGER maximum size of the conflict group to send to the synthesizer"
    and max_expressiveness_level  = flag "max-expressiveness-level"
                                         (optional_with_default Solver.Config.default._PIE._Synthesizer.max_expressiveness_level int)
                                         ~doc:"INTEGER maximum expressiveness level {1 = Equalities ... 6 = Peano Arithmetic}"
    and max_counterexamples       = flag "max-counterexamples"
                                         (optional_with_default Solver.Config.default.max_counterexamples int)
                                         ~doc:"INTEGER number of counterexamples to collect per violation"
    and start_with_true           = flag "bv-to-int"
                                         (optional_with_default Solver.Config.default.start_with_true bool)
                                         ~doc:"BOOLEAN start with `true` as the initial candidate solution(s)"
    in {
      Solver.Config.default with
        _PIE = {
          Solver.Config.default._PIE with
          _Synthesizer = {
            Solver.Config.default._PIE._Synthesizer with
            max_expressiveness_level
          }
        ; max_conflict_group_size
        }
    ; base_random_seed
    ; max_counterexamples
    ; start_with_true
    }
  ]

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Infer a loop invariant sufficient for proving the correctness of the input problem."
    [%map_open
      let z3_path            = flag "z3-path" (required string)
                                     ~doc:"FILENAME path to the z3 executable"
      and log_path           = flag "log-path" (optional string)
                                    ~doc:"FILENAME enable logging and output to the specified path"
      and config             = config_flags
      and sygus_path         = anon ("filename" %: string)
      in fun () -> begin
        Log.enable ~msg:"INFER" log_path ;
        let sygus = SyGuS.read_from sygus_path in
        let logic = Logic.of_string sygus.logic in
        let config = { config with
                       _PIE = { config._PIE with
                                _Synthesizer = { config._PIE._Synthesizer with logic }
                              ; max_conflict_group_size = logic.sample_set_size_multiplier
                                                        * config._PIE.max_conflict_group_size
                              }
                     }
         in let interpretations = Solver.solve ~config ~zpath:z3_path sygus
         in Out_channel.output_string
              Stdio.stdout
              (List.to_string_map interpretations ~sep:"\n" ~f:SyGuS.func_definition)
      end
    ]

let () =
  Command.run command
