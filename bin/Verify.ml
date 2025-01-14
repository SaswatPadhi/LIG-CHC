open Core

open LoopInvGen
open LoopInvGen.Utils

type result = PASS | FAIL

let check_solution ~zpath ~(sygus : SyGuS.t) in_chan : result =
  let open Sexplib.Sexp in
  let sexps = input_rev_sexps in_chan
   in ZProc.process ~zpath (fun z3->
        ignore (ZProc.run_queries z3 [] ~scoped:false ~db:(
          ("(set-logic " ^ (Logic.of_string sygus.logic).z3_name ^ ")") ::
          (List.map ~f:SyGuS.func_definition sygus.defined_functions) @
          (List.map sexps ~f:Sexp.to_string_hum)
        )) ;
        try
          List.iter (sygus.queries @ sygus.constraints)
                    ~f:(fun q -> if not (Solver.check_chc z3 q) then raise Caml.Exit) ;
          PASS
        with _ -> FAIL
    )

let string_of_result = function
  | PASS -> "PASS"
  | FAIL -> "FAIL"

let exit_code_of_result = function
  | PASS -> 0
  | FAIL -> 10

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Check sufficiency of a generated invariant for proving correctness."
    [%map_open
      let z3_path     = flag "z3-path" (required string)
                             ~doc:"FILENAME path to the z3 executable"
      and bv_to_int   = flag "bv-to-int" (optional_with_default (-1) int)
                             ~doc:"BOOLEAN convert bitvectors to integers"
      and sygus_path  = flag "sygus-path" (required string)
                             ~doc:"FILENAME input file containing the SyGuS-INV problem"
      and log_path    = flag "log-path" (optional string)
                             ~doc:"FILENAME enable logging and output to the specified path"
      and sol_path    = anon (maybe_with_default "-" ("filename" %: string))
      in fun () -> begin
        Log.enable ~msg:"VERIFY" log_path ;
        let sygus = SyGuS.parse ~bv_to_int (get_in_channel sygus_path) in
        let res = try check_solution ~zpath:z3_path ~sygus (get_in_channel sol_path)
                  with _ -> FAIL
        in Out_channel.output_string Stdio.stdout (string_of_result res)
         ; Caml.exit (exit_code_of_result res)
      end
    ]

let () =
  Command.run command
