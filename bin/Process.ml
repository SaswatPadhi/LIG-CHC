open Core

open LoopInvGen

let command =
  let open Command.Let_syntax in
  Command.basic
    ~summary: "Check, simplify, and optimize a SyGuS-INV problem."
    [%map_open
      let z3_path     = flag "z3-path" (required string)
                             ~doc:"FILENAME path to the z3 executable"
      and bv_to_int   = flag "bv-to-int" (optional_with_default (-1) int)
                             ~doc:"BOOLEAN convert bitvectors to integers"
      and out_path    = flag "out-path" (required string)
                             ~doc:"FILENAME (binary) output file for the post-processed SyGuS problem"
      and log_path    = flag "log-path" (optional string)
                             ~doc:"FILENAME enable logging and output to the specified path"
      and sygus_path  = anon (maybe_with_default "-" ("filename" %: string))
      in fun () -> begin
        Log.enable ~msg:"PROCESS" log_path ;
        let in_chan = Utils.get_in_channel sygus_path in
        let sygus = SyGuS.parse ~bv_to_int (in_chan)
         in SyGuS.(write_to out_path (SyGuS_Post.add_counter sygus))
          ; Stdio.In_channel.close in_chan
      end
    ]

let () =
  Command.run command
