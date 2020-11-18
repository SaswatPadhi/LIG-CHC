let () =
  Alcotest.run ~argv:[| "zpath" |] "LoopInvGen"
    (* FIXME: Find a way to pass command-line arguments within dune's runtest alias *)
    (let zpath = if (Array.length Sys.argv) > 1 then Sys.argv.(1) else ""
      in LoopInvGen.Log.enable (Some "Test.log")
       ; [ "Test_Synthesizer", Test_Synthesizer.all
         ])