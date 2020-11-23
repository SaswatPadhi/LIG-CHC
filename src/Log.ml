let indented_sep (indent : int) = "\n" ^ (String.make (45 + indent) ' ')

type level = Trace | Debug | Error | Info

[%%import "config.h"]

[%%if LOGGING = 0]
  (* If logging has been entirely disabled during compilation *)

  let trace _ = ()
  let debug _ = ()
  let info  _ = ()
  let error _ = ()
  
  let disable () = ()

  let [@warning "-27"] enable ?msg ?level _ = ()
[%%else]
  (* If logging has not been disabled, a user may still choose not to log
   * during a particular execution. Logging functions therefore accept `lazy`
   * strings that are forced only when they are actually logged. *)

  let level_str = function Trace -> "( trace )"
                         | Debug -> "[ debug ]"
                         | Info  -> "[  info ]"
                         | Error -> "< ERROR >"

  let log_chan = ref stderr
  let log_level = ref Debug

  let is_enabled = ref false
  let should_log level =
    if not !is_enabled then false
    else match level, !log_level with
         | Error , _ | Info , Info | Info, Debug | Debug, Debug | _ , Trace -> true
         | _ -> false

  let do_log level lstr =
    if should_log level
    then begin
      let open Core in
      Out_channel.fprintf
        !log_chan
        "%s  %s  %s\n"
        Time.(to_string (now ()))
        (level_str level)
        (Lazy.force lstr)
    end

    let trace lstr = do_log Trace lstr
    let debug lstr = do_log Debug lstr
    let info lstr = do_log Info lstr
    let error lstr = do_log Error lstr

  let disable () = is_enabled := false

  let enable ?(msg = "") ?(level = Debug) = function
    | None -> ()
    | Some filename
      -> log_chan := Core.Out_channel.create ~append:true filename
       ; log_level := level
       ; is_enabled := true
       ; info (lazy "")
       ; info (lazy (msg ^ String.(make (79 - (length msg)) '=')))
[%%endif]
