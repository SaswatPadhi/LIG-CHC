(* TODO: Refactor in to ocaml-sygus package. *)

open Core

open Exceptions
open Sexplib.Type
open Utils

type var = string * Type.t

type chc = {
  args : var list ;
  body : string ;
  head : string ;
  name : string ;
  tail : string ;
}

let empty_chc = {
  args = [] ;
  body = "" ;
  head = "" ;
  name = "" ; 
  tail = "" ;
}

type func = {
  args : var list ;
  name : string ;
  body : string ;
  return : Type.t ;
  expressible : bool ;
}

let empty_func = {
  args = [] ;
  name = "" ;
  body = "" ;
  return = Type.BOOL ;
  expressible = true ;
}

type t = {
  logic : string ;
  constants : Value.t list ;
  defined_functions : func list ;
  uninterpreted_functions : func list ;
  chcs : chc list ;
  query : chc ;
}

let rec extract_consts : Sexp.t -> Value.t list = function
  | List [] -> []
  | (Atom a) | List [Atom a] -> (try [ Value.of_atomic_string a ] with _ -> [])
  | List(_ :: fargs)
    -> let consts = List.fold fargs ~init:[] ~f:(fun consts farg -> (extract_consts farg) @ consts)
        in List.(dedup_and_sort ~compare:Value.compare consts)

let parse_variable_declaration : Sexp.t -> var = function
  | List [ Atom v ; t ] -> (v, (Type.of_sexp t))
  | sexp -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let parse_define_fun : Sexp.t list -> func * Value.t list = function
  | [Atom(name) ; List(args) ; r_typ ; expr]
    -> let args = List.map ~f:parse_variable_declaration args in
       let expr = remove_lets expr in
       let consts = extract_consts expr
        in ({ name = name
            ; body = (Sexp.to_string_hum expr)
            ; args = args
            ; return = (Type.of_sexp r_typ)
            ; expressible = true (* TODO: Check if function is expressible in the provided grammar, when we sypport it. *)
            }, consts)
  | sexp_list -> raise (Parse_Exn ("Invalid function definition: "
                                  ^ (Sexp.to_string_hum (List(Atom("define-fun") :: sexp_list)))))

let func_definition (f : func) : string =
  "(define-fun " ^ f.name ^ " ("
  ^ (List.to_string_map
       f.args ~sep:" " ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Type.to_string t) ^ ")"))
  ^ ") " ^ (Type.to_string f.return) ^ " " ^ f.body ^ ")"

let parse_sexps (sexps : Sexp.t list) : t =
  let chc_idx = 0 in
  let logic : string ref = ref "" in
  let consts : Value.t list ref = ref [] in
  let defined_funcs : func list ref = ref [] in
  let uninterpreted_funcs : func list ref = ref [] in
  let chcs : chc list ref = ref [] in
  let query : chc ref = ref empty_chc
   in List.iter sexps
        ~f:(function
              | List [ (Atom "check-synth") ] -> ()
              | List [ (Atom "set-logic") ; (Atom _logic) ]
                -> if String.equal !logic "" then logic := _logic
                   else raise (Parse_Exn ("Logic already set to: " ^ !logic))
              | List ( (Atom "define-fun") :: func_sexps )
                -> let (func, fconsts) = parse_define_fun func_sexps
                    in if List.mem !defined_funcs func ~equal:(fun x y -> String.equal x.name y.name)
                       (* FIXME: SyGuS format allows overloaded functions with different signatures *)
                       then raise (Parse_Exn ("Multiple definitions of function " ^ func.name))
                       else defined_funcs := func :: !defined_funcs ; consts := fconsts @ !consts
              | List [ (Atom "synth-fun") ; (Atom name) ; (List vars) ; _ ]
                -> uninterpreted_funcs := { args = List.map ~f:parse_variable_declaration vars ;
                                            name ;
                                            body = "" ;
                                            return = Type.BOOL ;
                                            expressible = true }
                                       :: !uninterpreted_funcs
              | List [ (Atom "synth-fun") ; (Atom name) ; (List vars) ; _ ; _ ]
                -> Log.error (lazy ("LoopInvGen currently does not allow custom grammars."))
                 ; uninterpreted_funcs := { args = List.map ~f:parse_variable_declaration vars ;
                                            name ;
                                            body = "" ;
                                            return = Type.BOOL ;
                                            expressible = true }
                                       :: !uninterpreted_funcs
              | List [ (Atom "constraint") ; List [ (Atom "forall") ; (List vars) ; List [ (Atom "=>") ; tail ; (Atom "false") ] ] ]
                -> consts := (extract_consts tail) @ !consts
                 ; query := { args = List.map ~f:parse_variable_declaration vars
                            ; name = "_chc_index__" ^ (Int.to_string chc_idx) ^ "_"
                            ; head = "false"
                            ; tail = Sexp.to_string tail
                            ; body = "(not " ^ (Sexp.to_string tail) ^ ")"
                            }
              | List [ (Atom "constraint") ; List [ (Atom "forall") ; (List vars) ; List [ (Atom "=>") ; tail ; head ] ] ]
                -> consts := (extract_consts tail) @ !consts
                 ; query := { args = List.map ~f:parse_variable_declaration vars
                            ; name = "_chc_index__" ^ (Int.to_string chc_idx) ^ "_"
                            ; head = Sexp.to_string head
                            ; tail = Sexp.to_string tail
                            ; body = "(not " ^ (Sexp.to_string tail) ^ ")"
                            }
              | sexp -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp))))
    ; consts := List.dedup_and_sort ~compare:Poly.compare !consts
    ; Log.debug (lazy ("Detected Constants: " ^ (List.to_string_map ~sep:", " ~f:Value.to_string !consts)))
    ; if String.equal !logic ""
      then (logic := "LIA" ; Log.debug (lazy ("Using default logic: LIA")))
    ; { constants = !consts
      ; logic = !logic
      ; defined_functions = !defined_funcs
      ; uninterpreted_functions = !uninterpreted_funcs
      ; chcs = !chcs
      ; query = !query
      }

let parse (chan : Stdio.In_channel.t) : t =
  parse_sexps (Sexplib.Sexp.input_sexps chan)

let write_to (filename : string) (sygus : t) : unit =
  let out_chan = Stdio.Out_channel.create filename
   in Caml.Marshal.to_channel out_chan sygus []
    ; Stdio.Out_channel.close out_chan

let read_from (filename : string) : t =
  let in_chan = Stdio.In_channel.create filename in
  let sygus = Caml.Marshal.from_channel in_chan
   in Stdio.In_channel.close in_chan
    ; sygus

let translate_smtlib_expr (expr : string) : string =
  if (String.equal expr "true") || (String.equal expr "false") then expr else
  let open Sexp in
  let rec helper = function
    | List [ (Atom "-") ; (Atom num) ] when (String.for_all num ~f:Char.is_digit)
      -> Atom ("-" ^ num)
    | List [ (Atom "-") ; name ]
      -> List [ (Atom "-") ; (Atom "0") ; name ]
    | List [ (Atom "let") ; List bindings ; body ]
      -> replace (List.map bindings
                           ~f:(function [@warning "-8"]
                               | List [ key ; data ]
                                 -> List [ key ; (helper data) ]))
                 (helper body)
    | List l -> List (List.map l ~f:helper)
    | sexp -> sexp
  in match Sexplib.Sexp.parse expr with
     | Done (sexp, _) -> Sexp.to_string_hum (helper (sexp))
     | _ -> expr (* TODO: parse does not work on single atoms *)