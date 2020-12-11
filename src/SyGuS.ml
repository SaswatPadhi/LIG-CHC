(* TODO: Refactor in to ocaml-sygus package. *)

open Core

open Exceptions
open Sexplib.Type
open Utils

type var = string * Type.t

type chc = {
  args : var list ;
  body : string ;
  head_ui_calls : (int * (string list)) list ;
  name : string ;
  tail_ui_calls : (int * (string list)) list ;
}

type func = {
  args : var list ;
  name : string ;
  body : string ;
  return : Type.t ;
  expressible : bool ;
}

type feature = Value.t Job.feature Job.with_desc

type t = {
  logic : string ;
  constants : Value.t list ;
  defined_functions : func list ;
  uninterpreted_functions : (func * string list) array ;
  constraints : chc list ;
  queries : chc list ;
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
       let expr = Transform.remove_lets expr in
       let consts = extract_consts expr
        in ({ name = name
            ; body = (Sexp.to_string_hum expr)
            ; args = args
            ; return = (Type.of_sexp r_typ)
            ; expressible = true (* TODO: Check if function is expressible in the provided grammar, when we sypport it. *)
            }, consts)
  | sexp_list -> raise (Parse_Exn ("Invalid function definition: "
                                  ^ (Sexp.to_string_hum (List(Atom("define-fun") :: sexp_list)))))

let var_declaration ((n, t) : var) : string =
  "(declare-const " ^ n ^ " " ^ (Type.to_string t) ^ ")"

let func_declaration (f : func) : string =
  "(declare-fun " ^ f.name ^ " ("
  ^ (List.to_string_map f.args ~sep:" " ~f:(fun (_, t) -> Type.to_string t))
  ^ ") " ^ (Type.to_string f.return) ^ ")"

let func_definition (f : func) : string =
  "(define-fun " ^ f.name ^ " ("
  ^ (List.to_string_map
       f.args ~sep:" " ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Type.to_string t) ^ ")"))
  ^ ") " ^ (Type.to_string f.return) ^ " " ^ f.body ^ ")"

let check_and_replace_vars uif_names bindings (expr : Sexp.t) : string option =
  let rec helper : Sexp.t -> Sexp.t =
    function [@warning "-8"]
    | List (op :: l) -> if Array.mem uif_names op ~equal:Sexp.equal then raise Exit else
                        List (op :: (List.map l ~f:helper))
    | Atom a -> match List.Assoc.find bindings a ~equal:String.equal with
                | None   -> ignore(Value.of_atomic_string a) ; Atom a
                | Some d -> d
   in try Some (Sexp.to_string_hum (helper expr))
      with _ -> None

let parse_sexps (sexps : Sexp.t list) : t =
  let chc_idx = ref 0 in
  let logic : string ref = ref "" in
  let consts : Value.t list ref = ref [] in
  let defined_funcs : func list ref = ref [] in
  let uninterpreted_funcs : func list ref = ref [] in
  let constraints : (chc * Sexp.t list) list ref = ref [] in
  let queries : chc list ref = ref []
   in List.iter sexps
        ~f:(function
              | List [ (Atom "check-synth") ] -> ()
              | List ( (Atom "set-info") :: _ ) -> ()
              | List ( (Atom "set-option") :: _ ) -> ()
              | List ( (Atom "get-model") :: _ ) -> ()
              | List [ (Atom "set-logic") ; (Atom _logic) ]
                -> if not (String.equal !logic "") then raise (Parse_Exn ("Logic already set to: " ^ !logic))
                 ; logic := String.chop_prefix_exn ~prefix:"CHC_" _logic
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
              | List [ (Atom "constraint") ; List [ (Atom "forall") ; (List vars) ; chc_body ] ]
                -> begin match Transform.remove_lets chc_body with
                     | List [ (Atom "=>") ; tail ; head ]
                       -> consts := (extract_consts tail) @ !consts
                        ; let conjuncts = match tail with
                                          | List ((Atom "and") :: conjuncts) -> conjuncts
                                          | (Atom _) as sexp -> [ sexp ]
                                          | (List ((Atom _) :: _)) as sexp -> [ sexp ]
                                          | _ -> raise (Parse_Exn ("Constraint not in CHC form: " ^ (Sexp.to_string_hum tail)))
                           in
                          let tail_data =
                              match tail with
                              | Atom a
                                -> begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                     | Some (i,_) -> [ (i,[]) ]
                                     | _ -> []
                                   end
                              | List ((Atom "and") :: conjuncts)
                                -> List.filter_map
                                     conjuncts
                                     ~f:(function [@warning "-8"]
                                         | Atom a
                                           -> begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                                | Some (i,_) -> Some (i,[])
                                                | _ -> None
                                              end
                                         | List ((Atom a) :: ops)
                                           -> begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                                | Some (i,_) -> Some (i,(List.map ops ~f:Sexp.to_string_hum))
                                                | _ -> None
                                              end)
                              | List ((Atom a) :: ops)
                                -> begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                     | Some (i,_) -> [ (i,(List.map ops ~f:Sexp.to_string_hum)) ]
                                     | _ -> []
                                   end
                              | _ -> raise (Parse_Exn ("Constraint not in CHC form: " ^ (Sexp.to_string_hum tail)))
                           in begin match head with
                                | Atom "false"
                                  -> queries := { args = List.map ~f:parse_variable_declaration vars
                                                ; name = "_query__" ^ (Int.to_string !chc_idx) ^ "_"
                                                ; head_ui_calls = []
                                                ; tail_ui_calls = tail_data
                                                ; body = "(not " ^ Sexp.to_string_hum tail ^ ")"
                                                } :: !queries
                                | Atom a
                                  -> let head_data = begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                                       | Some (i,_) -> [ (i,[]) ]
                                                       | _ -> []
                                                     end
                                      in constraints := ({ args = List.map ~f:parse_variable_declaration vars
                                                         ; name = "_constraint__" ^ (Int.to_string !chc_idx) ^ "_"
                                                         ; head_ui_calls = head_data
                                                         ; tail_ui_calls = tail_data
                                                         ; body = "(not (=> " ^ (Sexp.to_string_hum tail) ^ " " ^ a ^ ")"
                                                         }, conjuncts)
                                                     :: !constraints
                                | List ((Atom a) :: ops)
                                  -> let head_data = begin match List.findi !uninterpreted_funcs ~f:(fun _ f -> String.equal a f.name) with
                                                       | Some (i,_) -> [ (i,(List.map ops ~f:Sexp.to_string_hum)) ]
                                                       | _ -> []
                                                     end
                                      in constraints := ({ args = List.map ~f:parse_variable_declaration vars
                                                         ; name = "_constraint__" ^ (Int.to_string !chc_idx) ^ "_"
                                                         ; head_ui_calls = head_data
                                                         ; tail_ui_calls = tail_data
                                                         ; body = "(=> " ^ (Sexp.to_string_hum tail) ^ " " ^ (Sexp.to_string_hum head) ^ ")"
                                                         }, conjuncts)
                                                     :: !constraints
                                | _ -> raise (Parse_Exn ("Constraint not in CHC form: " ^ (Sexp.to_string_hum head)))
                              end
                            ; chc_idx := !chc_idx + 1
                     | _ -> raise (Parse_Exn ("Constraint not in CHC form: " ^ (Sexp.to_string_hum chc_body)))
                   end
              | sexp -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp))))
    ; consts := List.dedup_and_sort ~compare:Poly.compare !consts
    ; Log.debug (lazy ("Detected Constants: " ^ (List.to_string_map ~sep:", " ~f:Value.to_string !consts)))
    ; if String.equal !logic ""
      then (logic := "ALL" ; Log.debug (lazy ("Using default logic: ALL")))
    ; let uninterpreted_functions = Array.of_list_map !uninterpreted_funcs ~f:(fun f -> (f, ref []))
       in List.iter !constraints
                    ~f:(fun (chc, tail_conjuncts)
                        -> if not (List.is_empty chc.tail_ui_calls) then
                           if List.length chc.tail_ui_calls > 1 then raise (Invalid_argument "Non-linear CHC detected!")
                           else begin
                             let tail_ui_idx, tail_ui_args = List.hd_exn chc.tail_ui_calls in
                             let func, features = uninterpreted_functions.(tail_ui_idx) in
                             let tail_ui_arg_bindings = List.map2_exn tail_ui_args func.args ~f:(fun a (b,_) -> (a, (Atom b)))
                              in List.iter tail_conjuncts
                                           ~f:(fun conjunct -> match check_and_replace_vars (Array.map uninterpreted_functions ~f:(fun uif -> Atom (fst uif).name)) tail_ui_arg_bindings conjunct with
                                                               | None -> ()
                                                               | Some new_feature -> uninterpreted_functions.(tail_ui_idx) <- (func, ref (new_feature :: !features)))
                           end)
        ; { constants = !consts
          ; logic = !logic
          ; defined_functions = List.rev !defined_funcs
          ; uninterpreted_functions = Array.map uninterpreted_functions ~f:(fun (func,features) -> (func, !features))
          ; constraints = List.map !constraints ~f:fst
          ; queries = !queries
          }

let parse ?(bv_to_int : int = -1) (chan : Stdio.In_channel.t) : t =
  let sexps = Sexplib.Sexp.input_sexps chan in
  let sexps = if bv_to_int < 0 then sexps
              else List.map sexps ~f:(Transform.bv_to_int ~width:bv_to_int)
   in parse_sexps (List.map ~f:Transform.flatten sexps)

let write_to (filename : string) (sygus : t) : unit =
  let out_chan = Stdio.Out_channel.create filename
   in Caml.Marshal.to_channel out_chan sygus []
    ; Stdio.Out_channel.close out_chan

let read_from (filename : string) : t =
  let in_chan = Stdio.In_channel.create filename in
  let sygus = Caml.Marshal.from_channel in_chan
   in Stdio.In_channel.close in_chan
    ; sygus


let setup_z3 ?(user_features = []) (s : t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries z3 [] ~scoped:false ~db:((
    ("(set-logic " ^ (Logic.of_string s.logic).z3_name ^ ")")
    :: (List.map ~f:func_definition s.defined_functions)
     @ user_features)))

let translate_smtlib_expr (expr : string) : string =
  if (String.equal expr "true") || (String.equal expr "false") then expr else
  let open Sexp in
  let rec helper = function
    | List [ (Atom "-") ; (Atom num) ] when (String.for_all num ~f:Char.is_digit)
      -> Atom ("-" ^ num)
    | List [ (Atom "-") ; name ]
      -> List [ (Atom "-") ; (Atom "0") ; name ]
    | List [ (Atom "let") ; List bindings ; body ]
      -> Transform.replace (List.map bindings
                                     ~f:(function [@warning "-8"]
                                         | List [ key ; data ]
                                           -> List [ key ; (helper data) ]))
                           (helper body)
    | List l -> List (List.map l ~f:helper)
    | sexp -> sexp
  in match Sexplib.Sexp.parse expr with
     | Done (sexp, _) -> Sexp.to_string_hum (helper (sexp))
     | _ -> expr (* TODO: parse does not work on single atoms *)
