open Core

open LoopInvGen

open Exceptions
open Type

let target_equal t1 t2 =
  let open Unification in
  match t1, t2 with
  | TYPE_ i1, TYPE_ i2 -> Int.equal i1 i2
  | SIZE_ i1, SIZE_ i2 -> Int.equal i1 i2
  | _ -> false

let are_bindings_equal =
  List.equal (Tuple.T2.equal ~eq1:target_equal ~eq2:equal)

let monomorphic () =
  let domain1 = [ INT ; STRING ] in
  let domain2 = [ INT ; STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let bindings_correct = [] in
  let res = are_bindings_equal bindings bindings_correct
   in Alcotest.(check bool) "identical" true res

let without_dependencies () =
  let domain1 = [ ARRAY (TVAR 1, TVAR 2) ; INT ; STRING ] in
  let domain2 = [ ARRAY (INT,BOOL) ; INT ; STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let bindings_correct = [(Unification.TYPE_ 1, INT); (Unification.TYPE_ 2, BOOL)] in
  let res = are_bindings_equal bindings bindings_correct
   in Alcotest.(check bool) "identical" true res

let with_dependencies () =
  let domain1 = [ ARRAY (TVAR 1, TVAR 2) ; LIST(TVAR 1) ] in
  let domain2 = [ ARRAY (STRING,INT) ; LIST STRING ] in
  let bindings = Unification.of_types_exn domain1 domain2 in
  let correct_bindings = [(Unification.TYPE_ 1, STRING) ; (Unification.TYPE_ 2, INT)] in
  let res = are_bindings_equal bindings correct_bindings
   in Alcotest.(check bool) "identical" true res

let indirect_circular () =
  let domain1 = [(TVAR 1) ; ARRAY(TVAR 1,INT)] in
  let domain2 = [(ARRAY(INT,INT)) ; ARRAY(INT,INT)] in
  let test () = ignore (Unification.of_types_exn domain1 domain2)
   in Alcotest.check_raises "cannot unify" (Unification_Exn "Circular dependency!") test

let direct_circular () =
  let domain1 = [ ARRAY (ARRAY(INT,TVAR 1) , TVAR 1) ] in
  let domain2 = [ ARRAY (ARRAY(TVAR 2,TVAR 1) , INT) ] in
  let test () = ignore (Unification.of_types_exn domain1 domain2)
   in Alcotest.check_raises "cannot unify" (Unification_Exn "Circular dependency!") test

let substitution () =
  let env = [(Unification.TYPE_ 1, STRING) ; (Unification.TYPE_ 2, INT)] in
  let codomain = ARRAY(TVAR 2 , TVAR 1) in
  let resolved_codomain = ARRAY(INT,STRING) in
  let res = match Unification.substitute env codomain with
            | Some res -> equal res resolved_codomain
            | None -> false
   in Alcotest.(check bool) "correct application of env" true res

let incomplete_substitution () =
  let env = [(Unification.TYPE_ 1, INT)] in
  let codomain = ARRAY(TVAR 1 , TVAR 2) in
  let resolved_codomain = ARRAY (INT ,INT) in
  let res = match Unification.substitute env codomain with
            | Some res -> equal res resolved_codomain
            | None -> false
   in Alcotest.(check bool) "incorrect application of env" false res

let all = [
  "Unif. of monomorphic types",   `Quick, monomorphic ;
  "Unif. without dependencies",   `Quick, without_dependencies ;
  "Unif. with dependencies",      `Quick, with_dependencies ;
  "Direct circular dependency",   `Quick, direct_circular ;
  "Indirect circular dependency", `Quick, indirect_circular ;
  "Substitution",                 `Quick, substitution ;
  "Incomplete substitution",      `Quick, incomplete_substitution ;
]