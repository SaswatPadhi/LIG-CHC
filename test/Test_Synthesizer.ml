open Base

open LoopInvGen

open Synthesizer

let check_func task result =
  Array.iteri task.outputs
              ~f:(fun i out -> Alcotest.(check bool)
                                 "identical" true
                                 (Value.equal out (result.func (List.map task.inputs ~f:(fun iv -> iv.(i))))))

let plus_x_y () =
  let task = {
    arg_names = [ "x" ; "y" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 3 ; 7 ; (-1) ; (-4) |]
               ; [| 3 ; 2 ; 13 ; 11 |] ];
    outputs = Array.map ~f:(fun i -> Value.Int i) [| 6 ; 9 ; 12 ; 7 |];
    constants = []
  } in let result = solve task
    in Alcotest.(check string) "identical" "(+ x y)" result.string
     ; check_func task result

let ge_plus_x_z_y () =
  let task = {
    arg_names = [ "x" ; "y" ; "z" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 3 ; 7 ; (-1) ; (-4) ; 6 |]
               ; [| 9 ; (-3) ; (-10) ; 11 ; (-1)  |]
               ; [| 7 ; (-20) ; (-50) ; 11 ; (-1) |] ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| true ; false ; false ; false ; true |];
    constants = []
  } in let result = solve task
    in Alcotest.(check string) "identical" "(>= (+ x z) y)" result.string
    ; check_func task result

let not_or_eq_w_x_eq_y_z () =
  let task = {
    arg_names = [ "w" ; "x" ; "y" ; "z" ];
    inputs = List.map ~f:(Array.map ~f:(fun i -> Value.Int i))
               [ [| 4 ; (-1) ; (-5) ; 1 ; (-1) ; 2 |]
               ; [| 3 ; 7 ; (-1) ; (-4) ; 1 ; 2 |]
               ; [| 9 ; (-3) ; (-10) ; 11 ; (-10) ; 2  |]
               ; [| 1 ; (-6) ; (-10) ; 11 ; (-1) ; (-3) |] ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| true ; true ; false ; false ; true ; false |];
    constants = []
  }in let result = solve task
   in Alcotest.(check string) "identical" "(not (or (= w x) (= y z)))" result.string
    ; check_func task result

let select_a_k () =
  let task = {
    arg_names = [ "a" ; "k" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Value.Array (a,b,c,d))
                 [| (Type.INT, Type.STRING,
                     [ (Int 3, String "30")
                     ; (Int 2, String "20")
                     ; (Int 1, String "10") ],
                     String "1")
                  ; (Type.INT, Type.STRING,
                     [ (Int 2, String "20")
                     ; (Int 1, String "1024") ],
                     String "0")
                  ; (Type.INT, Type.STRING,
                     [ (Int 0, String "0") ],
                     String "30") |]);
      [| Int 1 ; Int 2 ; Int 3 |] ];
    outputs = Value.[| String "10" ; String "20" ; String "30" |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string) "identical" "(select a k)" result.string
     ; check_func task result

let select_a_k__with_duplicates () =
  let task = {
    arg_names = [ "a" ; "k" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT,
                     [ (Int 3, Int 10) ; (Int 3, Int 30) ; (Int 2, Int 20) ; (Int 1, Int 10) ],
                     Int 1)
                  ; (Type.INT, Type.INT,
                     [ (Int 2, Int 20) ; (Int 1, Int 1024) ],
                     Int 0)
                  ; (Type.INT, Type.INT,
                     [ (Int 0 , Int 0)],
                     Int 30) |]);
      [| Int 3 ; Int 2 ; Int 3 |] ];
    outputs = Value.[| Int 10 ; Int 20 ; Int 30 |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string) "identical" "(select a k)" result.string
     ; check_func task result

let store_a_k_v__empty () =
  let task = {
    arg_names = [ "a" ; "k" ; "v" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT, [], Int 1)
                  ; (Type.INT, Type.INT, [], Int 0)
                  ; (Type.INT, Type.INT, [], Int 30) |]);
      [| Int 1 ; Int 2 ; Int 3 |];
      [| Int 20 ; Int 40 ; Int 6 |] ];
    outputs = Value.[| Array (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 1)
                     ; Array (Type.INT, Type.INT, [ (Int 2, Int 40) ], Int 0)
                     ; Array (Type.INT, Type.INT, [ (Int 3, Int 6) ], Int 30) |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string) "identical" "(store a k v)" result.string
     ; check_func task result

let store_a_k_v__nonempty () =
  let task = {
    arg_names = [ "a" ; "k" ; "v"];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT, [ (Int 3, Int 20) ], Int 1)
                  ; (Type.INT, Type.INT, [ (Int 6, Int 20) ], Int 0)
                  ; (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 30) |]);
      [| Int 1 ; Int 2 ; Int 3 |];
      [| Int 20 ; Int 40 ; Int 6 |] ];
    outputs = Value.[| Array (Type.INT, Type.INT,
                              [ (Int 1, Int 20) ; (Int 3, Int 20) ],
                              Int 1)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 2, Int 40) ; (Int 6, Int 20) ],
                              Int 0)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 3, Int 6) ; (Int 1, Int 20) ],
                              Int 30) |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string) "identical" "(store a k v)" result.string
     ; check_func task result

let store_a_k_v__with_duplicates () =
  let task = {
    arg_names = [ "a" ; "k" ; "v" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT, [ (Int 3, Int 20) ], Int 1)
                  ; (Type.INT, Type.INT, [ (Int 6, Int 20) ], Int 0)
                  ; (Type.INT, Type.INT, [ (Int 1, Int 20) ], Int 30) |]);
      [| Int 3 ; Int 2 ; Int 3 |];
      [| Int 10 ; Int 40 ; Int 6 |] ];
    outputs = Value.[| Array (Type.INT, Type.INT,
                              [ (Int 3, Int 10) ; (Int 3, Int 20) ],
                              Int 1)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 2, Int 40) ; (Int 6, Int 20) ],
                              Int 0)
                     ; Array (Type.INT, Type.INT,
                              [ (Int 3 , Int 6) ; (Int 1, Int 20) ],
                              Int 30) |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string) "identical" "(store a k v)" result.string
     ; check_func task result

let simple_forall_test () =
  let task = {
    arg_names = [ "a" ; "i" ; "j" ];
    inputs = Value.[
      (Array.map ~f:(fun (a,b,c,d) -> Array (a,b,c,d))
                 [| (Type.INT, Type.INT,
                     [ (Int 2, Int 3) ; (Int 1, Int 20) ; (Int 5, Int (-4)) ; (Int 4, Int 64) ; (Int 3, Int 40) ; (Int 0, Int 10) ],
                     Int (-10))
                  ; (Type.INT, Type.INT,
                     [ (Int 1, Int 32) ; (Int 2, Int 40) ; (Int 0, Int 16) ; (Int 3, Int (-24)) ; (Int 4, Int 16) ],
                     Int (-2))
                  ; (Type.INT, Type.INT,
                     [ (Int 3, Int (-1)) ; (Int 2, Int (-3)) ; (Int 0, Int 3) ],
                     Int 0)
                  ; (Type.INT, Type.INT,
                     [ (Int 1, Int 24) ; (Int 0, Int 30) ],
                     Int 3)
                  ; (Type.INT, Type.INT,
                     [ (Int 1, Int 24) ; (Int 3, Int 48) ; (Int 2, Int 32) ; (Int 3, Int (-64)) ],
                     Int 0)
                  ; (Type.INT, Type.INT,
                     [ (Int 2, Int 52) ; (Int 3, Int 10) ; (Int 5, Int 24) ; (Int 7, Int 2) ; (Int 4, Int 48) ; (Int 6, Int 64) ],
                     Int 0)
                  |]);
      [| Int 0 ; Int 1 ; Int 3 ; Int 0 ; Int 1 ; Int 2 |];
      [| Int 4 ; Int 4 ; Int 3 ; Int 2 ; Int 3 ; Int 5 |] ];
    outputs = Value.[|
      Bool true ;
      Bool false ;
      Bool false ;
      Bool true ;
      Bool true ;
      Bool false |];
    constants = [ ]
  } in let result = solve ~config:{ Config.default with cost_limit = 10; logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string)
         "identical"
         "(forall ((__idx__ Int)) (=> (and (<= 1 __idx__) (<= __idx__ j)) (>= (select a __idx__) 1)))"
         result.string
     ; check_func task result

let forall_test () =
  let pred elems default_val key =
    let open Value in
    match default_val, (List.Assoc.find elems ~equal:equal key) with
    | (Int def), None -> Bool (def >= 1)
    | _, Some (Int value) -> Bool (value >= 1)
    | _ -> Bool false
   in
  let check elms def i j =
    1 <= j &&
    List.(for_all (range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 j)
                  ~f:(fun k -> Value.(equal (pred elms def (Int k)) (Bool true))))
   in
  let num_data_points = 16 in
  let raw_input_data =
    let config = { TestGen.Config.default with min_int = 0 ; max_int = 16 }
     in List.zip_exn (TestGen.list_of_random_values ~config num_data_points Type.(ARRAY (INT, INT)))
                     (List.zip_exn (TestGen.list_of_random_values ~config:{ config with seed = `Deterministic "seed1"} num_data_points Type.INT)
                                   (TestGen.list_of_random_values ~config:{ config with seed = `Deterministic "seed2"} num_data_points Type.INT))
  in
  let inputs , outputs =
    List.fold_left
      ~init:([[];[];[]], [])
      raw_input_data
      ~f:Value.(fun [@warning "-8"] ([a_inp; i_inp; j_inp], a_out) ((Array (t_k, t_v, elms, def)), ((Int i),(Int j)))
                -> let res = check elms def i j
                    in Log.debug (lazy ("+ " ^ (Bool.to_string res) ^ " -> (" ^ (Int.to_string i) ^ "," ^ (Int.to_string j) ^ ")  ;  "
                                                                    ^ (Value.to_string (Array (t_k, t_v, elms, def)))))
                     ; ([ (Array (t_k, t_v, elms, def)) :: a_inp ; (Int i) :: i_inp ; (Int j) :: j_inp ],
                        ((Bool res :: a_out))))
   in
  let task = {
    arg_names = [ "a" ; "i" ; "j" ];
    inputs = List.map ~f:Array.of_list inputs ;
    outputs = Array.of_list outputs ;
    constants = [ ]
  } in
  let result = solve ~config:{ Config.default with cost_limit = 10; logic = Logic.of_string "ALIA" } task
    in Alcotest.(check string)
         "identical"
         "(forall ((__idx__ Int)) (=> (and (<= 1 __idx__) (<= __idx__ j)) (>= (select a __idx__) 1)))"
         result.string
     ; check_func task result

let ge_y_len_x () =
  let task = {
    arg_names = [ "x" ; "y" ];
    inputs = Value.[
      Array.map ~f:(fun l -> List (Type.INT, (List.map l ~f:(fun i -> Int i))))
                [| [1; (-1); 2]
                 ; [1; (-1); 2]
                 ; [1; (-1); 2]
                 ; [3]
                 ; [1]
                 ; [2] |];
      Array.map ~f:(fun i -> Int i)
                [| 2; 3; 4; 5; 0; (-1) |];
    ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| false; true; true; true; false; false |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALL" } task
    in Alcotest.(check string) "identical" "(>= y (len x))" result.string
     ; check_func task result

let all_mapR_ge_l_0 () =
  let task = {
    arg_names = [ "l" ];
    inputs = Value.[
      Array.map ~f:(fun l -> List (Type.INT, (List.map l ~f:(fun i -> Int i))))
                [| [11; (-1); 0]
                 ; [7; 3; 1]
                 ; [2; (-3)]
                 ; [2]
                 ; [0; 1; 3; 6]
                 ; [(-1); 1; 9]
                 ; [] |]
    ];
    outputs = Array.map ~f:(fun b -> Value.Bool b)
                        [| false; true; false; true; true; false; true |];
    constants = []
  } in let result = solve ~config:{ Config.default with logic = Logic.of_string "ALL" } task
    in Alcotest.(check string) "identical" "(all (map-fixR-int-geq l 0))" result.string
     ; check_func task result

let all = [
  "(+ x y)",                         `Quick, plus_x_y ;
  "(>= (+ x z) y)",                  `Quick, ge_plus_x_z_y ;
  "(not (= (= w x) (= y z)))",       `Quick, not_or_eq_w_x_eq_y_z ;
  "(select a k)",                    `Quick, select_a_k ;
  "(forall ...) ; simple",           `Quick, simple_forall_test ;
  "(forall ...)",                    `Quick, forall_test ;
  "(store a k v) ; empty",           `Quick, store_a_k_v__empty ;
  "(store a k v) ; non-empty",       `Quick, store_a_k_v__nonempty ;
  "(select a k)  ; with duplicates", `Quick, select_a_k__with_duplicates ;
  "(store a k v) ; with duplicates", `Quick, store_a_k_v__with_duplicates ;
  "(>= y (len x))",                  `Quick, ge_y_len_x ;
  "(all (map-fixR-int-geq l 0))",    `Quick, all_mapR_ge_l_0 ;
]