open Core_kernel

type t = {
  name : string ;
  components_per_level : Expr.component list array ;
  sample_set_size_multiplier : int ;
  z3_name : string
}

(* TODO: Think about better strategies for combining grammar levels across multiple theories.
         Given levels L1 = {Ga_1 ⊆ ... Ga_m} and L2 = {Gb_1 ⊆ ... Gb_n}, such that n > m,
         currently I pad L1 with Ga_m at the end such that |L1| = |L2| and take a pairwise union. *)

let rec ( ** ) = fun x y ->
  if Array.(length y > length x) then y ** x
  else Array.(map ~f:(fun (ex,ey) -> ex @ ey)
                  (zip_exn x (append y (create (last y) ~len:(length x - length y)))))

let all_supported =
   let table = String.Table.create () ~size:8
   in List.iter ~f:(fun component -> String.Table.set table ~key:component.name ~data:component)
                [{
                   name = "ALIA" ;
                   (* FIXME: Determine levels of ArrayComponents for hybrid enumeration *)
                   components_per_level = ArrayComponents.read_only_levels
                                       ** BooleanComponents.levels
                                       ** IntegerComponents.linear_levels ;
                   sample_set_size_multiplier = 2 ;
                   z3_name = "ALL"
                 } ; {
                   name = "ALL" ;
                   (* FIXME: The verification side for lists, especially with transformed components,
                             doesn't work as of now -- we need to emit valid SMTLIB expressions for them *)
                   components_per_level = ArrayComponents.read_only_levels
                                       ** BooleanComponents.levels
                                       ** IntegerComponents.non_linear_levels
                                       ** BitVecComponents.levels
                                       ** ListComponents.levels ;
                   sample_set_size_multiplier = 8 ;
                   z3_name = "ALL"
                } ; {
                   name = "ANIA" ;
                   (* FIXME: Determine levels of ArrayComponents for hybrid enumeration *)
                   components_per_level = ArrayComponents.read_only_levels
                                       ** BooleanComponents.levels
                                       ** IntegerComponents.non_linear_levels ;
                   sample_set_size_multiplier = 8 ;
                   z3_name = "ALL"
                 } ; {
                   name = "BV" ;
                   components_per_level = BooleanComponents.levels
                                       ** BitVecComponents.levels ;
                   sample_set_size_multiplier = 1 ;
                   z3_name = "BV"
                 } ; {
                   name = "LIA" ;
                   components_per_level = BooleanComponents.levels
                                       ** IntegerComponents.linear_levels ;
                   sample_set_size_multiplier = 1 ;
                   z3_name = "LIA"
                 } ; {
                   name = "NIA" ;
                   components_per_level = BooleanComponents.levels
                                       ** IntegerComponents.non_linear_levels ;
                   sample_set_size_multiplier = 4 ;
                   z3_name = "NIA"
                 }]
    ; table

let of_string name = String.Table.find_exn all_supported name