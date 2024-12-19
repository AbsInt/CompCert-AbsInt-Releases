open AST

(* Function to get the target specific register class for AST types.
   We have two main register classes:
     0 for integer registers
     1 for floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation. *)

let class_of_type = function
  | Tint | Tlong -> 0
  | Tfloat | Tsingle -> 1
  | Tany32 -> 0
  | Tany64 -> 0


let interferes_caller_save tv mr = not (Conventions1.is_callee_save mr)

include ArchitectureInterface
