Require Import Nat.  

  
 

Parameters
    ground_truth 
    simul_max_fault_minus_1 
    persistence_lmt_minus_1    
    num_units
    delta_minus_1 
  : nat.

Definition simul_max_fault    := S simul_max_fault_minus_1.
Definition persistence_lmt    := S persistence_lmt_minus_1.
Definition min_required       := S simul_max_fault.
Definition delta              := S delta_minus_1.
Definition threshold          := 2*delta.
Definition invalid_age        := 2*persistence_lmt.



