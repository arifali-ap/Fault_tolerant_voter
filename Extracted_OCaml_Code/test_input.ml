open Voter_state_transition
(*function to convert int to nat*)
let rec  int_to_nat n =
  if n<=0 then O else S (int_to_nat (n-1))

(*function to convert nat to int*)
let rec nat_to_int n=
  match n with 
    O->0|
    S x->1+nat_to_int x

(*intial voter_state*)
let sig_init:signal={
    val0=int_to_nat 0;
    hw_hlth=Good;
  }

let u_status_init:unit_status={
    iso_status =Not_isolated;
    miscomp_status=Not_miscomparing;
    risky_count=int_to_nat 0;
  }

let voter_state_init:voter_state=
  let ls=List.init
           5(fun i->{
               u_output={
                 reading=sig_init;
                 
                 uid=int_to_nat( i+1);
               };
               u_status=u_status_init;}
           )  in
  {
    u_data_lst=ls;
    
    voter_output={
        reading=sig_init;
        uid=(int_to_nat 1);
      };
    
    voter_validity=Valid;
    
    output_age=int_to_nat 0;
    
    presrvd_data=List.hd ls;
  }
(*end of initial voter_state*)



(*sample input *)
let sample_lst:unit_output list=[
    (*first value*)  {      
      reading={
        val0=int_to_nat 10;
        hw_hlth=Good;
      };
      uid=int_to_nat 1;
    };
    (*second value*) {      
      reading={
        val0=int_to_nat 9;
        hw_hlth=Good;
      };
      uid=int_to_nat 2;
    };
    (*third value*) {
        reading={
          val0=int_to_nat 11;
          hw_hlth=Bad;
        };
        uid=int_to_nat 3;
      };
    (*fourth value*)  {
        reading={
          val0=int_to_nat 8;
          hw_hlth=Good;
        };
        uid=int_to_nat 4;
      };
    (*fifth value*)    {
        reading={
          val0=int_to_nat 15;
          hw_hlth=Good;
        };
        uid=int_to_nat 5;
      };
  ];;

(*end of sample input *)


(voter_state_transition  voter_state_init sample_lst);;
