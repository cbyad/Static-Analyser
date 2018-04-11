open Abstract_syntax_tree
open Value_reduction
open Parity_domain
open Interval_domain

module ParityIntervalsReduction =(struct

    module A = Parity  
    module B = Intervals

    type t = A.t * B.t

    let is_even (x:Z.t) : bool = Z.is_even x

    let is_a_part_of (x:Z.t) set :bool = 
        let x_pair = is_even x in match set with 
            (*Same value define in parity_domain.ml, this is a trick to deal with parity ... we can do better!!*)
            |(-1) -> false
            |2018-> true 
            |2 -> x_pair
            |1 -> not x_pair
            |_ -> invalid_arg "oups "

                
    let reduce ((par,itv):t) : t = 
     if B.is_bottom itv || A.is_bottom par then A.bottom,B.bottom else
        let  a = Z.of_int (B.get_value itv 1) in
        let  b = Z.of_int (B.get_value itv 2) in 
        let  parity= A.get_value par 55 in (* 55 0r others int (not important) *)
    
            let a' = if (is_a_part_of a parity) then a else (Z.add a Z.one)  in
            let b' = if (is_a_part_of b parity) then b else (Z.sub b Z.one)  in 

            if (Z.gt a' b') then A.bottom,B.bottom 
            else if (Z.equal a' b') then 
                let new_parity = if is_even a then A.const (Z.of_int 2) else A.const (Z.one) in
                new_parity,(B.rand a' b')
            else par,(B.rand a' b')

end : VALUE_REDUCTION)