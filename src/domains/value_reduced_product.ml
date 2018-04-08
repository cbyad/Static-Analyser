open Abstract_syntax_tree
open Value_reduction
open Value_domain

module ReducedProduct(R : VALUE_REDUCTION) =
  (struct
    module A = R.A
    module B = R.B
    type t = R.t (* A.t * B.t *)

    let top = A.top,B.top
    let bottom = A.bottom,B.bottom
    let const c = R.reduce (A.const c , B.const c) 
    let rand x y =  (A.rand x y ,B.rand x y )
    (* arithmetic operations *)

    (* set-theoretic operations *)
    let join (x:t) (y:t) : t = R.reduce (A.join (fst x)(fst y),B.join (snd x)(snd y) )
    let meet (x:t) (y:t) : t = R.reduce (A.meet (fst x) (fst y) ,B.meet (snd x)(snd y))
    let widen (x:t) (y:t) : t =  (A.widen (fst x ) (fst y) ,B.widen (snd x)(snd y))
    let subset (x:t) (y:t) : bool = (A.subset (fst x) (fst y )) && (B.subset (snd x) (snd y))
  
    (* comparison operations (filters) *)

    (* check the emptyness of the concretization *)
    let is_bottom x = A.is_bottom (fst x) && B.is_bottom (snd x) 

    (* prints abstract element *)

    let print fmt x =
        begin
            A.print fmt (fst x);
            Format.fprintf fmt " ∧ ";
            B.print fmt (snd x);
        end 

    (* operator dispatch *)
    let unary x op =R.reduce(A.unary (fst x) op ,B.unary (snd x) op)
    let binary x y op =R.reduce( A.binary (fst x) (fst y) op ,B.binary (snd x) (snd y) op)

    let compare a b op =
      match (A.compare (fst a) (fst b) op), (B.compare (snd a) (snd b) op) with 
      | (x,y), (z, w)-> (R.reduce (x, z), R.reduce (y, w))
                      
    let bwd_unary a op r = R.reduce (A.bwd_unary (fst a) op (fst r), B.bwd_unary (snd a) op (snd r))

    let bwd_binary a b op r =
      match (A.bwd_binary (fst a) (fst b) op (fst r), B.bwd_binary (snd a) (snd b) op (snd r)) with 
      | (x, y), (z, w) -> (R.reduce (x, z), R.reduce (y, w)) 

    (****************************)
    let get_value x y = invalid_arg "don't use just to write something"
    (****************************)

  end : VALUE_DOMAIN)