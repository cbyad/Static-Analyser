(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Yannick-Alain CB & Rudy Kruissel
*)

(* 
   The interval domain
 *)
open Abstract_syntax_tree
open Value_domain
  
module Intervals = (struct

(* Z U {+/-∞} *)
type bound = |Int of Z.t |PINF |MINF
type t  = Itv of bound*bound |BOT

(* -a *)
let bound_neg (a:bound) : bound = match a with
| MINF -> PINF | PINF -> MINF | Int i -> Int (Z.neg i)

(* a + b *)
let bound_add (a:bound) (b:bound) : bound = match a,b with
| MINF,PINF | PINF,MINF -> invalid_arg "bound_add" (* (+∞)+ (−∞) *)
| MINF,_ | _,MINF -> MINF
| PINF,_ | _,PINF -> PINF
| Int i, Int j -> Int (Z.add i j)

(* a - b *)
let bound_sub (a:bound) (b:bound) : bound = match a,b with 
| MINF,PINF | PINF,MINF -> invalid_arg "bound_sub" (* (+∞)- (−∞) *)
|_-> bound_add a (bound_neg b)

(* a * b *)
let bound_mul (a:bound) (b:bound) : bound = match a,b with 
|MINF,PINF|PINF,MINF -> MINF
|MINF,MINF | PINF,PINF -> PINF
|MINF,Int i| Int i,MINF| PINF, Int i | Int i,PINF when i=Z.zero -> Int Z.zero
|MINF,Int i |Int i,MINF -> if  i>Z.zero then MINF else PINF
|PINF,Int i |Int i,PINF -> if i<Z.zero then MINF else PINF
|Int i , Int j -> Int (Z.mul i j)

let bound_div (a:bound) (b:bound) : bound =match a,b with 
|Int c,MINF |Int c,PINF -> Int Z.zero
|PINF,PINF -> Int Z.zero (* cas particulier!!!*)
|PINF,Int c -> if c>Z.zero then PINF else MINF
|MINF,Int c -> if c>Z.zero then MINF  else PINF
|Int i,Int j -> Int (Z.div i j) 
|_-> invalid_arg "bound_div"

(* compare a et b, retourne -1, 0 ou 1 *)
let bound_cmp (a:bound) (b:bound) : int = match a,b with
| MINF,MINF | PINF,PINF -> 0
| MINF,_ | _,PINF -> -1
| PINF,_ | _,MINF -> 1
| Int i, Int j -> Z.compare i j

(* unrestricted set: [-∞,+∞] *)
    let top = Itv(MINF,PINF)
        
    (* empty set *)
    let bottom = BOT

    (* constant: {c} *)
    let const (a:Z.t): t = Itv(Int a,Int a)

    (* interval: [a,b] *)
    let rand  (a:Z.t)  (b:Z.t) : t = match a,b with 
    |x,y  when  Z.compare x y >0 -> BOT
    |_->Itv(Int a, Int b)


(* set-theoretic operations *)
 
    (* subset inclusion *)  
    let subset (x:t) (y:t) : bool = match x,y with
    |BOT,_ -> true
    |_,BOT -> false
    |Itv (a,b), Itv (c,d) -> bound_cmp a c >=0 && bound_cmp b d <= 0

    let meet (x:t)  (y:t) : t = match x,y with
    |a,b when subset a b -> a
    |a,b when subset b a -> b
    |Itv(a,b),Itv(c,d) when (bound_cmp a c) <=0 && (bound_cmp b d)<=0 -> Itv(c,b)
    |Itv(a,b),Itv (c,d) when (bound_cmp a c >=0) && (bound_cmp b d)>=0 -> Itv(a,d)
    |_ -> BOT

    let join  (x:t)  (y:t) : t = match x,y with 
    |a,b when subset a b -> b
    |a,b when subset b a -> a 
    |Itv(a,b),Itv(c,d) when (bound_cmp a c) <=0 && (bound_cmp b d)<=0 -> Itv(a,d)
    |Itv(a,b),Itv (c,d) when (bound_cmp a c >=0) && (bound_cmp b d)>=0 -> Itv(c,b)
    |_ -> BOT


    (* emptyness testing *)
    let is_bottom t = t=BOT 

    (* print abstract element *)
    (*    [a;b] [-∞;+∞] [a;+∞] [-∞;b]  *)
    let print fmt x = match x with
    |BOT -> Format.fprintf fmt "⊥"
    |Itv(x,y)-> match x,y with 
                |MINF,PINF -> Format.fprintf fmt "[-∞;+∞]"
                |MINF,Int i -> Format.fprintf fmt "[-∞;%s]" (Z.to_string i)
                |Int i ,PINF -> Format.fprintf fmt "[%s;+∞]" (Z.to_string i)
                |Int i ,Int j -> Format.fprintf fmt "[%s;%s]" (Z.to_string i) (Z.to_string j)
                |_-> ()

         
(* extension of f by f (BOT) = BOT *)
let lift1 f x = match x with
| Itv (a,b) -> f a b
| BOT -> BOT

(* the same for f(BOT,_)=f(_,BOT)=BOT*)
let lift2 f x y = match x,y with
|BOT,_ |_,BOT -> BOT
|Itv(a,b),Itv(c,d)-> f a b c d 
   
(* ---------------------------------arithmetic operations--------------------------------- *)

(* -x dans les intervalles *)
let neg (x:t) : t =
lift1 (fun a b -> Itv (bound_neg b, bound_neg a)) x

let add (x:t) (y:t) : t =
lift2 (fun a b c d-> Itv(bound_add a c,bound_add b d)) x y 

let sub (x:t) (y:t) : t =
lift2 (fun a b c d -> Itv(bound_sub a d, bound_sub b c)) x y

(*max between four bounds*)
let max4_mul  (a:bound)  (b:bound)  (c:bound) (d:bound) : bound =
    let res1= match (bound_cmp (bound_mul a c) (bound_mul a d)) with 
      |0 |1 -> bound_mul a c 
      |_ ->  bound_mul a d  in

      let res2=match (bound_cmp (bound_mul b c) (bound_mul b d))  with 
      |0 |1 -> bound_mul b c
      |_ -> bound_mul b d  in

      match (bound_cmp res1 res2) with 
      |0 |1 -> res1 
      |_ -> res2

(*min between four bounds*)
let min4_mul  (a:bound)  (b:bound)  (c:bound) (d:bound) : bound =
    let res1= match (bound_cmp (bound_mul a c) (bound_mul a d)) with 
      |0|1 -> bound_mul a d 
      |_ -> bound_mul a c in

      let res2=match (bound_cmp (bound_mul b c) (bound_mul b d)) with 
      |0|1 -> bound_mul b d
      |_ -> bound_mul b c in

      match (bound_cmp res1 res2) with 
      |0 |1 -> res2
      |_ -> res1

let mul (x:t) (y:t) : t =
lift2 (fun a b c d -> Itv(min4_mul a b c d ,max4_mul a b c d)) x y

let min2_div (a:bound) (b:bound) (c:bound) (d:bound) : bound = match c,d with 
    |Int i,_ when i>=Z.of_int 1 -> (match (bound_cmp (bound_div a c) (bound_div a d)) with
                                        |0|1 -> bound_div a d
                                        |_ -> bound_div a c )
    |_ -> (match (bound_cmp (bound_div b c) (bound_div b d)) with
                                        |0|1 -> bound_div b d
                                        |_ -> bound_div b c )
    
 let max2_div (a:bound) (b:bound) (c:bound) (d:bound) : bound = match c,d with 
    |Int i,_ when i>=Z.of_int 1 -> (match (bound_cmp (bound_div b c) (bound_div b d)) with
                                        |0|1 -> bound_div b c
                                        |_ -> bound_div b d )
    |_-> (match (bound_cmp (bound_div a c) (bound_div a d)) with
                                        |0|1 -> bound_div a c
                                        |_ -> bound_div a d )
     
let div (x:t) (y:t) : t = match y with 
    |Itv(_,Int i) when i=Z.zero ->BOT
    |Itv(Int i,_) when i=Z.zero ->BOT
    |_ -> let left = meet y (Itv( Int(Z.of_int 1) , PINF)) in 
          let rigth = meet y (Itv (MINF,Int(Z.of_int (-1)))) in

(* (don't know for the moment why didn't work)
          let res1= lift2 (fun a b c d ->Itv(min2_div a b c d , max2_div a b c d)) x left in
          let res2= lift2 (fun a b c d ->Itv(min2_div a b c d , max2_div a b c d)) x rigth in 
*)
          let res1= lift2 (fun a b c d ->Itv(min2_div a b d d , max2_div a b c d)) x left in
          let res2= lift2 (fun a b c d ->Itv(min2_div a b c c , max2_div a b c d)) x rigth in 
          join res1 res2
(*---------------------------------------------------------------------------*)
            
     (* unary operation *)
    let unary (x:t) (op:int_unary_op) :t = match op with
    |AST_UNARY_PLUS -> x
    |AST_UNARY_MINUS -> neg x
    
    (* binary operation *)
    let binary (x:t) (y:t) (op:int_binary_op) :t= match op with 
    |AST_PLUS -> add x y 
    |AST_MINUS -> sub x y 
    |AST_MULTIPLY -> mul x y 
    |AST_DIVIDE -> div x y
        
    (* widening, for loops *)
    let widen = join (*todo just to silent error *)

(* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
    let compare  (x:t)  (y:t)  (op:compare_op) : (t * t) = BOT,BOT


    (* 
       the following, more advanced operations are useful to handle
       complex tests more precisely
     *)

        
    (* backards unary operation *)
    (* [bwd_unary x op r] returns x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x

       it is safe, as first approximation, to implement it as the identity:
       let bwd_unary x _ _ = x
     *)
    let bwd_unary (x:t)  (op:int_unary_op)  (r:t) : t = match op with 
    |AST_UNARY_PLUS ->  meet x r
    |AST_UNARY_MINUS-> meet (neg x ) r

  
     (* backward binary operation *)
     (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r

       it is safe, as first approximation, to implement it as the identity:
       let bwd_binay x y _ _ = (x,y)
      *)
    let bwd_binary  (x:t)  (y:t) (op:int_binary_op)  (r:t) : (t * t)= match op with 
      | AST_PLUS ->
      (* r=x+y => x=r-y and y=r-x *)      
      meet x (sub r y), meet y (sub r x)

      |AST_MINUS ->
      (* r=x-y => x=y+r and y=x-r *)
      meet x (add y r), meet y (sub x r)

      |_ -> BOT,BOT  (*todo just to silent error *)

  
end : VALUE_DOMAIN)

