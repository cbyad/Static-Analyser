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

(* a /b *)
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

(*min (a,b)*)
let bound_min (a:bound) (b:bound) :bound = match (bound_cmp a b) with |0|1-> b   |_->a

(*max (a,b)*)
let bound_max (a:bound) (b:bound) :bound = match (bound_cmp a b) with |0|1-> a   |_->b

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
    |Itv(a,b),Itv(c,d) -> Itv(bound_min a c ,bound_max b d )
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
          let res1= lift2 (fun a b c d ->Itv(min2_div a b d d , max2_div a b c d)) x left in
          let res2= lift2 (fun a b c d ->Itv(min2_div a b c c , max2_div a b c d)) x rigth in 
          join res1 res2
(*---------------------------------------------------------------------------*)

(*----------------------------------comparaison------------------------------*)
let eq (x:t) (y:t) : t*t = match x ,y with 
|Itv(a,b),Itv(c,d) -> if bound_cmp a c =0 && bound_cmp b d =0 then x,x else  meet x y , meet y x
|BOT,a -> a,a |a,BOT -> a,a 

let neq (x:t) (y:t) : t*t =  match x,y with 
|Itv(a,b),Itv(c,d) when bound_cmp a b =0 && bound_cmp b c =0 -> 
      Itv(a,b),Itv(bound_add  c (Int(Z.one)),d)

|Itv(a,b),Itv(c,d) when bound_cmp a b =0 && bound_cmp b d =0 -> 
      Itv(a,b),Itv(c,bound_add  d (Int(Z.minus_one)))

|Itv(a,b),Itv(c,d) when bound_cmp c d =0 && bound_cmp d a =0 -> 
      Itv(bound_add  a (Int(Z.one)),b),Itv(c,d)
     
|Itv(a,b),Itv(c,d) when bound_cmp c d =0 && bound_cmp d b =0 -> 
      Itv(a,bound_add  b (Int(Z.minus_one ))),Itv(c,d)
|_ -> x,y

let leq (x:t) (y:t) : (t*t) =  match x,y with 
  |Itv(a,b),Itv(c,d) when bound_cmp c d =0 -> if (bound_cmp a c )<=0 then Itv(a,bound_min b c),Itv(a,bound_min b c)
  else BOT,BOT
  |Itv(a,b),Itv(c,d) when bound_cmp a b =0 -> if (bound_cmp c a) <=0  then Itv(bound_max c a,d),Itv(bound_max c a ,d)
  else BOT,BOT
  |Itv(a,b),Itv(c,d) -> if (bound_cmp a d) <=0 then Itv(a,bound_min b d),(Itv(bound_max a c,d))
  else BOT,BOT
  |_-> x,y

let lt (x:t) (y:t) : (t*t) = match x,y with 
  |Itv(a,b),Itv(c,d) -> if (bound_cmp a d) <0 then Itv(a,bound_add (bound_min b d) (Int(Z.of_int (-1) )) ),(Itv(bound_add (bound_max a c) (Int(Z.of_int (1) )),d))
  else BOT,BOT
  |_ -> x,y

(*
let lt (x:t) (y:t) : (t*t) =  match x,y with 
  |Itv(a,b),Itv(c,d) when bound_cmp a b =0 && bound_cmp c d =0 ->
    if (bound_cmp c a) !=0 
      then BOT,BOT
      else Itv(a,b),Itv(a,b)
  |Itv(a,b),Itv(c,d) when bound_cmp a b =0 ->
    if (bound_cmp c a) <=0 
      then Itv(bound_add a (Int(Z.one)), d),Itv(bound_add a (Int(Z.one)), d)
      else BOT,BOT
  |Itv(a,b),Itv(c,d) when bound_cmp c d =0 ->
    if (bound_cmp a c )<0
      then Itv(a, bound_sub c (Int(Z.one))) , Itv(a, bound_sub c (Int(Z.one)))
      else BOT,BOT

  |Itv(a,b),Itv(c,d) -> if (bound_cmp a d) <0 then Itv(bound_max (bound_add a (Int(Z.one))) c, bound_min b d ), 
                                                  Itv(bound_max a c,bound_min (bound_sub d (Int(Z.one))) b)  
  else x,y
  |_-> invalid_arg "oupsss"
*)

(*  rudy
let lt (x:t) (y:t) : (t*t) = match x,y with 
| Itv(a,b),Itv(c,d) when bound_cmp c a <= 0 && bound_cmp b d >= 0  ->
    Itv(a,bound_add  d (Int(Z.of_int (-1) )) ),Itv(bound_add  a (Int(Z.of_int 1 )), d)
| Itv(a,b),Itv(c,d) when bound_cmp b d >= 0 ->
    Itv(a,bound_add  d (Int(Z.of_int (-1) )) ), Itv(c,d)
| Itv(a,b),Itv(c,d) when bound_cmp c a <= 0 ->
    Itv(a,b),Itv(bound_add  a (Int(Z.of_int 1 )), d)

|_-> x,y 
*)

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

    let compare  (x:t)  (y:t)  (op:compare_op) : (t * t) = match op with 
    |AST_EQUAL -> eq x y 
    |AST_NOT_EQUAL -> neq x y  
    |AST_LESS_EQUAL -> leq x y
    |AST_LESS -> lt x y 
    |AST_GREATER_EQUAL -> let y',x' = leq y x in x',y'
    |AST_GREATER -> let y',x' = lt y x in x',y'

    let bwd_unary (x:t)  (op:int_unary_op)  (r:t) : t = match op with 
    |AST_UNARY_PLUS ->  meet x r
    |AST_UNARY_MINUS-> meet (neg x ) r

    let bwd_binary  (x:t)  (y:t) (op:int_binary_op)  (r:t) : (t * t)= match op with 
      | AST_PLUS ->
      (* r=x+y => x=r-y and y=r-x *)      
      meet x (sub r y), meet y (sub r x)

      |AST_MINUS ->
      (* r=x-y => x=y+r and y=x-r *)
      meet x (add y r), meet y (sub x r)

      |_ -> x,y  (*todo just to silent error *)

end : VALUE_DOMAIN)