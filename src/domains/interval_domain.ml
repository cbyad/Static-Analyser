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
|PINF,PINF -> Int Z.zero (* cas particulier!!!*)
|Int c,MINF |Int c,PINF -> Int Z.zero
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
let bound_min (a:bound) (b:bound) :bound =  if bound_cmp a b <=0  then a  else  b 

(*max (a,b)*)
let bound_max (a:bound) (b:bound) :bound =  if bound_cmp a b <=0  then b  else  a 

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

    let meet a b = match a,b with
    |Itv (a, b), Itv (c, d) -> 
      if (bound_cmp (bound_max a c) (bound_min b d)) = 1 then BOT
      else Itv(bound_max a c, bound_min b d)
    | _ -> BOT

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

let min2_div (a:bound) (b:bound) (c:bound) (d:bound) : bound = 
      if bound_cmp (Int Z.one) c <=0 then  bound_min (bound_div a c) (bound_div a d)
    else 
        if bound_cmp d (Int Z.minus_one)<=0 then bound_min (bound_div b c ) (bound_div b d)
        else invalid_arg "no match case"

let max2_div (a:bound) (b:bound) (c:bound) (d:bound) : bound = 
      if bound_cmp (Int Z.one) c <=0 then  bound_max (bound_div b c) (bound_div b d)
    else 
        if bound_cmp d (Int Z.minus_one)<=0 then bound_min (bound_div a c ) (bound_div a d)
        else invalid_arg "no match case"


 let div (x:t) (y:t) : t = match x,y with 
    |_,Itv(_,Int i) when i=Z.zero ->BOT
    |_,Itv(Int i,_) when i=Z.zero ->BOT
    |Itv(Int a , Int b),Itv(Int i , Int j ) -> if  bound_cmp (Int Z.one) (Int i)  <=0 then 
        Itv(min2_div (Int a) (Int b) (Int i) (Int j), max2_div (Int a) (Int b ) (Int i ) (Int j))
    else if bound_cmp  (Int j) (Int Z.minus_one) <=0 then 
        Itv(min2_div (Int a) (Int b) (Int i) (Int j), max2_div (Int a) (Int b ) (Int i ) (Int j))
    else 
          let left = meet y (Itv( Int(Z.one) , PINF)) in 
          let rigth = meet y (Itv (MINF,Int(Z.minus_one))) in
          let res1= lift2 (fun a b c d ->Itv(min2_div a b c d , max2_div a b c d)) x left in
          let res2= lift2 (fun a b c d ->Itv(min2_div a b c d , max2_div a b c d)) x rigth in 
          join res1 res2   
    |_,_ -> invalid_arg " don't known"        
(*---------------------------------------------------------------------------*)

(*----------------------------------comparaison------------------------------*)

let eq (x:t) (y:t) : t*t = match x ,y with 
|Itv(a,b),Itv(c,d) -> if bound_cmp a c =0 && bound_cmp b d =0 then x,x else meet x y , meet x y 
| _ -> BOT,BOT 

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

let leq (p:t) (m:t) : (t*t) =  match p,m with 
  |Itv(w,x),Itv(y,z) ->  if (bound_cmp y z) =0 then 
      (if bound_cmp w y <=0 then
        Itv(w,bound_min x y),m else BOT,BOT)
       else  
       if bound_cmp w z <=0 then  Itv(w,bound_min x z),Itv(bound_max w y,z) else BOT,BOT
  |_-> BOT,BOT

  let geq (p:t) (m:t) : t*t = match p, m with 
  | Itv(w,x), Itv(y,z) -> 
    if bound_cmp w x = 0 && bound_cmp y z = 0 then Itv(y,x),m
    else  
      Itv(bound_min x y, bound_max x y), Itv(bound_min x y, bound_max x y)
  | _->top,top

let gt a b = match a, b with
  | Itv(w,x), Itv(y,z) -> (match x, y with 
                          |Int i, Int j -> if (bound_cmp w y = 1) &&  (bound_cmp x z = 1) then a,b
                                          else 
                                          Itv(Int(Z.add j Z.one), bound_max x y),
                                          Itv(bound_min x y,Int(Z.sub i Z.one))
                          | _ -> a, b)
  | _,_-> a,b

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
        
   (*     
    let shrk x y :t = match x,y with 
    |Itv(a,b),Itv(c,d) -> Itv((if bound_cmp a MINF =0 then  c else a ), (if bound_cmp b PINF =0 then d else b))
     |_ -> invalid_arg "nothing to do in shrinken"
   *)

    (* widening, for loops *)
    let widen (x:t) (y:t) :t= match x,y with 
    |BOT,i | i,BOT -> i
    |Itv(a,b),Itv(c,d)->Itv((if bound_cmp a c <=0 then a else MINF),(if bound_cmp b d >=0 then b else PINF))

    let compare  (x:t)  (y:t)  (op:compare_op) : (t * t) = match op with 
    |AST_EQUAL -> eq x y 
    |AST_NOT_EQUAL -> neq x y  
    |AST_GREATER_EQUAL ->   geq x y
    |AST_GREATER ->  gt x y 
    |AST_LESS_EQUAL -> leq x y
    |AST_LESS ->   let y',x' = gt y x in x',y' 
    
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

    | AST_MULTIPLY ->
      (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
      let contains_zero o = subset (const Z.zero) o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))
        
  | AST_DIVIDE ->
  (* r=x/y => (x=r*y or y=r=0) and (y=r*x or x=r=0)  *)
    let contains_zero o = subset (const Z.zero) o in
      (if contains_zero y && contains_zero r then x else meet x (mul r y)),
      (if contains_zero x && contains_zero r then y else meet y (mul r x))
      (* this is sound, but not precise *)
  

(****************************)
 let get_value (x:t) (pos:int) : int = match x with 
      |Itv(a,b)-> (let res = if pos=1 then a else b in 
          match res with 
          |Int c -> Z.to_int c
          |_ -> invalid_arg "bound int?? :-(")
  |_ -> invalid_arg "interval ?? :-(" 
(****************************)

end : VALUE_DOMAIN)