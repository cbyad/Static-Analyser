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
let bound_mul (a:bound) (b:bound) : bound =match a,b with
|MINF,PINF |PINF,MINF -> MINF 
|MINF,MINF| PINF,PINF -> PINF
|MINF,Int c when c<Z.zero -> PINF
|MINF,Int c when c> Z.zero -> MINF
|PINF, Int c when c> Z.zero -> PINF
|PINF,Int c when c< Z.zero -> MINF 
|Int i , Int j -> 


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
    val rand: Z.t -> Z.t -> t


(* set-theoretic operations *)
    (* emptyness testing *)
    let is_bottom t = t=BOT 






(* extension of f by f (BOT) = BOT *)
let lift1 f x = match x with
| Itv (a,b) -> f a b
| BOT -> BOT

(* the same for f(BOT,_)=f(_,BOT)=BOT*)
let lift2 f x y = match x,y with
|BOT,_ |_,BOT -> BOT
|Itv(a,b),Itv(c,d)-> f a b c d 
   
  (* arithmetic operations *)

(* -x dans les intervalles *)
let neg (x:t) : t =
lift1 (fun a b -> Itv (bound_neg b, bound_neg a)) x

let add (x:t) (y:t) : t =
lift2 (fun a b c d-> Itv(bound_add a c,bound_add b d)) x y 

let sub (x:t) (y:t) : t =
lift2 (fun a b c d -> Itv(bound_sub a d, bound_sub b c)) x y

(*let mul *)



end : VALUE_DOMAIN)

