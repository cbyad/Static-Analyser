open Abstract_syntax_tree
open Value_reduction
open Value_domain

module ReducedProduct(R : VALUE_REDUCTION) =
(struct
module A = R.A
module B = R.B
type t = R.t (* A.t * B.t *)

let top = R.A.top,R.B.top
(* bottom value *)
let bottom = R.A.top,R.B.top
(* constant *)
let const c = R.A.top,R.B.top

let rand x y = R.A.top,R.B.top
(* arithmetic operations *)
let neg (x : t) : t = R.A.top,R.B.top 
let add x y = R.A.top,R.B.top
let sub x y = R.A.top,R.B.top
let mul x y = R.A.top,R.B.top
let div x y = R.A.top,R.B.top
(* set-theoretic operations *)
let join x y = R.A.top,R.B.top
let meet x y = R.A.top,R.B.top
(* subset inclusion of concretizations *)
let subset (x : t) (y : t) : bool = false
(* no need for a widening as the domain has finite height; we use the join *)
let widen x y = join x y
(* comparison operations (filters) *)
let eq a b = (R.A.top,R.B.top),(R.A.top,R.B.top)
let neq a b = (R.A.top,R.B.top),(R.A.top,R.B.top)
let leq a b = (R.A.top,R.B.top),(R.A.top,R.B.top)
let geq a b = (R.A.top,R.B.top),(R.A.top,R.B.top)
let gt a b = (R.A.top,R.B.top),(R.A.top,R.B.top)
(* check the emptyness of the concretization *)
let is_bottom a = false
(* prints abstract element *)
let print fmt x = match x with
| a,b -> A.print fmt a
(* operator dispatch *)
let unary x op = match op with
| AST_UNARY_PLUS  -> x
| AST_UNARY_MINUS -> neg x
let binary x y op = match op with
| AST_PLUS     -> add x y
| AST_MINUS    -> sub x y
| AST_MULTIPLY -> mul x y
| AST_DIVIDE   -> div x y
let compare x y op = match op with
| AST_EQUAL         -> eq x y
| AST_NOT_EQUAL     -> neq x y
| AST_GREATER_EQUAL -> geq x y
| AST_GREATER       -> gt x y
| AST_LESS_EQUAL    -> leq x y (*let y',x' = geq y x in x',y'*)
| AST_LESS          -> let y',x' = gt y x in x',y'
        
let bwd_unary x op r = match op with
| AST_UNARY_PLUS  -> meet x r
| AST_UNARY_MINUS -> meet x (neg r)
let bwd_binary x y op r = match op with
| AST_PLUS ->
    (* r=x+y => x=r-y and y=r-x *)      
    meet x (sub r y), meet y (sub r x)
| AST_MINUS ->
    (* r=x-y => x=y+r and y=x-r *)
    meet x (add y r), meet y (sub x r)
| AST_MULTIPLY ->
    (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
    let contains_zero o = subset (const Z.zero) o in
    (if contains_zero y && contains_zero r then x else meet x (div r y)),
    (if contains_zero x && contains_zero r then y else meet y (div r x))
| AST_DIVIDE ->
    (* this is sound, but not precise *)
    x, y

end : VALUE_DOMAIN)