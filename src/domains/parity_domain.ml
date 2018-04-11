(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Yannick-Alain CB & Rudy Kruissel
*)

(* 
   The parity domain
 *)
open Abstract_syntax_tree
open Value_domain
  
module Parity = (struct



  (* types *)

  (* type of abstract values *)
  type t = | Odd | Even | BOT | TOP     

  let lift1 x =
    match x with
    | BOT -> BOT
    | TOP -> TOP
    | Odd -> Odd
    | Even -> Even



  (* lift binary arithmetic operations *)
  let lift2 f x y =
    match x,y with
    | BOT,_ | _,BOT -> BOT
    | TOP,_ | _,TOP -> TOP
    | _ -> f x y
          
  (* interface implementation *)

  (* unrestricted value *)
  let top = TOP

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = if Z.is_even c then Even else Odd

  (* interval *)
  let rand x y =
    if x=y then const x
    else if x<y then TOP
    else BOT

  (* arithmetic operations *)
  let neg (x:t) :t = lift1 x (*idem with x *)

  let parity_add_or_sub (x:t) (y:t) :t = match x,y with
  |Even,Even ->  Even
  |Odd,Even |Even,Odd -> Odd
  |Odd,Odd -> Even
  |_ -> BOT

  let parity_mul (x:t) (y:t) :t = match x,y with 
  |Even,Even ->  Even
  |Odd,Even |Even,Odd -> Even
  |Odd,Odd -> Odd
  |_ -> BOT

  let parity_div (x:t) (y:t) :t = match x,y with (*not sure*)
  |Even,Odd -> Even
  |Odd,Odd -> Odd
  |Even,Even ->  TOP (*can be odd or even*)
  |_ -> BOT

  let add (x:t) (y:t) :t = lift2 (fun a b -> parity_add_or_sub a b) x y
  let sub (x:t) (y:t) :t = lift2 (fun a b -> parity_add_or_sub a b) x y
  let mul (x:t) (y:t) :t = lift2 (fun a b -> parity_mul a b) x y
  let div (x:t) (y:t) :t = lift2 (fun a b -> parity_div a b) x y

  (* set-theoretic operations *)
  
  let join a b = match a,b with
  | BOT,x | x,BOT -> x
  | Odd,Odd -> Odd
  | Even,Even -> Even
  | Even,Odd | Odd,Even -> TOP
  | _ -> BOT

  let meet a b = match a,b with
  | TOP,x | x,TOP -> x
  | Even,Even ->  Even
  | Odd,Odd ->  Odd
  | Odd,Even | Even,Odd ->  BOT
  | _ -> TOP
  
  let widen = join (*see after *)

  (* comparison operations (filters) *)

  (* subset inclusion of concretizations *)
  let subset a b = match a,b with
  | BOT,_ | _,TOP -> true
  | Even,Even | Odd,Odd -> true
  | _ -> false

  (* check the emptyness of the concretization *)
  let is_bottom a = a=BOT

  (* prints abstract element *)
  let print fmt x = match x with
  | Odd -> Format.fprintf fmt "odd"
  | Even -> Format.fprintf fmt "even" 
  | BOT -> Format.fprintf fmt "⊥"
  | TOP -> Format.fprintf fmt "⊤"

  let eq (x:t) (y:t) :t*t = match x,y with 
  |Odd,Odd | Even,Even -> x,y
  |Even , BOT |Even , TOP | Odd,BOT | Odd,TOP-> x,x
  |BOT,Even |TOP, Even |BOT,Odd |TOP,Odd -> y,y
  |Even,Odd| Odd,Even -> TOP,TOP  
  |_,_ -> x,y 
    
  let neq (x:t) (y:t) :t*t =x,y 
  (* match x,y with 
  |Odd,Odd -> Even,Odd 
  | Even,Even -> x,y
  |Even , BOT |Even , TOP | Odd,BOT | Odd,TOP-> x,x
  |BOT,Even |TOP, Even |BOT,Odd |TOP,Odd -> y,y
  |Even,Odd| Odd,Even -> TOP,TOP  
  |_,_ -> x,y 
  *)

  let geq x y = x,y
  let gt x y = x,y 
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
  | AST_LESS_EQUAL    -> let y',x' = geq y x in x',y'
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
        (****************************)


 let get_value (x:t) (wtf:int) : int  =match x with 
  |BOT -> -1
  |TOP -> 2018 (*simulate max value*)
  |Odd -> 1
  |Even -> 2

 (****************************)

 let get_parity x = match x with |Odd->Odd |Even->Even |_-> invalid_arg "oups"



end )