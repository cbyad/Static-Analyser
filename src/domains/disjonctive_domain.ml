open Abstract_syntax_tree
open Value_domain
   
open Interval_domain

module DisjunctiveIntervals = (struct

  module A = Intervals

  type t = A.t list

  let top = [A.top]

  let bottom = [A.bottom]

  let const x = [A.const x]

  let rand x y = [A.rand x y]

  let fuse xs = 
    List.fold_left (fun acc x -> 
      match acc with
      | head::tail when not (A.is_bottom (A.meet x head)) -> (A.join x head) :: tail
      | _ -> x :: acc
      )
    [List.hd xs] xs

  let join x y = fuse (List.sort (fun a b ->
    match a, b with
    | A.BOT, _ -> -1
    | _, A.BOT -> 1
    | A.Itv(v1, _), A.Itv(v2, _) when A.less_than v1 v2 -> -1
    | _, _ -> 1
    ) (x @ y))

  let meet xs ys =
    List.fold_left (fun acc x -> 
      List.fold_left (fun acc y -> 
        A.meet x y :: acc) 
      acc ys) 
    [] xs

  (* val subset: t -> t -> bool *)
  let subset xs ys =  List.fold_left (fun acc x -> 
    List.fold_left (fun acc y -> 
      if (A.subset x y) then acc else false)
    acc ys)
  true xs

  let is_bottom x = match x with
  | [] -> true
  | _ -> (List.fold_left (fun acc e -> acc && A.is_bottom e) true x)

  let widen x y = fuse (List.map (fun (e1, e2) -> A.widen e1 e2)
  (List.combine x y))
  let print fmt xs = if is_bottom xs then
    Format.fprintf fmt "⊥"
      else
        match (fuse xs) with
    | h :: t -> Format.fprintf fmt "%s"
                  (List.fold_left (fun acc e -> acc ^ " or " ^ (A.string_of_interval e))
                  (A.string_of_interval h) t)
    | _ -> () (* Not reachable, but make the compiler happy *)



  let unary x op = List.map (fun e -> A.unary e op) x

  let binary x y op = fuse (List.flatten (List.map (fun e1 -> List.map
  (fun e2 -> A.binary e1 e2 op) y) x))

  let compare x y op = List.split (List.fold_left (fun acc e1 -> acc @ List.fold_left (fun acc e2 ->
    acc @ [A.compare e1 e2 op]) [] y) [] x)

  let bwd_unary x op r = x

  let bwd_binary x y op r = (x, y)


(****************************)
 let get_value (x:t) (pos:int) : int = invalid_arg "Nothing"
(****************************)
end)
