(** A nested list is either a singleton or a list of nested lists. *)
type 'a t = Nested of 'a t list | Singleton of 'a 

let pp pp_elt ppf =
  let empty_flag = ref true in
  let rec pp' pp_elt ppf = function
    | Nested [] -> ()
    | Nested (Singleton x :: xs) ->
        if !empty_flag = false then Format.fprintf ppf ";@ ";
        Format.fprintf ppf "%a" pp_elt x;
        empty_flag := false;
        pp' pp_elt ppf (Nested xs)
    | Nested (Nested x :: xs) ->
        Format.fprintf ppf "%a" (pp' pp_elt) (Nested x);
        pp' pp_elt ppf (Nested xs)
    | Singleton x ->
        if !empty_flag = false then Format.fprintf ppf ";@ ";
        Format.fprintf ppf "%a" pp_elt x;
        empty_flag := false
  in
  Format.fprintf ppf "@[<hov 2>[%a]@]" (pp' pp_elt)

(** [is_empty l] returns [true] if [l] is empty, [false] otherwise. 
  
    [l] is empty if it is [Nested []] or [Nested [...]] where all the nested lists inside are empty. *)
let rec is_empty = function
  | Nested [] -> true
  | Nested (Singleton _ :: _) -> false
  | Nested (Nested x :: xs) ->
      if is_empty (Nested x) then is_empty (Nested xs) else false
  | Singleton _ -> false


(** [empty] is the empty nested list [Nested []]. *)
let empty = Nested []

(** [front l] returns the first element of [l] if it exists, [None] otherwise. *)
let rec front = function
  | Nested [] -> None
  | Nested (Singleton x :: _) -> Some x
  | Nested (Nested x :: xs) -> (
      match front (Nested x) with None -> front (Nested xs) | Some x -> Some x)
  | Singleton x -> Some x

(** [back l] returns the last element of [l] if it exists, [None] otherwise. *)
let rec back = function
  | Nested [] -> None
  | Nested (Singleton x :: []) -> Some x
  | Nested (Singleton _ :: xs) -> back (Nested xs)
  | Nested (Nested x :: xs) -> (
      match back (Nested xs) with None -> back (Nested x) | Some x -> Some x)
  | Singleton x -> Some x

let flatten lst = 
  let rec flatten' acc = function
    | [] -> List.rev acc
    | Nested (Singleton x :: xs) :: ys -> flatten' (x :: acc) (Nested xs :: ys)
    | Nested (Nested x :: xs) :: ys -> flatten' acc (Nested x :: Nested xs :: ys)
    | Singleton x :: ys -> flatten' (x :: acc) ys
    | Nested [] :: ys -> flatten' acc ys
  in
  flatten' [] [lst]

let rec find_opt p = function
  | Nested [] -> None
  | Nested (Singleton x :: xs) -> if p x then Some x else find_opt p (Nested xs)
  | Nested (Nested x :: xs) -> (
      match find_opt p (Nested x) with None -> find_opt p (Nested xs) | Some x -> Some x)
  | Singleton x -> if p x then Some x else None

let equal eq (l1: 'a t) (l2: 'a t) = 
  let f1 = flatten l1 and f2 = flatten l2 in 
  List.compare_lengths f1 f2 = 0 && List.equal eq f1 f2

let concat l1 l2 = 
  if is_empty l1 then l2 else if is_empty l2 then l1 else Nested [l1; l2]