type 'a t = Nested of 'a t list | Singleton of 'a [@@deriving show]

let rec is_empty = function
  | Nested [] -> true
  | Nested (Singleton _ :: _) -> false
  | Nested (Nested x :: xs) ->
      if is_empty (Nested x) then is_empty (Nested xs) else false
  | Singleton _ -> false

let empty = Nested []

let rec front = function
  | Nested [] -> None
  | Nested (Singleton x :: _) -> Some x
  | Nested (Nested x :: xs) -> (
      match front (Nested x) with None -> front (Nested xs) | Some x -> Some x)
  | Singleton x -> Some x
let rec back = function
  | Nested [] -> None
  | Nested (Singleton x :: []) -> Some x
  | Nested (Singleton _ :: xs) -> back (Nested xs)
  | Nested (Nested x :: xs) -> (
      match back (Nested xs) with None -> back (Nested x) | Some x -> Some x
  )
  | Singleton x -> Some x
