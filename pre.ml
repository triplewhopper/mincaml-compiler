type lit_kind = I | B | F | Op | S
type kind = Lit of lit_kind * int * string | Word of int * string | Eof of int

let string_of_lit_kind = function
  | I -> "I"
  | B -> "B"
  | F -> "F"
  | Op -> "Op"
  | S -> "S"

let print_kind = function
  | Lit (S, offset, s) -> 
      Printf.printf "%d %s %s" offset (string_of_lit_kind S) (Base64.encode_string s)
  | Lit (k, offset, s) -> 
      Printf.printf "%d %s %s" offset (string_of_lit_kind k) s
  | Word (offset, s) -> 
      Printf.printf "%d W %s" offset (String.escaped s)
  | Eof offset -> 
      Printf.printf "%d EOF EOF" offset

