type position = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
} [@@deriving show]
type t = {start: position; stop: position; text: string} [@@deriving show]

let make (start, stop) text = {start; stop; text}

