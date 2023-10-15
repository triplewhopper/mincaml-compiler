type position = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
}
[@@deriving show]

type t = { start : position; stop : position; text : string }

let make (start, stop) text = { start; stop; text }

let pp fmt { start; stop; text } =
  if start.pos_fname = stop.pos_fname then
    Format.fprintf fmt "@[%s:%d:%d-%d:@ \"%s\"@]" start.pos_fname start.pos_lnum
      (start.pos_cnum - start.pos_bol)
      (stop.pos_cnum - stop.pos_bol)
      (String.escaped text)
  else
    Format.fprintf fmt "@[%s:%d:%d-%d:%d:@ \"%s\"@]" start.pos_fname
      start.pos_lnum
      (start.pos_cnum - start.pos_bol)
      stop.pos_lnum
      (stop.pos_cnum - stop.pos_bol)
      (String.escaped text)
