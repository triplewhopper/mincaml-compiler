let () = Printexc.record_backtrace true
let () =
  if Array.length Sys.argv <> 2 then (
    Printf.eprintf "Usage: %s <file>\n" Sys.argv.(0);
    exit 1);
  let file = open_in Sys.argv.(1) in
  let a = Lexing.from_channel file in
  while true do
    let tok =
      try Lexer.token a with
      | Lexer.UnknownToken ({ pos_lnum; pos_bol; pos_cnum }, s) ->
          let e = Printf.sprintf
            "file \"%s\", line %d, character %d: unknown token \"%s\"\n"
            Sys.argv.(1) pos_lnum (pos_cnum - pos_bol) (String.escaped s) in 
          Printf.printf "%d E %s\n" pos_cnum (Base64.encode_string e);
          exit 0
      | Lexer.UnTerminatedComment { pos_lnum; pos_bol; pos_cnum } ->
          let e = Printf.sprintf
            "file \"%s\", line %d, character %d: unterminated comment\n"
            Sys.argv.(1) pos_lnum (pos_cnum - pos_bol) in
          Printf.printf "%d E %s\n" pos_cnum (Base64.encode_string e);
          exit 0
    in
    Pre.print_kind tok;
    print_newline ();
    match tok with Eof _ -> exit 0 | _ -> ()
  done
