let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan l onParsed onKNormalized = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  Parser.exp Lexer.token l |> 
  (fun parsetree -> onParsed parsetree; parsetree)
  |> Typing.f |> KNormal.f |> 
  (fun knormal -> onKNormalized knormal; knormal) 
  |> Alpha.f |> iter !limit  |> Closure.f |> Virtual.f |> Simm.f |> RegAlloc.f |> Emit.f outchan

let onParsed f (tree: Syntax.t) = if f = "" then () else
  let oc = open_out (f ^ ".parsed") in let ff = Format.formatter_of_out_channel oc in
  Format.fprintf ff "@[%a@]@." Syntax.pp tree;
  close_out oc
let onKNormalized f (tree: KNormal.t) = if f = "" then () else
  let oc = open_out (f ^ ".knormalized") in let ff = Format.formatter_of_out_channel oc in
  Format.fprintf ff "@[%a@]@." KNormal.pp tree; 
  close_out oc

let string s = lexbuf stdout (Lexing.from_string s) (onParsed "") (onKNormalized "")(* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  try
    lexbuf outchan (Lexing.from_channel inchan) (onParsed f) (onKNormalized f);
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
