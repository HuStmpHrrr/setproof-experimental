open Base
open Setproof

let _ =
  try Parser.parse_file (Sys.get_argv ()).(1)
  with Parser.ParserError msg ->
    Stdio.Out_channel.output_string Stdio.stderr msg;
    Caml.exit 0
