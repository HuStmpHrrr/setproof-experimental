open Base
open Setproof

let _ =
  try
    (Sys.get_argv ()).(1) |> Parser.parse_file |> Elaborate.elab_module_def
  with
  | Parser.ParserError msg ->
      Stdio.Out_channel.output_string Stdio.stderr msg;
      Caml.exit 0
