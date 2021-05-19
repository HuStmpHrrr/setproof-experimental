open Base
open Setproof

let _ = Earley_core.Earley.debug_lvl := 0

let _ =
  (Sys.get_argv ()).(1)
  |> Earley_core.Earley.handle_exception Parser.parse_file
  |> Elaborate.elab_module_def
