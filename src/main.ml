open Base
open Setproof

let _ = Parser.parse_file (Sys.get_argv ()).(1)
