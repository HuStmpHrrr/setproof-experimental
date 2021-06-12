open Base
open Setproof

let data_path file_name = "./data/" ^ file_name

let test_parser_util file_name =
  let open Parser in
  let open OUnit2 in
  let test _ =
    try ignore (parse_file (data_path file_name)) with
    | ParserError msg -> assert_failure msg
  in
  file_name >:: test

let suite =
  let open OUnit2 in
  "Parser"
  >::: [
         "parses valid files"
         >::: [
                test_parser_util "random-grammars.set";
                test_parser_util "simple-data.set";
              ];
       ]

let _ =
  Caml.print_string (Caml.Sys.getcwd ());
  OUnit2.run_test_tt_main suite
