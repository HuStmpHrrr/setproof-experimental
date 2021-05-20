open Lib

(** JaneStreet's Base wrapper *)
module Base = struct
  include MParser

  let map m ~f = m |>> f

  module Monad_arg = struct
    type nonrec ('a, 'e) t = ('a, 'e) t

    let return = return
    let bind m ~f = bind m f
    let apply mf m = bind mf ~f:(fun f -> map ~f m)

    let map = `Custom map
  end

  include Monad.Make2 (Monad_arg)
  include Applicative.Make2 (Monad_arg)
end

include Base

(** Debugging functions *)

let debugging_level = ref 0

let debug min_lv m pp p =
  let open Caml.Format in
  if !debugging_level >= min_lv
  then
    let p' s =
      fprintf err_formatter "@[<v2>Start %s@," m;
      let res = p s in
      ( match res with
      | Empty_failed _        -> fprintf err_formatter "@[<v2>Empty_failed@]"
      | Empty_ok _            -> fprintf err_formatter "@[<v2>Empty_ok@]"
      | Consumed_failed _     -> fprintf err_formatter "@[<v2>Consumed_failed@]"
      | Consumed_ok (v, _, _) ->
          fprintf err_formatter "@[<v2>Consumed_ok@,%a@]" pp v
      );
      fprintf err_formatter "@]@,End %s@." m;
      res
    in
    p'
  else p

(** OCaml 4.08 Binding operators *)

let ( let* ) m f = bind m ~f
let ( and* ) a b = both a b

let ( let+ ) m f = map m ~f
let ( and+ ) = ( and* )

(** More operators *)

let ( <$> ) f m = ( let+ ) m f

(** More functions *)

(** Fixpoint for parser *)
let recur f =
  let rec p s = f p s in
  p

let delay f =
  let p s = (Lazy.force f) s in
  p

let gen_nonzero () : (char, 's) t =
  satisfy (fun c -> Char.(c <> '0') && Char.is_digit c)

let gen_integer () : (int, 's) t =
  let nonzero = gen_nonzero () in
  Int.of_string
  <$> (string "0"
      <|> (String.of_char_list
          <$> ((fun a b -> a :: b) <$> nonzero <*> many digit)
          )
      )

let gen_line_comment s : (string, 's) t =
  let* _ = string s in
  many_chars any_char

let gen_block_comment op cl =
  let start = string op in
  let end_ = string cl in
  let nonp =
    many1_chars (not_followed_by (start <|> end_) "" >> any_char_or_nl)
  in
  recur (fun p -> between start end_ (map ~f:String.concat (many (p <|> nonp))))

let parse_test p str s =
  match parse_string p str s with
  | Success a -> Either.First a
  | Failed (m, _) ->
     Stdio.print_string m;
     Either.Second ()
