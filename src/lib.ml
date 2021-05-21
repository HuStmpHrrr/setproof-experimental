include Base
module StrM = struct
  include Map.M (String)

  let pp pp_data fmt (m : 'a t) =
    let pp_entry ~key ~data =
      Caml.Format.fprintf fmt "%s -> %a;@ " key pp_data data
    in
    Caml.Format.fprintf fmt "@[<hov2>Map [@,";
    Map.iteri m ~f:pp_entry;
    Caml.Format.fprintf fmt "@]@,]"
end

exception Impossible
exception NotImplemented

let pp_conv pp oc = pp (Caml.Format.formatter_of_out_channel oc)

exception DifferentFileLocations of string * string

(* a data carrying location information *)
type 'a real_location = {
  file : string;
  start_l : int;
  start_c : int;
  end_l : int;
  end_c : int;
  data : 'a;
}
[@@deriving show { with_path = false }]

let real_pp_real_loc ?(with_file = true) fmt l =
  Caml.Format.fprintf fmt "<loc:%d,%d - %d,%d" l.start_l l.start_c l.end_l
    l.end_c;
  if with_file
  then Caml.Format.fprintf fmt " in %s" l.file;
  Caml.Format.pp_print_string fmt ">"

type 'a location =
  | RealLoc  of 'a real_location
  | GhostLoc of 'a
[@@deriving show { with_path = false }]

type loc = unit location [@@deriving show { with_path = false }]

let real_pp_loc fmt = function
  | RealLoc l   -> real_pp_real_loc fmt l
  | GhostLoc () -> Caml.Format.fprintf fmt "<loc:booo>"

let loc_dummy : loc = GhostLoc ()

let loc_ghost d = GhostLoc d

let loc_combine l1 l2 : loc =
  match (l1, l2) with
  | GhostLoc _, _          -> l2
  | _, GhostLoc _          -> l1
  | RealLoc l1, RealLoc l2 ->
      if String.(l1.file = l2.file)
      then RealLoc { l1 with end_l = l2.end_l; end_c = l2.end_c; data = () }
      else raise (DifferentFileLocations (l1.file, l2.file))

let loc_erase l : loc =
  match l with
  | GhostLoc _ -> GhostLoc ()
  | RealLoc l  -> RealLoc { l with data = () }

let loc_data l =
  match l with
  | GhostLoc a -> a
  | RealLoc l  -> l.data

module Loc : sig
  include Base.Equal.S1 with type 'a t = 'a location

  val put : 'a t -> 'b -> 'b t
  val map : 'a t -> ('a -> 'b) -> 'b t
end = struct
  type 'a t = 'a location

  let put l data =
    match l with
    | RealLoc rl -> RealLoc { rl with data }
    | GhostLoc _ -> GhostLoc data

  let map l f =
    match l with
    | RealLoc rl -> RealLoc { rl with data = f rl.data }
    | GhostLoc a -> GhostLoc (f a)

  let equal eq l0 l1 =
    match (l0, l1) with
    | GhostLoc a, GhostLoc b -> eq a b
    | RealLoc l1, RealLoc l2 ->
        String.equal l1.file l2.file
        && Int.equal l1.start_l l2.start_l
        && Int.equal l1.start_c l2.start_c
        && Int.equal l1.end_l l2.end_l
        && Int.equal l1.end_c l2.end_c
    | _                      -> false
end

module Tuple2 : sig
  type ('a, 'b) t = 'a * 'b

  val map1 : ('a, 'b) t -> f:('a -> 'c) -> ('c, 'b) t
  val map2 : ('a, 'b) t -> f:('b -> 'c) -> ('a, 'c) t
  val bimap : ('a, 'b) t -> f:('a -> 'c) -> g:('b -> 'd) -> ('c, 'd) t

  val curry : (('a, 'b) t -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> ('a, 'b) t -> 'c
end = struct
  type ('a, 'b) t = 'a * 'b

  let map1 (a, b) ~f = (f a, b)
  let map2 (a, b) ~f = (a, f b)

  let bimap (a, b) ~f ~g = (f a, g b)

  let curry f a b = f (a, b)
  let uncurry f (a, b) = f a b
end
