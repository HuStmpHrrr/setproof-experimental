include Base
module StrM = Map.M (String)

exception Impossible
exception NotImplemented

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

type 'a location =
  | RealLoc  of 'a real_location
  | GhostLoc of 'a

type loc = unit location

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
  | RealLoc l -> l.data

module Loc = struct
  let put l data =
    match l with
    | RealLoc rl -> RealLoc { rl with data }
    | GhostLoc _ -> GhostLoc data

  let map l f =
    match l with
    | RealLoc rl -> RealLoc { rl with data = f rl.data }
    | GhostLoc a -> GhostLoc (f a)

end
