include Base
module StrM = Map.M (String)

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

exception DifferentFileLocations of string * string

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
  | RealLoc l -> RealLoc { l with data = () }
