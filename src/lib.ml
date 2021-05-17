include Base

module StrM = Map.M (String)

(* a data carrying location information *)
type 'a location = {
    start_l : int;
    start_c : int;
    end_l   : int;
    end_c   : int;
    data    : 'a
  }

type loc = unit location

let loc_combine l1 l2 : loc = {
    start_l = l1.start_l;
    start_c = l1.start_c;
    end_l   = l2.end_l;
    end_c   = l2.end_c;
    data    = ()
  }

let loc_erase l : loc =
  { l with
    data = ()
  }
