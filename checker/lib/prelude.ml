
module RocqStr = struct
  type t = char list

  let from_string (s : string) : t =
    List.init (String.length s) (String.get s)

  let to_string (s : t) : string =
    String.init (List.length s) (List.nth s)
end


