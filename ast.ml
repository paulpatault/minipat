type action = A of string | Let of string * expr * action | Unit
and expr = V of string | P of int * expr

type pattern = { pat_desc : pat_desc; pat_loc : Location.t }

and pat_desc =
  | Pwild
  | Pvar of string
  | Papp of string * pattern list
  | Por of pattern * pattern
  | Pas of pattern * string

type value =
  | Vwild
  | Vvar of string
  | Vapp of string * value list
  | Vor of value * value

type match_with = string * string * (pattern * action) list
type adt = string * (string * string list) list
type file = { tdef : adt list; cases : match_with list }

let mk_pat_unlock pat_desc = { pat_desc; pat_loc = Location.none }

let rec pattern2value p =
  match p.pat_desc with
  | Pwild -> Vwild
  | Pvar s -> Vvar s
  | Papp (s, pl) -> Vapp (s, List.map pattern2value pl)
  | Por (p1, p2) -> Vor (pattern2value p1, pattern2value p2)
  | Pas (p, _) -> pattern2value p

let rec value2pattern = function
  | Vwild -> mk_pat_unlock Pwild
  | Vvar s -> mk_pat_unlock (Pvar s)
  | Vapp (s, pl) -> mk_pat_unlock (Papp (s, List.map value2pattern pl))
  | Vor (v1, v2) -> mk_pat_unlock (Por (value2pattern v1, value2pattern v2))

let get_action ip il c =
  let _, _, pat = List.nth c ip in
  let _, act = List.nth pat il in
  match act with A s -> s | _ -> assert false

type mode = Exh | Red

open Fmt

let nl = any "@\n"
let nl2 = any "@\n@\n"
let star = any " * "

let tdef_cases =
  let pp_v ppf (s, t) =
    pf ppf "| %s" s;
    if t <> [] then pf ppf " of %a" (list ~sep:star string) t
  in
  list ~sep:nl pp_v

let adt ppf (s, l) = pf ppf "type %s =@\n  @[%a@]" s tdef_cases l
let is_tuple a = String.length a > 5 && String.sub a 0 5 = "tuple"

let rec pat ppf p =
  match p.pat_desc with
  | Pwild -> pf ppf "_"
  | Pvar s -> pf ppf "%s" s
  | Papp (c, []) -> pf ppf "%s" c
  | Papp (c, pl) when is_tuple c -> pf ppf "%a" (list ~sep:comma pat) pl
  | Papp (c, pl) -> pf ppf "%s%a" c (parens (list ~sep:comma pat)) pl
  | Por (p1, p2) -> pf ppf "%a@ | %a" (parens pat) p1 (parens pat) p2
  | Pas (p1, s) -> pf ppf "%a as %s" pat p1 s

let value ppf e = pat ppf (value2pattern e)

let rec expr ppf = function
  | V s -> pf ppf "%s" s
  | P (i, e) -> pf ppf "#%i(%a)" i expr e

let rec action ppf = function
  | Unit -> pf ppf "()"
  | A s -> pf ppf "%s" s
  | Let (s, e, a') -> pf ppf "let %s = %a in %a" s expr e action a'

let case ppf (p, a) = pf ppf "| %a -> @[%a@]" pat p action a

let cases ppf (s, typ, t) =
  pf ppf "match %s : %s with@\n  @[%a@]" s typ (list ~sep:nl case) t

let file ppf f =
  pf ppf "%a@\n@\n%a@." (list ~sep:nl2 adt) f.tdef (list ~sep:nl2 cases) f.cases
