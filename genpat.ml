open Ast

(* Args *)

let ntyp = ref 1
let n_contrs_args = ref 2
let npat = ref 3
let max_depth = ref 2
let max_rows = ref max_int
let path = ref ""
let shuffle = ref false
let mkorpat = ref false
let gen = ref false
let suppr = ref false
let gospel = ref false
let input_files = ref []
let anon_fun filename = input_files := filename :: !input_files
let seed_ = ref None
let tuple = ref 1
let pwhen = ref 0.

let speclist =
  [
    ("-ntyp", Arg.Set_int ntyp, "  nombre de types");
    ( "-pwhen",
      Arg.Set_float pwhen,
      "  proba d'appartition d'un when sur une ligne" );
    ("-seed", Arg.Int (fun n -> seed_ := Some n), " <int>  random seed");
    ("-dmax", Arg.Set_int max_depth, "  profondeur max des patmat");
    ("-lmax", Arg.Set_int max_rows, "  nb max de lignes des patmat");
    ("-npat", Arg.Set_int npat, " nombre de patterns par type");
    ("-gen", Arg.Set gen, " generation au lieu de print");
    ("-shuffle", Arg.Set shuffle, " melange les lignes");
    ("-suppr", Arg.Set suppr, " retire des lignes de l'exh");
    ("-orpat", Arg.Set mkorpat, " créé des or-patterns");
    ("-path", Arg.Set_string path, " chemin relatif dans test/...");
    ( "-typ-args",
      Arg.Set_int n_contrs_args,
      " nb max d'args pour les constr de types" );
    ("-gospel", Arg.Set gospel, " output gospelable");
    ("-tuple", Arg.Set_int tuple, " tuple constr lvl1");
  ]

let usage_msg = "usage: " ^ Sys.argv.(0) ^ " <input>.mp [options]"
let () = Arg.parse speclist anon_fun usage_msg

let seed =
  match !seed_ with
  | None ->
      Random.self_init ();
      Random.int (1 lsl 29)
  | Some s -> s

let () = Random.init seed

(* Utils *)

let knuth_shuffle arr =
  for n = Array.length arr - 1 downto 1 do
    let k = Random.int (n + 1) in
    let temp = arr.(n) in
    arr.(n) <- arr.(k);
    arr.(k) <- temp
  done

let rec suppr_rand l =
  let r = List.filter (fun _ -> Random.int 3 <> 0) l in
  if r <> [] then r else suppr_rand l

let orpat a =
  let a = Array.map (fun e -> Some e) a in
  for i = 0 to Array.length a - 2 do
    if Option.is_some a.(i) && Random.int 3 = 0 then (
      a.(i) <-
        Some
          Ast.
            {
              pat_desc = Por (Option.get a.(i), Option.get a.(i + 1));
              pat_loc = (Option.get a.(i)).pat_loc;
            };

      a.(i + 1) <- None)
  done;
  Array.to_list a |> List.filter Option.is_some |> List.map Option.get

module PP = struct
  open Fmt

  let case =
    let i = ref 0 in
    fun ppf p ->
      incr i;
      pf ppf "| @[%a@] %s-> " Ast.pat p
        (if Random.float 1. <= !pwhen then "when true " else "");
      if !gospel then pf ppf "true" else pf ppf "\"act %d\"" !i

  let cases ppf (s, typ, t) =
    let open Fmt in
    if !gospel then
      pf ppf
        "val f_%s : (%s) ref -> unit\n\
         (*@@ f_%s x_%s\n\
        \    modifies x_%s\n\
        \    ensures\n\
        \      match !x_%s with@\n\
        \      @[%a@] *)" s typ s s s s (list ~sep:Ast.nl case) t
    else
      pf ppf "let _ = fun x_%s -> match x_%s with@\n  @[%a@]" s s
        (list ~sep:Ast.nl case) t

  let pp_pat_l ppf =
    let open Fmt in
    pf ppf "[@[<hov 2>%a@]]," (list ~sep:comma Ast.pat)

  let pp_pat_ll ppf pll = pf ppf "[%a]" (list pp_pat_l) pll

  let command ppf () =
    pf ppf
      "(*\n\
      \    dune exec bin/genpat.exe -- -ntyp %d -dmax %d -lmax %d -npat %d \
       -typ-args %d -seed %d -tuple %d -pwhen %f%s%s%s%s%s%s\n\
       *)@."
      !ntyp !max_depth !max_rows !npat !n_contrs_args seed !tuple !pwhen
      (if !shuffle then " -shuffle" else "")
      (if !gen then " -gen" else "")
      (if !mkorpat then " -orpat" else "")
      (if !suppr then " -suppr" else "")
      (if !gospel then " -gospel" else "")
      (if !path = "" then "" else " -path " ^ !path)
end

(* Corps *)

let wild_or_var =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Ast.mk_pat_unlock Ast.Pwild
(* (if !mkorpat || Random.bool () then Ast.Pwild
   else Ast.Pvar (Format.sprintf "x%d" !cpt)) *)

let gen_rand_type ?(size_max = 3) ?(arg_max = 2) ~name () : Ast.adt list =
  let sub_gen_rand_type i =
    assert (size_max > 1);
    assert (arg_max > 0);
    assert (name <> "");
    let size = Random.int (size_max - 2) + 2 in
    let constr = [| "A"; "B"; "C"; "D"; "E" |] in

    knuth_shuffle constr;

    let res =
      List.init size (fun j ->
          let args =
            if Random.int 3 = 0 then []
            else
              List.init
                (Random.int arg_max + 1)
                (fun _ -> if Random.int 3 = 0 then "int" else name ^ i)
          in
          (constr.(j) ^ i, args))
    in
    res
  in
  assert (!tuple > 0);
  List.init !tuple (fun i ->
      let i = string_of_int i in
      (name ^ i, sub_gen_rand_type i))

let rec fd ctyp (typ : Ast.adt list) : (string * string list) list =
  match typ with
  | [] -> raise Not_found
  | e :: k -> (
      let s, sl = e in
      if s = ctyp then sl
      else
        try
          let ass = List.assoc ctyp sl in
          [ (ctyp, ass) ]
        with Not_found -> fd ctyp k)

let rec cart l =
  match l with
  | [] -> l
  | [ h ] -> List.map (fun e -> [ e ]) h
  | h :: t ->
      let c = cart t in
      List.map (fun x -> List.map (fun sc -> x :: sc) c) h |> List.flatten

let apply constr pl = Ast.mk_pat_unlock (Ast.Papp (constr, pl))

let choose w k l =
  let rec aux acc n k = function
    | [] -> acc
    | h :: t ->
        if Random.float 1. < float_of_int k /. float_of_int n then
          aux (h :: acc) (n - 1) (k - 1) t
        else aux acc (n - 1) k t
  in
  let n = List.length l in
  if n > k then aux [ w ] n (k - 1) l else l

let ni =
  let i = ref 0 in
  fun () ->
    incr i;
    !i

let rec gen_rand_pat ~depth ~rows curr_typ typ =
  if depth = 0 || rows = 1 (*|| Random.int 4 = 0*) then [ wild_or_var () ]
  else
    match curr_typ with
    | "int" ->
        let len = min rows 5 in
        List.init len (fun i ->
            if i = len - 1 then wild_or_var ()
            else
              Ast.mk_pat_unlock
                (Ast.Papp (Format.sprintf "%di" (Random.int 42), [])))
    | _ ->
        let todo_type = fd curr_typ typ in
        let len = List.length todo_type in
        if len > rows then [ wild_or_var () ]
        else
          let k = rows / len in
          let i = ref 0 in
          List.fold_right
            (fun (pname, args) acc ->
              let k =
                incr i;
                if !i = len then rows - ((len - 1) * (rows / len)) else k
              in
              let len = List.length args in
              if len = 0 then Ast.mk_pat_unlock (Papp (pname, [])) :: acc
              else
                let sub_pat =
                  List.map
                    (fun i -> gen_rand_pat ~depth:(depth - 1) ~rows:k i typ)
                    args
                in
                let w = List.init len (fun _ -> Ast.mk_pat_unlock Pwild) in
                let cc = cart sub_pat |> choose w k |> List.map (apply pname) in
                cc @ acc)
            todo_type []

(* dune exec bin/genpat.exe -- -ntyp 1 -dmax 3 -lmax 50 -npat 1 -path -typ-args -typ-args 2 -seed 349533869 -tuple 1 -gospel *)

(****************************************************)

let gen_pats adts ti =
  let tuplet, str_typ =
    let adts = List.tl adts in
    ( String.concat " * " (List.map (fun (n, _) -> n) adts),
      Format.asprintf "%s\n"
        (String.concat "\n\n" (List.map (Format.asprintf "%a" Ast.adt) adts)) )
  in

  let file =
    if not !gen then (
      Fmt.pr "%a" PP.command ();
      None)
    else (
      if !path <> "" && not (String.ends_with ~suffix:"/" !path) then
        path := !path ^ "/";
      let file = Format.sprintf "%s__autogen_%d.mp" !path ti in
      Some (open_out file))
  in

  for i = 1 to !npat do
    (match file with
    | None -> Fmt.pr "%s@." str_typ
    | Some file -> Printf.fprintf file "%s" str_typ);

    let rand_pat =
      let rdpa =
        gen_rand_pat ~rows:!max_rows ~depth:!max_depth (fst (List.hd adts)) adts
        |> choose (Ast.mk_pat_unlock Pwild) !max_rows
        |> Array.of_list
      in
      if !shuffle then knuth_shuffle rdpa;
      if !mkorpat then orpat rdpa
      else Array.to_list rdpa |> fun l -> if !suppr then suppr_rand l else l
    in

    match file with
    | None ->
        let s = (Format.sprintf "%d_%d" ti i, tuplet, rand_pat) in
        Fmt.pr "%a\n\n" PP.cases s
    | Some file ->
        let s = (Format.sprintf "generated_%d_%d" ti i, tuplet, rand_pat) in
        let pg = Format.asprintf "%a\n\n" PP.cases s in
        Printf.fprintf file "%s" pg
  done;
  match file with None -> () | Some file -> close_out file

let () =
  for ti = 1 to !ntyp do
    let adts =
      gen_rand_type ~size_max:4 ~arg_max:!n_contrs_args
        ~name:(Format.sprintf "t%d" ti) ()
    in

    let adt =
      ( "tuple" ^ string_of_int ti,
        [
          ( "tuple" ^ string_of_int ti ^ string_of_int (List.length adts),
            List.map fst adts );
        ] )
    in

    gen_pats (adt :: adts) ti
  done
