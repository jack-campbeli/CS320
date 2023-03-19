type const =
  | Unit
  | Int of int
  | Bool of bool
  | Name of string

type cmd =
  | Push of const
  | Pop of int
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | Equal
  | Lte
  | And
  | Or
  | Not
  | Trace of int
  | Local
  | Global
  | Lookup
  | BeginEnd of cmds
  | IfElse of cmds * cmds

and cmds = cmd list

type env = (string * value) list

and value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VName of string

type stack = value list

type log = string list

let string_of_value v =
  match v with
  | VUnit -> "()"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "True"
    else
      "False"
  | VName n -> n

let debug v =
  match v with
  | VUnit -> "VUnit"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "V(True)"
    else
      "V(False)"
  | VName n -> n

let rec addn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x + y, ls)
      | None -> None)
    | _ -> None

let subn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x - y, ls)
      | None -> None)
    | _ -> None

let rec muln n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (y, ls) -> Some (x * y, ls)
      | None -> None)
    | _ -> None

let rec divn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (0, ls) -> None
      | Some (y, ls) -> Some (x / y, ls)
      | None -> None)
    | _ -> None

let rec popn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ls
  else
    match ls with
    | _ :: ls -> (
      match popn (n - 1) ls with
      | Some ls -> Some ls
      | None -> None)
    | _ -> None

let rec tracen n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ([], ls)
  else
    match ls with
    | v :: ls -> (
      match tracen (n - 1) ls with
      | Some (log, ls) -> Some (string_of_value v :: log, ls)
      | None -> None)
    | _ -> None

let rec eval (g : env) (l : env) (st : stack) (log : log) (cmds : cmds) :
    env * log * stack option =
  match cmds with
  | Push cst :: cmds -> (
    match cst with
    | Unit -> eval g l (VUnit :: st) log cmds
    | Int i -> eval g l (VInt i :: st) log cmds
    | Bool b -> eval g l (VBool b :: st) log cmds
    | Name n -> eval g l (VName n :: st) log cmds)
  | Pop n :: cmds -> (
    match popn n st with
    | Some st -> eval g l st log cmds
    | _ -> (g, log, None))
  | Add n :: cmds -> (
    match addn n st with
    | Some (x, st) -> eval g l (VInt x :: st) log cmds
    | _ -> (g, log, None))
  | Sub n :: cmds -> (
    match subn n st with
    | Some (x, st) -> eval g l (VInt x :: st) log cmds
    | _ -> (g, log, None))
  | Mul n :: cmds -> (
    match muln n st with
    | Some (x, st) -> eval g l (VInt x :: st) log cmds
    | _ -> (g, log, None))
  | Div n :: cmds -> (
    match divn n st with
    | Some (x, st) -> eval g l (VInt x :: st) log cmds
    | _ -> (g, log, None))
  | Equal :: cmds -> (
    match st with
    | VInt i1 :: VInt i2 :: st -> eval g l (VBool (i1 = i2) :: st) log cmds
    | _ -> (g, log, None))
  | Lte :: cmds -> (
    match st with
    | VInt i1 :: VInt i2 :: st -> eval g l (VBool (i1 <= i2) :: st) log cmds
    | _ -> (g, log, None))
  | And :: cmds -> (
    match st with
    | VBool b1 :: VBool b2 :: st -> eval g l (VBool (b1 && b2) :: st) log cmds
    | _ -> (g, log, None))
  | Or :: cmds -> (
    match st with
    | VBool b1 :: VBool b2 :: st -> eval g l (VBool (b1 || b2) :: st) log cmds
    | _ -> (g, log, None))
  | Not :: cmds -> (
    match st with
    | VBool b :: st -> eval g l (VBool (not b) :: st) log cmds
    | _ -> (g, log, None))
  | Trace n :: cmds -> (
    match tracen n st with
    | Some (lg, st) -> eval g l st (List.rev lg @ log) cmds
    | _ -> (g, log, None))
  | Local :: cmds -> (
    match st with
    | VName n :: v :: st -> eval g ((n, v) :: l) (VUnit :: st) log cmds
    | _ -> (g, log, None))
  | Global :: cmds -> (
    match st with
    | VName n :: v :: st -> eval ((n, v) :: g) l (VUnit :: st) log cmds
    | _ -> (g, log, None))
  | Lookup :: cmds -> (
    match st with
    | VName n :: st -> (
      match List.assoc_opt n (l @ g) with
      | Some v -> eval g l (v :: st) log cmds
      | None -> (g, log, None))
    | _ -> (g, log, None))
  | BeginEnd bod :: cmds -> (
    match eval g l [] log bod with
    | g, log, Some (v :: _) -> eval g l (v :: st) log cmds
    | g, log, _ -> (g, log, None))
  | IfElse (cmds1, cmds2) :: cmds -> (
    match st with
    | VBool b :: st ->
      if b then
        eval g l st log (cmds1 @ cmds)
      else
        eval g l st log (cmds2 @ cmds)
    | _ -> (g, log, None))
  | _ -> (g, log, Some st)

(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
 fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
 fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
 fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
    match p2 ls with
    | Some (_, ls) -> Some (x, ls)
    | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let rec many (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
 fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
 fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
 fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()

(* end of parser combinators *)

let reserved = [ "True"; "False" ]

let name : string parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
  let s = implode (c :: cs) in
  if List.exists (fun x -> x = s) reserved then
    fail
  else
    pure s << ws

let name_parser () =
  let* n = name in
  pure (Name n)

let unit_parser () =
  let* _ = keyword "()" in
  pure Unit

let int_parser () =
  (let* n = natural in
   pure (Int n) << ws)
  <|> let* _ = keyword "-" in
      let* n = natural in
      pure (Int (-n)) << ws

let true_parser () =
  let* _ = keyword "True" in
  pure true

let false_parser () =
  let* _ = keyword "False" in
  pure false

let bool_parser () =
  let* b = true_parser () <|> false_parser () in
  pure (Bool b)

let const_parser () =
  int_parser () <|> name_parser () <|> bool_parser () <|> unit_parser ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  pure (Push cst)

let rec pop_parser () =
  let* _ = keyword "Pop" in
  let* n = natural in
  pure (Pop n) << ws

and add_parser () =
  let* _ = keyword "Add" in
  let* n = natural in
  pure (Add n) << ws

and sub_parser () =
  let* _ = keyword "Sub" in
  let* n = natural in
  pure (Sub n) << ws

and mul_parser () =
  let* _ = keyword "Mul" in
  let* n = natural in
  pure (Mul n) << ws

and div_parser () =
  let* _ = keyword "Div" in
  let* n = natural in
  pure (Div n) << ws

and equal_parser () =
  let* _ = keyword "Equal" in
  pure Equal

and lte_parser () =
  let* _ = keyword "Lte" in
  pure Lte

and and_parser () =
  let* _ = keyword "And" in
  pure And

and or_parser () =
  let* _ = keyword "Or" in
  pure Or

and not_parser () =
  let* _ = keyword "Not" in
  pure Not

and trace_parser () =
  let* _ = keyword "Trace" in
  let* n = natural in
  pure (Trace n) << ws

and local_parser () =
  let* _ = keyword "Local" in
  pure Local

and global_parser () =
  let* _ = keyword "Global" in
  pure Global

and lookup_parser () =
  let* _ = keyword "Lookup" in
  pure Lookup

and begin_parser () =
  let* _ = keyword "Begin" in
  let* cmds = cmds_parser () in
  let* _ = keyword "End" in
  pure (BeginEnd cmds)

and ifelse_parser () =
  let* _ = keyword "If" in
  let* cmds1 = cmds_parser () in
  let* _ = keyword "Else" in
  let* cmds2 = cmds_parser () in
  let* _ = keyword "End" in
  pure (IfElse (cmds1, cmds2))

and cmd_parser () =
  push_parser () <|> pop_parser () <|> trace_parser () <|> add_parser ()
  <|> sub_parser () <|> mul_parser () <|> div_parser () <|> equal_parser ()
  <|> lte_parser () <|> and_parser () <|> or_parser () <|> not_parser ()
  <|> local_parser () <|> global_parser () <|> lookup_parser ()
  <|> begin_parser () <|> ifelse_parser ()

and cmds_parser () = many (cmd_parser ())

let parse_cmds s = parse (ws >> cmds_parser ()) s

let interp (src : string) : string list =
  match parse_cmds src with
  | Some (cmds, []) -> (
    match eval [] [] [] [] cmds with
    | _, log, Some _ -> log
    | _, _, None -> [ "Error" ])
  | _ -> [ "Error" ]

let main fname =
  let src = readlines fname in
  interp src
