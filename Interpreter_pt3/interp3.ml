type const =
  | CUnit
  | CInt of int
  | CBool of bool
  | CName of string

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
  | Fun of const * const * cmds 
  | Call
  | Try of cmds 

and cmds = cmd list

type env = (string * value) list

and value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VName of string
  | Clo of (env * const * const * cmds)

type stack = value list

type output = string list

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
  | Clo (fenv , fname , farg , fcmds) -> "<clo>"

let string_of_const v =
  match v with
  | CUnit -> "()"
  | CInt i -> string_of_int i
  | CBool b ->
    if b then
      "True"
    else
      "False"
  | CName n -> n

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
  | Clo (fenv , fname , farg , fcmds) -> "<clo>"

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
        | Some (output, ls) -> Some (string_of_value v :: output, ls)
        | None -> None)
    | _ -> None

let copy_env env = 
  let rec aux env output =
    match env with
    | [] -> List.rev output
    | head::tail -> aux tail (head::output)
  in aux env []

let rec eval (global : env) (local : env) (stack : stack) (output : output) (cmds : cmds) :
  env * output * stack option =
  match cmds with
  | Push cst :: cmds -> (
      match cst with
      | CUnit -> eval global local (VUnit :: stack) output cmds
      | CInt i -> eval global local (VInt i :: stack) output cmds
      | CBool b -> eval global local (VBool b :: stack) output cmds
      | CName n -> eval global local (VName n :: stack) output cmds)
  | Pop n :: cmds -> (
      match popn n stack with
      | Some stack -> eval global local stack output cmds
      | _ -> (global, output, None))
  | Add n :: cmds -> (
      match addn n stack with
      | Some (x, stack) -> eval global local (VInt x :: stack) output cmds
      | _ -> (global, output, None))
  | Sub n :: cmds -> (
      match subn n stack with
      | Some (x, stack) -> eval global local (VInt x :: stack) output cmds
      | _ -> (global, output, None))
  | Mul n :: cmds -> (
      match muln n stack with
      | Some (x, stack) -> eval global local (VInt x :: stack) output cmds
      | _ -> (global, output, None))
  | Div n :: cmds -> (
      match divn n stack with
      | Some (x, stack) -> eval global local (VInt x :: stack) output cmds
      | _ -> (global, output, None))
  | Equal :: cmds -> (
      match stack with
      | VInt i1 :: VInt i2 :: stack -> eval global local (VBool (i1 = i2) :: stack) output cmds
      | _ -> (global, output, None))
  | Lte :: cmds -> (
      match stack with
      | VInt i1 :: VInt i2 :: stack -> eval global local (VBool (i1 <= i2) :: stack) output cmds
      | _ -> (global, output, None))
  | And :: cmds -> (
      match stack with
      | VBool b1 :: VBool b2 :: stack -> eval global local (VBool (b1 && b2) :: stack) output cmds
      | _ -> (global, output, None))
  | Or :: cmds -> (
      match stack with
      | VBool b1 :: VBool b2 :: stack -> eval global local (VBool (b1 || b2) :: stack) output cmds
      | _ -> (global, output, None))
  | Not :: cmds -> (
      match stack with
      | VBool b :: stack -> eval global local (VBool (not b) :: stack) output cmds
      | _ -> (global, output, None))
  | Trace n :: cmds -> (
      match tracen n stack with
      | Some (lg, stack) -> eval global local stack (List.rev lg @ output) cmds
      | _ -> (global, output, None))
  | Local :: cmds -> (
      match stack with
      | VName n :: v :: stack -> eval global ((n, v) :: local) (VUnit :: stack) output cmds
      | _ -> (global, output, None))
  | Global :: cmds -> (
      match stack with
      | VName n :: v :: stack -> eval ((n, v) :: global) local (VUnit :: stack) output cmds
      | _ -> (global, output, None))
  | Lookup :: cmds -> (
      match stack with
      | VName n :: stack -> (
          match List.assoc_opt n (local @ global) with
          | Some v -> eval global local (v :: stack) output cmds
          | None -> (global, output, None))
      | _ -> (global, output, None))
  | BeginEnd cmd_lst :: cmds -> (
      match eval global local [] output cmd_lst with
      | global, output, Some (v :: _) -> eval global local (v :: stack) output cmds
      | global, output, _ -> (global, output, None))
  | IfElse (cmds1, cmds2) :: cmds -> (
      match stack with
      | VBool b :: stack ->
        if b then
          eval global local stack output (cmds1 @ cmds)
        else
          eval global local stack output (cmds2 @ cmds)
      | _ -> (global, output, None))
  | Fun (CName fname, CName farg, fcmds) :: cmds -> (
      (*creating a closure of the function and then adding it to the local env*)
      let fclosure = Clo (local, CName fname, CName farg, fcmds) in
      eval global ((fname, fclosure) :: local) stack output cmds)
  | Call :: cmds -> ( 
      match stack with
      | (Clo (fenv, CName fname, CName farg, fcmds)) :: arg :: stack -> (
          (
            (* evaluating all commands found within the closure *)
            match eval global ((fname, Clo(fenv, CName fname, CName farg, fcmds))::(farg,arg)::fenv) [] output fcmds with
            (*taking the top most value of the new stack and pushing it onto the global stack*)
            | new_global, output, Some (v::rest) -> eval new_global local (v::stack) output cmds
            | _, _, _ -> (global, output, None)))
      | _ -> (global, output, None))
  | Try cmd_lst :: cmds -> (
      match eval global local [] output cmd_lst with
      | new_global, new_output, Some (v :: _) -> eval new_global local (v :: stack) new_output cmds
      | new_global, new_output, _ -> eval new_global local stack new_output cmds
    )
  | _ -> (global, output, Some stack)

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

let return (x : 'a) : 'a parser = fun ls -> Some (x, ls)

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
    return s << ws

let name_parser () = 
  let* str = name in
  return (CName str)

let unit_parser () =
  let* _ = keyword "()" in
  return CUnit

let int_parser () =
  (let* n = natural in
   return (CInt n) << ws)
  <|> let* _ = keyword "-" in
  let* n = natural in
  return (CInt (-n)) << ws

let true_parser () =
  let* _ = keyword "True" in
  return true

let false_parser () =
  let* _ = keyword "False" in
  return false

let bool_parser () =
  let* b = true_parser () <|> false_parser () in
  return (CBool b)

let const_parser () =
  int_parser () <|> name_parser () <|> bool_parser () <|> unit_parser ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  return (Push cst)

let rec pop_parser () =
  let* _ = keyword "Pop" in
  let* n = natural in
  return (Pop n) << ws

and add_parser () =
  let* _ = keyword "Add" in
  let* n = natural in
  return (Add n) << ws

and sub_parser () =
  let* _ = keyword "Sub" in
  let* n = natural in
  return (Sub n) << ws

and mul_parser () =
  let* _ = keyword "Mul" in
  let* n = natural in
  return (Mul n) << ws

and div_parser () =
  let* _ = keyword "Div" in
  let* n = natural in
  return (Div n) << ws

and equal_parser () =
  let* _ = keyword "Equal" in
  return Equal

and lte_parser () =
  let* _ = keyword "Lte" in
  return Lte

and and_parser () =
  let* _ = keyword "And" in
  return And

and or_parser () =
  let* _ = keyword "Or" in
  return Or

and not_parser () =
  let* _ = keyword "Not" in
  return Not

and trace_parser () =
  let* _ = keyword "Trace" in
  let* n = natural in
  return (Trace n) << ws

and local_parser () =
  let* _ = keyword "Local" in
  return Local

and global_parser () =
  let* _ = keyword "Global" in
  return Global

and lookup_parser () =
  let* _ = keyword "Lookup" in
  return Lookup

and begin_parser () =
  let* _ = keyword "Begin" in
  let* cmds = cmds_parser () in
  let* _ = keyword "End" in
  return (BeginEnd cmds)

and ifelse_parser () =
  let* _ = keyword "If" in
  let* cmds1 = cmds_parser () in
  let* _ = keyword "Else" in
  let* cmds2 = cmds_parser () in
  let* _ = keyword "End" in
  return (IfElse (cmds1, cmds2))

and fun_parser () =
  let* _ = keyword "Fun" in
  let* fname = name_parser () in
  let* farg = name_parser () in
  let* cmds = cmds_parser () in
  let* _ = keyword "End" in
  return (Fun (fname, farg, cmds))

and call_parser () =
  let* _ = keyword "Call" in
  return (Call)

and try_parser () =
  let* _ = keyword "Try" in
  let* cmds = cmds_parser () in
  let* _ = keyword "End" in
  return (Try cmds)

and cmd_parser () =
  push_parser () <|> pop_parser () <|> trace_parser () <|> add_parser ()
  <|> sub_parser () <|> mul_parser () <|> div_parser () <|> equal_parser ()
  <|> lte_parser () <|> and_parser () <|> or_parser () <|> not_parser ()
  <|> local_parser () <|> global_parser () <|> lookup_parser () <|> begin_parser () 
  <|> ifelse_parser () <|> fun_parser () <|> call_parser () <|> try_parser ()

and cmds_parser () = many (cmd_parser ())

let parse_cmds s = parse (ws >> cmds_parser ()) s

let interp (src : string) : string list =
  match parse_cmds src with
  | Some (cmds, []) -> (
      match eval [] [] [] [] cmds with
      | _, output, Some _ -> output
      | _, _, None -> [ "Error" ])
  | _ -> [ "Error" ]

let main fname =
  let src = readlines fname in
  interp src
