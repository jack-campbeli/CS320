type const =
  | Unit
  | Int of int
  | Bool of bool
  | Name of string

type command =
  | Push of const
  | Pop of int
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | Trace of int
  | And
  | Or
  | Not
  | Equal
  | Lte
  | Local
  | Global
  | Lookup
  | BeginEnd of commands
  | IfElse of commands * commands

and commands = command list

type env = (string * value) list

(*stack value*)
and value =
  | VUnit
  | VInt of int
  | VBool of bool 
  | VName of string

type stack = value list

type output = string list

let string_of_value v =
  match v with
  | VName n -> n
  | VUnit -> "()"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "True"
    else
      "False"

let debug v =
  match v with
  | VName n -> "VName"
  | VUnit -> "VUnit"
  | VInt i -> string_of_int i
  | VBool b ->
    if b then
      "V(True)"
    else
      "V(False)"

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

let rec andn ls = 
  match ls with
  | [] -> None
  | _::[] -> None
  | VBool v1 :: VBool v2 :: tail  ->
    (
      match v1, v2 with
      | true, true  -> Some (true, tail)
      | _ -> Some (false, tail)
    )
  | _ -> None 

let rec orn ls = 
  match ls with
  | [] -> None
  | _::[] -> None
  | VBool v1 :: VBool v2 :: tail  ->
    (
      match v1, v2 with
      | false, false  -> Some (false, tail)
      | _ -> Some (true, tail)
    )
  | _ -> None 

let rec notn ls = 
  match ls with
  | [] -> None
  | VBool v :: tail  ->
    (
      match v with
      | false -> Some (true, tail)
      | true -> Some (false, tail)
    )
  | _ -> None 

let rec equaln ls = 
  match ls with
  | [] -> None
  | _::[] -> None
  | VInt v1 :: VInt v2 :: tail  ->
    if v1 = v2 
    then Some (true, tail)
    else Some (false, tail)
  | _ -> None 

let rec lten ls = 
  match ls with
  | [] -> None
  | _::[] -> None
  | VInt v1 :: VInt v2 :: tail  ->
    if v1 <= v2 
    then Some (true, tail)
    else Some (false, tail)
  | _ -> None 

(*
  assign ():
    takes in a name, value, and current environment
    and checks if the name is already present. If it
    is, then you reassign the value. Else, you create
    a new value-pair assignment and add it the the 
    current environment if applicable. 
*)
let rec assign newName newValue env =
  match env with
  | [] -> [(newName, newValue)]
  | (name, value)::rest -> 
    if newName = name 
    then (name,newValue)::rest
    else
      (name, value) :: assign newName newValue rest

let rec localn local ls =
  match ls with
  | [] -> None
  | _::[] -> None
  | VName name :: value :: tail -> 
    (
      match value with
      | VBool b -> 
        let l = assign name (VBool b) local in
        Some ((), tail, l)
      | VInt i -> 
        let l = assign name (VInt i) local in
        Some ((), tail, l)
      | VName n -> 
        let l = assign name (VName n) local in
        Some ((), tail, l)
      | VUnit -> 
        let l = assign name (VUnit) local in
        Some ((), tail, l)
    )
  | _ -> None 

let rec globaln global ls =
  match ls with
  | [] -> None
  | _::[] -> None
  | VName name :: value :: tail -> 
    (
      match value with
      | VBool b -> 
        let g = assign name (VBool b) global in
        Some ((), tail, g)
      | VInt i -> 
        let g = assign name (VInt i) global in
        Some ((), tail, g)
      | VName n -> 
        let g = assign name (VName n) global in
        Some ((), tail, g)
      | VUnit -> 
        let g = assign name (VUnit) global in
        Some ((), tail, g)
    )
  | _ -> None 

let rec lookupn ls env = 
  match ls with
  | [] -> None
  | VName vname :: tail -> 
    (
      match env with 
      | [] -> None
      | (name, value)::rest -> 
        if vname = name 
        then Some(value,tail)
        else 
          lookupn ls rest
    )
  | _ -> None 

let copy_env env = 
  let rec aux env output =
    match env with
    | [] -> List.rev output
    | head::tail -> aux tail (head::output)
  in aux env []

let rec eval (stack : stack) (output : output) (local : env) (global : env) (commands : commands) : (output * stack option) * (env * env) =
  match commands with
  | Push cst :: commands -> (
      match cst with
      | Name n -> eval (VName n :: stack) output local global commands
      | Unit -> eval (VUnit :: stack) output local global commands
      | Int i -> eval (VInt i :: stack) output local global commands
      | Bool b -> eval (VBool b :: stack) output local global commands)
  | Pop n :: commands -> (
      match popn n stack with
      | Some stack -> eval stack output local global commands
      | _ -> ((output, None),([],[])))
  | Trace n :: commands -> (
      match tracen n stack with
      | Some (lg, stack) -> eval stack (List.rev lg @ output) local global commands
      | _ -> ((output, None),([],[])))  
  | Add n :: commands -> (
      match addn n stack with
      | Some (x, stack) -> eval (VInt x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Sub n :: commands -> (
      match subn n stack with
      | Some (x, stack) -> eval (VInt x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Mul n :: commands -> (
      match muln n stack with
      | Some (x, stack) -> eval (VInt x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Div n :: commands -> (
      match divn n stack with
      | Some (x, stack) -> eval (VInt x :: stack) output local global commands
      | _ -> ((output, None),([],[]))) 
  | And :: commands -> (
      match andn stack with
      | Some (x, stack) -> eval (VBool x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Or :: commands -> (
      match orn stack with
      | Some (x, stack) -> eval (VBool x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Not :: commands -> (
      match notn stack with
      | Some (x, stack) -> eval (VBool x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Equal :: commands -> (
      match equaln stack with
      | Some (x, stack) -> eval (VBool x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Lte :: commands -> (
      match lten stack with
      | Some (x, stack) -> eval (VBool x :: stack) output local global commands
      | _ -> ((output, None),([],[])))
  | Local :: commands -> (
      match localn local stack with
      | Some (x, stack, new_local) -> eval (VUnit :: stack) output (new_local) global commands
      | _ -> ((output, None),([],[])))
  | Global :: commands -> (
      match globaln global stack with
      | Some (x, stack, new_global) -> eval (VUnit :: stack) output local (new_global) commands
      | _ -> ((output, None),([],[])))
  | Lookup :: commands -> (
      match lookupn stack local, lookupn stack global with
      (*If there are any local values*)
      | Some (lVal, lStack), _ -> (
          match lVal with
          | VName n -> eval (VName n :: lStack) output local global commands
          | VUnit -> eval (VUnit :: lStack) output local global commands
          | VInt i -> eval (VInt i :: lStack) output local global commands
          | VBool b -> eval (VBool b :: lStack) output local global commands) 
      (*If there are global but no local values*)    
      | None, Some (gVal, gStack) -> (
          match gVal with
          | VName n -> eval (VName n :: gStack) output local global commands
          | VUnit -> eval (VUnit :: gStack) output local global commands
          | VInt i -> eval (VInt i :: gStack) output local global commands
          | VBool b -> eval (VBool b :: gStack) output local global commands) 
      | _ -> ((output, None),([],[])))
  | BeginEnd (cmd_lst) :: commands -> (
      match (eval [] [] (copy_env local) (copy_env global) cmd_lst) with
      | ((out, Some (h::t)),(localx, global)) -> (eval (h::stack) (out@output) local global commands)
      | _ -> ((output, None),([],[])))
  | IfElse (cmd_lst1,cmd_lst2) :: commands -> (
    (
      match stack with
      | VBool b :: rest -> (
          if b = true 
          then (
            match (eval rest output local global cmd_lst1) with
            | ((out, Some (stk)),(new_local, new_global)) -> 
              (eval (stk) (output) (local@new_local) (global@new_global) commands)
            | _ -> ((output, None),([],[])))
          else  
            (
              match (eval rest output local global cmd_lst2) with
              | ((out, Some (stk)),(new_local, new_global)) -> 
                (eval (stk) (output) (local@new_local) (global@new_global) commands)
              | _ -> ((output, None),([],[]))))
      | _ -> ((output, None),([],[]))
    )
  )
  | _ -> ((output, Some stack), (local, global))

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

let reserved =
  [ "Push"
  ; "True"
  ; "False"
  ; "Pop"
  ; "Add"
  ; "Sub"
  ; "Mul"
  ; "Div"
  ; "Equal"
  ; "Lte"
  ; "And"
  ; "Or"
  ; "Not"
  ; "Trace"
  ; "Local"
  ; "Global"
  ; "Lookup"
  ; "Begin"
  ; "If"
  ; "Else"
  ; "Fun"
  ; "End"
  ; "Call"
  ; "Try"
  ; "Switch"
  ; "Case"
  ]

let name : string parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
  let s = implode (c :: cs) in
  if List.exists (fun x -> x = s) reserved then
    fail
  else
    return s << ws

let unit_parser () =
  let* _ = keyword "()" in
  return Unit

let int_parser () =
  (let* n = natural in
   return (Int n) << ws)
  <|> let* _ = keyword "-" in
  let* n = natural in
  return (Int (-n)) << ws

let true_parser () =
  let* _ = keyword "True" in
  return true

let false_parser () =
  let* _ = keyword "False" in
  return false

let bool_parser () =
  let* b = true_parser () <|> false_parser () in
  return (Bool b)

let name_parser () = 
  let* str = name in
  return (Name str)

let const_parser () = 
  int_parser () <|> 
  bool_parser () <|> 
  unit_parser () <|> 
  name_parser ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  return (Push cst)

let rec pop_parser () =
  let* _ = keyword "Pop" in
  let* n = natural in
  return (Pop n) << ws

and trace_parser () =
  let* _ = keyword "Trace" in
  let* n = natural in
  return (Trace n) << ws

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

(*and*)
and and_parser () = 
  let* _ = keyword "And" in
  ws >>= fun _ ->
  return (And) 

(*or*)
and or_parser () = 
  let* _ = keyword "Or" in
  ws >>= fun _ ->
  return (Or) 

(*not*)
and not_parser () = 
  let* _ = keyword "Not" in
  ws >>= fun _ ->
  return (Not) 

(*equal*)
and equal_parser () = 
  let* _ = keyword "Equal" in
  ws >>= fun _ ->
  return (Equal) 

(*lte*)
and lte_parser () = 
  let* _ = keyword "Lte" in
  ws >>= fun _ ->
  return (Lte) 

(*Local*)
and local_parser () = 
  let* _ = keyword "Local" in
  ws >>= fun _ ->
  return (Local) 

(*global*)
and global_parser () = 
  let* _ = keyword "Global" in
  ws >>= fun _ ->
  return (Global) 

(*lookup*)
and lookup_parser () = 
  let* _ = keyword "Lookup" in
  ws >>= fun _ ->
  return (Lookup) 

and beginEnd_parser () = 
  let* _ = keyword "Begin" in
  let* cmd_lst = commands_parser () in
  let* _ = keyword "End" in
  return (BeginEnd cmd_lst)

and ifElse_parser () = 
  let* _ = keyword "If" in
  let* cmd_lst1 = commands_parser () in
  let* _ = keyword "Else" in
  let* cmd_lst2 = commands_parser () in
  let* _ = keyword "End" in
  return (IfElse (cmd_lst1,cmd_lst2))

and command_parser () =
  push_parser () <|> 
  pop_parser () <|> 
  trace_parser () <|> 
  add_parser () <|>
  sub_parser () <|> 
  mul_parser () <|> 
  div_parser () <|>
  and_parser () <|>
  or_parser () <|>
  not_parser () <|>
  equal_parser () <|>
  lte_parser () <|>
  local_parser () <|>
  global_parser () <|>
  lookup_parser () <|>
  beginEnd_parser () <|>
  ifElse_parser ()

and commands_parser () = many (command_parser ())

let parse_commands s = parse (ws >> commands_parser ()) s

let interp (src : string) : string list =
  match parse_commands src with
  | Some (commands, []) -> (
      (* stack output commands*)
      match eval [] [] [] [] commands with
      | ((output, Some _),(x,y)) -> output
      | _ -> ["Error"])
  | _ -> ["Error"]

let main fname =
  let src = readlines fname in
  interp src
