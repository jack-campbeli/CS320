(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

(*string -> character list*)
let explode s = List.of_seq (String.to_seq s)

(*character list -> string*)
let implode ls = String.of_seq (List.to_seq ls)

(*returns a string of the characters in the file*)
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

(*automatically explodes the string into a character list*)
let parse (parser : 'a parser) (str : string) : ('a * char list) option = 
  parser (explode str)

(*same as return*)
let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let return = pure

(*for in a parser fails*)
let fail : 'a parser = fun ls -> None

(*_*)
let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

(*can use either of these for bind*)
let ( >>= ) = bind
let ( let* ) = bind

(*a parser that outputs (first char of the string * [the rest]) *)
let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

(*a parser that creates a parser that *)
let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

(*
  let test = satisfy (fun x -> x = 'a')
  creates a parser test that parses a string and checks if the first character is equal to 'a'
*)

(*
  a char parser that parsers the matching input
  if there is not match None is returned
*)
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

(*runs the p1 parser and if p1 fails, you run the p2 parser*)
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

(*runs the parser 0 or more times*)
let rec many (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)
(*
  let test = satisfy (fun x -> x = 'a')
  parse (many test) "aaaaaaxyz"
    output: Some (['a';'a';'a';'a';'a';'a'],['x';'y';'z'])
*)

(*runs the parser 1 or more times*)
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

(*a digit parser that parses the first digit of a string*)
let digit_parser : char parser = satisfy is_digit

(*a digit parser that parses the first letter of a string*)
let letter_parser : char parser = satisfy is_alpha

let natural_parser : int parser =
  fun ls ->
  match many1 digit_parser ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

(*runs natural and if it fails runs the other parser which returns a negative digit*)
let int_parser : int parser =
  natural_parser 
  <|> 
  (
    satisfy (fun x -> x = '-') >>= fun _ ->
    natural_parser >>= fun number ->
    return (-1 * number) 
  )

(*consumes entire series of specified strings*)
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
(*
    let test = literal "Push" [consumes the first occurance of "Push"]
    test "Push5Push7" 
      output: Some ((),['5';'P';'u';'s';'h';'7'])
*)

(*checks if there is a "Push #" found in the input string*)
let literal_str =
  satisfy (fun x -> x = 'P') >>= fun c1 ->
  satisfy (fun x -> x = 'u') >>= fun c2 ->
  satisfy (fun x -> x = 's') >>= fun c3 ->
  satisfy (fun x -> x = 'h') >>= fun c4 ->
  whitespace >>= fun c5 ->
  int_parser >>= fun num1 ->
  return () (* implode goes from list to string *)

(*
  what about mulitple literal_str

  parse ((many (literall_str >>= fun whitespace))) "Push 1 Push 2 Push 3 Add 2"

  THIS SOLUTION ONLY WORKS FOR MULTIPLE OCCURANCES OF PUSH

  parse ((many (literall_str >>= fun whitespace))) "Push 1"

*)

(*defining the stack values*)
type stackValue =
  | Int of int
  | Bool of bool
  | Unit of unit

(*defining the stack commands*)
type command =
  | Push of stackValue
  | Pop of int
  | Trace of int
  | Add of int
  | Subtract of int
  | Multiply of int
  | Divide of int

(*stack value parsers*)
(*parsing stack boolean true*)
let true_sparser: stackValue parser =
  ws >>= fun _ ->
  literal "True" >>= fun _ ->
  ws >>= fun _ ->
  return (Bool (true))

(*parsing stack boolean false*)
let false_sparser: stackValue parser =
  ws >>= fun _ ->
  literal "False" >>= fun x ->
  ws >>= fun _ ->
  return (Bool (false))

(*parsing a stack int*) 
let int_sparser: stackValue parser = 
  ws >>= fun _ -> 
  int_parser >>= fun num ->
  return (Int (num))

(*parsing a stack unit*) 
let unit_sparser: stackValue parser =
  ws >>= fun _ ->
  literal "()" >>= fun unit ->
  ws >>= fun _ ->
  return (Unit ())

(*parsing a stack boolean*)   
let boolean_sparser: stackValue parser =
  true_sparser <|> false_sparser

(*parsing all stack values*)   
let stackValueParser: stackValue parser =
  int_sparser <|>  
  boolean_sparser <|> 
  unit_sparser

(*command parsers*)
(*push int*)
let pushInt_parser: command parser = 
  literal "Push" >>= fun _ ->
  ws1 >>= fun _ ->
  int_sparser >>= fun num ->
  ws >>= fun _ ->
  return (Push (num)) 

(*push bool*)
let pushBool_parser: command parser = 
  literal "Push" >>= fun _ ->
  ws1 >>= fun _ ->
  boolean_sparser >>= fun bool ->
  ws >>= fun _ ->
  return (Push (bool)) 

(*push unit*)
let pushUnit_parser: command parser = 
  literal "Push" >>= fun _ ->
  ws1 >>= fun _ ->
  unit_sparser >>= fun unit ->
  ws >>= fun _ ->
  return (Push (unit)) 

(*push stackValue*)
let push_parser: command parser =
  pushInt_parser <|>
  pushBool_parser <|>
  pushUnit_parser 

(*pop*)
let pop_parser: command parser = 
  literal "Pop" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Pop (num)) 

(*trace*)
let trace_parser: command parser = 
  literal "Trace" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Trace (num)) 

(*add*)
let add_parser: command parser = 
  literal "Add" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Add (num)) 

(*sub*)
let sub_parser: command parser = 
  literal "Sub" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Subtract (num)) 

(*mul*)
let mul_parser: command parser = 
  literal "Mul" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Multiply (num)) 

(*div*)
let div_parser: command parser = 
  literal "Div" >>= fun _ ->
  ws1 >>= fun _ ->
  int_parser >>= fun num ->
  ws >>= fun _ ->
  return (Divide (num)) 

(*runParsers*)
(*parses all commands once*)
let parseCommands =
  push_parser <|> 
  pop_parser <|> 
  trace_parser <|> 
  add_parser <|> 
  sub_parser <|> 
  mul_parser <|> 
  div_parser

let keyword (s : string) : unit parser = literal s >> ws >| ()

(* end of parser combinators *)

let nElements num stack = 
  if (num < 0 || num > (List.length stack))
  then (["Error"],["Error"])
  else
    (
      let rec aux num stack acc =
        if num = 0 
        then (acc,stack)
        else(
          match stack with
          | [] -> failwith "stack empty"
          | head::tail -> aux (num-1) tail (head::acc)
        )
      in aux num stack []
    )

let stackValue_to_String (stackVal: stackValue): string = 
  match stackVal with
  | Int i -> string_of_int i
  | Bool b -> (match b with
      | true -> "True"
      | false -> "False")
  | Unit () -> "()"

let isInt (str: string): string =
  match (parse (stackValueParser) str) with
  | Some (Int x, _) -> string_of_int x
  | Some (Bool b, _) -> "Error"
  | Some (Unit (), _) -> "Error"
  | None -> "Error"

let addList (str_lst: string list): string list = 
  let rec aux str_lst sum =
    match str_lst with
    | [] -> [string_of_int sum]
    | head::tail ->
      (
        match (parse (stackValueParser) head) with
        | Some (Int x, _) -> aux tail (x+sum)
        | Some (Bool b, _) -> ["Error"]
        | Some (Unit (), _) -> ["Error"]
        | None -> ["Error"]
      )
  in aux str_lst 0

let mulList (str_lst: string list): string list = 
  let rec aux str_lst product =
    match str_lst with
    | [] -> [string_of_int product]
    | head::tail ->
      (
        match (parse (stackValueParser) head) with
        | Some (Int x, _) -> aux tail (x*product)
        | Some (Bool b, _) -> ["Error"]
        | Some (Unit (), _) -> ["Error"]
        | None -> ["Error"]
      )
  in aux str_lst 1

(*created sting to stackvalue 
  patten match the stack value to make sure that ecah of them are of type INt
  if they are Bool or Unit return [Error]
*)

let rec evaluate (stack: string list) (output: string list) (cmdList: command list): string list= 
  match cmdList with
  | [] -> output
  | head::rest ->
    match head with
    | Trace num -> 
      (
        (*Getting n elements off the stack*)
        match (nElements num stack) with
        | (["Error"],["Error"]) -> ["Error"]
        | (acc, stack) -> evaluate stack (acc @ output) rest
      )
    | Add num -> 
      (
        (*Getting n elements off the stack*)
        match (nElements num stack) with
        | (["Error"],["Error"]) -> ["Error"]
        | (acc, stack) -> 
          (
            match (addList acc) with
            | ["Error"] -> ["Error"]
            | sum -> evaluate (sum @ stack) output rest
          )
      )
    | Multiply num -> 
      (
        (*Getting n elements off the stack*)
        match (nElements num stack) with
        | (["Error"],["Error"]) -> ["Error"]
        | (acc, stack) -> 
          (
            match (mulList acc) with
            | ["Error"] -> ["Error"]
            | product -> evaluate (product @ stack) output rest
          )
      )
    | Subtract num -> 
      if num > 0 then
        (
          match stack with
          | [] -> ["Error"]
          | head::tail ->
            (
              (*Getting n-1 elements off the stack*)
              match (nElements (num-1) tail) with
              | (["Error"],["Error"]) -> ["Error"]
              | (acc, stack) -> 
                (
                  (*summing n-1 elements*)
                  match (addList acc) with
                  | ["Error"] -> ["Error"]
                  | sum -> 
                    (
                      (*subtracting the head from the sum of (n-1) elements*)
                      match isInt head, sum with 
                      | "Error",[sum] -> ["Error"]
                      | vl,[sum] -> 
                        (
                          let difference = ((int_of_string vl) - (int_of_string sum)) in
                          let difference_str = string_of_int difference in
                          evaluate (difference_str::stack) output rest
                        )
                      | _,_ -> ["Error"]
                    )
                )
            )
        ) else evaluate ("0"::stack) output rest
    | Divide num -> 
      if num > 0 then
        (
          match stack with
          | [] -> ["Error"]
          | head::tail ->
            (
              (*Getting n-1 elements off the stack*)
              match (nElements (num-1) tail) with
              | (["Error"],["Error"]) -> ["Error"]
              | (acc, stack) -> 
                (
                  (*summing n-1 elements*)
                  match (mulList acc) with
                  | ["Error"] | ["0"] -> ["Error"]
                  | product -> 
                    (
                      (*subtracting the head from the sum of (n-1) elements*)
                      match isInt head, product with 
                      | "Error",[product] -> ["Error"]
                      | vl,[product] -> 
                        (
                          let quotient = ((int_of_string vl) / (int_of_string product)) in
                          let quotient_str = string_of_int quotient in
                          evaluate (quotient_str::stack) output rest
                        )
                      | _,_ -> ["Error"]
                    )
                )
            )
        ) else evaluate ("1"::stack) output rest
    | Push stackVal -> evaluate (stackValue_to_String stackVal::stack) output rest 
    (*POP IS NOT CORRECT*)
    | Pop num ->  
      (
        match (nElements num stack) with
        | (["Error"],["Error"]) -> ["Error"]
        | (_, stack) -> evaluate stack output rest
      )

let interp (src : string) : string list = 
  let output = parse (ws >> many(parseCommands)) src in
  match output with
  | Some (cmdList, []) -> evaluate [] [] cmdList
  | _ -> ["Error"]
(*parse automatically explodes the string to a -> char list*)

(*
  string -> char list -> [] -> simpler form -> eval -> results

  - need a working stack: https://www.cs.cornell.edu/courses/cs3110/2012sp/recitations/rec07.html
    - push
    - pop
  - trace() pops n elements in the stack and 
      adds there string representation to an output list.
  - add() pops n elements from the stack, adds there values, 
      and pushes the sum back on the stack.
  - sub() pops the top n elements from the stack and subtracts 
      the top element from the sum of the rest (n-1) elements.
  - mul() pops the top n elements from the stack and pushs their product.
  - div() pops the top n elements from the stack and divides 
      the top element from the product of the rest (n-1) elements.

      [-]               digit   {digit} 
      [might have it] has value {has zero or more values in addition}
*)

(*
  1. figure out what to output when the parser fails
  2. define different command types
  3. define different stack value types
  4. create parser for each command
    a. push
    b. pop
    c. add
    ...
  5. create parser for individual digits and characters
  6. create a parser that will parse a list of commands into a tuple list
    - after, all the commands into a list with just the commands.
  7. create an evaluation function (very last part)

*)

(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src