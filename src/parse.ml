open Syntax

type token = Lower of string | Upper of string | Int of string | Sym of char | Eof

type lexer = { src : string; file : string; mutable i : int; mutable line : int; mutable bol : int }

let pos lx = { file = lx.file; line = lx.line; col = lx.i - lx.bol + 1 }

let peekc lx k = if lx.i + k < String.length lx.src then Some lx.src.[lx.i + k] else None

let advance lx =
  if lx.src.[lx.i] = '\n' then begin
    lx.line <- lx.line + 1;
    lx.bol <- lx.i + 1
  end;
  lx.i <- lx.i + 1

let rec skip lx =
  match peekc lx 0 with
  | Some (' ' | '\t' | '\r' | '\n') ->
    advance lx;
    skip lx
  | Some '(' when peekc lx 1 = Some '*' ->
    let start = pos lx in
    advance lx;
    advance lx;
    let rec close depth =
      match peekc lx 0, peekc lx 1 with
      | None, _ -> error start "unterminated comment"
      | Some '*', Some ')' ->
        advance lx;
        advance lx;
        if depth > 1 then close (depth - 1)
      | Some '(', Some '*' ->
        advance lx;
        advance lx;
        close (depth + 1)
      | _ ->
        advance lx;
        close depth
    in
    close 1;
    skip lx
  | _ -> ()

let ident_char = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true | _ -> false

let take lx p =
  let start = lx.i in
  while match peekc lx 0 with Some c -> p c | None -> false do
    advance lx
  done;
  String.sub lx.src start (lx.i - start)

let next lx =
  skip lx;
  let at = pos lx in
  let tok =
    match peekc lx 0 with
    | None -> Eof
    | Some ('a' .. 'z' | '_') -> Lower (take lx ident_char)
    | Some 'A' .. 'Z' -> Upper (take lx ident_char)
    | Some '0' .. '9' -> Int (take lx ident_char)
    | Some (('=' | '|' | '{' | '}' | ':' | ';' | '(' | ')') as c) ->
      advance lx;
      Sym c
    | Some c -> error at "unexpected character %C" c
  in
  { it = tok; at }

type state = { lx : lexer; mutable tok : token located }

let shift st = st.tok <- next st.lx

let show = function
  | Lower s | Upper s | Int s -> Printf.sprintf "'%s'" s
  | Sym c -> Printf.sprintf "'%c'" c
  | Eof -> "end of file"

let fail st expected = error st.tok.at "expected %s but found %s" expected (show st.tok.it)

let sym st c = if st.tok.it = Sym c then shift st else fail st (Printf.sprintf "'%c'" c)

let keyword st k = if st.tok.it = Lower k then shift st else fail st (Printf.sprintf "'%s'" k)

let lower st what =
  match st.tok with
  | { it = Lower s; at } ->
    shift st;
    { it = s; at }
  | _ -> fail st what

let count st =
  match st.tok with
  | { it = Int s; at } ->
    shift st;
    let n =
      match int_of_string_opt s with
      | Some n when String.for_all (function '0' .. '9' -> true | _ -> false) s -> n
      | _ -> error at "binder count %s is not a representable natural number" s
    in
    { it = n; at }
  | _ -> fail st "a binder count"

let base st =
  let container =
    match st.tok.it with
    | Lower ("list" | "option" as c) ->
      shift st;
      if st.tok.it <> Sym '(' then fail st "'(' after a container";
      Some (if c = "list" then `List else `Option)
    | _ -> None
  in
  match container with
  | None -> { sort = lower st "a sort"; container = `One }
  | Some container ->
    sym st '(';
    let sort = lower st "a sort" in
    sym st ')';
    { sort; container }

let field st =
  let label = lower st "a field name" in
  sym st ':';
  let bind =
    if st.tok.it = Lower "bind" then begin
      shift st;
      let k = count st in
      keyword st "in";
      Some k
    end
    else None
  in
  { label; bind; base = base st }

let ctor st =
  match st.tok with
  | { it = Upper name; at } ->
    shift st;
    let cname = { it = name; at } in
    if st.tok.it = Lower "of" then begin
      shift st;
      match st.tok.it with
      | Lower "index" ->
        shift st;
        { cname; body = Index }
      | Sym '{' ->
        shift st;
        let rec fields acc =
          if st.tok.it = Sym '}' then List.rev acc
          else
            let f = field st in
            if st.tok.it = Sym ';' then begin
              shift st;
              fields (f :: acc)
            end
            else List.rev (f :: acc)
        in
        let fs = fields [] in
        if fs = [] then error st.tok.at "constructor %s has an empty field list" name;
        sym st '}';
        { cname; body = Fields fs }
      | _ -> fail st "'index' or '{'"
    end
    else { cname; body = Nullary }
  | _ -> fail st "a constructor name"

let decl st =
  let name = lower st "a sort name" in
  sym st '=';
  if st.tok.it = Sym '|' then shift st;
  let rec ctors acc =
    let c = ctor st in
    if st.tok.it = Sym '|' then begin
      shift st;
      ctors (c :: acc)
    end
    else List.rev (c :: acc)
  in
  { name; ctors = ctors [] }

let schema ~file src =
  let lx = { src; file; i = 0; line = 1; bol = 0 } in
  let st = { lx; tok = { it = Eof; at = pos lx } } in
  shift st;
  let rec groups acc =
    match st.tok.it with
    | Eof -> List.rev acc
    | Lower "type" ->
      shift st;
      let rec decls acc =
        let d = decl st in
        if st.tok.it = Lower "and" then begin
          shift st;
          decls (d :: acc)
        end
        else d :: acc
      in
      groups (decls acc)
    | _ -> fail st "'type'"
  in
  let ds = groups [] in
  if ds = [] then error st.tok.at "schema declares no sorts";
  ds
