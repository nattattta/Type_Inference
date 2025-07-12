
type expr =
  | Var of string
  | Abs of string * expr
  | App of expr * expr
  | Let of string * expr * expr
  | Int of int
  | Bool of bool


type ty =
  | TVar of string
  | TArrow of ty * ty

type scheme =
  | Mono of ty
  | Forall of string list * ty

type env = (string * scheme) list

let is_reserved_type x = x = "int" || x = "bool"

let fresh_tyvar =
  let counter = ref 0 in
  fun () -> incr counter; "t" ^ string_of_int !counter

let rec ftv_ty = function
  | TVar x -> [x]
  | TArrow (t1, t2) -> List.concat [ftv_ty t1; ftv_ty t2]

let ftv_scheme = function
  | Mono t -> ftv_ty t
  | Forall (vars, t) -> List.filter (fun v -> not (List.mem v vars)) (ftv_ty t)

let ftv_env env =
  List.flatten (List.map (fun (_, s) -> ftv_scheme s) env)

let remove_assoc_many keys assoc =
  List.filter (fun (k, _) -> not (List.mem k keys)) assoc

module Subst = struct
  type t = (string * ty) list

  let empty = []

  let rec apply s = function
    | TVar x -> (try List.assoc x s with Not_found -> TVar x)
    | TArrow (t1, t2) -> TArrow (apply s t1, apply s t2)

  let apply_scheme s = function
    | Mono t -> Mono (apply s t)
    | Forall (vars, t) ->
        let s' = remove_assoc_many vars s in
        Forall (vars, apply s' t)

  let apply_env s env =
    List.map (fun (x, sch) -> (x, apply_scheme s sch)) env

  let compose s1 s2 =
    let s2' = List.map (fun (v, t) -> (v, apply s1 t)) s2 in
    s2' @ s1
end

let generalize env t =
  let env_fvs = ftv_env env in
  let t_fvs = ftv_ty t in
  let vars = List.filter (fun v -> not (List.mem v env_fvs) && not (is_reserved_type v)) t_fvs in
  Forall (vars, t)

let instantiate = function
  | Mono t -> t
  | Forall (vars, t) ->
      let subst = List.map (fun v -> (v, TVar (fresh_tyvar ()))) vars in
      Subst.apply subst t

exception TypeError of string

let rec occurs x = function
  | TVar y -> x = y
  | TArrow (t1, t2) -> occurs x t1 || occurs x t2

let rec string_of_ty_debug = function
  | TVar x -> "TVar \"" ^ x ^ "\""
  | TArrow (t1, t2) ->
      "TArrow (" ^ string_of_ty_debug t1 ^ ", " ^ string_of_ty_debug t2 ^ ")"

let rec unify t1 t2 =
  match t1, t2 with
  | t1', t2' when t1' = t2' -> Subst.empty
  | TVar x, TVar y ->
      let x_is_reserved = is_reserved_type x in
      let y_is_reserved = is_reserved_type y in

      if x_is_reserved && y_is_reserved then
        raise (TypeError ("Cannot unify distinct concrete types " ^ x ^ " and " ^ y))
      else if x_is_reserved then
        [(y, TVar x)]
      else if y_is_reserved then
        [(x, TVar y)]
      else
        if occurs x (TVar y) then
          raise (TypeError ("Occurs check failed: " ^ x ^ " in " ^ y))
        else
          [(x, TVar y)]
  | TVar x, t ->
      if is_reserved_type x then
        raise (TypeError ("Cannot unify concrete type " ^ x ^ " with " ^ string_of_ty_debug t))
      else if occurs x t then
        raise (TypeError ("Occurs check failed: " ^ x ^ " in " ^ string_of_ty_debug t))
      else
        [(x, t)]
  | t, TVar x ->
      if is_reserved_type x then
        raise (TypeError ("Cannot unify " ^ string_of_ty_debug t ^ " with concrete type " ^ x))
      else
        unify (TVar x) t
  | TArrow (a1, b1), TArrow (a2, b2) ->
      let s1 = unify a1 a2 in
      let s2 = unify (Subst.apply s1 b1) (Subst.apply s1 b2) in
      Subst.compose s2 s1
  | _ -> raise (TypeError ("Unification failed between " ^ string_of_ty_debug t1 ^ " and " ^ string_of_ty_debug t2))

  let lookup env x =
  try instantiate (List.assoc x env)
  with Not_found -> raise (TypeError ("Unbound variable: " ^ x))

let rec infer env expr =
  match expr with
  | Var x ->
      (Subst.empty, lookup env x)

  | Int _ -> (Subst.empty, TVar "int")

  | Bool _ -> (Subst.empty, TVar "bool")

  | Abs (x, e) ->
      let tv = TVar (fresh_tyvar ()) in
      let env' = (x, Mono tv) :: env in
      let s1, t1 = infer env' e in
      (s1, TArrow (Subst.apply s1 tv, t1))

  | App (e1, e2) ->
      let s1, t1 = infer env e1 in
      let s2, t2 = infer (Subst.apply_env s1 env) e2 in
      let tv = TVar (fresh_tyvar ()) in
      let s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv)) in
      let s = Subst.compose s3 (Subst.compose s2 s1) in
      (s, Subst.apply s tv)

  | Let (x, e1, e2) ->
      let s1, t1 = infer env e1 in
      let t1_gen = generalize (Subst.apply_env s1 env) 
      (Subst.apply s1 t1) in
      let env' = (x, t1_gen) :: env in
      let s2, t2 = infer (Subst.apply_env s1 env') e2 in
      (Subst.compose s2 s1, t2)

let show_ty ty =
  let counter = ref 0 in
  let names = Hashtbl.create 10 in
  let rec show = function
    | TVar x when is_reserved_type x -> x
    | TVar x ->
        if Hashtbl.mem names x then Hashtbl.find names x
        else let name = "'" ^ String.make 1 (char_of_int (97 + !counter)) in
             incr counter;
             Hashtbl.add names x name;
             name
    | TArrow (t1, t2) -> "(" ^ show t1 ^ " -> " ^ show t2 ^ ")"
  in
  show ty


type token =
  | IDENT of string
  | ARROW
  | FUN
  | LET
  | IN
  | LPAREN
  | RPAREN
  | EQ
  | INT_LIT of int
  | BOOL_LIT of bool

let explode str =
  let rec aux i acc =
    if i < 0 then acc else aux (i - 1) (str.[i] :: acc)
  in aux (String.length str - 1) []

let is_digit c = c >= '0' && c <= '9'
let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'


exception ParseError of string


let lex chars =
  let skip = function ' ' | '\n' | '\t' | '\r' -> true | _ -> false in
  let rec tokenize acc = function
    | [] -> List.rev acc
    | '(' :: rest -> tokenize (LPAREN :: acc) rest
    | ')' :: rest -> tokenize (RPAREN :: acc) rest
    | '=' :: rest -> tokenize (EQ :: acc) rest
    | '-' :: '>' :: rest -> tokenize (ARROW :: acc) rest
    | c :: cs when skip c -> tokenize acc cs
    | c :: cs when is_letter c ->
        let rec take ident = function
          | x :: xs when is_letter x || is_digit x -> take (x :: ident) xs
          | rest -> (List.rev ident, rest)
        in
        let ident, rest = take [c] cs in
        let str = String.of_seq (List.to_seq ident) in
        let token =
          match str with
          | "fun" -> FUN
          | "let" -> LET
          | "in" -> IN
          | "true" -> BOOL_LIT true
          | "false" -> BOOL_LIT false
          | _ -> IDENT str
        in
        tokenize (token :: acc) rest
    | c :: cs when is_digit c ->
        let rec take_digits d = function
          | x :: xs when is_digit x -> take_digits (x :: d) xs
          | rest -> (List.rev d, rest)
        in
        let digits, rest = take_digits [c] cs in
        let str = String.of_seq (List.to_seq digits) in
        tokenize (INT_LIT (int_of_string str) :: acc) rest
    | c :: cs -> raise (ParseError ("Unexpected character: " ^ String.make 1 c))
  in tokenize [] chars

let tokenize str = lex (explode str)

let rec parse_expr tokens =
  parse_let tokens

and parse_let tokens =
  match tokens with
  | LET :: IDENT name :: EQ :: rest ->
      let e1, rem1 = parse_expr rest in
      (match rem1 with
       | IN :: rem2 ->
           let e2, rem3 = parse_expr rem2 in
           (Let (name, e1, e2), rem3)
       | _ -> raise (ParseError "Expected 'in' after let binding"))
  | _ -> parse_fun tokens

and parse_fun tokens =
  match tokens with
  | FUN :: IDENT x :: ARROW :: rest ->
      let body, rem = parse_expr rest in
      (Abs (x, body), rem)
  | _ -> parse_app tokens

and parse_app tokens =
  let e1, rem1 = parse_atom tokens in
  let rec apply_loop current_expr rem_tokens =
    match parse_atom rem_tokens with
    | e2, rem2 -> apply_loop (App (current_expr, e2)) rem2
    | exception (ParseError _) -> (current_expr, rem_tokens)
  in
  apply_loop e1 rem1

and parse_atom tokens =
  match tokens with
  | INT_LIT i :: rest -> (Int i, rest)
  | BOOL_LIT b :: rest -> (Bool b, rest)
  | IDENT x :: rest -> (Var x, rest)
  | LPAREN :: rest ->
      let e, rem = parse_expr rest in
      (match rem with
       | RPAREN :: rem' -> (e, rem')
       | _ -> raise (ParseError "Expected ')' after parenthesized expression"))
  | _ -> raise (ParseError "Expected an atomic expression (variable, literal, or parenthesized expression)")

let parse s =
  let tokens = tokenize s in
  let expr, rest = parse_expr tokens in
  match rest with
  | [] -> expr
  | _ -> raise (ParseError ("Unexpected tokens at end: " ^ (String.concat " " (List.map (fun t -> match t with IDENT s -> s | ARROW -> "->" | FUN -> "fun" | LET -> "let" | IN -> "in" | LPAREN -> "(" | RPAREN -> ")" | EQ -> "=" | INT_LIT i -> string_of_int i | BOOL_LIT b -> string_of_bool b) rest))))


let infer_string_expr env s =
  let ast = parse s in
  let subst, ty = infer env ast in
  let final_ty = Subst.apply subst ty in
  show_ty final_ty

let test expr env =
  try
    let ty = infer_string_expr env expr in
    Printf.printf "✓ %s  ⇒  %s\n" expr ty
  with TypeError msg ->
    Printf.printf "✗ %s  ⇒  Type error: %s\n" expr msg

let () =
  test "fun x -> 5" [];
  test "fun x -> x" [];
  test "fun x -> fun y -> x" [];
  test "let id = fun x -> x in id" [];
  test "let id = fun x -> x in id 5" [];
  test "let flip = fun f -> fun x -> fun y -> f y x in flip" [];
  test "let id = fun x -> x in let a = id 5 in id true"
    [];
  test "let const = fun x -> fun y -> x in let a = const 1 true in const"
    [];
  test "let a = fun x -> x in let b = fun y -> y in a" [];
  test "let id = fun x -> x in id (id (id 5))" [];
  test "x" [];
  test "let f = fun x -> x in f f" [];
  test "fun x -> let y = x in y" [];


  (*you can run this file directly in ocaml online compiler*)




