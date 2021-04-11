type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string





let rec replace : var -> exp -> exp -> exp
= fun x e1 e2 -> match e2 with
|VAR y -> if (x=y) then e1 else e2
|CONST n -> e2
|ADD (e3, e4) -> ADD (replace x e1 e3, replace x e1 e4)
|SUB (e3, e4) -> SUB (replace x e1 e3, replace x e1 e4)
|MUL (e3, e4) -> MUL (replace x e1 e3, replace x e1 e4)
|DIV (e3, e4) -> DIV (replace x e1 e3, replace x e1 e4)
|ISZERO e -> ISZERO (replace x e1 e)
|READ -> READ
|IF (e3, e4, e5) -> IF (replace x e1 e3, replace x e1 e4, replace x e1 e5)
|LET (y, e3, e4) -> LET (x, replace x e1 e3, replace x e1 e4)
|CALL (e3, e4) -> CALL (replace x e1 e3, replace x e1 e4)
|PROC (y,e3) -> PROC (y, replace x e1 e3)
|_ -> e2


let rec check : var -> exp -> bool->bool
= fun x e a -> match e with
ADD (e1, e2) |SUB (e1,e2) |MUL(e1,e2) |DIV(e1,e2) -> (check x e1 a) || (check x e2 a) 
|CONST n -> a
|VAR y -> if (y=x) then true else a
|ISZERO e1 -> check x e1 a
|READ -> a
|IF (e1,e2, e3 ) -> (check x e1 a) || (check x e2 a) || (check x e3 a)
|LET(y,e1,e2) -> (check x e1 a) ||(check x e2 a)
|LETREC (f,y, e1,e2) -> (check x e1 a) ||(check x e2 a)
|PROC (y,e1) -> (check x e1 a)
|CALL (e1, e2) -> (check x e1 a) ||(check x e2 a)

let rec expand : exp -> exp 
=fun e -> match e with
|LET (x,e1,e2) -> if (check x e2 false) then replace x e1 e2 else e
|ADD (e1,e2) -> ADD (expand e1, expand e2)
|SUB (e1,e2) -> SUB (expand e1, expand e2)
|MUL (e1,e2) -> MUL (expand e1, expand e2)
|DIV (e1,e2) -> DIV (expand e1, expand e2)
|ISZERO e -> ISZERO (expand e)
|IF (e1,e2,e3) -> IF (expand e1, expand e2, expand e3)
|PROC (x, e) -> PROC (x, expand e)
|CALL (e1,e2) -> CALL (expand e1, expand e2)
|_ -> e;;



(*확인하려고 만든 함수*)
let rec pgm2str : exp -> string 
= fun v -> match v with
|CONST n -> "CONST " ^ string_of_int n
|VAR x -> "VAR " ^ x
|ADD (e1,e2) -> "ADD ("^ (pgm2str e1)^","^(pgm2str e2)^")"
|SUB (e1,e2) -> "SUB ("^ (pgm2str e1)^","^(pgm2str e2)^")"
|MUL (e1,e2) -> "MUL ("^ (pgm2str e1)^","^(pgm2str e2)^")"
|DIV (e1,e2) -> "DIV ("^ (pgm2str e1)^","^(pgm2str e2)^")"
|ISZERO e -> "ISZERO ("^ (pgm2str e) ^")"
|READ -> "READ"
|IF (e1,e2,e3) -> "IF ("^(pgm2str e1)^ "," ^(pgm2str e2)^"," ^(pgm2str e3)^")"
|LET (x,e1,e2) -> "LET ("^ x ^ "," ^(pgm2str e1)^"," ^(pgm2str e2)^")"
|LETREC (f,x,e1,e2) -> "LETREC ("^f ^","^ x^","^ (pgm2str e1)^","^ (pgm2str e2)^")"
|PROC (x, e) -> "PROC ("^ x^","^ (pgm2str e)^")"
|CALL (e1,e2) -> "CALL ("^ (pgm2str e1)^","^(pgm2str e2)^")";;


let x = expand (CALL( PROC ( "y" , ADD( VAR "y" , LET ("x", CONST 3, ADD( CONST 3, VAR "x")))), CONST 5) ) in
let y = expand ( ADD(CONST 3, 
LET ("f", PROC ("x", VAR "x"),
IF (CALL (VAR "f", ISZERO (CONST 0)),
CALL (VAR "f", CONST 11),
CALL (VAR "f", CONST 22))))) in 
let pgm1 = expand (LET ("x", CONST 1, VAR "x")) in
let pgm2 =  expand (
LET ("f", PROC ("x", VAR "x"),
IF (CALL (VAR "f", ISZERO (CONST 0)),
CALL (VAR "f", CONST 11),
CALL (VAR "f", CONST 22)))) in
let pgm3 = expand (LET ("x", ADD (CONST 1, ISZERO (CONST 0)), CONST 2)) in
(print_endline (pgm2str x)); (print_endline (pgm2str y)) ;(print_endline (pgm2str pgm1)); (print_endline (pgm2str pgm2));(print_endline (pgm2str pgm3));;