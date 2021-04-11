type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var 
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp 
  | EQUAL of exp * exp
  | LESS of exp * exp  
  | NOT of exp
  | NIL  
  | ISNIL of exp 
  | CONS of exp * exp 
  | APPEND of exp * exp  
  | HEAD of exp  
  | TAIL of exp
  | PRINT of exp  
  | SEQ of exp * exp  
  | IF of exp * exp * exp  
  | LET of var * exp * exp  
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp  
  | CALL of exp * exp  
and var = string

  
type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env  
  | MRecProcedure of var * var * var * exp * env  
and env = (var * value) list  

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl


let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ List.fold_left (fun s x -> (if s = "" then x else s ^ ", " ^ x)) "" (List.map string_of_value lst) ^ "]"
  | Unit -> ""
  | _ -> "(functional value)"  

exception UndefinedSemantics



let rec eval : exp -> env -> value
=fun exp env ->
  match exp with 
  | UNIT -> Unit
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST n -> Int n
  | VAR x -> lookup_env x env
  | ADD (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> Int (n1+n2)
					 | _ -> raise (Failure ("Type Error")))
  | SUB (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> Int (n1-n2)
					 | _ -> raise (Failure ("Type Error")))
  | MUL (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> Int (n1*n2)
					 | _ -> raise (Failure ("Type Error")))
  | DIV (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> Int (n1/n2)
					 | _ -> raise (Failure ("Type Error")))
  | EQUAL (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> if (n1=n2) then Bool true else Bool false
					 | _ -> raise (Failure ("Type Error")))
  | LESS (e1, e2) ->  let v1 = eval e1 env in 
                     let v2 = eval e2 env in
					 (match v1,v2 with
					 | Int n1, Int n2 -> if (n1<n2) then Bool true else Bool false
					 | _ -> raise (Failure ("Type Error")))                        
  | NOT e -> let v = eval e env in
             (match v with
              | Bool b -> Bool (not b)
              | _ -> raise (Failure ("Type Error")))
  | NIL -> List []			
  | ISNIL e -> let v = eval e env in 
               if v = (List []) then Bool true else Bool false 
  | CONS (e1,e2) -> ( match (eval e2 env )with 
                    | List v -> List ((eval e1 env)::v)
                    | _ -> raise (Failure ("Type Error")))	
  | APPEND (e1, e2) -> let v1 = eval e1 env in 
                       let v2 = eval e2 env in
                       (match v1, v2 with 
                       |List lst1 , List lst2 -> List (lst1@lst2)
                       |_ -> raise (Failure ("Type Error")))					   
  | HEAD e -> ( match (eval e env) with
               | List (hd::tl) -> hd
               | _ -> raise (Failure ("Type Error")))		   
  | TAIL e -> ( match (eval e env) with
               | List (hd::tl) -> List tl
               | _ -> raise (Failure ("Type Error")))
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | SEQ (e1, e2) -> ((eval e1 env) ; (eval e2 env)) 
  | IF (e1,e2,e3) -> ( match (eval e1 env) with
                     |Bool true -> (eval e2 env)
					 |Bool false -> (eval e3 env)
					 |_ -> raise(Failure("Type Error")))
  | LET(x,e1,e2) -> eval e2 (extend_env (x,eval e1 env)  env)	
  | PROC (x,e) -> Procedure (x,e,env)  
  | CALL (e1,e2) -> let v = (eval e1 env) in 
                    (match v with
                    |Procedure (x,e,env1) -> (eval e (extend_env (x,eval e2 env) env1))
                    |RecProcedure (f,x,e,env1) -> (eval e (extend_env (x,eval e2 env) (extend_env (f,v) env1)))	
                    |MRecProcedure (f,g,x,e,env1) -> (eval e  (extend_env (g, (lookup_env g env)) (extend_env (f, v) (extend_env (x,eval e2 env) env1))) )					
					|_ -> raise (Failure("Type Error")))
  | LETREC (f,x,e1,e2) -> eval e2 (extend_env(f, RecProcedure(f,x,e1,env)) env)				
  | LETMREC ((f,x,e1),(g,y,e2),e3) -> eval e3 (extend_env (f,MRecProcedure(f,g,x,e1,env)) (extend_env (g,MRecProcedure(g,f,y,e2,env)) env) )
  
let runml : program -> value
=fun pgm -> eval pgm empty_env			   
			   
(*//////////////////////////*)			   

let exam1 = LET ("x", CONST 1,
LET ("f", PROC ("y", ADD (VAR "x", VAR "y")),
LET ("x", CONST 2,
LET ("g", PROC ("y", ADD (VAR "x", VAR "y")),
ADD (CALL (VAR "f", CONST 1), CALL (VAR "g", CONST 1))))));;

let exam2 = LETREC ("double", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 0,
ADD (CALL (VAR "double", SUB (VAR "x", CONST 1)), CONST 2)),
CALL (VAR "double", CONST 6));;

let exam3 = LETMREC
(("even", "x",
IF (EQUAL (VAR "x", CONST 0), TRUE,
CALL (VAR "odd", SUB (VAR "x", CONST 1)))),
("odd", "x",
IF (EQUAL (VAR "x", CONST 0), FALSE,
CALL (VAR "even", SUB (VAR "x", CONST 1)))),
CALL (VAR "odd", CONST 13));;

let exam4 = LETREC ("factorial", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 1,
MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")),
LETREC ("loop", "n",
IF (EQUAL (VAR "n", CONST 0), UNIT,
SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
CALL (VAR "loop", CONST 10)));;

let exam5 = LETREC ("range", "n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1)))),
CALL (VAR "range", CONST 10));;

let exam6 = LETREC ("reverse", "l",
IF (ISNIL (VAR "l"), NIL,
APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
CALL (VAR "reverse", CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL)))));;

let exam7 = LET ("fix",
PROC ("f",
CALL
(PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
LET ("f",
CALL (VAR "fix",
PROC ("f",
PROC ("x",
IF (EQUAL (VAR "x", CONST 0), CONST 1,
MUL (CALL (VAR "f", SUB (VAR "x", CONST 1)), VAR "x"))))),
CALL (VAR "f", CONST 10)));;

let exam7_2 = LET ("fix",
PROC ("f",
CALL
(PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
LET ("f",
CALL (VAR "fix",
PROC ("range",
PROC ("n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1))))))),
CALL (VAR "f", CONST 10)));;





print_endline (string_of_value (runml exam4));;
