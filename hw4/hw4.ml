type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(************************************)
(*      List utility functions      *)
(************************************)
let rec list_length : 'a list -> int
= fun lst ->
  match lst with
  | [] -> 0
  | hd::tl -> 1 + list_length tl

(*list에 원하는 조건의 원소가 존재하는가 판단하는 함수*)
let rec list_exists : ('a -> bool) -> 'a list -> bool
= fun pred lst ->
  match lst with 
  | [] -> false 
  | hd::tl -> if (pred hd) then true else list_exists pred tl

let rec list_fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
= fun func acc lst1 lst2 ->
  match (lst1, lst2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func (func acc hd1 hd2) tl1 tl2
  | _ -> raise (Failure "list_fold2 : two lists have different length")

(*fold_left*)
let rec list_fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold func (func acc hd) tl
  
  
  
let rec list_fold3 : ('a -> 'a list-> 'a list) -> 'a list -> 'a list -> 'a list
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold3 func (func hd acc) tl

(********************************)
(*     Handling environment     *)
(********************************)
let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if (x = id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if (x = id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)
let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc, v)::tl -> if (l = loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

let size_of_mem mem = 
  let add_if_new x l = if list_exists (fun y -> x = y) l then l else x::l in
  let dom = list_fold (fun dom loc -> add_if_new loc dom) [] mem  in
    list_length dom


(*기존 memory domain(혹은 record) 에 없는 새로운 random location int 생성하기*)
let rec new_loc = fun lst -> let a = Random.int 100000 in
                              if (list_exists (fun x-> match x with |(l,_)-> l= a) lst)then new_loc lst            
                              else a
							  
(***************************)
(*     Handling record     *)
(***************************)
let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
  | [] -> raise(Failure ("field "^ id ^" is not included in record"))
  | (x, l)::tl -> if (id = x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(******************)
(* Pretty printer *)
(******************)
let rec value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record r -> "{" ^ record2str r ^ "}" 

and record2str : record -> string
= fun record ->
  match record with
  | [] -> ""
  | [(x, l)] -> x ^ "->" ^ string_of_int l
  | (x, l)::tl-> x ^ "->" ^ string_of_int l ^ ", " ^ record2str tl

let mem2str : memory -> string
= fun mem -> 
  let rec aux mem =
    match mem with
    | [] -> ""
    | [(l, v)] -> string_of_int l ^ "->" ^ value2str v
    | (l, v)::tl -> string_of_int l ^ "->" ^ value2str v ^ ", " ^ aux tl
  in
  "[" ^ aux mem ^ "]"

let rec env2str : env -> string
= fun env -> 
  let rec aux env =
    match env with
    | [] -> ""
    | [binding] -> binding2str binding
    | binding::tl -> binding2str binding ^ ", " ^ aux tl
  in
  "[" ^ aux env ^ "]"

and binding2str : binding -> string
= fun binding ->
  match binding with
  | LocBind (x, l) -> x ^ "->" ^ string_of_int l
  | ProcBind (x, proc) -> x ^ "->" ^ "(" ^ proc2str proc ^ ")"

and proc2str : proc -> string
= fun (xs, e, env) ->  
  let rec args2str xs =
    match xs with
    | [] -> ""
    | [x] -> x
    | x::tl -> x ^ ", " ^ args2str tl
  in
  "(" ^ args2str xs ^ ")" ^ ", E" ^ ", " ^ env2str env

(***************************)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented;;
exception UndefinedSemantics;;

(*사칙연산 eval 할때 간단하게 하는용*)
let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")


and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  let mem = gc env mem in
  print_endline("env"^env2str env) ;
  print_endline("mem"^mem2str mem) ; 
 
  match e with
  | WRITE e ->   (*value v를 print하고 (v,mem)을 반환함*)
    let (v1, mem1) = eval env mem e in
    let _ = print_endline (value2str v1) in
    (v1, mem1)
  | NUM n -> (Num n, mem)
  | UNIT -> (Unit, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | VAR x -> let loc1 = lookup_loc_env x env in
             let v1 =  lookup_mem loc1 mem in
			 (v1, mem)
			 
  | ADD (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x+y)   
  | SUB (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x-y) 
  | MUL (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x*y) 
  | DIV (e1, e2) -> eval_aop env mem e1 e2 (fun x y -> x/y) 
  | EQUAL (e1, e2) ->  (let (v1, mem1) = eval env mem e1 in
                       let (v2, mem2) = eval env mem1 e2 in
					   match (v1,v2) with
					    |(Num n1, Num n2) -> if (n1=n2) then (Bool true, mem2) else (Bool false, mem2)
						|(Bool b1, Bool b2) -> if (b1=b2) then (Bool true, mem2) else (Bool false, mem2)
						| (Unit, Unit) -> (Bool true, mem2)
						| _ -> raise (Failure "value type does not match in EQUAL step"))
						
  | LESS (e1, e2) -> (let (v1, mem1) = eval env mem e1 in
                       let (v2, mem2) = eval env mem1 e2 in
					   match (v1,v2) with
					    |(Num n1, Num n2) -> (Bool (n1 <n2), mem2)
						| _ -> raise (Failure "value type does not match in LESS step"))

 | NOT e -> let (v1, mem1) = eval env mem e in
            (match v1 with
            | Bool b -> (Bool (not b), mem1)
            |_ -> raise (Failure "the value type is not Bool"))
			
 | SEQ (e1,e2) -> let (v1, mem1) = eval env mem e1 in eval env mem1 e2 
 | IF (e1, e2, e3) -> let (v1, mem1) = eval env mem e1 in
                      (match v1 with
					  |Bool b -> if b then eval env mem1 e2 else eval env mem1 e3
					  |_ -> raise (Failure "Type error in IF step"))
					  
					  
 | WHILE (e1, e2) -> let (v1, mem1) =  eval env mem e1 in
                     (match v1 with
                     |Bool b -> if (not b) then (Unit, mem1) else 
					  let (v2, mem2) = eval env mem1 e2 in eval env mem2 (WHILE (e1, e2))		
                     |_ -> raise (Failure "Type error in WHILE step"))					  
  
 | LETV (x,e1,e2) -> let (v1, mem1) = eval env mem e1 in 
                     let l = new_loc mem1 in eval (extend_env (LocBind (x,l)) env) (extend_mem (l, v1) mem1) e2
 | LETF (f, lst, e1, e2) -> eval (extend_env (ProcBind (f, (lst, e1, env)))  env) mem e2
 
 | CALLV (f, lst) -> let (id_lst, body, call_env) = lookup_proc_env f env in
                     let (final_env, final_mem, mem_n) = final id_lst lst env mem (ProcBind(f,lookup_proc_env f env)::call_env) [] in
					 eval final_env (final_mem@mem_n) body  
 
 | CALLR (f, lst) -> let (id_lst, body, call_env) = lookup_proc_env f env in
                     let final_env = final_env_r id_lst lst env (ProcBind(f,lookup_proc_env f env)::call_env) in
                     eval final_env mem body                   

 | ASSIGN (x, e) -> let (v1, mem1) = eval env mem e in 
                    let l = lookup_loc_env x env in (v1, extend_mem (l, v1) mem1)

 | RECORD lst -> if lst=[] then (Unit, mem) else
                 let (a,b,mem_n) = (record_ lst env mem [] []) in (Record a, b@mem_n)
 | FIELD (e,x) -> let (v1, mem1) = eval env mem e in (match v1 with
                  |Record r -> let l = (lookup_record x r) in ((lookup_mem l mem1), mem1)
				  |_ -> raise (Failure "type Error"))
				  
 | ASSIGNF (e1,x,e2) -> let (v1,mem1) = eval env mem e1 in
                        let (v2, mem2) = eval env mem1 e2 in
                        match v1 with
                        | Record r -> let l = (lookup_record x r) in (v2, extend_mem (l,v2) mem2)		
                        | _ -> raise (Failure "type Error")						
  
                   
 | _ -> raise NotImplemented 




and record_ 
= fun lst env mem a b->
 match lst with
 |[] -> (a,b,mem)
 |(x,e)::tl -> let (v1,mem1) = eval env mem e in
               let l = new_loc mem1 in
			   (record_ tl env mem1 ((x,l)::a) ((l,v1)::b))
			   

and final_env_r
 = fun id_lst lst env a ->
                 match (id_lst, lst) with
					 |([],[])-> a
					 |(hd1::tl1, hd2::tl2) -> let l = (lookup_loc_env hd2 env) in (final_env_r tl1 tl2 env (LocBind(hd1, l)::a))
                     |_ -> raise(Failure "number of argument not match")
 

and final 
= fun id_lst lst env mem a b ->
				match (id_lst, lst) with
					 |([],[])-> (a,b,mem)
					 |(hd1::tl1, hd2::tl2) ->let (v,mem1) = eval env mem hd2 in
					                         let l = new_loc mem1 in 
					                         
											 final tl1 tl2 env mem1 (LocBind(hd1, l)::a) ((l,v)::b)	 
                     |_ -> raise(Failure "number of argument not match")											 
  


and reach 
= fun env mem a-> match env with
|[] -> a
|LocBind(x, l)::tl -> let v1 = (lookup_mem l mem) in (match v1 with
                                                     |Record r -> (reach tl mem (add_if_new_list (r_reach r mem [(l,v1)] ) a) )
                                                     |_ -> (reach tl mem (add_if_new (l, v1) a) ) )
|ProcBind(f, (lst, body, call_env))::tl -> let temp_mem = (reach call_env mem []) in 
                                           (reach tl mem (add_if_new_list temp_mem a) )


and add_if_new =
fun x l -> if list_exists (fun y -> x = y) l then l else x::l 

and r_reach =
fun lst mem a -> match lst with
                 | [] -> a
                 |(x,l)::tl -> let v1 =(lookup_mem l mem) in (r_reach tl mem ((l, v1)::a) )
				 
and add_if_new_list l1 l2 = list_fold3 (add_if_new) l2 l1 


and gc : env -> memory -> memory
= fun env mem -> reach env mem [] 

let runb : exp -> value 
= fun exp ->
  let (v, m) = eval empty_env empty_mem exp in
  let _ = print_endline ("memory size: " ^ string_of_int (size_of_mem m)) in
    v;;




let pg3 = LETV ("f", RECORD ([("x", NUM 10); ("y", NUM 13)]),
LETF ("swap", ["a"; "b"],
LETV ("temp", VAR "a",
SEQ (
ASSIGN ("a", VAR "b"),
ASSIGN ("b", VAR "temp"))),
SEQ (
CALLV("swap", [FIELD (VAR "f", "x"); FIELD (VAR "f", "y")]),
FIELD (VAR "f", "x")
)
)
)


in print_endline(value2str (runb pg3)) ;;








