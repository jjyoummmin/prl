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

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
ADD (e1, e2) | SUB (e1,e2) | MUL (e1,e2) | DIV(e1,e2) -> (ty, TyInt) :: (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
|CONST n -> [(ty, TyInt)]
|VAR x -> [(ty, TEnv.find tenv x)]
|ISZERO e -> (ty, TyBool) :: (gen_equations tenv e TyInt)
|IF (e1,e2,e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
|READ -> []
|LET (x,e1,e2) -> let a = fresh_tyvar () in (gen_equations tenv e1 a) @ (gen_equations (TEnv.extend (x, a) tenv) e2 ty)
|PROC (x, e) -> let a1 = fresh_tyvar () in
                 let a2 = fresh_tyvar () in 
				 (ty, TyFun (a1, a2)) :: (gen_equations (TEnv.extend (x, a1) tenv) e a2)
|CALL (e1,e2) -> let a = fresh_tyvar () in 
                 (gen_equations tenv e1 (TyFun(a,ty))) @ (gen_equations tenv e2 a)
|LETREC (f,x,e1,e2) -> let a1 = fresh_tyvar ()  in 
                       let a2 = fresh_tyvar () in
                       let f_tenv = TEnv.extend ( f, TyFun (a1, a2) ) tenv in
                       (gen_equations (TEnv.extend (x, a1) f_tenv ) e1 a2 ) @ (gen_equations f_tenv e2 ty)
 					   

let rec occur : typ -> typ -> bool
= fun t1 t2 -> match t2 with
|TyFun (a,b) -> ((occur t1 a) || (occur t1 b))
| _ -> if t1 = t2 then true else false


			 
let rec unify :typ -> typ -> Subst.t -> Subst.t
= fun t1 t2 subst -> if (t1=t2) then subst else match t1 with
TyInt | TyBool -> (match t2 with 
                   |TyVar x-> (unify t2 t1 subst)
		           |_ -> raise TypeError)
| TyVar	x -> if (occur t1 t2) then raise TypeError else (Subst.extend x t2 subst) 
| TyFun (a,b) -> (match t2 with
                 | TyFun (c,d) -> let s1 = (unify a c  subst) in 
                                  let s2 = (unify (Subst.apply b s1) (Subst.apply d s1) s1) in s2
                 | _ -> (unify t2 t1 subst)	)							  

and unifyall : typ_eqn -> Subst.t -> Subst.t
= fun eqns subst -> match eqns with
| [] -> subst
| (t1,t2)::tl -> let s1 = (unify (Subst.apply t1 subst) (Subst.apply t2 subst) subst) in (unifyall tl s1)



and solve : typ_eqn -> Subst.t
=fun eqns -> (unifyall eqns Subst.empty)




let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;
  


(*확인*)
let pgm1 = PROC ("f",
PROC ("x", SUB (CALL (VAR "f", CONST 3),
CALL (VAR "f", VAR "x"))))in 
typeof(pgm1) ;;

let pgm2 = PROC ("f", CALL (VAR "f", CONST 11))in
typeof(pgm2) ;;

let pgm3 = LET ("x", CONST 1,
IF (VAR "x", SUB (VAR "x", CONST 1), CONST 0))in
typeof(pgm3) ;;