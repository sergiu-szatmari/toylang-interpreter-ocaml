(* ============================== ToyLang Abstract Syntax Tree ============================== *)
(* ==============================             (AST)            ============================== *)

type tPrim = Tint | Tbool | Tvoid;;
type typ = Tprim of tPrim | Tbot | Taddr of typ;;
type paramList = (typ * string) list;;

type value = Vnull 
  | Vaddr of int 
  | Vint of int  
  | Vbool of bool
  | Vvoid;;      

type exp = Eval of value
  | Evar of string
  | Ederef of string
  | Eassignvar of string * exp
  | Eassignloc of string * exp
  | Eret of string * exp
  | Eblk of typ * string * exp
  | Eseq of exp * exp
  | Eif of exp * exp * exp
  | Eplus of exp * exp 
  | Eminus of exp * exp 
  | Estar of exp * exp 
  | Ediv of exp * exp 
  | Eless of exp * exp 
  | Eeq of exp * exp 
  | Egreater of exp * exp 
  | Eneq of exp * exp 
  | Eand of exp * exp 
  | Eor of exp * exp
  | Enot of exp
  | Eprint of exp
  | Enew of typ (* string*)
  | Efcall of string * (string list)
  | Ewhile of exp * exp
  | Edelete of string;;

type funDecl = (typ * string * paramList * exp);;
type program = funDecl list;;