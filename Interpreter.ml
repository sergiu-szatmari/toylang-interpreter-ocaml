(* ============================== ToyLang Interpreter ============================== *)

open AST;;

(* V *)
type typVal = typ * value;;
type varEnv = (string * typVal) list;;

(* H *)
type heap = (int * typVal) list;;

(* O *)
type output = value list;;

type state = {
  f : program;
  h : heap;
  v : varEnv;
  o : output;
  e : exp
  };;
  
  
let errState : state =  { f=[]; h=[]; v=[]; o=[Vvoid]; e=(Eval(Vint 0))}


let rec getVal (var: string) (vEnv: varEnv) : value option = 
  match vEnv with
  | [] -> None
  | ((varName, (_, value))::_) when var = varName -> Some value
  | _::t -> getVal var t


let rec getContent (loc: int) (h : heap) : value option =
  match h with
  | [] -> None
  | ((addr, (_, value))::_) when addr = loc -> Some value
  | _::t -> getContent loc t


let rec getVarType (var: string) (vEnv: varEnv) : typ option =
  match vEnv with
  | [] -> None
  | ((varName, (ty, _))::_) when var = varName -> Some ty
  | _::t -> getVarType var t

let rec getLocType (loc: int) (h: heap) : typ option =
  match h with
  | [] -> None
  | ((addr, (ty, _))::_) when addr = loc -> Some ty
  | _::t -> getLocType loc t



let getValType (expr: exp): typ option = 
  match expr with
  | Eval value -> (
      match value with
      | Vvoid -> Some Tbot
      | Vint _ -> Some (Tprim Tint)
      | Vbool _ -> Some (Tprim Tbool)
      | Vaddr _ -> Some (Taddr (Tprim Tint))
      | Vnull -> Some (Taddr Tbot)
  )
  | _ -> None

let eq_prim t1 t2 = 
  match (t1,t2) with
  | (Tint, Tint) -> true
  | (Tbool, Tbool) -> true
  | (Tvoid, Tvoid) -> true
  | (_, _) -> false;;

let rec eq_type t1 t2 =
  match (t1,t2) with
  | (Tprim ta, Tprim tb) -> eq_prim ta tb
  | (Tbot, Tbot) -> true
  | (Tbot, Taddr _) -> true
  | (Taddr _, Tbot) -> true
  | (Taddr ta,Taddr tb) -> eq_type ta tb
  | (_,_) -> false;;

let rec update (vEnv: varEnv) (var: string) (v: value) : varEnv = 
  match vEnv with
  | [] -> []
  | ((varName, (varType, _))::t) when varName = var -> (varName, (varType, v))::t
  | h::t -> h::(update t var v)

let rec updateHeap (h: heap) (loc: int) (newVal: value) : heap =
  match h with
  | [] -> []
  | ((addr, (typ, _))::t) when addr = loc -> (addr, (typ, newVal))::t
  | h::t -> h::(updateHeap t loc newVal)

let init (ty:typ) : value = 
  match ty with
  | Tprim Tint -> Vint 0
  | Tprim Tbool -> Vbool false
  | Tprim Tvoid -> Vvoid
  | Tbot -> Vnull
  | Taddr _ -> Vaddr 0

let rec erase (vEnv:varEnv) (var:string) : varEnv =
  match vEnv with
  | [] -> []
  | ((varName, (ty, v))::t) when varName = var -> t
  | _ :: t -> (erase t var)

let rec eraseFromHeap (h: heap) (loc: int) : heap = 
  match h with
  | [] -> []
  | ((location, (ty, v))::t) when location = loc -> t
  | _::t -> eraseFromHeap t loc

let rec newAddress (h: heap) : int = 
  match h with
  | [] -> 1
  | (a, _)::[] -> (a + 1)
  | _::t -> newAddress t

let rec findFunction (p: program) (funcName: string) : funDecl option = 
  match p with
  | [] -> None 
  | (ty, fName, params, expr)::_ when funcName = fName -> Some (ty, fName, params, expr)
  | _::t -> findFunction t funcName

let rec checkParameters (vEnv: varEnv) (givenParams: string list) (funcParams: paramList) : varEnv option = 
  match givenParams with
  | [] -> Some []
  | paramName::t -> (
      let vOpt = getVal paramName vEnv in
      match vOpt with
      | None -> None
      | Some value -> (
          let vTypeOpt = getValType (Eval value) in
          match vTypeOpt with
          | None -> None
          | Some ty -> (
              match funcParams with
              | [] -> None 
              | (fParamType, fParamName)::fParamTail -> (
                  let sameTypes = (eq_type ty fParamType) in  
                  match sameTypes with
                  | false -> None
                  | true -> (
                      let optNextParams = (checkParameters vEnv t fParamTail) in
                      match optNextParams with
                      | None -> None 
                      | Some tail -> Some ((fParamName, (fParamType, value))::tail)
                  )
              )
          )
      )
  )

let rec freeVariables (varNames: string list) (expr: exp) : exp = 
  match varNames with
  | [] -> expr
  | varName::t -> Eret(varName, (freeVariables t expr))

let rec evalE (s : state) : state = 
  match s.e with
  | Eval value -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval value }

  | Evar var -> (
      let valOpt = getVal var s.v in
      match valOpt with
      | None -> errState
      | Some value -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval value }
  )

  | Ederef addr -> (
      let valOpt = getVal addr s.v in
                    match valOpt with
                    | None -> errState
                    | Some loc -> (
                        match loc with
                        | Vaddr address -> (
                            let vOpt = getContent address s.h in 
                            match vOpt with
                            | None -> errState 
                            | Some value -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval value }
                        )
                        | _ -> errState
                    )
  )
  
  | Eassignvar (var, expr) -> (
      let typVarOpt = getVarType var s.v in 
      match typVarOpt with
      | None -> errState
      | Some typVar -> (
          let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr } in 
          match v1.e with
          | Eval v -> (
              let typValOpt = getValType v1.e in 
              match typValOpt with
              | None -> errState 
              | Some typVal -> (
                  match (eq_type typVal typVar) with
                  | false -> errState 
                  | true -> { f = s.f; h = s.h; v = (update s.v var v); o = s.o; e = v1.e }
              )
          )
          | _ -> errState
      )
  )

  | Eassignloc (var, expr) -> (
      let locOpt = getVal var s.v in 
      match locOpt with
      | Some (Vaddr loc) -> (
          let locTyp = getLocType loc s.h in 
          match locTyp with
          | None -> errState 
          | Some ty -> (
             let v = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr } in
             match v.e with
             | Eval value -> (
                let valTyp = getValType v.e in
                match valTyp with 
                | None -> errState
                | Some ty2 -> (
                    let sameType = eq_type ty ty2 in 
                    match sameType with
                    | false -> errState
                    | true -> { f = s.f; h = (updateHeap s.h loc value); v = s.v; o = s.o; e = v.e }
                )
             )
             | _ -> errState
          )
      )
      | Some _ | None -> errState
  )

  | Eret (var, expr) -> (
      match expr with
      | Eval value -> {f=s.f; h=s.h; v=s.v; o=s.o; e=(Eval value)}
      | _ -> evalE {f=s.f; h=s.h; v=s.v; o=s.o; e=expr}
  )

  | Eblk (ty, var, expr) -> (
      let retState = evalE 
      { 
        f = s.f; 
        h = s.h; 
        v = (var, (ty, (init ty)))::s.v;
        o = s.o;
        e = (Eret (var, expr));  
      } in
      {
        f = retState.f;
        h = retState.h;
        v = (erase retState.v var);
        o = retState.o;
        e = retState.e;
      }
  )

  | Eseq (expr1, expr2) -> (
      let stateExpr1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in
        evalE { f= stateExpr1.f; h=stateExpr1.h; v = stateExpr1.v; o = stateExpr1.o; e = expr2 }
  )

  | Eif (condition, expr1, expr2) -> (
      let evalCond = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = condition } in 
      match evalCond.e with
      | Eval (Vbool true) -> evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 }
      | Eval (Vbool false) -> evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 }
      | _ -> errState
  )

  | Eplus(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vint (intValue1 + intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Eminus(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vint (intValue1 - intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Estar(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vint (intValue1 * intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Ediv(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vint (intValue1 / intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Eless(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool (intValue1 < intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Egreater(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool (intValue1 > intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Eeq(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool (intValue1 = intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Eneq(expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with 
      | Eval (Vint intValue1) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in
          match v2.e with 
          | Eval (Vint intValue2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool (intValue1 != intValue2)) }
          | _ -> errState
      )
      | _ -> errState
  )

  | Eand (expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with
      | Eval (Vbool true) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in 
            match v2.e with
            | Eval (Vbool b2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool b2) }
            | _ -> errState
      )
      | Eval (Vbool false) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool false) }
      | _ -> errState
  )

  | Eor (expr1, expr2) -> (
      let v1 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr1 } in 
      match v1.e with
      | Eval (Vbool false) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr2 } in 
            match v2.e with
            | Eval (Vbool b2) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool b2) }
            | _ -> errState
      )
      | Eval (Vbool true) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool true) }
      | _ -> errState
  )

  | Enot (expr) -> (
      let v = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr } in 
      match v.e with
      | Eval (Vbool true) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool false) }
      | Eval (Vbool false ) -> { f = s.f; h = s.h; v = s.v; o = s.o; e = Eval (Vbool true) }
      | _ -> errState
  )

  | Eprint (expr) -> (
      let v = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr } in 
      match v.e with 
      | Eval expression -> { f = s.f; h = s.h; v = s.v; o = expression::s.o; e = v.e }
      | _ -> errState
  )

  | Ewhile (cond, expr) -> (
      let v = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = cond } in
      match v.e with
      | Eval (Vbool true) -> (
          let v2 = evalE { f = s.f; h = s.h; v = s.v; o = s.o; e = expr } in 
            evalE { f = v2.f; h = v2.h; v = v2.v; o = v2.o; e = (Ewhile (cond, expr)) }
      )
      | Eval (Vbool false) -> s
      | _ -> errState
  )

  | Enew (ty) -> (
      let addr = newAddress s.h in 
        { f = s.f; h = ((addr, (ty,(Vint 0))))::s.h; v = s.v; o = s.o; e = (Eval (Vint addr)) }
  )

  | Edelete (var) -> (
      let loc = getVal var s.v in 
      match loc with
      | Some (Vaddr loc) -> { f = s.f; h = (eraseFromHeap s.h loc); v = s.v; o = s.o; e = s.e }
      | _ -> errState 
  )

  | Efcall (funcName, param) -> (
      let func = findFunction s.f funcName in 
      match func with
      | None -> errState
      | Some (ty, _, params, expr) -> (
          let funcEnvOpt = (checkParameters s.v param params) in
          match funcEnvOpt with
          | None -> errState
          | Some funcEnv -> (
            let funcExp = (freeVariables param expr) in
              evalE {f = s.f; h = s.h; v = funcEnv; o = s.o; e = funcExp}
          )
      )
  )

let evalP (p: program) : state = 
  match (findFunction p "main") with
  | None -> errState
  | Some mainFunc -> (
      let (_, _, _, funcBody) = mainFunc in
       let progState = {f = p; h = []; v = []; o = []; e = funcBody } in evalE progState
  )
        
let rec printOutput (o:output) = 
  match o with 
  | [] -> ()
  | Vnull :: tail -> printOutput tail; print_string "null\n"
  | (Vint int1) :: tail -> printOutput tail; print_int int1; print_string "\n";
  | (Vbool true) :: tail -> printOutput tail; print_string "true\n"
  | (Vbool false) :: tail -> printOutput tail; print_string "false\n"
  | Vvoid :: tail -> printOutput tail; print_string "void\n"
  | (Vaddr _) :: tail -> printOutput tail; print_string "addres\n";;
  
