(* ============================== ToyLang Type Checker ============================== *)

open AST;;

let rec typechecker_getVarType (varName: string) (g: (typ * string) list) : typ option =
  match g with
  | [] -> None
  | (ty, var) :: [] when var = varName -> Some ty
  | _ :: t -> (typechecker_getVarType varName t)

let rec typechecker_checkParams (g: (typ * string) list) (givenParams: string list) (funcParams: paramList) : bool =
  match givenParams, funcParams with
  | [], [] -> true
  | [], _ | _, [] -> false
  | givenParam::t1, funcParam::t2 -> (
      match (typechecker_getVarType givenParam g), funcParam with
      | Some type1, (type2, _) when eq_type type1 type2 -> typechecker_checkParams g t1 t2
      | _, _ -> false
  )

let rec typecheck_exp (f: program) (g:(typ*string) list) (e: exp) : typ option =
  match e with
  | Eval Vnull -> Some Tbot
  | Eval Vvoid -> Some (Tprim Tvoid)
  | Eval Vint kInt -> Some (Tprim Tint)
  | Eval Vbool kBool -> Some (Tprim Tbool)
  | Eval Vaddr kInt -> Some (Taddr (Tprim Tint))
  | Evar var -> (typechecker_getVarType var g)
  | Ederef var -> (
      let ty = (typechecker_getVarType var g) in
      match ty with
      | Some (Taddr addr) -> Some addr
      | _ -> None
  )
  | Eassignvar (var, expr) -> (
      let optType1 = (typecheck_exp f g (Evar var)) in
      match optType1 with
      | None -> None
      | Some opt1 -> (
          let optType2 = (typecheck_exp f g expr) in
          match optType2 with
          | None -> None
          | Some opt2 -> (
              let sameTypes = eq_type opt1 opt2 in
              match sameTypes with
              | true -> Some (Tprim Tvoid)
              | false -> None
          ) 
      )
  )

  | Eassignloc (var, expr) -> (
      let optType1 = (typechecker_getVarType var g) in
      match optType1 with
      | Some (Taddr type1) -> (
          let optType2 = (typecheck_exp f g expr) in
          match optType2 with
          | None -> None
          | Some type2 -> (
              let sameTypes = eq_type type1 type2 in
              match sameTypes with
              | true -> Some (Tprim Tvoid)
              | false -> None
          )
      )
      | Some _ | None -> None
  )

  | Eblk (ty, value, expr) -> (typecheck_exp f ((ty, value) :: g) expr)

  | Eseq (expr1, expr2) -> (
      let optType1 = (typecheck_exp f g expr1) in
      match optType1 with
      | None -> None
      | Some type1 -> (typecheck_exp f g expr2)
  )
  
  | Eif (cond, expr1, expr2) -> (
      let optCond = typecheck_exp f g cond in
      match optCond with
      | Some (Tprim Tbool) -> (
          let optType1 = (typecheck_exp f g expr1) in
          match optType1 with
          | None -> None
          | Some type1 -> (
              let optType2 = (typecheck_exp f g expr2) in
              match optType2 with
              | None -> None
              | Some type2 -> (
                  let sameTypes = eq_type type1 type2 in
                  match sameTypes with
                  | false -> None
                  | true -> Some type1
              )
          )
      )
      | Some _ | None -> None
  )

  | Eplus (expr1, expr2) | Eminus (expr1, expr2) | Estar (expr1, expr2) | Ediv (expr1, expr2) -> (
      let optType1 = (typecheck_exp f g expr1) in 
      match optType1 with
      | Some (Tprim Tint) -> (
          let optType2 = (typecheck_exp f g expr2) in
          match optType2 with 
          | Some (Tprim Tint) -> Some (Tprim Tint)
          | Some _ | None -> None
      )
      | Some _ | None -> None
  ) 

  | Eeq (expr1, expr2) | Egreater (expr1, expr2) | Eneq (expr1, expr2) | Eless (expr1, expr2) -> (
      let optType1 = (typecheck_exp f g expr1) in 
      match optType1 with
      | Some (Tprim Tint) -> (
          let optType2 = (typecheck_exp f g expr2) in
          match optType2 with 
          | Some (Tprim Tint) -> Some (Tprim Tbool)
          | Some _ | None -> None
      )
      | Some _ | None -> None
  )

  | Eand (expr1, expr2) | Eor (expr1, expr2) -> (
      let optType1 = (typecheck_exp f g expr1) in 
      match optType1 with
      | Some (Tprim Tbool) -> (
          let optType2 = (typecheck_exp f g expr2) in
          match optType2 with 
          | Some (Tprim Tbool) -> Some (Tprim Tbool)
          | Some _ | None -> None
    )
    | Some _ | None -> None
)


  | Enot expr -> (
    let optType = (typecheck_exp f g expr) in
    match optType with 
    | Some (Tprim Tbool) -> Some (Tprim Tbool)
    | Some _ | None -> None
  )

  | Enew ty -> Some ty

  | Ewhile (cond, expr) -> (
      let optCond = (typecheck_exp f g cond) in
      match optCond with
      | Some (Tprim Tbool) -> Some (Tprim Tvoid)
      | Some _ | None -> None
  )

  | Edelete varName -> (
      let varOpt = (typechecker_getVarType varName g) in
      match varOpt with
      | Some (Taddr _ ) -> Some (Tprim Tvoid)
      | Some _ | None -> None
  )

  | Eret _ -> None

  | Eprint _ -> Some (Tprim Tvoid)

  | Efcall (funcName, givenParams) -> (
      let optFuncName = (findFunction f funcName) in
      match optFuncName with
      | Some (ty, _, funcParams, expr) -> (
          match typechecker_checkParams g givenParams funcParams with
          | false -> None
          | true -> (
              let optType = typecheck_exp f g expr in
              match optType with
              | Some typ when eq_type ty typ -> Some ty
              | _ -> None
          )
      )
      | _ -> None
  )

let typecheck_func (funcDecl: funDecl) (p: program) : bool =
  let (ty, _, funcParams, funcBody) = funcDecl in
  match typecheck_exp p funcParams funcBody with
  | None -> false
  | Some value -> eq_type value ty

let typecheck_prog (p: program) (p1: program) : bool =
  match p1 with
  | [] -> true
  | [(ty, funcName, funcParams, funcBody)] when funcName = "main" -> (
      typecheck_func (ty, funcName, funcParams, funcBody) p1
  )
  | fDecl::tail -> typecheck_func fDecl p1

  