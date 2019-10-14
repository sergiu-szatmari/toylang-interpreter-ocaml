open AST;;
open Interpreter;
open TypeChecker;

let prOK =
  [ 
    (Tprim Tint, "main", [],
      Eblk (Tprim Tint, "x",
        Eseq ( Eassignvar ("x", Eval (Vint 20)),
          Eseq ( Ewhile (Egreater (Evar "x", Eval (Vint 0)),
            Eseq( Eprint (Evar "x"),
              Eassignvar ("x", Eminus (Evar "x",Eval (Vint 1)))
            )
          ),
        Evar "x"
        )
      )
    )
  ) 
  ];;

let prNotOK =
  [ 
    (Tprim Tint, "main", [],
      Eblk (Tprim Tbool, "x",
        Eseq ( Eassignvar ("x", Eval (Vint 20)),
          Eseq ( Ewhile (Egreater (Evar "x", Eval (Vint 0)),
            Eseq( Eprint (Evar "x"),
              Eassignvar ("x", Eminus (Evar "x",Eval (Vint 1)))
            )
          ),
        Evar "x"
        )
      )
    )
  ) 
  ];; 

(* OK *)
let outOk = typecheck_prog prOK prOK in
  match outOk with
  | false -> print_string ":(\n"
  | true -> (
      let st = evalP prOK in
        printOutput st.o
);;


(* Not OK *)
let outNotOk = typecheck_prog prNotOK prNotOK in
  match outNotOk with
  | false -> print_string ":(\n"
  | true -> (
      let st = evalP prNotOK in
        printOutput st.o
);;