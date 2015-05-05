(* datatype *)

datatype obj =
         NIL
         | NUM of int
         | REAL of real
         | SYM of string
         | ERROR of string
         | CONS of obj ref * obj ref
         | FUNC of (obj -> obj) ref
         | EXPR of obj * obj * obj

fun car obj =
  case obj of
      CONS(ref a, ref b) => a
   | _ => NIL

fun cdr obj =
  case obj of
      CONS(ref a, ref b) => b
   | _ => NIL

fun cons a b = CONS(ref a, ref b)

fun list lst =
  let fun sub ([]) =
        NIL
        | sub (x::xs) = 
          cons x (sub (xs))
  in
      sub (lst)
  end
        
fun append a b =
  case a of
      NIL => b
    | _ => (cons (car a) (append (cdr a) b))
  
fun makePairList a b =
  let fun sub a b acc =
        case (a, b) of
            (CONS (ref a1, ref b1), CONS (ref a2, ref b2)) =>
            sub b1 b2 (append acc (cons (cons a1 a2) NIL))
         |  _ => acc
  in
      sub a b NIL
  end

val symTable = ref [("nil", NIL)]

fun findSym str1 =
  let fun sub (_, []) = NONE
        | sub (str1 : string, (str2, sym)::rest) =
          if str1 = str2 then
              SOME sym
          else
              sub (str1, rest)
  in
      sub (str1, !symTable)
  end
                 
fun makeSym str =
  case findSym (str) of
      SOME sym => sym
    | NONE =>
      let val sym = SYM str
      in
          symTable := (str, sym)::(!symTable);
          sym
      end

val tSym = makeSym "t"
val setqSym = makeSym "setq"
val ifSym = makeSym "if"
val lambdaSym = makeSym "lambda"
val defunSym = makeSym "defun"
val quoteSym = makeSym "quote"

fun eqlSym a b =
  case (a, b) of
      (SYM sym1, SYM sym2) => sym1 = sym2
   | _ =>  false

fun expr args env =
  EXPR(car args, cdr args, env)
                 
fun printObj obj =
  case obj of
      NIL => "nil"
   |  NUM n => Int.toString(n)
   |  SYM s => s
   |  ERROR s => "<error: " ^ s ^ ">"
   |  CONS _ => "(" ^ (printList obj) ^ ")"
   |  FUNC(_) => "<func>"
   |  EXPR(_, _, _) => "<expr>"

and printList obj =
    let fun sub obj delimiter acc =
          case obj of
              CONS(ref a, ref d) =>
              sub d " " (acc ^ delimiter ^ printObj a)
           |  NIL => acc
           |  _ => acc ^ " . " ^ printObj obj
    in
        sub obj "" ""
    end

(* Reader *)

val lparens = #"("
val rparens = #")"
val quote = #"'"

fun isWhiteSpace c =
  c = #"\t" orelse c = #"\r" orelse c = #"\n" orelse c = #" "

fun isDeliminater c =
  c = lparens orelse c = rparens orelse c = quote orelse isWhiteSpace c

fun skipWhiteSpaces str =
  let fun sub lst =
        case lst of
            [] => []
          | x::xs =>
            if isWhiteSpace x then
                sub xs
            else
                lst
  in
          implode (sub (explode str))
  end

fun position (f, str) =
  let fun sub (_, [], _) = NONE
        | sub (f, x::xs, n) = 
          if f x then
              SOME n
          else
              sub (f, xs, n + 1)
  in
      sub (f, explode str, 0)
  end
      
fun read str =
  let fun advavce str =
        substring (str, 1, size str - 1)
  in
      let val skipped = skipWhiteSpaces str
      in
          case explode skipped of
              [] => (ERROR "Empty input.", "")
            | x::xs =>
              if x = lparens then
                  readList (advavce skipped)
              else if x = rparens then
                  (ERROR ("invalid syntax:" ^ skipped), "")
              else if x = quote then
                  readQuote (advavce skipped)
              else
                  readAtom skipped
      end
  end

and readAtom str =
  let fun sub str =
        case Int.fromString str of
            SOME n => NUM n
          | NONE => makeSym str
  in
      case position (isDeliminater, str) of
          SOME n =>
          (sub (substring (str, 0, n)), substring (str, n , size str - n))
        | NONE => 
          (sub str, "")
  end
      
and readList str =
    let fun sub str acc =
          case explode str of
              [] => (ERROR "Unexpected EOF.", "")
            | x::xs =>
              if x = rparens then
                  (acc, implode xs)
              else
                  case read str of
                      (ERROR err, next) => (ERROR err, next)
                    | (elem, next) => sub next (append acc (cons elem NIL))
    in
        sub str NIL
    end

and readQuote str =
    case read str of
        (elem, next) =>
        (cons quoteSym (cons elem NIL), next)

(* Eval *)
            
val globalEnv = cons NIL NIL

fun findVarInFrame sym1 frame =
  case car (car frame) of
      SYM sym2 =>
      if eqlSym sym1 (makeSym sym2) then
          car frame
      else
          findVarInFrame sym1 (cdr frame)
    | _ => NIL
               
fun findVar sym env =
  case env of
      CONS (ref a, ref b) =>
      (case findVarInFrame sym a of
           NIL => findVar sym b
         | pair => pair)
    | _ => NIL

fun addToFrame sym value frame =
  cons (cons sym value) frame

fun addToCurrentEnv sym value env =
  case env of
      CONS (current, rest) =>
      current := addToFrame sym value (!current)
    | _ => ()

fun eval obj env =
  case obj of
      SYM _ =>
      (case findVar obj env of
           NIL => ERROR ((printObj obj) ^ " is unbound.")
         | pair => cdr pair)
    | CONS _ => evalCons obj env
    | _ => obj

and evalCons obj env =
    let val operat = car obj
        val args = cdr obj
    in
        if eqlSym operat quoteSym then
            car args
        else if eqlSym operat ifSym then
            case eval (car args) env of
                NIL => eval (car (cdr (cdr args))) env
              | _ => eval (car (cdr args)) env
        else if eqlSym operat lambdaSym then
            expr args env
        else if eqlSym operat defunSym then
            (addToCurrentEnv (car args) (expr (cdr args) env) globalEnv;
             (car args))
        else if eqlSym operat setqSym then
            let val sym = car args
                val value = eval (car (cdr args)) env
            in
                case findVar sym env of
                    CONS (a, b) =>
                    b := value
                  | _ => addToCurrentEnv sym value globalEnv;
                value
            end
        else
            apply (eval operat env) (evalList args env) env
    end

and evalList lst env =
    case lst of
        NIL => NIL
      | _ =>
        (case eval (car lst) env of
             ERROR err => ERROR err
           | elem => cons elem (evalList (cdr lst) env))

and apply f args env =
    case (f, args) of
        ((ERROR err), _) => ERROR err
      | (_, (ERROR err)) => ERROR err
      | (FUNC(ref f), _) => f args
      | (EXPR(head, tail, env), _) =>
        progn tail (cons (makePairList head args) env)

and progn body env =
    let fun sub body env last =
          case body of
              CONS (ref a, ref b) => sub b env (eval a env)
           |  _ => last
    in
        sub body env NIL
    end

fun eqlObj a b =
  case (a, b) of
      (NIL, NIL) => tSym
   |  (NUM a, NUM b) => if a = b then tSym else NIL
   |  (SYM a, SYM b) => if a = b then tSym else NIL
   |  (ERROR a, ERROR b) => if a = b then tSym else NIL
   |  (CONS a, CONS b) => if a = b then tSym else NIL
   |  (FUNC a, FUNC b) => if a = b then tSym else NIL
   |  (EXPR(a1, b1, c1), EXPR(a2, b2, c2)) => (
       case (eqlObj a1 a2, eqlObj b1 b2, eqlObj c1 c2) of
           (NIL, _, _) => NIL
        |  (_, NIL, _) => NIL
        |  (_, _, NIL) => NIL
        |   _ => tSym)
   |  _ => NIL

fun first (x, y) = x

fun repl prompt =
  (TextIO.print prompt;
   case TextIO.inputLine TextIO.stdIn of
       SOME line =>
       (print ((printObj (eval(first(read line)) globalEnv)) ^ "\n");
        repl prompt)
    |  NONE => ())

(* init *)

fun carFun args =
  car (car args)

fun cdrFun args =
  cdr (car args)

fun consFun args =
  cons (car args) (car (cdr args))

fun listFun args =
  case args of
      NIL => NIL
    | _ => cons (car args) (listFun (cdr args))
                
fun eqlFun args =
  eqlObj (car args) (car (cdr args))

fun atomFun args =
  case car args of
      CONS _ => NIL
    | _ => tSym

fun numberpFun args =
  case car args of
      NUM _ => tSym
    | _ => NIL

fun symbolpFun args =
  case car args of
      SYM _ => tSym
    | _ => NIL

fun addFun args =
  let fun sub args acc =
        case args of
            CONS (ref (NUM n), ref rest) => sub rest (acc + n)
         |  CONS _ => ERROR "wrong type"
         |  _ => NUM acc
  in
      sub args 0
  end

fun multipleFun args =
  let fun sub args acc =
        case args of
            CONS (ref (NUM n), ref rest) => sub rest (acc * n)
         |  CONS _ => ERROR "Wrong type."
         |  _ => NUM acc
  in
      sub args 1
  end

fun subFun args =
  let fun sub args acc =
        case args of
            CONS (ref (NUM n), ref rest) => sub rest (acc - n)
         |  CONS _ => ERROR "Wrong type."
         |  _ => NUM acc
  in
      sub args 0
  end

fun divFun args =
  case ((car args), (car (cdr args))) of
      (NUM a, NUM b) =>
      REAL ((Real.fromInt a) / (Real.fromInt b))
    | (REAL a, NUM b) => 
      REAL (a / (Real.fromInt b))
    | (NUM a, REAL b) => 
      REAL ((Real.fromInt a) / b)
    | (REAL a, REAL b) => 
      REAL (a / b)
    | _ => ERROR "Wrong type."

fun modFun args =
  case ((car args), (car (cdr args))) of
      (NUM a, NUM b) => NUM (a mod b)
    | _ => ERROR "Wrong type."

fun run _ =
  (addToCurrentEnv (makeSym "car") (FUNC(ref(carFun))) globalEnv;
   addToCurrentEnv (makeSym "cdr") (FUNC(ref(cdrFun))) globalEnv;
   addToCurrentEnv (makeSym "cons") (FUNC(ref(consFun))) globalEnv;
   addToCurrentEnv (makeSym "list") (FUNC(ref(listFun))) globalEnv;
   addToCurrentEnv (makeSym "eql") (FUNC(ref(eqlFun))) globalEnv;
   addToCurrentEnv (makeSym "atom") (FUNC(ref(atomFun))) globalEnv;
   addToCurrentEnv (makeSym "numberp") (FUNC(ref(numberpFun))) globalEnv;
   addToCurrentEnv (makeSym "symbolp") (FUNC(ref(symbolpFun))) globalEnv;
   addToCurrentEnv (makeSym "+") (FUNC(ref(addFun))) globalEnv;
   addToCurrentEnv (makeSym "*") (FUNC(ref(multipleFun))) globalEnv;
   addToCurrentEnv (makeSym "-") (FUNC(ref(subFun))) globalEnv;
   addToCurrentEnv (makeSym "/") (FUNC(ref(divFun))) globalEnv;
   addToCurrentEnv (makeSym "mod") (FUNC(ref(modFun))) globalEnv;
   addToCurrentEnv (makeSym "t") (makeSym "t") globalEnv;
   repl "> ")
