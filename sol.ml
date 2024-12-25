
type info = Info of int*bool;;

type argumentSig = PredicateSig of int | IndividualSig;;
type formula = Bot | App of term*(term list) | 
And of formula*formula | Or of formula*formula | 
Neg of formula | Imp of formula*formula | 
Forall of term*formula | Exists of term*formula
and term = Constant of string*argumentSig | 
Variable of string*(argumentSig*info) | Lambda of (term list)* formula;;

let opt_to_bool op = match op with
 Some x -> true
|None -> false;;

let opt_to_list op = match op with
 Some x -> x
| None -> [];;

let rec lookup k = function
| [] -> None
| (k', v) :: t -> if k = k' then Some v else lookup k t

let insert k v lst = (k, v) :: lst

let parenthesis list = if (List.length list) < 3 then false else if (List.nth list 0) = "(" && (List.nth (List.rev list) 0 ) = ")" then true else false;;

let rec inner list = match list with
 a::b -> List.rev (outer b) 
|_ -> []
and
outer list = match List.rev list with
a::b -> b
|_ ->[];;


let rec bin_op sep parser1 parser2 pairexp = match pairexp with
  (a,b::c) -> if opt_to_bool (parser1 (List.rev a)) && opt_to_bool(parser2 c) && b = sep then Some (List.rev a, c) else bin_op sep parser1 parser2 (b::a ,  c)
  | (a,[]) -> None;;


let rec sep_star sep parser pairexp = match pairexp with
  (a,b::c) ->  if opt_to_bool( parser (List.rev a)) && opt_to_bool(sep_star sep parser ([],c)) && b = sep then Some ((List.rev a)::opt_to_list (sep_star sep parser ([],c) ))
   else sep_star sep parser (b::a,c)
 | (a,[]) -> None;;

let rec star parser pairexp = match pairexp with
  |([],[])  ->  Some []
  |(a,b::c) ->  if opt_to_bool( parser (List.rev a)) && opt_to_bool(star parser ([],b::c))  then Some ((List.rev a)::opt_to_list (star parser ([],b::c) ))
   else star parser (b::a,c)
 | (a,[]) -> if opt_to_bool (parser (List.rev a)) then Some [a]  else None;;

let simple_parse list exp = if List.length exp = 1 && List.mem (List.nth exp 0) list then Some true else None;;

let const_dic = ref [("*", IndividualSig); ("C", PredicateSig 1) ];;
let var_dic = ref [("x", (IndividualSig, Info (0,false))) ;("y", (IndividualSig, Info (0,false)))   ];;

let variable_parser  exp = if List.length exp = 1 && opt_to_bool(lookup (List.nth exp 0) !var_dic) then (match  lookup (List.nth exp 0) !var_dic with
 Some (x,y) -> Some (  Variable (List.nth exp 0 ,  (x , y) )  )
| None -> None )  else None;; 

let constant_parser  exp = if List.length exp = 1 && opt_to_bool(lookup (List.nth exp 0) !const_dic) then (match  lookup (List.nth exp 0) !const_dic with
 Some x -> Some (Constant (List.nth exp 0 , x )  )
| None -> None )  else None;;

let rec list_parser parser_list exp = match parser_list with
 a::b -> if  opt_to_bool (a exp) then (a exp) else list_parser b exp
|_ -> None;;


let opt_to_form  o = match o with
Some x -> x
| None -> Bot;; 

let rec pre_and_parser parser pairexp = match pairexp with
  (a,b::c) -> if opt_to_bool (parser (List.rev a)) && opt_to_bool(parser c) && b = "&"
   then Some (And (opt_to_form (parser (List.rev a)), opt_to_form (parser c)) )  else pre_and_parser parser (b::a ,  c)
  | (a,[]) -> None;;

let and_parser parser exp = if List.length exp > 2 && parenthesis exp then pre_and_parser parser ([],inner exp) else None;;


let rec pre_or_parser parser pairexp = match pairexp with
  (a,b::c) -> if opt_to_bool (parser (List.rev a)) && opt_to_bool(parser c) && b = "or"
   then Some (And (opt_to_form (parser (List.rev a)), opt_to_form (parser c)) )  else pre_or_parser parser (b::a ,  c)
  | (a,[]) -> None;;

let or_parser parser exp = if List.length exp > 2 && parenthesis exp then pre_or_parser parser ([],inner exp) else None;;

let rec pre_imp_parser parser pairexp = match pairexp with
  (a,b::c) -> if opt_to_bool (parser (List.rev a)) && opt_to_bool(parser c) && b = "&"
   then Some (And (opt_to_form (parser (List.rev a)), opt_to_form (parser c)) )  else pre_imp_parser parser (b::a ,  c)
  | (a,[]) -> None;;

let imp_parser parser exp = if List.length exp > 2 && parenthesis exp then pre_imp_parser parser ([],inner exp) else None;;


let bot_parser exp = if List.length exp = 1 && List.nth exp 0 = "_|_" then Some Bot else None;;

let rec parser_test exp = if opt_to_bool (bot_parser exp) then bot_parser exp else and_parser parser_test exp;;

let opt_forall x y = match x with 
 Some a -> (match y with 
             Some b -> Forall (a,b)  
             |_ -> Bot)
 |_ -> Bot;; 

 let opt_exists x y = match x with 
 Some a -> (match y with 
             Some b -> Forall (a,b)  
             |_ -> Bot)
 |_ -> Bot;; 

let opt_lambda x y = match x with 
 Some a -> (match y with 
             Some b -> Lambda (a,b)  
             |_ -> Constant ("*", IndividualSig))
 |_ -> Constant("*", IndividualSig);;     

let opt_app x y = match x with 
 Some a -> (match y with 
             Some b -> App (a,b)  
             |_ -> Bot)
 |_ -> Bot;;    


let rec pre_forall_parser parser exppair = match exppair with
 (a, b::c) ->let aux = List.rev a in let f = parser (b::c) in if List.length a = 2 &&  let v = variable_parser [List.nth aux 1] in List.nth aux 0 = "forall" && 
 opt_to_bool v  && opt_to_bool f  then let v = variable_parser [List.nth aux 1] in  Some (opt_forall v f)  else  (pre_forall_parser parser)  (b::a , c)
 |(a,[]) -> None;;


let forall_parser parser exp = pre_forall_parser parser ([],exp);;


let rec pre_exists_parser parser exppair = match exppair with
 (a, b::c) ->let aux = List.rev a in let f = parser (b::c) in if List.length a = 2 &&  let v = variable_parser [List.nth aux 1] in List.nth aux 0 = "forall" && 
 opt_to_bool v  && opt_to_bool f  then let v = variable_parser [List.nth aux 1] in  Some (opt_exists v f)  else  (pre_exists_parser parser)  (b::a , c)
 |(a,[]) -> None;;


let exists_parser parser exp = pre_exists_parser parser ([],exp);;

let rec opt_list parser l = match l with
 a::b -> if opt_to_bool (parser a) then (match parser a with
                                          Some w ->  w::opt_list parser b 
                                          |_ -> []) else []
 |_ -> [];;                                         

let opt_list_var exp = let aux =(star variable_parser ([],exp)) in if opt_to_bool aux then (match aux with
 Some list -> Some (opt_list variable_parser list)
|None -> None) else None;;  

let tail list = match list with
a::b -> b
|_ -> [];;

let rec pre_lambda_parser parser exppair = match exppair with
 (a1::a2, b::c) -> let aux = List.rev (a1::a2) in let f = parser (b::c) in let v = opt_list_var (tail aux) in if List.nth aux 0 = "lambda" && 
 opt_to_bool v  && opt_to_bool f  then let v = opt_list_var (tail aux) in  Some (opt_lambda v f)  else  (pre_lambda_parser parser)  (b::a1::a2 , c)
 |([], b::c) -> (pre_lambda_parser parser)  (b::[] , c)
 |(a,[]) -> None;;


let lambda_parser parser exp = pre_lambda_parser parser ([],exp);;

let opt_list_app parser exp = let aux =(star parser ([],exp)) in if opt_to_bool aux then (match aux with
 Some list -> Some (opt_list parser list)
|None -> None) else None;;  

let rec indVarCheck list = match list with
 []    -> true
 | a:: b ->  match a with
             Variable (x , (y , i) ) -> if y = IndividualSig then (indVarCheck b) else false
             |_ -> false;;

let arity arg = match arg with
  PredicateSig n -> n 
  |_ -> -1;;  

let check_app t l = match t,l with 
                 Some Lambda (x,g), Some m  -> ((List.length x) = (List.length m))  && (indVarCheck x)
                |Some Constant (s,arg), Some m -> (List.length m) = (arity arg)  
                |Some Variable (s,(arg,i)), Some m -> (List.length m) = (arity arg) 
                |_ -> false;; 

let rec pre_app_parser parser exppair = match exppair with
 (a, b::c) -> let t = parser (List.rev a) in let args = opt_list_app parser (b::c) in if opt_to_bool t && opt_to_bool args && check_app t args then 
 let t = parser (List.rev a) in let args = opt_list_app parser (b::c) in Some (opt_app t args) else pre_app_parser parser (b::a,c)
|(a,[]) -> None;;

let app_parser parser exp = pre_app_parser parser ([],exp);;

let rec formula_parser exp = list_parser [bot_parser  ; and_parser formula_parser; or_parser formula_parser; imp_parser formula_parser;
forall_parser formula_parser; exists_parser formula_parser; app_parser term_parser] exp
and
term_parser exp = list_parser [lambda_parser formula_parser; constant_parser; variable_parser] exp;;



let rec mapBool cond list = match list with
 [] -> true
| a:: b -> if (cond a) then (mapBool cond b) else false;;

 
let rec appCheckT term = match term with
  Lambda (x, g) -> appCheckF g 
  |_ -> true
 and  appCheckF form = match form with 
  Forall (x,f) ->  appCheckF f
 | Exists (x,f) -> appCheckF f
 | And (f,g)  ->  (appCheckF f) && (appCheckF g)
 | Or (f,g)    ->   (appCheckF f) && (appCheckF g)
 | Imp (f,g)   ->  (appCheckF f) && (appCheckF g)
 | Neg f     -> appCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  -> ((List.length x) = (List.length l)) && (indVarCheck x) && appCheckF g && (mapBool appCheckT l)
                |Constant (s,arg) -> (List.length l) = (arity arg) && (mapBool appCheckT l)  
                |Variable (s,(arg,i)) -> (List.length l) = (arity arg)) && (mapBool appCheckT l)
 |_ -> true;;



let rec quantCheckT term = match term with
  Lambda (x, g) -> quantCheckF g 
  |_ -> true
 and  quantCheckF form = match form with 
  Forall (x,f) ->  (match x with
                         Variable (a,(b,i)) -> quantCheckF f
                         |_ -> true)
 | Exists (x,f) ->  (match x with
                         Variable (a,(b,i)) -> quantCheckF f
                         |_ -> true)
 | And (f,g)  ->  (quantCheckF f) && (quantCheckF g)
 | Or (f,g)    ->   (quantCheckF f) && (quantCheckF g)
 | Imp (f,g)   ->  (quantCheckF f) && (quantCheckF g)
 | Neg f     -> quantCheckF f
 | App (t,l) -> (match t with 
                  Lambda (x,g)  ->  quantCheckF g && (mapBool quantCheckT l)
                |_ -> mapBool quantCheckT l )
 |_ -> true;;

let checkF exp = (appCheckF exp) && (quantCheckF exp);;

let var_eq v w = match v with
  Variable(s,(arg,i)) -> (match w with 
                           Variable(t,(arg2,j)) ->  s = t 
                           |_ -> false)
  |_ -> false;;

let rec var_mem v list = match list with
  a::b  -> if (var_eq a v) then true else var_mem v list
  |_ -> false;;


let rec freeVariablesF bag form = match form with
  And (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Or (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Imp (f,g) -> freeVariablesF bag f @ freeVariablesF bag g
| Neg f -> freeVariablesF bag f
| Bot ->  []
| Forall (x,f)  ->   freeVariablesF (bag @ [x]) f 
| Exists (x,f)  ->   freeVariablesF (bag @ [x]) f
| App (t,l)  ->  (freeVariablesT bag t) @  (List.concat (List.map (fun x -> freeVariablesT bag x)  l))
and
freeVariablesT bag term = match term with
 Lambda (x,g) ->  freeVariablesF (bag @ x) g
| Variable (s,(arg,i)) -> if not (var_mem (Variable (s,(arg,i))) bag) then [Variable (s,(arg,i))] else []
|_ ->  [] ;;
