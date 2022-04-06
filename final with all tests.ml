(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [("1;", Right (Int 1)); ]

    (* run_free_vars_tests () *)
let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  (Primop (Times, [Var "x"; Var "y"; Int 3; Var "z"]), ["x";"y";"z"]);
  (* f 1 *)
  (Apply (Var "f", Int 1), ["f"]);
  (* let fun f x = x in f 1
  "let fun f : int -> int = fn x :int => x in f 1 end;" *)
  (Let
     ([Val (Rec ("f", TArrow (TInt, TInt), Fn ("x", Some TInt, Var "x")), "f")],
      Apply (Var "f", Int 1)), []);
  (Let
     ([Val (Int 2, "a"); Val (Primop (Times, [Int 1; Var "a"]), "b");
       Val (Primop (Times, [Var "a"; Var "b"]), "c")],
      Primop (Times,
              [Primop (Times, [Primop (Times, [Var "a"; Var "b"]); Var "c"]); Var "d"])), ["d"]);
  (* "let val x = x in y end;" *)
  (Let ([Val (Var "x", "x")], Var "y"), ["x"; "y"]);
  (* "let val (x,y) = (x,y) val (u,v) = (x+y, y) in u+v end;" Piazza 761*)
  (Let
     ([Valtuple (Tuple [Var "x"; Var "y"], ["x"; "y"]);
       Valtuple (Tuple [Primop (Plus, [Var "x"; Var "y"]); Var "y"],
                 ["u"; "v"])],
      Primop (Plus, [Var "u"; Var "v"])), ["x"; "y"]);
]
   
 (* helper functions *)

let extractVarNames (decl : dec) =
          (* return a list of variable names in a dec *)
  match decl with
  | Val (e, v) -> [v]
  | ByName (e, v) -> [v]
  | Valtuple (e, nameList) -> nameList
    
let rec getDecListVarNames (decList : dec list) = 
          (* return a list of variable names in a dec list*)
  match decList with
  | [] -> []
  | x::xs -> union (extractVarNames x) (getDecListVarNames xs)
     
let remove_first_occur (lst: 'a list) (element: 'a) =     
  let rec remove_first_rec (lst: 'a list) (element: 'a) = 
    match lst with
    | [] -> []
    | x::xs -> 
        begin
          if x = element then xs
          else x::(remove_first_rec xs element)
        end 
  in
  remove_first_rec lst element
    
let remove_first_occur_list (lst: 'a list) (elements: 'a list) =
  let rec helper (lst: 'a list) (elements: 'a list) = 
    match elements with
    | [] -> lst
    | x::xs -> helper (remove_first_occur lst x) xs
  in
  helper lst elements 
    
exception InvalidInput
exception Error
(* rename variable in an expression*)
let rec rename (original_name: name) (new_name: name) (e: exp) =
  if original_name = new_name then e
  else
    match e with
    | Var y -> 
        (* if a variable is already using the new name *)
        if y = new_name then raise InvalidInput
        else if y = original_name then Var new_name 
        else Var y
    | Int n -> Int n
    | Bool b -> Bool b
    | If (e, e1, e2) -> If ((rename original_name new_name e), (rename original_name new_name e1), (rename original_name new_name e2))
    | Primop (po, eList) -> 
        let new_eList = List.map (rename original_name new_name) eList in
        Primop (po, new_eList)
    | Tuple eList ->
        let new_eList = List.map (rename original_name new_name) eList in
        Tuple new_eList 
    | Fn (y, Some typ, e) -> 
        (* if a variable is already using the new name *)
        if y = new_name then raise InvalidInput
        else if y = original_name then Fn (new_name, Some typ, (rename original_name new_name e))
        else Fn (y, Some typ, (rename original_name new_name e))
    | Fn (y, None, e) -> 
        (* if a variable is already using the new name *)
        if y = new_name then raise InvalidInput
        else if y = original_name then Fn (new_name, None, (rename original_name new_name e))
        else Fn (y, None, (rename original_name new_name e))
    | Rec (y, typ, e) -> 
        (* if a variable is already using the new name *)
        if y = new_name then raise InvalidInput
        else if y = original_name then Rec (new_name, typ, (rename original_name new_name e))
        else Rec (y, typ, (rename original_name new_name e))
    | Let (decList, e2) -> 
        begin
          let rename_dec (decl : dec) =
          (* return a list of free variable names in a dec *)
            match decl with
            | Val (e, y) -> 
                (* if a variable is already using the new name *)
                if y = new_name then raise InvalidInput
                else if y = original_name then Val ((rename original_name new_name e), new_name)
                else Val ((rename original_name new_name e), y)
            | ByName (e, y) -> 
                (* if a variable is already using the new name *)
                if y = new_name then raise InvalidInput
                else if y = original_name then ByName ((rename original_name new_name e), new_name)
                else ByName ((rename original_name new_name e), y)
            | Valtuple (e, nameList) -> 
                (* if a variable is already using the new name *)
                if (member new_name nameList) then raise InvalidInput
                else if (member original_name nameList) then 
                  let rec rename_vars_in_list (nameList: name list) (original_name: name) (new_name: name) =
                    match nameList with
                    | [] -> []
                    | x::xs ->
                        if x = original_name then new_name::(rename_vars_in_list xs original_name new_name)
                        else x::(rename_vars_in_list xs original_name new_name)
                  in
                  Valtuple ((rename original_name new_name e), (rename_vars_in_list nameList original_name new_name))
                else Valtuple ((rename original_name new_name e), nameList)
          in 
          let rec rename_decls (decls : dec list) =
            match decls with
            | [] -> []
            | x::xs -> (rename_dec x)::(rename_decls xs)
          in
          Let ((rename_decls decList), (rename original_name new_name e2))
        end
    | Apply (e1, e2) -> Apply ((rename original_name new_name e1), (rename original_name new_name e2)) 
    | Anno (e, typ) -> Anno ((rename original_name new_name e), typ)
                         

               
(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = 
  match e with 
  | Var y -> [y]
  | Int n -> []
  | Bool b -> []
  | If (e, e1, e2) -> union (free_vars e) (union (free_vars e1) (free_vars e2))
  | Primop (po, eList) -> 
      List.fold_right (fun e1 -> union (free_vars e1) ) eList [] 
  | Tuple eList -> List.fold_right (fun e1 -> union (free_vars e1) ) eList []
                     (*
                       let rec free_vars_of_list eList =
                         match eList with
                         | [] -> []
                         | x::xs -> union (free_vars x) (free_vars_of_list xs)
                       in
                       free_vars_of_list eList
*)
  | Fn (y, Some typ, e) -> delete [y] (free_vars e)
  | Fn (y, None, e) -> delete [y] (free_vars e)
  | Rec (y, typ, e) -> delete [y] (free_vars e)
  | Let (decList, e2) -> 
      begin
        let free_vars_in_dec (decl : dec) =
          (* return a list of free variable names in a dec *)
          match decl with
          | Val (e, y) -> free_vars e
          | ByName (e, y) -> free_vars e
          | Valtuple (e, nameList) -> free_vars e
        in                     
        let rec free_vars_in_decList (decList : dec list) =
          (* return a list of free variable names in a dec list *)
          match decList with
          | [] -> []
          | x::xs -> 
              union (free_vars_in_dec x) (delete (extractVarNames x) (free_vars_in_decList xs))
        in
        union (free_vars_in_decList decList) (delete (getDecListVarNames decList) (free_vars e2)) 
      end
  | Apply (e1, e2) -> union (free_vars e1) (free_vars e2) 
  | Anno (e, typ) -> free_vars e


let unused_vars_tests : (exp * name list) list = [
  (* x + 1 *)
  (Primop (Plus, [Var "x"; Int 1]), []);
  (* fun x = 1 *)
  (Fn ("x", None, Int 1), ["x"]);
  (* let x = 1 x = 2 in x *)
  (Let ([Val (Int 2, "x"); Val (Int 4, "x")], Var "x"), ["x"]);
  (* let fun f x = 1 in f 100
"let fun f (x : int) : int = 1 in f 100 end;"*)
  (Let
     ([Val (Rec ("f", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 1)), "f")],
      Apply (Var "f", Int 100)), ["x"]);
  (Let
     ([Val
         (Rec ("f", TArrow (TInt, TInt),
               Fn
                 ("x", Some TInt, Primop (Plus, [Var "x"; Apply (Var "f", Var "x")]))),
          "f")],
      Int 1), ["f"]);
  (* "let val (x,y) = (x,y) val (u,v) = (x+y, y) in u+v end;" Piazza 761*)
  (Let
     ([Valtuple (Tuple [Var "x"; Var "y"], ["x"; "y"]);
       Valtuple (Tuple [Primop (Plus, [Var "x"; Var "y"]); Var "y"],
                 ["u"; "v"])],
      Primop (Plus, [Var "u"; Var "v"])), []);
    (* "let fun test (x : int): int = 4 in 4 end;" Piazza 691 *)
  (Let
     ([Val (Rec ("test", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 4)),
            "test")],
      Int 4), ["test"; "x"]);
    (* "let fun test (x : int): int = 4 in test 4 end;" Piazza 691*)
  (Let
     ([Val (Rec ("test", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 4)),
            "test")],
      Apply (Var "test", Int 4)), ["x"]);
  (* "let val x = x in y end;" *)
  (Let ([Val (Var "x", "x")], Var "y"), ["x"]);
  (* "let val x = x-1 in x-1 end;"  Piazza 751 *)
  (Let ([Val (Primop (Minus, [Var "x"; Int 1]), "x")],
        Primop (Minus, [Var "x"; Int 1])), []);
    (* "let val x = true in let val y = 4 in x + 5 end end;" from pdf *)
  (Let ([Val (Bool true, "x")],
        Let ([Val (Int 4, "y")], Primop (Plus, [Var "x"; Int 5]))), ["y"]);
  (* "let val x = 3 in let val x = 4 in x + x end end;" from pdf*)
  (Let ([Val (Int 3, "x")],
        Let ([Val (Int 4, "x")], Primop (Plus, [Var "x"; Var "x"]))), ["x"]);
  
]

(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = 
  let rec unused_vars_in_list (lst: exp list) : name list =
    match lst with
    | [] -> []
    | x::xs -> (unused_vars x) @ (unused_vars_in_list xs)
  in
  match e with 
  | Var y -> []
  | Int n -> []
  | Bool b -> []
  | If (e, e1, e2) -> (unused_vars e) @ ((unused_vars e1) @ (unused_vars e2))
  | Primop (po, eList) -> unused_vars_in_list eList
  | Tuple eList -> unused_vars_in_list eList 
  | Fn (y, Some typ, e) -> 
      (* If x is a free variable of e, x is used in e. Else it is unused *)
      if (member y (free_vars e))
      then (unused_vars e)
      else y::(unused_vars e) 
  | Fn (y, None, e) -> 
      if (member y (free_vars e))
      then (unused_vars e)
      else y::(unused_vars e)  
  | Rec (y, typ, e) -> 
      if (member y (free_vars e))
      then (unused_vars e)
      else (unused_vars e)
  | Let (decList, e2) -> 
      begin 
        let unused_vars_in_dec (decl : dec) =
          (* return a list of unused variable names in a dec *)
          match decl with
          | Val (e, y) -> y::unused_vars e
          | ByName (e, y) -> y::unused_vars e
          | Valtuple (e, nameList) -> nameList @ unused_vars e
        in 
        let rec remove_vars_if_used (e : exp) (varList: name list) (checkList: name list) = 
          (* remove variables from list if they are used in e *)
          match checkList with
          | [] -> varList
          | x::xs -> 
              if (member x (free_vars e))
              then remove_vars_if_used e (remove_first_occur varList x) xs
              else remove_vars_if_used e varList xs
        in
        let update_varList (decl : dec) (varList: name list) =
          (* see if elements of varList are in free_vars of dec and remove if they are *)
          match decl with
          | Val (e, y) -> remove_vars_if_used e varList varList
          | ByName (e, y) -> remove_vars_if_used e varList varList
          | Valtuple (e, nameList) -> remove_vars_if_used e varList varList
        in 
        let rec unused_vars_in_decList (decList : dec list) (varList: name list) =
          (* return a list of unused variable names in a dec list *) 
          match decList with
          | [] -> varList
          | x::xs -> 
              let new_varList = update_varList x varList in
              unused_vars_in_decList xs ((unused_vars_in_dec x) @ new_varList)
        in 
        let unused_decList = unused_vars_in_decList decList [] in
        (*
          Printf.printf ("unused_decList: ");
          List.iter (Printf.printf "%s, ") unused_decList;
          print_newline ();
        *)
        (remove_first_occur_list unused_decList (free_vars e2)) @ (unused_vars e2)
      end
  | Apply (e1, e2) -> union (unused_vars e1) (unused_vars e2) 
  | Anno (e, typ) -> unused_vars e

;;

reset_ctr ();;
let subst_tests : (((exp * name) * exp) * exp) list = [
  (* "let val a = 2 + a in a+b end;" [z/a] *)
  (((Var "z", "a"), (Let ([Val (Primop (Plus, [Int 2; Var "a"]), "a")],
                          Primop (Plus, [Var "a"; Var "b"])))), 
   (Let ([Val (Primop (Plus, [Int 2; Var "z"]), "1a")],
         Primop (Plus, [Var "1a"; Var "b"]))));
  (* "let val a = 2 + a in a+b end;" [z/b] *)
  (((Var "z", "b"), (Let ([Val (Primop (Plus, [Int 2; Var "a"]), "a")],
                          Primop (Plus, [Var "a"; Var "b"])))), 
   (Let ([Val (Primop (Plus, [Int 2; Var "a"]), "2a")],
         Primop (Plus, [Var "2a"; Var "z"]))));
  (* "let val a = 2 + a val a = 3 + a in a+b end;" [z/a] *)
  (((Var "z", "a"), (Let
                       ([Val (Primop (Plus, [Int 2; Var "a"]), "a");
                         Val (Primop (Plus, [Int 3; Var "a"]), "a")],
                        Primop (Plus, [Var "a"; Var "b"])))), 
   (Let
      ([Val (Primop (Plus, [Int 2; Var "z"]), "3a");
        Val (Primop (Plus, [Int 3; Var "3a"]), "4a")],
       Primop (Plus, [Var "4a"; Var "b"]))));
  (* "let val a = 2 + a val a = 3 + b in a+b end;" [z/b] *)
  (((Var "z", "b"), (Let
                       ([Val (Primop (Plus, [Int 2; Var "a"]), "a");
                         Val (Primop (Plus, [Int 3; Var "b"]), "a")],
                        Primop (Plus, [Var "a"; Var "b"])))), 
   (Let
      ([Val (Primop (Plus, [Int 2; Var "a"]), "5a");
        Val (Primop (Plus, [Int 3; Var "z"]), "6a")],
       Primop (Plus, [Var "6a"; Var "z"]))));
  (* "let val a = 2 + a val a = (let val a = a in a end) in a+b end;" [z/a] *)
  (* "let val d = 2 + z val e = (let val f = d in f end) in e+b end;" *)
  (((Var "z", "a"), (Let
                       ([Val (Primop (Plus, [Int 2; Var "a"]), "a");
                         Val (Let ([Val (Var "a", "a")], Var "a"), "a")],
                        Primop (Plus, [Var "a"; Var "b"])))), 
   (Let
      ([Val (Primop (Plus, [Int 2; Var "z"]), "7a");
        Val (Let ([Val (Var "7a", "9a")], Var "9a"), "8a")],
       Primop (Plus, [Var "8a"; Var "b"]))));
  (* let fun f x = 1 in f 100
  "let fun f (x : int) : int = 1 in f 100 end;" [z/f] *)
  (((Var "z", "f"), (Let
                       ([Val (Rec ("f", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 1)), "f")],
                        Apply (Var "f", Int 100)))), 
   (Let
      ([Val (Rec ("f", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 1)), "f")],
       Apply (Var "f", Int 100))));
  
]

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp = 
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (ds, e2) -> 
      begin 
        let rec add_new_name (y: name) vars =
          match vars with
          | [] -> [(y, (fresh_var y))]
          | x::xs ->
              let (a, a') = x in
              if y = a (* y already exists in list overwrite it *)
              then (y, (fresh_var y))::xs
              else x::(add_new_name y xs)
        in
        let rec add_new_names (y_list: name list) vars =
          match y_list with
          | [] -> vars
          | x::xs -> add_new_names xs (add_new_name x vars)
        in
        let rec find_new_name (var_name: name) vars =
          match vars with
          | [] -> raise Error
          | x::xs ->
              let (y, y') = x in
              if y = var_name then y'
              else find_new_name var_name xs
        in 
        let rec find_new_names (var_names: name list) vars =
          match var_names with
          | [] -> []
          | x::xs -> (find_new_name x vars)::(find_new_names xs vars)
        in
        let rec rename_vars (e: exp) vars =
          match vars with
          | [] -> e
          | x::xs -> 
              let (y, y') = x in
              rename_vars (rename y y' e) xs
        in
        let rename_vars_in_dec (decl: dec) vars =
          match decl with
          | Val (e1, y) -> 
              let e1' = rename_vars e1 vars in
              let new_vars = add_new_name y vars in
              let y' = find_new_name y new_vars in
              (Val (e1', y'), new_vars)
          | ByName (e1, y) -> 
              let e1' = rename_vars e1 vars in
              let new_vars = add_new_name y vars in
              let y' = find_new_name y new_vars in
              (ByName (e1', y'), new_vars)
          | Valtuple (e1, nameList) ->
              let e1' = rename_vars e1 vars in
              let new_vars = add_new_names nameList vars in
              let new_nameList = find_new_names nameList new_vars in
              (Valtuple (e1', new_nameList), new_vars)
        in
        let rec rename_vars_in_dec_list (decList: dec list) (renamed_list: dec list) vars =
          match decList with
          | [] -> (renamed_list, vars)
          | x::xs -> 
              let (renamed_x, new_vars) = rename_vars_in_dec x vars in
              let new_renamed_list = renamed_list @ [renamed_x] in
              rename_vars_in_dec_list xs new_renamed_list new_vars 
        in 
        
        let subst_dec (decl : dec) = 
          match decl with
          | Val (e1, y) -> Val ((subst (e', x) e1), y)
          | ByName (e1, y) -> ByName ((subst (e', x) e1), y)
          | Valtuple (e1, nameList) -> Valtuple ((subst (e', x) e1), nameList)
        in
        let rec subst_decList (decList: dec list) = 
          match decList with
          | [] -> []
          | x::xs -> (subst_dec x)::(subst_decList xs)
        in
        let (new_ds, vars) = rename_vars_in_dec_list ds [] [] in
        let e2' = rename_vars e2 vars in
        (*
          Printf.printf "before substitution: ";
          print_string (Print.exp_to_string (Let (new_ds, e2')));
          print_newline ();
        *)
        Let ((subst_decList new_ds), (subst (e', x) e2'))
      end
  | Apply (e1, e2) -> Apply ((subst (e', x) e1), (subst (e', x) e2))
  | Fn (y, t, e1) -> if (x = y) then
        let y' = fresh_var y in
        let renamed_e1 = rename y y' e1 in
        Fn (y', t, (subst (e', x) renamed_e1))
      else Fn (y, t, (subst (e', x) e1))
  | Rec (y, t, e1) -> if (x = y) then
        let y' = fresh_var y in
        let renamed_e1 = rename y y' e1 in
        Rec (y', t, (subst (e', x) renamed_e1))
      else Rec (y, t, (subst (e', x) e1)) 
          

let eval_tests : (exp * exp) list = [
  (* "1+1;" *)
  ((Primop (Plus, [Int 1; Int 1])), (Int 2));
  (* "if (1 = 1) then true else false;" *)
  ((If (Primop (Equals, [Int 1; Int 1]), Bool true, Bool false)), (Bool true));
  (* "if (1 = 2 || true) then true else false;" *)
  ((If (Primop (Or, [Primop (Equals, [Int 1; Int 2]); Bool true]), Bool true,
        Bool false)), (Bool true));
  (* "let val x = 1 in x + 1 end;" *)
  ((Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 1]))), (Int 2));
  (* "let fun f : bool -> bool = fn x => x in f false end;" *)
  ((Let
      ([Val (Rec ("f", TArrow (TBool, TBool), Fn ("x", None, Var "x")), "f")],
       Apply (Var "f", Bool false))), (Bool false)); 
  (* "let fun factorial : int -> int = fn n: int => if n <= 1 then 1 else n * factorial (n - 1) in factorial 5 end;" *)
  ((Let
      ([Val
          (Rec ("factorial", TArrow (TInt, TInt),
                Fn
                  ("n", Some TInt,
                   If (Primop (LessEqual, [Var "n"; Int 1]), Int 1,
                       Primop (Times,
                               [Var "n";
                                Apply (Var "factorial", Primop (Minus, [Var "n"; Int 1]))])))),
           "factorial")],
       Apply (Var "factorial", Int 5))), (Int 120));
]

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
      | Apply (e1, e2) -> 
          begin
            let e1' = eval e1 and e2' = eval e2 in
            match e1' with
            | Fn (y, t, e) -> eval (subst (e2', y) e)
            | _ -> stuck "first argument to Apply operation is not a function"
          end
      | Rec (f, t, e) -> eval (subst (Rec (f, t, e), f) e) 
      | Primop (And, es) -> 
          begin 
            if List.length es <> 2 then stuck "need two arugments to And operation" else
              let vs = List.map eval es in
              match vs with
              | [Bool false; _ ] -> Bool false
              | [Bool true; v] -> v
              | _ -> stuck "bad arguments to And operation" 
          end
      | Primop (Or, es) ->
          begin 
            if List.length es <> 2 then stuck "need two arugments to Or operation" else
              let vs = List.map eval es in
              match vs with
              | [Bool true; _ ] -> Bool true
              | [Bool false; v] -> v 
              | _ -> stuck "bad arguments to Or operation" 
          end   
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end 
      | Let (ds, e) -> 
          begin
            match ds with
            | [] -> eval e
            | x::xs -> 
                begin
                  match x with
                  | Val (e1, y) -> eval(subst (e1, y) (Let (xs, e)))
                  | ByName (e1, y) -> eval(subst (e1, y) (Let (xs, e)))
                  | Valtuple (e1, nameList) -> 
                      begin 
                        match e1 with
                        | Tuple es -> if (List.length es <> List.length nameList) then stuck "number of expressions doesn't match number of variables in valtuple"
                            else 
                              let rec subst_list (e: exp) (eList: exp list) (nameList: name list) =
                                match eList with
                                | [] -> e
                                | y::ys -> 
                                    begin
                                      match nameList with
                                      | [] -> stuck "error in evaluating valtuple in Let expression"
                                      | z::zs -> subst_list (subst (y, z) e) ys zs
                                    end
                              in
                              let new_e = subst_list (Let (xs, e)) es nameList in
                              eval(new_e)
                        | _ -> stuck "error in evaluating Let expression"
                      end
                end
          end
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result 

let unify_tests : ((typ * typ) * unit) list = [
] 

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let unify (ty1 : typ) (ty2 : typ) : unit = 
  let rec unify_rec (ty1 : typ) (ty2 : typ) : unit =
    let rec unify_list (typ_list1 : typ list) (typ_list2 : typ list) = 
      match typ_list1 with
      | [] -> ()
      | x::xs -> begin
          match typ_list2 with
          | [] -> type_fail "cannot unify two TProduct with different lengths"
          | y::ys -> unify_rec x y; unify_list xs ys
        end
    in
    match ty1 with
    | TArrow (t1, t2) -> 
        begin
          match ty2 with
          | TArrow (t3, t4) -> unify_rec t1 t3; unify_rec t2 t4
          | TProduct tList2 -> type_fail "TArrow cannot unify with TProduct"
          | TInt -> type_fail "TArrow cannot unify with TInt"
          | TBool -> type_fail "TArrow cannot unify with TBool"
          | TVar tOption_ref -> 
              begin
                match !tOption_ref with
                | Some t ->
                    begin
                      match t with
                      | TArrow (t3, t4) -> unify_rec t1 t3; unify_rec t2 t4;
                          tOption_ref := Some (TArrow (t3, t4))
                      | _ -> type_fail "TArrow could not unify with TVar"
                    end
                | None -> tOption_ref := Some ty1
              end
        end
    | TProduct tList -> 
        begin
          match ty2 with
          | TArrow (t1, t2) -> type_fail "TProduct cannot unify with TArrow(t1, t2)"
          | TProduct tList2 -> 
              if (List.length tList) <> (List.length tList2) then type_fail "cannot unify two TProduct with different lengths"
              else unify_list tList tList2
          | TInt -> type_fail "TProduct cannot unify with TInt"
          | TBool -> type_fail "TProduct cannot unify with TBool"
          | TVar tOption_ref -> 
              begin
                match !tOption_ref with
                | Some t ->
                    begin
                      match t with
                      | TProduct tList2 -> 
                          if (List.length tList) <> (List.length tList2) then type_fail "cannot unify two TProduct with different lengths"
                          else unify_list tList tList2; tOption_ref := Some (TProduct tList2)
                      | _ -> type_fail "TProduct could not unify with TVar"
                    end
                | None -> tOption_ref := Some ty1
              end
        end
    | TInt -> 
        begin
          match ty2 with
          | TArrow (t1, t2) -> type_fail "TInt cannot unify with TArrow(t1, t2)"
          | TProduct tList -> type_fail "TInt cannot unify with TProduct(t1, t2)"
          | TInt -> ()
          | TBool -> type_fail "TInt cannot unify with TBool"
          | TVar tOption_ref -> 
              begin
                match !tOption_ref with
                | Some t ->
                    begin
                      match t with
                      | TInt -> ()
                      | _ -> type_fail "TInt could not unify with TVar"
                    end
                | None -> tOption_ref := Some TInt
              end
        end
    | TBool -> 
        begin
          match ty2 with
          | TArrow (t1, t2) -> type_fail "TBool cannot unify with TArrow(t1, t2)"
          | TProduct tList -> type_fail "TBool cannot unify with TProduct(t1, t2)"
          | TInt -> type_fail "TBool cannot unify with TInt"
          | TBool -> ()
          | TVar tOption_ref -> 
              begin
                match !tOption_ref with
                | Some t ->
                    begin
                      match t with
                      | TBool -> ()
                      | _ -> type_fail "TBool could not unify with TVar"
                    end
                | None -> tOption_ref := Some TBool
              end
        end
    | TVar tOption_ref -> 
        begin
          match !tOption_ref with
          | Some t ->
              begin
                match ty2 with
                | TArrow (t1, t2) -> 
                    begin
                      match t with
                      | TArrow (t3, t4) -> 
                          unify_rec t1 t3; unify_rec t2 t4;
                          tOption_ref := Some (TArrow (t3, t4))
                      | _ -> type_fail "TVar could not unify with TArrow"
                    end
                | TProduct tList -> 
                    begin
                      match t with
                      | TProduct tList2 -> 
                          if (List.length tList) <> (List.length tList2) then type_fail "cannot unify two TProduct with different lengths"
                          else unify_list tList tList2; tOption_ref := Some (TProduct tList2)
                      | _ -> type_fail "TVar could not unify with TList"
                    end
                | TInt -> 
                    begin
                      match t with
                      | TInt -> ()
                      | _ -> type_fail "TVar could not unify with TInt"
                    end
                | TBool ->
                    begin
                      match t with
                      | TBool -> ()
                      | _ -> type_fail "TVar could not unify with TBool"
                    end
                | TVar tOption_ref2 -> unify_rec t ty2; tOption_ref := Some ty2
              end
          | None -> tOption_ref := Some ty2
        end
  in
  unify_rec ty1 ty2    

let ctx = Ctx []
let infer_tests : ((context * exp) * typ) list = [ 
  ((ctx, (Int 1)), TInt);
  (* "if 1 + 2 = 3 then true else false;" *)
  ((ctx, (If (Primop (Equals, [Primop (Plus, [Int 1; Int 2]); Int 3]), Bool true,
              Bool false))), TBool);
  (* "fn x: int => 3*x + 2;" *)
  ((ctx, (Fn
            ("x", Some TInt, Primop (Plus, [Primop (Times, [Int 3; Var "x"]); Int 2])))), TArrow (TInt, TInt));
  (* "let val x = 1 in x + 1 end;" *)
  ((ctx, (Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 1])))), TInt);
  
  (* "let fun f (x : int) : int = 1 in f 100 end;" *)
  ((ctx, (Let
            ([Val (Rec ("f", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 1)), "f")],
             Apply (Var "f", Int 100)))), TInt);
  (* "let fun factorial : int -> int = fn n: int => if n <= 1 then 1 else n * factorial (n - 1) in factorial 5 end;" *)
  ((ctx, (Let
            ([Val
                (Rec ("factorial", TArrow (TInt, TInt),
                      Fn
                        ("n", Some TInt,
                         If (Primop (LessEqual, [Var "n"; Int 1]), Int 1,
                             Primop (Times,
                                     [Var "n";
                                      Apply (Var "factorial", Primop (Minus, [Var "n"; Int 1]))])))),
                 "factorial")],
             Apply (Var "factorial", Int 5)))), TInt);
  (* fun x -> x + 1*)
  ((ctx, (Fn ("x", None, Primop (Plus, [Var "x"; Int 1])))), TArrow (TVar {contents = Some TInt}, TInt));
]

(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let infer (ctx : context) (e : exp) : typ = 
  let rec infer_rec (ctx : context) (e : exp) : typ =
    let rec infer_exp_list (es: exp list) (ctx : context) : typ list =
      match es with
      | [] -> []
      | x::xs -> (infer_rec ctx x)::(infer_exp_list xs ctx)
    in
    match e with
    | Int n -> TInt
    | Bool b -> TBool
    | If (e1, e2, e3) ->
        if (infer_rec ctx e1) = TBool then
          let t2 = (infer_rec ctx e2) and t3 = (infer_rec ctx e3) in
          if (t2 = t3) then t2
          else type_fail "both return expressions in If statement must result in the same type"
        else type_fail "first expression of If statement does not result in a Bool"
    | Primop (po, es) -> 
        begin
          let rec type_list = infer_exp_list es ctx in
          match po with
          | Plus | Minus | Times | Div ->
              begin
                match type_list with
                | [TInt; TInt] -> TInt
                | [TInt; t1] -> (unify TInt t1); TInt
                | [t1; TInt] -> (unify t1 TInt); TInt
                | _ -> type_fail "incorrect input types for primop"
              end
          | Equals | NotEquals | LessThan | LessEqual | GreaterThan | GreaterEqual ->
              begin
                match type_list with
                | [TInt; TInt] -> TBool
                | [TInt; t1] -> (unify TInt t1); TBool
                | [t1; TInt] -> (unify t1 TInt); TBool
                | _ -> type_fail "incorrect input types for primop"
              end
          | And | Or ->
              begin
                match type_list with
                | [TBool; TBool] -> TBool
                | [TBool; t1] -> (unify TBool t1); TBool
                | [t1; TBool] -> (unify t1 TBool); TBool
                | _ -> type_fail "incorrect input types for primop"
              end
          | Negate -> 
              begin
                match type_list with
                | [TInt] -> TInt
                | _ -> type_fail "incorrect input types for primop"
              end
        end 
    | Tuple es -> TProduct (infer_exp_list es ctx)
    | Fn (x, t, e) ->
        begin
          match t with
          | Some t' ->
              let Ctx ctx_list = ctx in
              let new_ctx = Ctx ((x, t')::ctx_list) in
              let exp_type = infer_rec new_ctx e in
              TArrow (t', exp_type)
          | None -> 
              let Ctx ctx_list = ctx in
              let tv = fresh_tvar () in 
              let new_ctx = Ctx ((x, tv)::ctx_list) in
              let exp_type = infer_rec new_ctx e in
              unify tv exp_type;
              TArrow (tv, exp_type) 
        end 
    | Rec (f, t, e) -> 
        let Ctx ctx_list = ctx in
        let new_ctx = Ctx ((f, t)::ctx_list) in 
        infer_rec new_ctx e 
    | Let (ds, e) ->
        let infer_dec (decl: dec) (ctx: context) : (name * typ) list =
          match decl with
          | Val (e1, y) -> [(y, (infer_rec ctx e1)) ]
          | ByName (e1, y) -> [(y, (infer_rec ctx e1))]
          | Valtuple (e1, nameList) -> 
              let type_e1 = infer_rec ctx e1 in
              let rec add_to_list (nameList: name list) (tList: typ list) =
                match nameList with
                | [] -> []
                | x::xs -> 
                    begin
                      match tList with
                      | [] -> type_fail "number of expressions and variables in valtuple doesn't match"
                      | y::ys -> (x, y)::(add_to_list xs ys)
                    end 
              in 
              begin
                match type_e1 with
                | TProduct ts -> if (List.length ts <> List.length nameList) then type_fail "number of expressions and variables in valtuple doesn't match"
                    else add_to_list nameList ts
                | _ -> type_fail "not enough expressions in valtuple"
              end
        in
        let rec infer_dec_list (decList: dec list) (ctx: context) : context =
          match decList with
          | [] -> ctx
          | x::xs -> 
              let dec_type = infer_dec x ctx in
              let Ctx ctx_list = ctx in
              let new_ctx = Ctx (dec_type @ ctx_list) in 
              infer_dec_list xs new_ctx
        in 
        let new_ctx = infer_dec_list ds ctx in
        infer_rec new_ctx e 
    | Apply (e1, e2) ->
        begin
          let type_e1 = infer_rec ctx e1 and type_e2 = infer_rec ctx e2 in
          match type_e1 with
          | TArrow(t, t') ->
              if type_e2 = t then t'
              else type_fail "incorrect expression type for second input of Apply"
          | _ -> type_fail "incorrect expression type for first input of Apply"
        end
    | Var x -> 
        begin
          let Ctx ctx_list = ctx in
          try List.assoc x ctx_list
          with Not_found -> type_fail "type does not exist for this expression"
        end
    | Anno (e, t) -> 
        if (infer_rec ctx e) = t then t
        else type_fail "Expression type and input type does not match for Anno"
  in 
  infer_rec ctx e 


(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *                     Tester template:                     *
 *         Codes to test your interpreter by yourself.      *
 *         You can change these to whatever you want.       *
 *                We won't grade these codes                *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output);
            print_newline ()
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn);
          print_newline ()
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

(* You may want to change this to use the unification (unify) instead of equality (<>) *)
let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
