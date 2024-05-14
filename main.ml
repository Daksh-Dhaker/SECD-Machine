type opcode = LDN of int | LDB of bool | LOOKUP of string | PLUS
              | TIMES | AND | OR | NOT | EQ | GT | COND of (opcode list)*(opcode list) 
              | APP | MKCLOS of string*(opcode list) | RET | PAIR | SND | FST 
              | CASE of (((opcode list)*(opcode list)) list) ;;

type exp = Num of int | Bl of bool | V of string | Plus of exp*exp
           | Times of exp*exp | And of exp*exp | Or of exp*exp | Not of exp
           | Eq of exp*exp | Gt of exp*exp | IfTE of exp*exp*exp
           | Pair of exp*exp | Fst of exp | Snd of exp | Lambda of string*exp | Funct of exp*exp
           | Case of (exp)*((exp*exp) list) ;;

type values = N of int | B of bool | P of values*values 
              | VCLOS of string*(opcode list)*((string*values) list) ;;

type dump = DUMP of (values list)*((string*values) list)*(opcode list);;

exception Stuck of ((string*values) list) * (values list) * (opcode list) * (dump list);;

(*--------------------Helper Functions---------------------------*)
let rec look_up g x = 
  match g with
  | [] -> N 0
  | hd::tl -> let (a,b) = hd in 
              if (a = x) then b else look_up tl x

let rec mem g x = 
  match g with 
  | [] -> false
  | hd::tl -> let (a,b) = hd in 
              if (a = x) then true else (mem tl x)

let rec filter g x a =
  match g with
  | [] -> []
  | hd::tl -> let (c,d) = hd in
              if (c = x) then
                (c,a)::(filter tl x a)
              else
                hd::(filter tl x a)

let augment g x a = 
  if (mem g x) then (filter g x a) else ((x,a)::g)
(*------------------------------------------------------------------*)

(*------------------------Compile Function--------------------------*)
let rec compile e =
  match e with 
  | Num n -> [ LDN n]
  | Bl b -> [LDB b]
  | V x -> [LOOKUP x]
  | Plus (e1,e2) -> (compile e1)@(compile e2)@[PLUS]
  | Times (e1,e2) -> (compile e1)@(compile e2)@[TIMES]
  | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
  | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
  | Not e1 -> (compile e1) @ [NOT]
  | Eq (e1, e2) -> (compile e1) @ (compile e2) @ [EQ]
  | Gt(e1, e2) -> (compile e1) @ (compile e2) @ [GT] 
  | IfTE(e0,e1,e2) -> (compile e0)@[COND(compile e1, compile e2)]
  | Pair (e1,e2) -> (compile e1)@(compile e2)@[PAIR]
  | Fst e1 -> (compile e1)@[FST]
  | Snd e1 -> (compile e1)@[SND]
  | Lambda (x,e1) -> [MKCLOS(x,(compile e1) @ [RET])]
  | Funct (e1,e2) -> (compile e1) @ (compile e2) @ [APP] 
  | Case (e1,l) -> let rec case_compile lst = 
                    match lst with
                    | [] -> []
                    | hd::tl -> let (a,b) = hd in
                              ((compile a),(compile b))::(case_compile tl)
                  in 
                  let compiled_lst = case_compile l in 
                  (compile e1)@[CASE(compiled_lst)]
(*--------------------------------------------------------------*)

(*------------------SECD Machine--------------------------------*)
let rec secd_mc gamma stack comp_list dump = 
  match gamma, stack, comp_list, dump with
  | g, v::_, [], d -> v
  | g, s, (LDN n)::c1, d -> secd_mc g ((N n)::s) c1 d
  | g, s, (LDB b)::c1, d -> secd_mc g ((B b)::s) c1 d
  | g, s, (LOOKUP x)::c1, d -> secd_mc g ((look_up g x)::s) c1 d
  | g, (N n2)::(N n1)::s1, PLUS::c1, d -> secd_mc g ((N (n1+n2))::s1) c1 d
  | g, (N n2)::(N n1)::s1, TIMES::c1, d -> secd_mc g ((N (n1*n2))::s1) c1 d
  | g, (B b2)::(B b1)::s1, AND::c1, d -> secd_mc g (B(b1 && b2)::s1) c1 d
  | g, (B b2)::(B b1)::s1, OR::c1, d -> secd_mc g (B(b1 || b2)::s1) c1 d
  | g, (B b1)::s1, NOT::c1, d -> secd_mc g (B(not b1)::s1) c1 d
  | g, n2::n1::s1, EQ::c1, d -> secd_mc g (B(n1 = n2)::s1) c1 d
  | g, n2::n1::s1, GT::c1, d -> secd_mc g (B(n1 > n2)::s1) c1 d
  | g, (B true)::s1, COND(c1,c2)::c3, d -> secd_mc g s1 (c1 @ c3) d
  | g, (B false)::s1, COND(c1,c2)::c3, d -> secd_mc g s1 (c2 @ c3) d
  | g, a::b::s1, PAIR::c1, d -> secd_mc g (P(b,a)::s1) c1 d 
  | g, P(a,b)::s1, FST::c1, d -> secd_mc g (a::s1) c1 d 
  | g, P(a,b)::s1, SND::c1, d -> secd_mc g (b::s1) c1 d 
  | g, s, MKCLOS(x,c1)::c2, d -> secd_mc g (VCLOS(x,c1,g)::s) c2 d 
  | g, a::VCLOS(x,c1,g1)::s, APP::c2, d -> secd_mc (augment g1 x a) ([]) c1 (DUMP(s,g,c2)::d)
  | g1, a::s1, RET::c1, DUMP(s,g,c2)::d -> secd_mc g (a::s) c2 d 
  | g, a::s1, CASE(l)::c1, d -> let rec compare_case lst x =
                                  match lst with
                                  | [] -> [LDN 0] (*This condition is never reached*)
                                  | hd::tl -> let (b,c) = hd in 
                                              let eval_exp = secd_mc gamma [] b [] in
                                              if (eval_exp = x) then c else (compare_case tl x)
                                in
                                let c2 = compare_case l a in 
                                secd_mc g s1 (c2 @ c1) d
  | _, _, _, _ -> raise (Stuck (gamma,stack,comp_list,dump))

(*----------------------------------------------------------------------------------------*)
(*----------------------------------TestCases-------------------------------------------- *)
(*
            (Testing of Plus and Times)
1. let e1 = Plus(V "x",Times(V "y",Plus(V "z",Num 2)));;   
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e1) [];; -> values = N 1021

            (Testing of And, Or and Not)
2. let e1 = And(Bl true,Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e1) [];; -> values = B true

3. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e1) [];; -> values = B true

            (Testing of IfTE (if then else construct))
4. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   Ans -> secd_mc g [] (compile e2) [];; -> values = P (N 1, B true)

5. let e1 = And(Eq(V "a",(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   Ans -> secd_mc g [] (compile e2) [];; -> values = B false

            (Testing of Pair and Projection constructs (Pair, Fst and Snd))
6. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   let e3 = Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a")));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e3) [];; -> values = P (P (B true, P (N 1, B true)), B true)

7. let e1 = And(Eq(V "a",(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   let e3 = Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a")));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e3) [];; -> values = P (P (B false, B false), B true)

8. let e1 = And(Eq(V "a",(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   let e3 = Fst(Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a"))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e3) [];; -> values = P (B false, B false)

9. let e1 = And(Eq(V "a",Not(Bl false)),Or(V "b",And(V "c",Not(V "d"))));;
   let e2 = IfTE(e1,Pair(Num 1,V "a"),e1);;
   let e3 = Fst(Snd(Fst(Pair(Pair(e1,e2),Snd(Pair(Pair(Num 1,V "x"),V "a"))))));;
   let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
   Ans -> secd_mc g [] (compile e3) [];; -> values = N 1

            (Testing of Lambda functions (Lambda and Funct constructs))
10. let e4 = Lambda("x",Plus(Num 1,V "x"));;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e4) [];; -> values = VCLOS ("x", [LDN 1; LOOKUP "x"; PLUS; RET],
                                                      [("x", N 1); ("y", N 10); ("z", N 100); ("a", B true);
                                                       ("b", B false); ("c", B true); ("d", B false)])

11. let e4 = Funct(Lambda("x",Plus(Num 1,V "x")),Num 2);;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e4) [];; -> values = N 3

12. let e4 = Funct(Lambda("d",Funct(Lambda("c",(Pair(V "c",V "d"))),Plus(Num 1,V "x"))),V "y");;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e4) [];; -> values = P (N 2, N 10)

13. let e4 = Funct(Lambda("x",Plus(V "x",Num 1)),Snd(Funct(Lambda("d",Funct(Lambda("c",(Pair(V "c",V "d"))),Num 1)),V "y")));;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e4) [];; -> values = N 11

                        (Testing of Case Construct)
14. let e1 = Case(Plus(Num 1,Times(Num 2,Num 3)),[(Plus(V "x",Num 4),Num 1);(Times(V "x",V "y"),Num 2);(Plus(Num 6,V "x"),Num 3);(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e1) [];; -> values = N 3

15. let e1 = Case(Plus(Num 1,Times(Num 2,Num 3)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e1) [];; -> values = N 34

16. let e1 = Case(Plus(Num 1,Times(Num 1,Num 9)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e1) [];; -> values = B false

17. let e1 = Case(Plus(Num 1,Times(Num 1,Num 4)),[(Plus(V "x",Num 4),Or(V "a",V "b"));(Times(V "x",V "y"),And(V "a",V "d"));(Plus(Num 6,V "x"),Plus(Num 1,Num 33));(Plus(Num 1,Num 2),Num 4)]);;
    let g = [("x",N 1);("y",N 10);("z",N 100);("a",B true);("b",B false);("c",B true);("d",B false)];;
    Ans -> secd_mc g [] (compile e1) [];; -> values = B true

 *)