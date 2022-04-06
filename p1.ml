#load "talf.cma";;
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(* 
Af (Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
    Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
    Estado "0",
    Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a");
              Arco_af (Estado "1", Estado "1", Terminal "b");
              Arco_af (Estado "1", Estado "2", Terminal "a");
              Arco_af (Estado "2", Estado "0", Terminal "");
              Arco_af (Estado "2", Estado "3", Terminal "");
              Arco_af (Estado "2", Estado "3", Terminal "c")],
    Conjunto [Estado "1"; Estado "3"])
*)

let a1 = af_of_string "0 1; a b; 0; 0; 0 1 a; 0 1 b; 1 0 a; 1 0 b;";;
let a2 = af_of_string "0 1; a b; 0; 1; 0 0 a; 0 0 b; 0 1 b;";;


let input = cadena_of_string "a a b";;

let estados_to_string conjest =
    let rec aux string = function
        | Conjunto [] -> string
        | Conjunto ((Estado h)::t) -> aux (string ^ h ^ " ") (Conjunto t) (* Estado of string *)
    in aux "" conjest;;

(* let convert_ *)

(* Auto.simbolo list -> Auto.af -> bool *)
let traza_af input (Af (_, _, q0, _, qf) as af) =
    let rec aux = function
        (Conjunto [], _) -> false
        
    | (curr, []) -> 
            (print_endline ("("^(estados_to_string curr) ^ ", )");
            not (es_vacio (interseccion curr qf)))

    | (curr, s::t) -> 
            print_endline ("("^(estados_to_string curr) ^ ", " ^ (string_of_cadena (s::t))^")");
            aux ((epsilon_cierre (avanza s curr af) af), t)

    in aux ((epsilon_cierre (Conjunto [q0]) af), input);;


traza_af input a1;; (* false *) 
traza_af input a2;; (* true *)

(* ----------------------------------------------------------------- *)

let calcular_cartesiano_arcos arcos1 arcos2 = 
    let cart = cartesiano arcos1 arcos2 in
    let rec aux acum c = match c with
    | Conjunto [] -> conjunto_of_list acum
    | Conjunto ((Arco_af (Estado e1, Estado e2, t1), Arco_af (Estado e3, Estado e4, t2))::t) -> 
        if t1 = t2 then aux ((Arco_af (Estado (e1^e3), Estado (e2^e4), t1))::acum) (Conjunto t) (* ((Arco_af (e1, e2, t1))::(Arco_af (e3, e4, t1))::acum) *)
        else aux acum (Conjunto t) in 
    aux [] cart;;
    

let cartesiano_estado0 (Estado q01) (Estado q02) = 
    Estado (q01 ^ q02);;

let calcular_cartesiano_estados estados1  estados2  = 
    let cart = cartesiano estados1 estados2 in
    let rec aux acum c = match c with
    | Conjunto [] -> conjunto_of_list acum
    | Conjunto ((Estado e1, Estado e2)::t) -> aux ((Estado (e1^e2))::acum) (Conjunto t) in 
    aux [] cart;;


(* Auto.af -> Auto.af -> Auto.af *)
let cartesiano_af (Af (estados1, acciones1, q01, arcos1, qf1))
    (Af (estados2, acciones2, q02, arcos2, qf2)) = 
    let new_arcos = calcular_cartesiano_arcos arcos1 arcos2 in
    let new_estados = calcular_cartesiano_estados estados1 estados2 in
    let new_goals = calcular_cartesiano_estados qf1 qf2 in
    let new_q0 = cartesiano_estado0 q01 q02 in
    Af (new_estados, union acciones1 acciones2, new_q0, new_arcos, new_goals);;


(* Auto.af -> Auto.af -> Auto.af *)
let ej_1 = Conjunto
[Arco_af (Estado "0", Estado "1", Terminal "a");
 Arco_af (Estado "0", Estado "1", Terminal "b");
 Arco_af (Estado "1", Estado "0", Terminal "a");
 Arco_af (Estado "1", Estado "0", Terminal "b")];;

 let ej_2 = Conjunto
 [Arco_af (Estado "0", Estado "0", Terminal "a");
  Arco_af (Estado "0", Estado "0", Terminal "b");
  Arco_af (Estado "0", Estado "1", Terminal "b")];;

calcular_cartesiano_arcos ej_1 ej_2;;

(* Auto.af -> Auto.af -> bool *)
    
let a12 = cartesiano_af a1 a2;;

escaner_af (cadena_of_string "a b b a b") a12;;
(* false *)
escaner_af (cadena_of_string "a b a b") a12;;
(* true *)
escaner_af (cadena_of_string "a a b b b b b a") a12;;
(* false *)

traza_af (cadena_of_string "a b a b a b") a12;;


let a3 = af_of_string "0 1 2 3; a b; 0; 3; 0 1 a; 1 2 b; 2 3 a; 0 0 b; 1 1 a; 2 0 b; 3 2 b; 3 1 a;";; (* aba *)
let a4 = af_of_string "0 1 2 3 4; a b c; 0; 4; 0 1 a; 1 2 a; 2 3 a; 3 4 a;
                                                 0 0 b; 1 1 b; 2 2 b; 3 3 b; 4 4 b; 
                                                 0 0 c; 1 1 c; 2 2 c; 3 3 c; 4 4 c; 4 4 a;";; (* al menos 4 aes *)



let a34 = cartesiano_af a3 a4;;

traza_af (cadena_of_string "") a12;;
dibuja_af ~titulo:"(a U b)*aba" a3;;
dibuja_af ~titulo:"aaaa" a4;;
dibuja_af ~titulo:"a34" a34;;