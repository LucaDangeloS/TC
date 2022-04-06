(* 1) 
*)

let rec mapdoble f1 f2 l =
    match l with
        [] -> []
    |   h::[] -> (f1 h)::[]
    |   h1::h2::t -> (f1 h1)::(f2 h2)::(mapdoble f1 f2 t);;

mapdoble (function x -> x) (function x -> -x) [1;1;1;1;1];;

(* 
Tipo de funcion:
val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun>
*)

(*  
Valor de:
mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;

Error: This expression has type string but an expression was expected of type
         int
*)

(*
Tipo de:
let y = function x -> 5 in mapdoble y;;

- : ('_weak1 -> int) -> '_weak1 list -> int list = <fun>
*)


(* 2)
*)

let rec primero_que_cumple f l =
    match l with
        [] -> None
    |   h::t -> if (f h) = true then Some h
                else primero_que_cumple (f) (t);;

(*
Tipo de:

val primero_que_cumple : ('a -> bool) -> 'a list -> 'a option = <fun>
*)

let existe f l = 
    match primero_que_cumple f l with
        None -> false
    |   Some x -> true;;
        

let asociado l e =
    let res = primero_que_cumple (function (x1, x2) -> if x1 = e then true else false) l in
        match res with
            Some (x, y) -> y
        |   None -> raise (Not_found);;


(* 3)
*)

type 'a arbol_binario =
    Vacio
    | Nodo of 'a * 'a arbol_binario * 'a arbol_binario;;

let t = 
Nodo(3, 
    Nodo(2, 
        Vacio, 
        Vacio
        ), 
    Nodo(5, 
        Nodo(4, Vacio, Vacio), 
        Nodo(1, Vacio, Vacio)
        )
)

let rec in_orden = function
        Vacio -> []
    |   Nodo (v, izq, der) -> in_orden izq @ (v :: in_orden der);;

in_orden t;;

let rec pre_orden = function
    Vacio -> []
|   Nodo (v, izq, der) -> v::(pre_orden izq @ pre_orden der);;

pre_orden t;;

let rec post_orden = function
    Vacio -> []
|   Nodo (v, izq, der) -> post_orden izq @ post_orden der @ [v];;

post_orden t;;

let rec anchura arbol = let 
    rec aux to_visit accumulative = match to_visit with 
        [] -> accumulative
    |   h::t -> match h with
            Vacio -> aux t accumulative
        |   Nodo (v, izq, der) -> aux (t @ [izq] @ [der]) (accumulative @ [v])
    in
    aux [arbol] [];;

anchura t;;

(* 4)
*)

type 'a conjunto = Conjunto of 'a list;;
let conjunto_vacio = Conjunto [];;
(*let test = Conjunto [1;2;3;4];;
let test2 = Conjunto [5;2;3;4;7];;
let test_list = [1;1;2;2;3;4;5;5;6];; 
    Conjuntos y listas usadas para testing
*)

let rec pertenece x = function
    Conjunto l -> match l with
        [] -> false
    |   h::t -> if h=x then true
        else pertenece x (Conjunto t);;

let rec agregar x = 
    let rec presente x2 l = match l with
        [] -> false
    |   h2::t2 -> if h2=x2 then true
    else presente x2 t2
    in
    function Conjunto l -> match l with 
        [] -> Conjunto [x]
    |   h::t -> if x=h || presente x t 
                then Conjunto l
                else Conjunto (x::l);;


let conjunto_of_list input =
    let rec aux pre_c = function
    l -> match l with
            []      -> pre_c
        |   h::t    -> aux (agregar h pre_c) t
in aux (Conjunto []) input;;

let suprimir x l =
    let rec aux l_before = function
    Conjunto l -> match l with
        []      -> Conjunto l
    |   h::t    -> if h = x then Conjunto (l_before@t)
    else aux (h::l_before) (Conjunto t) in

    aux [] l;;

let cardinal c = 
    let rec aux n  = function
    Conjunto l -> match l with
            []      -> n
        |   h::t    -> aux (n+1) (Conjunto t) 
    in

    aux 0 c;;

let union c1 c2 =  
    let rec presente x l = match l with
        [] -> false
        |   h::t -> if h=x then true
            else presente x t
    in
    let rec construir (Conjunto c1) (Conjunto c2) = match (c1, c2) with
            ([], _) -> Conjunto c2
        |   (_, []) -> Conjunto c1
        |   (h1::t1, _) -> if presente h1 c2
                                then construir (Conjunto t1) (Conjunto c2)
                                else construir (Conjunto t1) (Conjunto (h1::c2))
    in
    construir c1 c2;;

let interseccion c1 c2 =  
    let rec presente x l = match l with
        [] -> false
        |   h::t -> if h=x then true
            else presente x t
    in
    let rec construir (Conjunto c1) (Conjunto c2) c3 = match (c1, c2, c3) with
            ([], [], _) -> Conjunto c3
        |   (h::t, [], _) | ([], h::t, _) -> Conjunto c3
        |   (h1::t1, _, _) -> if presente h1 c2
                                then construir (Conjunto t1) (Conjunto c2) (h1::c3)
                                else construir (Conjunto t1) (Conjunto c2) c3
    in
    construir c1 c2 [];;


let diferencia c1 c2 =  
    let rec presente x l = match l with
        [] -> false
        |   h::t -> if h=x then true
            else presente x t
    in
    let rec construir (Conjunto c1) (Conjunto c2) c3 = match (c1, c2, c3) with
            ([], [], _) -> Conjunto c3
        |   ([], h::t, _) -> Conjunto c3
        |   (h1::t1, _, _) -> if presente h1 c2
                                then construir (Conjunto t1) (Conjunto c2) c3
                                else construir (Conjunto t1) (Conjunto c2) (h1::c3)
    in
    construir c1 c2 [];;

let incluido (Conjunto c1) (Conjunto c2) =  
    let rec presente x l = match l with
    [] -> false
    |   h::t -> if h=x then true
        else presente x t
    in
    let rec aux c1 c2 = match (c1, c2) with
        ([], _) -> true
    |   (h::t, _) -> if presente h c2
                    then aux t c2
                    else false
    in
    aux c1 c2;;

let igual (Conjunto c1) (Conjunto c2) =  
    let rec presente x l = match l with
    [] -> false
    |   h::t -> if h=x then true
        else presente x t
    in
    let rec aux c1 c2 = match (c1, c2) with
        ([], _) -> true
    |   (h::t, _) -> if presente h c2
                    then aux t c2
                    else false
    in
    if aux c1 c2 && aux c2 c1
        then true
        else false;;

let producto_carteasiano (Conjunto c1) (Conjunto c2) =
    let rec aux c1 c2 c3 = match (c1, c2) with
        ([], []) -> Conjunto c3
    |   ([], _) | (_, []) -> raise (Invalid_argument "Conjuntos tienen que ser del mismo cardinal")
    |   (h1::t1, h2::t2) -> aux t1 t2 ((h1,h2)::c3)
    in
    aux c1 c2 [];;

let list_of_conjunto = function Conjunto c -> c;;