(* #load "talf.cma";; *)
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

(* Ap:
    Conjunto de estados,
    Alfabeto de simbolos terminales de entrada,
    Alfabeto de la pila,
    Estado inicial,
    Conjunto de funciones de transicion,
    Simbolo de inicio de la pila,
    Conjunto de estados finales

    transicion -> (
      estado origen, 
      estado destino, 
      simbolo terminal de entrada, 
      simbolo de cima de la pila, 
      cadena de simbolos que reemplazan
    )
*)
let ap_1 = Ap (
  Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
  Conjunto [Terminal "a"; Terminal "b"],
  Conjunto [No_terminal ""; No_terminal "A"],
  Estado "0",
  Conjunto [
    Arco_ap (Estado "0", Estado "1", Terminal "a",
      No_terminal "",
      [No_terminal "A"; No_terminal ""]);
    Arco_ap (Estado "1", Estado "1", Terminal "a",
      No_terminal "A",
      [No_terminal "A"; No_terminal "A"]);
    Arco_ap (Estado "1", Estado "2", Terminal "b",
      No_terminal "A",
      []);
    Arco_ap (Estado "2", Estado "2", Terminal "b",
      No_terminal "A",
      []);
    Arco_ap (Estado "2", Estado "3", Terminal "",
      No_terminal "",
      [No_terminal ""])],
  No_terminal "",
  Conjunto [Estado "3"]
  );;

let simbolos_nt = Conjunto [No_terminal "S"; No_terminal "A"; No_terminal "B"; No_terminal "C"];;
let simbolos_t = Conjunto [Terminal "a"; Terminal "b"; Terminal "c"];;
let reglas = Conjunto [
  Regla_gic (No_terminal "S", [Terminal "b"; Terminal "a"; No_terminal "A"]);
  Regla_gic (No_terminal "A", [Terminal "a"; Terminal "a"]);
  Regla_gic (No_terminal "B", [Terminal "a"; Terminal "b"; No_terminal "A"]);
  Regla_gic (No_terminal "C", [Terminal "c"; Terminal "a"; No_terminal "B"]);
  ];;

let simbolos_nt_2 = Conjunto [No_terminal "S"];;
let simbolos_t_2 = Conjunto [Terminal "a" ; Terminal "b" ; Terminal "c"];;
let reglas_2 = Conjunto [
  Regla_gic (No_terminal "S", [Terminal "a"; No_terminal "S"; Terminal "a" ] );
  Regla_gic (No_terminal "S", [Terminal "b"; No_terminal "S"; Terminal "b" ] );
  Regla_gic (No_terminal "S", [Terminal "c" ] );
];;

let gic_1 = Gic (simbolos_nt, simbolos_t, reglas, (No_terminal "S"));;
let gic_2 = Gic (simbolos_nt_2, simbolos_t_2, reglas_2, (No_terminal "S"));;

(* Desapila símbolos terminales *)
let arcos_term (Gic (noTerm, (Conjunto term), (Conjunto reglas), _)) = 
  let rec aux accum pend = match pend with
      [] -> Conjunto accum
    | h::t -> aux ((Arco_ap ( Estado "q2", Estado "q2", h, h, []))::accum) t
  in aux [] term
;;

(* Forma arcos de símbolos no terminales con las reglas de la gic *)
let arcos_ap (Gic (noTerm, term, (Conjunto reglas), _) as gic) = 
  let estadosExtremos = Conjunto [
    Arco_ap (Estado "q1", Estado "q2", Terminal "", No_terminal "",
      [No_terminal "S"; No_terminal ""]);
    Arco_ap (Estado "q2", Estado "q3", Terminal "", No_terminal "",
      [No_terminal ""])
  ] in
  let rec aux accum pend = match pend with
      [] -> union (union (Conjunto accum) (estadosExtremos)) (arcos_term gic)
    | (Regla_gic (izq, der))::t -> aux ((Arco_ap ( Estado "q2", Estado "q2", Terminal "", izq, der))::accum) t
  
  in aux [] reglas;;

  let ap_of_gic (Gic (noTerm, term, reglas, simIni) as gic) =
  Ap (
    Conjunto [Estado "q1"; Estado "q2"; Estado "q3"], (* Conjunto de estados posibles *)
    term, (* Alfabeto de símbolos entrada *)
    (union (Conjunto [No_terminal ""]) (union noTerm term)), (* Alfabeto de pila *)
    Estado "q1",   (* Estado inicial *)
    (arcos_ap (gic)), (* Conjunto de arco_ap, funciones de transicion *)
    No_terminal "", (* Simbolo de inicio de pila *)
    Conjunto [Estado "q3"] (* Estados final *)
  );;

(* dibuja_ap (ap_of_gic gic_1);; *)
(* dibuja_ap (ap_of_gic gic_2);; *)


(* ----------------------------------------------------------------------------------- *)

exception No_encaja;;

let encaja (estado, cadena, pila_conf) (Arco_ap (origen, destino, entrada, cima, pila_arco) as arc) =
  let
    nuevo_estado =
      if estado = origen then
        destino
      else
        raise No_encaja
  and
      nueva_cadena =
        if entrada = Terminal "" then
          cadena
        else
          if (cadena <> []) && (entrada = List.hd cadena) then
            List.tl cadena
          else
            raise No_encaja
  and
      nueva_pila_conf =
        if cima = Terminal "" then
          pila_arco @ pila_conf
        else
          if (pila_conf <> []) && (cima = List.hd pila_conf) then
            pila_arco @ (List.tl pila_conf)
          else
            raise No_encaja
  in
      ((nuevo_estado, nueva_cadena, nueva_pila_conf), arc)
  ;;

let es_conf_final finales = function
  (estado, [], _) -> pertenece estado finales
| _ -> false;;


let reglas_activ cadena (Ap (_, _, _, inicial, Conjunto delta, zeta, finales)) =
  let rec aux = function
      ([], [], arcos, arcos_activ, _) -> (false, arcos_activ)
    | (_, _, arcos, arcos_activ, true) -> (true, arcos_activ)
    | ([], l, _, arcos_activ, false) -> aux (l, [], delta, arcos_activ, false)
    | (_::cfs, l, [], arcos_activ, false) -> aux (cfs, l, delta, arcos_activ, false)
    | (cf::cfs, l, a::arcos, arcos_activ,false) ->
          try
              let
                (ncf, pila_arco) = encaja cf a
              in
                aux (cf::cfs, ncf::l, arcos, union (Conjunto [pila_arco]) (arcos_activ), es_conf_final finales ncf)
          with
              No_encaja -> aux (cf::cfs, l, arcos, arcos_activ, false)
  in
    aux ([(inicial, cadena, [zeta])], [], delta, Conjunto [], false)
;;


(* gic_2 palíndromos  *)
let cad1 = cadena_of_string "a b c b a";;
reglas_activ cad1 (ap_of_gic gic_2);;

(* ap_1 aes y bes *)
let cad2 = cadena_of_string "a a b b";;
reglas_activ cad2 ap_1;;


(* dibuja_ap (ap_of_gic gic_2);; *)