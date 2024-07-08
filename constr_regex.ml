type automate_general = {
  nb_etats : int;
  initiaux : int list; (*Dans le cas de l'automate de B-S, qu'un seul état initial*)
  terminaux : bool array;
  transitions : (char*int) list array;
}

let rec log_2 n = if n=1 then 0, 1 else let k, p = log_2 (n/2) in (k+1, p + (n mod 2))
let rec exp a n = if n=0 then 1 else if n mod 2 = 0 then exp (a*a) (n/2) else a* exp (a*a) ((n-1)/2)
let id i = i

let maxi l = match l with
| [] -> failwith"liste vide"
| d::fin -> List.fold_right max fin d

(*Pour switcher entre les différentes représentations d'ensembles (int list/ bool array)*)
let tableau_vers_liste a = 
  let l, n = ref [], Array.length a in
  for i = n-1 downto 0 do
    if a.(i) then l := i::!l;
  done;
!l

let liste_vers_tableau l = 
  let a = Array.make (maxi l + 1) false
in List.iter (fun i -> a.(i) <- true) l; a

exception Found
(*Renvoie vrai si l et e on un élément en commun*)
let exist l e = 
  try let n = min (Array.length e) (Array.length l) in
    for i=0 to (n-1) do
      if e.(i)&&l.(i) then raise Found
    done;
    false
  with Found -> true

(*Renvoie vrai ssi u est reconnu par a
Complexité : pourrie*)
let reconnu (u : string) (a : automate_general) =
  let n = String.length u in
  let rec aux i (visites : bool array) = 
    if i=n then exist visites a.terminaux
    else begin
      let new_v = Array.make (a.nb_etats) false in                              (*On n'utilise pas les effets de bord*)
      Array.iteri (fun e b -> if b then                                         (*On parcourt l'ensemble des noeuds Qi  (b = true ssi e est dans Qi) *)
        List.iter (fun (c', next) -> if u.[i] = c' then new_v.(next) <- true)   (*pour ajouter leurs successeurs au nouvel ensemble*)
        a.transitions.(e)
      ) visites;
      aux (i+1) new_v 
    end
in aux 0 (liste_vers_tableau a.initiaux)

(*La manière dont on marque les lettres fait que chaque lettre a un indice unique, par lequel on représente son état dans l'automate*)
let liste_marquee_vers_arr (l : (int*char) list) n =
  let a = Array.make n false in 
  List.iter (fun (i, _) -> a.(i) <- true) l;
a

(*Construit l'automate local d'un language local caractérisé par l'ensembles des préfixes, des suffixes et des facteurs*)
(*n : nb de lettres dans la regex linéaire (avant oubli de marques). L'état initial est l'état (n+1), et est terminal ssi has_eps*)
let automate_local_avec_oubli (p : (int*char) list) (s : (int*char) list) (f : ((int*char)*(int*char)) list) has_eps n = 
  let a = {nb_etats = n+1; initiaux = [n]; terminaux = liste_marquee_vers_arr s (n+1); transitions = Array.make (n+1) []} in
  List.iter (fun ((i, c1), (j, c2)) -> a.transitions.(i) <- (c2, j)::a.transitions.(i)) f;
  List.iter (fun (i, d) -> a.transitions.(n) <- (d, i)::a.transitions.(n)) p;
  if has_eps then a.terminaux.(n) <- true;
a


(*Partie regex*)
type regex =
| Eps
| C of int*char
| Quest of regex
| Concat of regex * regex
| Or of regex*regex
| S of regex (*Star*)

(*Transforme le point en une alternative de toutes les lettres (pas la meilleure manière du tout mais bon)*)
let point_to_re it = 
  let rec aux i = 
    incr it;
    if i=255 then C (!it - 1, char_of_int i) else Or (C (!it - 1, char_of_int i), aux (i+1))
in aux 0

(*Si on a une regex de la forme a*?*?*?, renvoie en partant du premier char après a le nb de * ainsi que l'indice à partir duquel il n'y en a plus,
pour que soit un seul ? ou une seule * soit prise en compte (en mettre plus ne change rien)
Fonction auxilliare à la réalisation de l'éléphant qui suit*)
let rec search_for_more re i_d i_f =
  let i, s = ref 1, ref false in
  while (!i + i_d < i_f) && ((re.[!i + i_d] = '*') || (re.[!i + i_d] = '?')) do
    s := !s || (re.[!i + i_d] = '*');
    incr i;
  done;
!i, !s

(*ATTENTION : en infixe, on a besoin des parenthèses, qui ne peuvent donc pas être utilisées dans la regex elle-même*)
let regex_of_infixe re =
  let n, it = String.length re, ref 0 in (* p contient des couples regex, opt *)
  assert(n>0);                           (*avec opt un char qui vaut | si ou, @ si concat et ' ' si pas d'operation*)
  let rec aux i_d i_f p =
    if i_d = i_f then fst (Stack.pop p), i_f else match re.[i_d] with   (*Si jamais je savait qui a mis un fst ici...*)
    | '('-> let acc', i_f' = aux (i_d +1) i_f (Stack.create ()) in
            let res = ref acc' in
            let k, b = search_for_more re (i_f'-1) i_f in
            if b then res := S (!res)
            else if k>1 then res := Quest (!res); 
            if Stack.is_empty p then begin Stack.push (!res, ' ') p; aux (i_f' +k-1) i_f p end 
            else begin
              let r = match Stack.pop p with
                | acc, '@' -> Concat(acc, !res)
                | acc, '|' -> Or(acc, !res)
                | _ -> !res
              in if i_f' +k-1 = i_f then r, i_f 
              else begin Stack.push (r, ' ') p; aux (i_f' +k-1) i_f p end
            end
    | ')' -> let res, opt = Stack.pop p in assert (opt = ' '); (res, i_d+1)
    | '?' -> let r, opt = Stack.pop p in assert (opt = ' '); Stack.push (Quest r, ' ') p; aux (i_d +1) i_f p
    | '*' -> let r, opt = Stack.pop p in assert (opt = ' '); Stack.push (S r, ' ') p; aux (i_d +1) i_f p
    | '.' ->  let res = point_to_re it in 
              if (i_d < i_f-1)&&(re.[i_d +1] = '*' || re.[i_d + 1] = '?')   (*S'il y a une étoile après le .*)
                then let k, b = search_for_more re i_d i_f in
                if b then
                  if Stack.is_empty p then begin Stack.push (S res, ' ') p; aux (i_d +k) i_f p end
                  else begin
                    let r = match Stack.pop p with
                      | acc, '@' -> Concat(acc, S res)
                      | acc, '|' -> Or(acc, S res)
                      | _ -> S res
                    in Stack.push (r, ' ') p; aux (i_d +k) i_f p
                  end
                else                        (*S'il y a un ? après le .*)
                  if Stack.is_empty p then begin Stack.push (Quest res, ' ') p; aux (i_d +k) i_f p end
                  else begin
                    let r = match Stack.pop p with
                      | acc, '@' -> Concat(acc, Quest res)
                      | acc, '|' -> Or(acc, Quest res)
                      | _ -> Quest res
                    in Stack.push (r, ' ') p; aux (i_d +k) i_f p
                  end
              else
                if Stack.is_empty p then begin Stack.push (res, ' ') p; aux (i_d +1) i_f p end
                else begin
                  let r = match Stack.pop p with
                    | acc, '@' -> Concat(acc, res)
                    | acc, '|' -> Or(acc, res)
                    | _ -> res
                  in Stack.push (r, ' ') p; aux (i_d +1) i_f p
                end
    | '@' -> assert(not(Stack.is_empty p)); let r,_ = Stack.pop p in Stack.push (r, '@') p; aux (i_d+1) i_f p
    | '|' -> assert(not(Stack.is_empty p)); let r,_ = Stack.pop p in 
            let res, i_f' = aux (i_d+1) i_f (Stack.create ()) in
            begin Stack.push (Or(r, res), ' ') p;
              match re.[i_f'-1] with
              | ')' -> aux (i_f'-1) i_f p
              | _ -> aux i_f' i_f p
            end 
    | c ->  let res = C(!it, c) in incr it;
            if (i_d < i_f-1)&&(re.[i_d +1] = '*' || re.[i_d + 1] = '?')   (*S'il y a une étoile après la lettre*)
              then let k, b = search_for_more re i_d i_f in
              if b then
                if Stack.is_empty p then begin Stack.push (S res, ' ') p; aux (i_d +k) i_f p end
                else begin
                  let r = match Stack.pop p with
                    | acc, '@' -> Concat(acc, S res)
                    | acc, '|' -> Or(acc, S res)
                    | _ -> S res
                  in Stack.push (r, ' ') p; aux (i_d +k) i_f p
                end
              else                        (*S'il y a un ? après la lettre*)
                if Stack.is_empty p then begin Stack.push (Quest res, ' ') p; aux (i_d +k) i_f p end
                else begin
                  let r = match Stack.pop p with
                    | acc, '@' -> Concat(acc, Quest res)
                    | acc, '|' -> Or(acc, Quest res)
                    | _ -> Quest res
                  in Stack.push (r, ' ') p; aux (i_d +k) i_f p
                end
            else
              if Stack.is_empty p then begin Stack.push (res, ' ') p; aux (i_d +1) i_f p end
              else begin
                let r = match Stack.pop p with
                  | acc, '@' -> Concat(acc, res)
                  | acc, '|' -> Or(acc, res)
                  | _ -> res
                in Stack.push (r, ' ') p; aux (i_d +1) i_f p
              end
in let res, _ = aux 0 n (Stack.create ()) in res, !it    (*On pourrait mettre un assert le 2eme membre vaut n*) 


(*Prend une regex sous la forme d'une chaîne de caractères en 
notation postfixe non parenthésée et la transforme en une regex linéaire du bon type, tout en renvoyant le nombre de lettres*)
let regex_of_str re = 
  let n, it, p = String.length re, ref 0, Stack.create () in 
  begin match re.[0] with
  | '.' -> Stack.push (point_to_re it) p
  | c -> Stack.push (C (!it, c)) p; incr it end;
  for i=1 to (n-1) do
    match re.[i] with
    | '?' -> let r = Stack.pop p in Stack.push (Quest r) p
    | '*' -> let r = Stack.pop p in Stack.push (S r) p
    | '.' -> Stack.push (point_to_re it) p
    | '@' -> let r2 = Stack.pop p in let r1 = Stack.pop p in Stack.push (Concat(r1, r2)) p
    | '|' -> let r2 = Stack.pop p in let r1 = Stack.pop p in Stack.push (Or(r1, r2)) p
    | c -> Stack.push (C (!it, c)) p; incr it
  done;
  Stack.pop p, !it

(*Fusionne 2 listes triées en enlevant les doublons*)
let rec merge l1 l2 = match l1, l2 with
| [], _ -> l2
|_, [] -> l1
| d1::fin1, d2::fin2 -> if d1=d2 then d1::merge fin1 fin2
  else if d1>d2 then d2::merge l1 fin2 else d1::merge fin1 l2

let produit_car l1 l2 = List.fold_right (fun a acc -> (List.map (fun b -> (a, b)) l2)@acc) l1 []

(*Invariant : p, s, f sont triées par indice
Ceci est garanti par le fait que l'expression régulière est linéaire*)
let rec pref_suff_fact regex = match regex with
| Eps -> [], [], [], true
| C(i, c) -> [(i, c)], [(i ,c)], [], false
| Quest e -> let p, s, f, _ = pref_suff_fact e in (p, s, f, true)
| Or(r1, r2) -> let (p1, s1, f1, b1), (p2, s2, f2, b2) = pref_suff_fact r1, pref_suff_fact r2
                in (p1@p2, s1@s2, f1@f2, b1||b2)
| S r -> let p, s, f, _ = pref_suff_fact r in (p, s, merge f (produit_car p s), true)
| Concat(r1, r2) -> begin match pref_suff_fact r1, pref_suff_fact r2 with
                  | (p1, s1, f1, true), (p2, s2, f2, true) -> (p1@p2, s1@s2, merge (f1@f2) (produit_car s1 p2), true)
                  | (p1, s1, f1, true), (p2, s2, f2, false) -> (p1@p2, s2, merge (f1@f2) (produit_car s1 p2), false)
                  | (p1, s1, f1, false), (p2, s2, f2, true) -> (p1, s1@s2, merge (f1@f2) (produit_car s1 p2), false)
                  | (p1, s1, f1, false), (p2, s2, f2, false) -> (p1, s2, merge (f1@f2) (produit_car s1 p2), false) end

(*Construit, à partir d'une expression régulière un automate le reconnaissant*)
let berry_sethi (re : string) : automate_general = 
  let regex, n = regex_of_str re in
  let p, s, f, has_eps = pref_suff_fact regex in
  automate_local_avec_oubli p s f has_eps n

(* Rapide (et unique) test*)
(*
let s = "ab|*a@"
let e, n = regex_of_str s
let a = pref_suff_fact e
let a = berry_sethi s
*)