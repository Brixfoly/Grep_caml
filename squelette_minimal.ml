
(*::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::*)
(* Nicolas Pécheux <info.cpge@cpge.info>                            *)
(* http://cpge.info                                                 *)
(*::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::*)

(* À modifier : ce que l'on fait pour chaque ligne. En l'état, on
   affiche toujours la ligne. *)
let process_line line (a : automate_general) =
  if reconnu line a then Printf.printf "%s\n%!" line



(* Lecture de l'entrée, ligne par ligne *)
let process input a =
  try
    while true do
      let line = Stdlib.input_line input in
      process_line line a
    done
  with End_of_file -> ()

let main () =
  (* Vérifie que l'expression régulière est bien présente en premier
     argument. Sinon, on affiche un message indiquant comment utiliser
     ce programme et on quitte avec un code d'erreur de `1`. *)
  let argc = Array.length Sys.argv in
  if argc < 2 || argc > 3 then begin
    Printf.printf "usage : %s regex [file]\n%!" Sys.argv.(0);
    exit 1
  end;
  (* S'il y a un deuxième argument c'est qu'il faut lire dans ce
     fichier, sinon, on utilise l'entrée standard. *)
  let input =
    if (argc = 3) then begin
      Stdlib.open_in Sys.argv.(2)
    end else
      Stdlib.stdin
  in
  Printf.printf
    "* Regexp you entered is '%s'\n* Reading from %s\n\n%!"
    Sys.argv.(1)
    (if argc = 3 then Sys.argv.(2) else "stdin");


  let regex = Sys.argv.(1) in
  let a = berry_sethi regex in
  process input a;

  if argc = 3 then Stdlib.close_in input

let () = main ()
