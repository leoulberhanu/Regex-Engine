open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let rec move_aux nfaDelta s x a = 
  match nfaDelta with
    | [] -> a
    | h :: t -> 
    let (source, channel, destination) = h in if (x = source && s = channel && (mem destination a = false)) then destination :: a else (move_aux t s x a)
    
;;
let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  (*List.fold_right (fun x a -> move_aux nfa.delta s x a) qs []*)
  List.fold_left (fun a x -> let (source, channel, destination) = x in if ((elem source qs) && channel = s) then insert destination a else a ) [] nfa.delta


;;

let rec e_closure_aux nfa x =
  let e = move nfa x None in 
  let iter = union x e in
  if iter = union iter (move nfa iter None) then iter else e_closure_aux nfa iter

  

;;
let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
 (* List.fold_left (fun x a -> (union [x] (move_aux nfa.delta  None x a))) qs []*)
  (*List.fold_left (fun x a -> a @ if move nfa [x] None = [] then move nfa [x] None else move nfa [x] None @ move nfa (move nfa [x] None) None) qs []*)
  (*List.fold_left (fun x a -> let hi = e_closure_aux nfa x in if eq a hi then a else union a hi) qs []*)
  e_closure_aux nfa qs
  (*whenever theres something wrong in nfa to dfa, check move or dfa or anything that uses recursion *)
  (**dont try to use recursion inside recursion for part 2 *)
;;

(*helper function creates an iterbale variable then combine 0 with e closure from 0 and combine it with*)

let rec accept_aux nfa charList stateList = 
  
  match charList with
    | [] -> fold_left (fun a x -> if (elem x nfa.fs) then true else a) false stateList
    | h :: t -> accept_aux nfa t (e_closure  nfa (move nfa stateList (Some h)))
  
;;
(*not sure if it should be with eclosure then move or vice versa *)

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let charList = explode s in accept_aux nfa charList (e_closure nfa [nfa.q0])
  
;;

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  (*fold_left (fun a x -> union a (fold_left (fun b y ->  union b (move nfa [x] (Some y))) [] nfa.sigma)) [] qs*)
  fold_left (fun a x -> insert (e_closure  nfa (move nfa qs (Some x))) a) [] nfa.sigma

;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  map (fun x -> (qs,(Some x), e_closure nfa (move nfa qs (Some x)))) nfa.sigma 
;;
let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  fold_left (fun a x -> if (elem x nfa.fs) then insert qs a else a ) [] qs
;;

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
  match work with
    | [] -> dfa
    | h :: t -> nfa_to_dfa_step nfa {
      qs = insert h dfa.qs
      ; sigma= nfa.sigma
      ; delta= union (new_trans nfa h)  dfa.delta
      ; q0= dfa.q0
      ; fs= union (new_finals nfa h) dfa.fs
    } (diff (union (new_states nfa h)  t) dfa.qs)
  (*
  green stuff is what goes into work
  fter processing generate a new state
*)
(*
having a helper function add as many params as you like
tail recursion
at some condition you can just return the dfa
you need to modify the dfa param
tail recursion u have an accum -> u add to the accum (the dfa) and at some point you return it
the work list is the condition -> you need to work on something and onc

start w nfa and work list
dfa is a blank canvas
you want to iterate recursively through the work list and update that dfa as you iterate
once u are done with the worklist, you have a final dfa that u return
u create the work list in the nfa to dfa function

the start state of the dfa is the e closure of the start state in the nfa
refer to previous examples to
your work list changes as you update the 

this function has similar logic to e closure 
*)
let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let start_state = e_closure nfa [nfa.q0] in let dfa =  { qs= [start_state]
  ; sigma= nfa.sigma
  ; delta= []
  ; q0= start_state
  ; fs= [] }  in nfa_to_dfa_step nfa dfa [start_state]
  ;;
  (* start state returns a list but i have it in q0. shouldnt it be a single value *)
  (* where do i go once i have this set up *)
