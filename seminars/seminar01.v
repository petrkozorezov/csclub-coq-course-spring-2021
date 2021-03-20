From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:=
  fun '((a, b), c) => (a, (b, c)).

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=
  fun s =>
    match s with
    | inr c       => inr (inr c)
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:= fun p =>
  match p with
    | (a, inl b) => inl (a, b)
    | (a, inr c) => inr (a, c)
  end.


Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:= fun p =>
  match p with
  | inl a      => (inl a, inl a)
  | inr (b, c) => (inr b, inr c)
  end.

Definition comp (A B C : Type) (f : B -> A) (g : C -> B) : C -> A
:=
  fun c => f (g c).


(*Definition comp (A B C : Type) : (B -> A) -> (C -> B) -> C -> A
:= fun f g => fun c => f (g c).
*)

(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)

(* Introduce empty type, call `void` *)

Inductive void := .

Definition void_terminal (A : Type) :
  void -> A
:= fun p => match p with end.


(* Introduce `unit` type (a type with exactly one canonical form) *)

Inductive unit : Type :=
  | u.

Definition unit_initial (A : Type) :
  A -> unit
:= fun '_ => u.

Variable x : void.
Check match x with end : nat.

Compute void_terminal _ x : nat.

(* Think of some more type signatures involving void, unit, sum, prod *)
