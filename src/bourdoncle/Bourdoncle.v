(** Type of a Bourdoncle component. *)

Require Import List.
Require Import BinPos.
Notation node := positive.

Inductive bourdoncle :=
| I : node -> bourdoncle
| L : node -> list bourdoncle -> bourdoncle.
