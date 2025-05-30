Require Import List.
Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(* ---------- PairingHeap Module Definition ---------- *)
Module pairingHeap.
Section Defs.

Variable A : Type.
Variable le : A -> A -> bool.

Inductive Heap : Type :=
  | Empty : Heap
  | Node : A -> list Heap -> Heap.

Definition find_min (h : Heap) : option A :=
  match h with
  | Empty => None
  | Node x _ => Some x
  end.

Definition meld (h1 h2 : Heap) : Heap :=
  match h1, h2 with
  | Empty, _ => h2
  | _, Empty => h1
  | Node x1 hs1, Node x2 hs2 =>
      if le x1 x2
      then Node x1 (h2 :: hs1)
      else Node x2 (h1 :: hs2)
  end.

Fixpoint pairwise_meld (hs : list Heap) : Heap :=
  match hs with
  | [] => Empty
  | [h] => h
  | h1 :: h2 :: hs' => meld (meld h1 h2) (pairwise_meld hs')
  end.

Definition delete_min (h : Heap) : Heap :=
  match h with
  | Empty => Empty
  | Node _ hs => pairwise_meld hs
  end.

Definition insert (x : A) (h : Heap) : Heap :=
  meld (Node x []) h.


(* ---------- Helper functions ---------- *)
Fixpoint heap_ordered (h : Heap) : bool :=
  match h with
  | Empty => true
  | Node x hs =>
      forallb (fun h' =>
        match h' with
        | Empty => true
        | Node y _ => le x y && heap_ordered h'
        end) hs
  end.

Fixpoint elements (h : Heap) : list A :=
  match h with
  | Empty => []
  | Node x hs => x :: flat_map elements hs
  end.


End Defs.
End pairingHeap.

Module PH := pairingHeap.

Definition HeapNat := PH.Heap nat.
Definition heap_ordered_nat := PH.heap_ordered nat Nat.leb.
Definition elements_nat := PH.elements nat.
Definition find_min_nat := PH.find_min nat.
Definition meld_nat := PH.meld nat Nat.leb.
Definition delete_min_nat := PH.delete_min nat Nat.leb.
Definition insert_nat := PH.insert nat Nat.leb.

(* ---------- Verification functions ---------- *)
Definition list_min (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => Some (fold_left Nat.min xs x)
  end.

Definition verify_find_min_correct (h : HeapNat) : bool :=
  match find_min_nat h, list_min (elements_nat h) with
  | Some a, Some b => Nat.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition meld_permutation (h1 h2 : HeapNat) : Prop :=
  Permutation (elements_nat (meld_nat h1 h2)) (elements_nat h1 ++ elements_nat h2).

Definition delete_min_permutation (h1 : HeapNat) : Prop :=
  Permutation (elements_nat (delete_min_nat h1)) (tl (elements_nat h1)).

Definition insert_permutation (x : nat) (h1 : HeapNat) : Prop :=
  Permutation (elements_nat (insert_nat x h1)) (x :: elements_nat h1).

(* ---------- Examples of pairing heaps functions ---------- *)
Definition h0 : HeapNat := PH.Empty _.
Definition h1 : HeapNat := PH.Node _ 1 [].
Definition h2 : HeapNat :=
  PH.Node _ 1 [
    PH.Node _ 2 [
      PH.Node _ 5 []
    ];
    PH.Node _ 3 [];
    PH.Node _ 4 []
  ].

Definition h3 : HeapNat :=
  PH.Node _ 1 [
    PH.Node _ 2 [
      PH.Node _ 5 [];
      PH.Node _ 6 []
    ];
    PH.Node _ 3 [
      PH.Node _ 7 []
    ]
  ].

Definition h_bad : HeapNat :=
  PH.Node _ 5 [
    PH.Node _ 6 [
      PH.Node _ 3 []
    ];
    PH.Node _ 2 [];
    PH.Node _ 4 [
      PH.Node _ 1 []
    ]
  ].

(* ---------- Calls of helper functions ---------- *)
Eval compute in heap_ordered_nat h0.
Eval compute in heap_ordered_nat h1.
Eval compute in heap_ordered_nat h2.
Eval compute in heap_ordered_nat h3.
Eval compute in heap_ordered_nat h_bad.

Eval compute in elements_nat h2.
Eval compute in elements_nat h3.
Eval compute in elements_nat h_bad.

(* ---------- Verification for findMin ---------- *)
Eval compute in find_min_nat h3.
Eval compute in elements_nat h3.
Eval compute in (find_min_nat h3 = list_min (elements_nat h3)).
Eval compute in (find_min_nat h0 = list_min (elements_nat h0)).
Eval compute in verify_find_min_correct h3.

(* ---------- Verification for meld ---------- *)
Eval compute in meld_nat h2 h3.
Eval compute in heap_ordered_nat (meld_nat h2 h3).
Eval compute in meld_permutation h2 h3.

(* ---------- Verification for delete min ---------- *)
Eval compute in delete_min_nat h2.
Eval compute in heap_ordered_nat (delete_min_nat h2).
Eval compute in elements_nat (delete_min_nat h2).
Eval compute in delete_min_permutation h2.

(* ---------- Verification for insert ---------- *)
Eval compute in insert_nat 5 h2.
Eval compute in heap_ordered_nat (insert_nat 5 h2).
Eval compute in elements_nat (insert_nat 5 h2).
Eval compute in insert_permutation 5 h2.