Require Import List.
Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
From Coq Require Import Lia.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

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

(* ---------- Proof that every singleton node is an ordered pairing heap ---------- *)
Lemma singleton_node_heap_ordered (x : nat) :
  heap_ordered_nat (PH.Node _ x []) = true.
Proof. simpl. reflexivity. Qed.



(* ---------- Merging proof ordered ---------- *)
Lemma meld_preserves_heap_order :
  forall h1 h2 : HeapNat,
    heap_ordered_nat h1 = true ->
    heap_ordered_nat h2 = true ->
    heap_ordered_nat (meld_nat h1 h2) = true.
Proof.
  intros h1 h2 Hord1 Hord2.
  unfold meld_nat.   
  unfold PH.meld.
  destruct h1 as [| x1 hs1].
  - (* h1 = Empty *)
    simpl. assumption.
  - destruct h2 as [| x2 hs2].
    + (* h2 = Empty *)
      simpl. assumption.
    + (* Both heaps non-empty *)
      simpl.
      destruct (Nat.leb x1 x2) eqn:Hle.
      * (* Case: x1 <= x2 *)
        simpl. apply andb_true_intro.
        split.
        -- apply andb_true_intro.
           split.
           ** apply Hle.
           ** apply Hord2.
        -- simpl in Hord1.
           apply Hord1.
      * (* Case: x1 > x2 *)
        simpl. apply andb_true_intro.
        split.
        -- apply andb_true_intro.
           split.
           ** Search leb false.
              apply leb_correct.
              apply leb_complete_conv in Hle.
              lia.
           ** apply Hord1.
        -- apply Hord2.
Qed.

(* ---------- Merging proof flatten elements ---------- *)
Lemma meld_permutation_elements :
  forall h1 h2 : HeapNat,
    Permutation (elements_nat (meld_nat h1 h2))
                (elements_nat h1 ++ elements_nat h2).
Proof.
  intros h1 h2.
  unfold meld_nat.
  unfold PH.meld.
  destruct h1 as [| x1 hs1].
  - (* Case: h1 = Empty *)
    simpl. apply Permutation_refl.
  - destruct h2 as [| x2 hs2].
    + (* Case: h2 = Empty *)
      simpl. rewrite app_nil_r. apply Permutation_refl.
    + (* Both heaps non-empty *)
      simpl.
      destruct (Nat.leb x1 x2) eqn:Hle.
      * (* Case: x1 <= x2 *)
        admit.
      * (* Case: x1 > x2 *)
        admit.
Admitted.

(* ---------- Inserting proof ordered ---------- *)
Lemma insert_preserves_heap_order :
  forall (x : nat) (h : HeapNat),
    heap_ordered_nat h = true ->
    heap_ordered_nat (insert_nat x h) = true.
Proof.
  intros x h Hord.
  unfold insert_nat, PH.insert.
  apply meld_preserves_heap_order.
  - apply singleton_node_heap_ordered.
  - exact Hord.
Qed.

(* ---------- Inserting proof elements ---------- *)
Lemma insert_permutation_elements :
  forall (x : nat) (h : HeapNat),
    Permutation (elements_nat (insert_nat x h))
                (x :: elements_nat h).
Proof.
  intros x h.
  unfold insert_nat, PH.insert, meld_nat, PH.meld.
  destruct h as [| xh hsl].
  - (* h = Empty *) 
    simpl; apply Permutation_refl.
  - simpl.
    destruct (Nat.leb x xh) eqn:Hle; simpl.
    + (* x ≤ xh: elements = x :: xh :: flat_map … ++ [] *)
      rewrite app_nil_r. 
      apply Permutation_refl.
    + (* x > xh: elements = xh :: x :: flat_map … *)
      apply perm_swap.
Qed.



(* ---------- Delete min proof ordered ---------- *)
Lemma delete_min_preserves_heap_order :
  forall h : HeapNat,
    heap_ordered_nat h = true ->
    heap_ordered_nat (delete_min_nat h) = true.
Proof.
  intros h Hord.
  unfold delete_min_nat.
  unfold PH.delete_min.
  destruct h as [| x hs].
  - (* Case: h = Empty *)
    simpl. reflexivity.
  - (* Case: Node x hs *)
    simpl.
    (* recursive case on pairwise_meld hs *)
    admit.
Admitted.

(* ---------- Delete min proof elements ---------- *)
Lemma delete_min_permutation_elements :
  forall h : HeapNat,
    Permutation (elements_nat (delete_min_nat h))
                (tl (elements_nat h)).
Proof.
  intros h.
  unfold delete_min_nat.
  unfold PH.delete_min.
  destruct h as [| x hs].
  - (* Case: h = Empty *)
    simpl. apply Permutation_refl.
  - (* Case: Node x hs *)
    simpl.
    (* recursive case on pairwise_meld hs *)
    admit.
Admitted.