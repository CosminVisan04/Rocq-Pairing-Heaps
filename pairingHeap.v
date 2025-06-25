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
  | h::hs => meld h (pairwise_meld hs)
  end.

Definition delete_min (h : Heap) : Heap :=
  match h with
  | Empty => Empty
  | Node _ hs => pairwise_meld hs
  end.

Definition insert (x : A) (h : Heap) : Heap :=
  meld (Node x []) h.

Definition extract_min (h : Heap) : option (A * Heap) :=
  match h with
  | Empty => None
  | Node x hs => Some (x, pairwise_meld hs)
  end.

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

Fixpoint PH_strong_ind (P : Heap -> Prop) (HE : P Empty)
  (Hind : forall x hs, Forall P hs -> P (Node x hs)) (h : Heap) : P h :=
  match h with
  | Empty => HE
  | Node x hs =>
      Hind x hs
        ((fix f (hs : list Heap) : Forall P hs :=
           match hs with
           | [] => Forall_nil _
           | h::hs => Forall_cons h (PH_strong_ind P HE Hind h) (f hs)
           end) hs)
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
Definition pairwise_meld_nat := PH.pairwise_meld nat Nat.leb.
Definition extract_min_nat := PH.extract_min nat Nat.leb.

(* ---------- Examples of pairing heaps ---------- *)
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

(* ---------- Auxuliary lemmas ---------- *)
Definition list_min (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => Some (fold_left Nat.min xs x)
  end.

Lemma forallb_Forall {A:Type} (p : A -> bool) (ls : list A) :
  forallb p ls = true <-> Forall (fun x => p x = true) ls.
Proof.
  induction ls as [| x xs IH]; simpl.
  - split; intros _; constructor.
  - split; intros H.
    + apply andb_true_iff in H as [Hx Hxs].
      constructor; [exact Hx | apply IH; exact Hxs].
    + inversion H as [| ? ? Hx Hxs].
      apply IH in Hxs.
      apply andb_true_iff; split; assumption.
Qed.

Lemma Forall_weaken {A:Type} (P Q : A -> Prop) (ls : list A) :
  (forall x, P x -> Q x) ->
  Forall P ls ->
  Forall Q ls.
Proof.
  intros HPQ H.
  induction H as [| x xs Hx Hxs IH].
  - constructor.
  - constructor.
    + apply HPQ. exact Hx.
    + apply IH.
Qed.

Lemma fold_left_min (l : list nat) (x : nat) :
  Forall (fun y => x <= y) l ->
  fold_left Nat.min l x = x.
Proof.
  induction l as [| y ys IH]; simpl; auto.
  intros Hf.
  inversion Hf as [| y' ys' Hxy Hys]; clear Hf; subst y';  
  simpl in *.
  destruct (Nat.leb_spec0 x y).
  - rewrite Nat.min_l; [ now apply IH | assumption ].
  - lia.
Qed.

Lemma heap_ordered_elements_nat (h : HeapNat) :
  heap_ordered_nat h = true ->
  match h with
  | PH.Empty _     => True
  | PH.Node _ x hs => Forall (fun y => x <= y) (flat_map elements_nat hs)
  end.
Proof.
  intros Hord.
  induction h as [ | x hs IH ] using PH.PH_strong_ind; simpl.
  - (* h = Empty *) 
    auto.
  - (* h = Node x hs *)
    simpl in Hord.
    apply forallb_Forall in Hord as Hforall.
    clear Hord.
    induction Hforall as [ | h' hs' Hhd Htl IHtl ]; simpl.
    + constructor.
    + (* h' :: hs'  *)
      apply Forall_app; split.
      * destruct h' as [| y ys]; simpl in Hhd; [ constructor | ].
        apply andb_true_iff in Hhd as [Hxy Hordh'].
        simpl; constructor.
        -- now apply Nat.leb_le in Hxy.
        -- apply Forall_weaken with (P := fun y0 : nat => x <= y0).
            --- lia.
            --- assert (Forall (fun y0 : nat => x <= y0) (flat_map elements_nat ys)) as H2. {
                  pose proof (Forall_inv IH) as IH_head.
                  apply Forall_weaken with (P := fun y0 => y <= y0).
                  - intros y0 Hle. apply Nat.leb_le in Hxy. lia.
                  - apply IH_head. exact Hordh'.
                }
                apply H2.
      * apply Forall_weaken with (P := fun y : nat => x <= y).
            --- lia.
            --- assert (Forall (fun y : nat => x <= y) (flat_map elements_nat hs')) as H2. {
                  pose proof (Forall_inv IH) as IH_head.
                  apply Forall_weaken with (P := fun y : nat => x <= y).
                  - intros y0 Hle. exact Hle.
                  - apply IHtl.
                    apply Forall_cons_iff in IH.
                    destruct IH as [_ IH].
                    apply IH.
                }
                apply H2.
Qed.

Lemma heap_ordered_root_lb_all (x : nat) (hs : list HeapNat) :
  heap_ordered_nat (PH.Node _ x hs) = true ->
  Forall (fun y => x <= y) (flat_map elements_nat hs).
Proof.
  apply (heap_ordered_elements_nat (PH.Node _ x hs)).
Qed.

Lemma find_mind_correct_Some h a :
  heap_ordered_nat h = true ->
  find_min_nat h = Some a ->
  list_min (elements_nat h) = Some a.
Proof.
  destruct h as [| x hs] eqn:E; simpl; [ congruence | ].
  intros Hord Hfind; inversion Hfind; subst a.
  unfold list_min; simpl.
  f_equal.
  apply fold_left_min, heap_ordered_root_lb_all; assumption.
Qed.

Definition hdOption {A} (ls : list A) : option A :=
  match ls with
  | [] => None
  | x::_ => Some x
  end.

Lemma elements_nat_min h :
  heap_ordered_nat h = true ->
  hdOption (elements_nat h) = list_min (elements_nat h).
Proof.
  intros Hord.
  destruct h as [| x hs]; simpl.
    - reflexivity.
    - unfold list_min; simpl.
  set (Hle := heap_ordered_elements_nat (PH.Node _ x hs) Hord).
  rewrite fold_left_min; [ reflexivity | exact Hle ].
Qed.

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
  unfold meld_nat, PH.meld.
  destruct h1 as [| x1 hs1]; simpl.
  - (* Case: h1 = Empty *)
    reflexivity.
  - destruct h2 as [| x2 hs2]; simpl.
    + (* Case: h2 = Empty *)
      rewrite app_nil_r; apply Permutation_refl.
    + (* Case: both heaps non-empty *)
      destruct (Nat.leb x1 x2) eqn:H; simpl.
      * (* x1 <= x2 *)
        apply perm_skip.
        apply (Permutation_app_comm
                 (x2 :: flat_map elements_nat hs2)
                 (flat_map elements_nat hs1)).
      * (* x1 > x2 *)
        transitivity (x1 :: x2 :: flat_map elements_nat hs1 ++ flat_map elements_nat hs2).
        -- apply perm_swap.
        -- apply perm_skip. apply Permutation_middle.
Qed.

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
  unfold insert_nat, PH.insert.
  apply perm_trans with (l' := elements_nat (PH.Node _ x []) ++ elements_nat h).
  - apply meld_permutation_elements.
  - simpl. apply Permutation_refl.
Qed.

(* ---------- Delete min proof ordered ---------- *)
Lemma pairwise_meld_preserves_heap_order hs :
  Forall (fun h => heap_ordered_nat h = true) hs ->
  heap_ordered_nat (pairwise_meld_nat hs) = true.
Proof.
  induction hs as [ | h hs]; simpl; auto.
  intros HF.
  apply meld_preserves_heap_order.
  - apply Forall_inv in HF; assumption.
  - apply IHhs.
    apply Forall_inv_tail in HF; assumption.
Qed.

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
    apply pairwise_meld_preserves_heap_order.
    simpl in Hord.
    apply forallb_Forall in Hord.
    eapply Forall_weaken.
    2: { apply Hord. }
    clear.
    intros h Hh. simpl in Hh.
    destruct h ; auto.
    apply andb_prop in Hh.
    destruct Hh as [_ Hh].
    assumption.
Qed.

(* ---------- Delete min proof elements ---------- *)
Lemma pairwise_meld_permutation_elements hs :
  Permutation (elements_nat (pairwise_meld_nat hs))
    (flat_map elements_nat hs).
Proof.
  induction hs as [ | h hs].
  - simpl. reflexivity.
  - simpl.
    transitivity (elements_nat h ++ elements_nat (pairwise_meld_nat hs)).
    + apply meld_permutation_elements.
    + rewrite IHhs.
      reflexivity.
Qed.

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
    simpl. apply pairwise_meld_permutation_elements.
Qed.

(* ---------- Extract min proof ordered ---------- *)
Lemma extract_min_preserves_heap_order :
  forall h x h',
    extract_min_nat h = Some (x, h') ->
    heap_ordered_nat h = true ->
    heap_ordered_nat h' = true.
Proof.
  intros h x h' Hext Hord.
  unfold extract_min_nat, PH.extract_min in Hext.
  destruct h as [| y hs].
  - discriminate Hext.
  - inversion Hext; subst x h'.
    apply pairwise_meld_preserves_heap_order.
    simpl in Hord.
    apply forallb_Forall in Hord.
    eapply Forall_weaken.
    2: { apply Hord. }
    clear.
    intros h Hh.
    destruct h as [| z zs]; auto.
    simpl in Hh. apply andb_prop in Hh as [_ Hrec]. exact Hrec.
Qed.

(* ---------- Extract min proof elements ---------- *)
Lemma extract_min_permutation_elements :
  forall h x h',
    extract_min_nat h = Some (x, h') ->
    Permutation (elements_nat h) (x :: elements_nat h').
Proof.
  intros h x h' Hext.
  unfold extract_min_nat, PH.extract_min in Hext.
  destruct h as [| y hs].
  - discriminate Hext.  (* extract_min = None for Empty heap *)
  - inversion Hext; subst x h'.
    simpl.
    rewrite <- pairwise_meld_permutation_elements.
    reflexivity.
Qed.