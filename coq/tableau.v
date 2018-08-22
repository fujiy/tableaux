Require Import List.
Require Import Bool.
Open Scope list_scope.
Load Arith.
Require Import Recdef.

Inductive form : Set :=
  | Atom : nat -> form
  | Neg  : form -> form
  | Conj : form -> form -> form
  | Disj : form -> form -> form
  | Impl : form -> form -> form.

(*
Definition foo (f : form) : nat :=
  match f with
    | Atom x => x
    | Neg (Atom x) => x
    | Neg (Neg a)  => 0
  end.
*)

Fixpoint form_size (f : form) : nat :=
  match f with
    | Atom _   => 1
    | Neg a    => 1 + form_size a
    | Conj a b => 2 + form_size a + form_size b
    | Disj a b => 2 + form_size a + form_size b
    | Impl a b => 2 + form_size a + form_size b
  end.

Lemma form_size_gt0 : forall (f : form),
  0 < form_size f.

  intro.
  induction f.
    compute.
    apply le_n.

    unfold form_size.
    apply gt_Sn_O.

    unfold form_size.
    apply gt_Sn_O.

    unfold form_size.
    apply gt_Sn_O.

    unfold form_size.
    apply gt_Sn_O.
Qed.

Lemma form_size_gt_conj_dm : forall (a b : form),
  form_size (Neg a) + form_size (Neg b) < form_size (Neg (Conj a b)).

  intros.
  unfold form_size.
  rewrite Nat.add_shuffle1.
  rewrite <- Nat.add_assoc.
  apply plus_lt_compat_l.
  rewrite Nat.add_assoc.
  apply plus_lt_compat_r.
  apply plus_lt_compat_r.
  apply Nat.lt_succ_diag_r.
Qed.

Fixpoint forms_size (l : list form) : nat :=
  match l with 
    | nil     => 0
    | f :: l' => form_size f + forms_size l'
  end.

Lemma forms_size_head : forall (l : list form) (f : form),
  forms_size (f :: l) = form_size f + forms_size l.

  intros.
  unfold forms_size.
  reflexivity.
Qed.

Lemma forms_size_app : forall (l1 l2: list form),
  forms_size (l1 ++ l2) = forms_size l1 + forms_size l2.

  intros.
  induction l1.
    reflexivity.

    rewrite <- app_comm_cons.
    rewrite forms_size_head.
    rewrite forms_size_head.
    rewrite IHl1.
    rewrite plus_assoc_reverse.
    reflexivity.
Qed.

(*
Lemma forms_size_add : forall (l : list form) (f : form),
  forms_size l < forms_size (f :: l).

  intros.
  rewrite <- plus_O_n at 1.
  unfold forms_size.
  apply plus_lt_compat_r.
  apply form_size_gt0.
Qed.

Lemma forms_size_lt_fst : forall (a b : form) (l : list form),
  form_size a < form_size b -> forms_size (a :: l) < forms_size (b :: l).

  intros.
  unfold forms_size.
  apply plus_lt_compat_r.
  apply H.
Qed.
*)

Lemma lt_plus_l : forall n m : nat, 0 < n -> m < n + m.
  intros.
  rewrite <- plus_O_n at 1.
  apply plus_lt_compat_r.
  apply H.
Qed.

Lemma lt_plus_r : forall n m : nat, 0 < n -> m < m + n.
  intros.
  rewrite plus_n_O at 1.
  apply plus_lt_compat_l.
  apply H.
Qed.

Function step (tl : list nat) (fl : list nat) (l : list form) {measure forms_size l} : bool :=
  match l with
    | nil => true
    | cons f l' =>
        match f with
          | Atom x =>
              if existsb (beq_nat x) fl
              then false
              else step (x :: tl) fl l'
          | Neg (Atom x) =>
              if existsb (beq_nat x) tl
              then false 
              else step tl (x :: fl) l'
          | Neg (Neg a) => 
              step tl fl (a :: l')
          | Conj a b =>
              step tl fl (a :: b :: l')
          | Neg (Conj a b) => orb
              (step tl fl (Neg a :: l'))
              (step tl fl (Neg b :: l'))
          | Disj a b => orb
              (step tl fl (a :: l'))
              (step tl fl (b :: l'))
          | Neg (Disj a b) =>
              step tl fl (Neg a :: Neg b :: l')
          | Impl a b => orb
              (step tl fl (Neg a :: l'))
              (step tl fl (b :: l'))
          | Neg (Impl a b) =>
              step tl fl (a :: Neg b :: l')
        end
  end.

  intros.
  rewrite forms_size_head.
  apply lt_plus_l.
  apply form_size_gt0.

  intros.
  rewrite forms_size_head.
  apply lt_plus_l.
  apply form_size_gt0.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite <- plus_assoc_reverse.
  apply lt_plus_l.
  apply Nat.lt_0_2.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  apply plus_lt_compat_l.
  apply lt_plus_l.
  apply Nat.lt_0_succ.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  apply plus_lt_compat_l.
  rewrite Nat.add_shuffle0.
  apply lt_plus_l.
  apply Nat.lt_0_succ.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  rewrite <- plus_assoc_reverse.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite <- Nat.add_assoc.
  apply plus_lt_compat_l.
  rewrite Nat.add_shuffle3.
  rewrite <- Nat.add_assoc.
  apply plus_lt_compat_r.
  apply Nat.lt_1_2.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  rewrite <- plus_assoc_reverse.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite Nat.add_shuffle3.
  apply plus_lt_compat_l.
  rewrite <- Nat.add_assoc.
  apply lt_plus_l.
  apply Nat.lt_0_2.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  rewrite <- plus_assoc_reverse.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite <- Nat.add_assoc.
  apply lt_plus_l.
  apply Nat.lt_0_2.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  apply lt_plus_l.
  apply Nat.lt_0_succ.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite Nat.add_shuffle0.
  apply lt_plus_l.
  apply Nat.lt_0_succ.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  apply lt_plus_l.
  apply Nat.lt_0_succ.

  intros.
  rewrite forms_size_head.
  rewrite forms_size_head.
  apply plus_lt_compat_r.
  unfold form_size.
  rewrite plus_assoc_reverse.
  apply plus_le_lt_compat.
    apply Nat.le_succ_diag_r.

    apply lt_plus_r.
    apply form_size_gt0.

Defined.


Definition tableau (premises : list form) (conseq : form) : bool :=
  negb (step nil nil (premises ++ (Neg conseq) :: nil)).


Eval compute in (tableau (Atom 0 :: nil) (Disj (Atom 0) (Atom 1))).
Eval compute in (tableau (Conj (Atom 0) (Atom 1) :: nil) (Atom 0)).
Eval compute in (tableau (Disj (Atom 0) (Atom 1) :: Neg (Atom 0) :: nil) (Atom 1)).
Eval compute in (tableau (Impl (Atom 0) (Atom 1) :: Atom 0 :: nil) (Atom 1)).
Eval compute in (tableau (Disj (Atom 0) (Atom 1) :: Impl (Atom 0) (Atom 2) :: Impl (Atom 1) (Atom 2) :: nil) (Atom 2)).
Eval compute in (tableau (Atom 0 :: Neg (Atom 0) :: nil) (Atom 1)).
Eval compute in (tableau (Impl (Atom 1) (Neg (Atom 0)) :: Impl (Neg (Atom 1)) (Atom 2) :: nil) (Impl (Atom 0) (Atom 2))).

Extraction Language Haskell.
