(* From HoTT Require Import Overture Datatypes.
Require Import Equations.Type.All. *)
From Coq Require Import Prelude List.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic.

Notation "e # t" := (transport _ e t) (at level 70).

Close Scope nat_scope.

Axiom Base : Set.

Inductive Ty : Set :=
  | base (b : Base)
  | arr (A B : Ty).

Notation "A → B" := (arr A B) (at level 70).

Definition Ctx := list Ty.

Notation "⋅" := (@nil Ty).
Notation "Γ ,, A" := (@cons Ty A Γ) (at level 50).
Notation "Γ ,,, Δ" := (@app Ty Δ Γ) (at level 60).


Inductive Var : Ctx -> Ty -> Set :=
  | here {Γ A} : Var (Γ ,, A) A
  | there {Γ A B} : Var Γ A -> Var (Γ,,B) A.


Equations lift_var {Γ Δ A B} (v : Var (Γ,,,Δ) A) : Var (Γ,,B,,,Δ) A :=
  lift_var (Δ := nil) here := (there here) ;
  lift_var (Δ := nil) (there v) := (there (there v)) ;
  lift_var (Δ := cons C Δ') here := here ;
  lift_var (Δ := cons C Δ') (there v) := there (lift_var v).

Module Export Tm.

Unset Elimination Schemes.

  #[private(matching)]Inductive Tm : Ctx -> Ty -> Set :=
    | var {Γ A} : Var Γ A -> Tm Γ A
    | lam {Γ} {A B : Ty} (t : Tm (Γ,, A) B) : Tm Γ (A → B)
    | app {Γ} {A B : Ty} (t : Tm Γ (A → B)) (u : Tm Γ A) : Tm Γ B.

  Notation "t @ u" := (app t u) (at level 50).

  Equations lift_tm {Γ Δ : Ctx} {A B} (t : Tm (Γ,,,Δ) A) : Tm (Γ,,B,,,Δ) A :=
    lift_tm (var v) := var (lift_var v) ;
    lift_tm (t @ u) := (lift_tm t) @ (lift_tm u) ;
    lift_tm (lam t) := lam (lift_tm (Δ := Δ,,_) t).

  Definition lift0_tm {Γ A B} (t : Tm Γ A) : Tm (Γ,,B) A := lift_tm (Δ := ⋅) t.

  Inductive  Sub : Ctx -> Ctx -> Set :=
    | snil {Γ} : Sub Γ ⋅
    | scons {Γ Δ A} : Sub Γ Δ -> Tm Γ A -> Sub Γ (Δ,,A).

  Notation "'ε'" := snil.
  Notation "t :: σ" := (scons σ t).

  Equations lift_sub {Γ Δ A} : Sub Γ Δ -> Sub (Γ,,A) Δ :=
    lift_sub ε := ε ;
    lift_sub (t :: σ) := (lift0_tm t) :: lift_sub σ.

  Equations id_sub {Γ} : Sub Γ Γ :=
    id_sub (Γ := ⋅) := ε ;
    id_sub (Γ := Γ,,A) := (var here) :: (lift_sub id_sub).

  Definition to_Sub {Γ A} (t : Tm Γ A) : Sub Γ (Γ,,A) := t :: id_sub.
  Coercion to_Sub : Tm >-> Sub.

  Definition shift {Γ Δ A} (σ : Sub Γ Δ) : Sub (Γ,,A) (Δ,,A) :=
    var here :: lift_sub σ.

  Equations sub_var {Γ Δ A} (σ : Sub Γ Δ) (v : Var Δ A) : Tm Γ A by struct σ :=
    sub_var (t :: _) here := t ;
    sub_var (_ :: σ) (there v) := sub_var σ v.
  
  Equations sub_tm {Γ Δ A} (σ : Sub Γ Δ) (t : Tm Δ A) : Tm Γ A by struct t :=
    sub_tm σ (var v) := sub_var σ v ;
    sub_tm σ (t @ u) := (sub_tm σ t) @ (sub_tm σ u) ;
    sub_tm σ (lam t) := lam (sub_tm (shift σ) t).

  Notation "t [ σ ]" := (sub_tm σ t) (at level 20).

  Axiom beta : forall {Γ A B} (t : Tm (Γ,,A) B) (u : Tm Γ A),
    (lam t) @ u = t[u] :> Tm Γ B.

  Definition Tm_ind
    (P : forall (Γ : Ctx) (A : Ty), Tm Γ A -> Type) :

    (forall (Γ : Ctx) (A : Ty) (v : Var Γ A), P Γ A (var v)) ->
    (forall (Γ : list Ty) (A B : Ty) (t : Tm (Γ,, A) B),
      P (Γ,, A) B t -> P Γ (A → B) (lam t)) ->
    (forall (Γ : Ctx) (A B : Ty) (t : Tm Γ (A → B)),
      P Γ (A → B) t -> forall u : Tm Γ A, P Γ A u -> P Γ B (t @ u)) ->

    (forall Γ A B (t : Tm (Γ,,A) B) (u : Tm Γ A) (x : P _ _ ((lam t) @ u)) (y : P _ _ (t[u])),
      (beta t u) # x = y) ->

    (forall (Γ : Ctx) (A : Ty) (t : Tm Γ A), P Γ A t) :=

  fun Hvar Hlam Happ _ =>
  fix f (Γ : Ctx) (A : Ty) (t : Tm Γ A) {struct t} : P Γ A t :=
    match t with
    | var v => Hvar _ _ v
    | lam t => Hlam _ _ _ _ (f _ _ t)
    | t @ u => Happ _ _ _ _ (f _ _ t) _ (f _ _ u)
    end.

End Tm.

Set Elimination Schemes.

Inductive RTm : forall {Γ A}, Tm Γ A -> Set :=
  | rvar {Γ A} (v : Var Γ A) : RTm (var v)
  | rlam {Γ} {A B} {t : Tm (Γ,, A) B} : RTm t -> RTm (lam t)
  | rapp {Γ} {A B : Ty} {t : Tm Γ (A → B)} {u : Tm Γ A} : RTm t -> RTm u -> RTm (t @ u).

Inductive RSub : forall {Γ Δ}, Sub Γ Δ -> Set :=
  | rnil {Γ} : RSub (Γ := Γ) ε
  | rcons {Γ Δ A} {σ : Sub Γ Δ} {t : Tm Γ A} : RTm t -> RSub σ -> RSub (t :: σ).

Equations lift_rtm {Γ Δ : Ctx} {A B} {t : Tm (Γ,,,Δ) A} (t' : RTm t) : RTm (lift_tm (B := B) t) :=
  lift_rtm (rvar v) := rvar (lift_var v) ;
  lift_rtm (rapp t' u') := rapp (lift_rtm t') (lift_rtm u') ;
  lift_rtm (rlam t') := rlam (lift_rtm (Δ := Δ,,_) t').

Definition lift0_rtm {Γ A B} {t : Tm Γ A} (t' : RTm t) : RTm (lift0_tm (B := B) t) :=
    lift_rtm (Δ := ⋅) t'.

#[derive(eliminator=no)]Equations
  rsub_var {Γ Δ A} {σ : Sub Γ Δ} (σ' : RSub σ) (v : Var Δ A) : RTm (sub_var σ v) :=
  
  rsub_var (rcons t' _) here := t' ;
  rsub_var (rcons _ σ') (there v) := rsub_var σ' v.

Equations lift_rsub {Γ Δ A} {σ : Sub Γ Δ} : RSub σ -> RSub (lift_sub (A := A) σ) :=
  
  lift_rsub rnil := rnil ;
  lift_rsub (rcons t' σ') := rcons (lift0_rtm t') (lift_rsub σ').


Equations id_rsub {Γ} : RSub (id_sub (Γ := Γ)) :=
  id_rsub (Γ := ⋅) := rnil ;
  id_rsub (Γ := Γ,,A) := rcons (rvar here) (lift_rsub id_rsub).

Definition to_RSub {Γ A} {t : Tm Γ A} (t' : RTm t) : RSub t := rcons t' id_rsub.
Coercion to_RSub : RTm >-> RSub.

Definition rshift {Γ Δ A} {σ : Sub Γ Δ} (σ' : RSub σ) : RSub (shift (A := A) σ) :=
  rcons (rvar here) (lift_rsub σ').

Equations rsub_tm {Γ Δ A} {σ : Sub Γ Δ} (σ' : RSub σ) {t : Tm Δ A} (t' : RTm t) : RTm (t[σ]) :=
  rsub_tm σ' (rvar v) := rsub_var σ' v ;
  rsub_tm σ' (rapp t' u') := rapp (rsub_tm σ' t') (rsub_tm σ' u') ;
  rsub_tm σ' (rlam t') := rlam (rsub_tm (rshift σ') t').

Reserved Notation "t ⤳ u" (at level 80).
Reserved Notation "t ⤳* u" (at level 80).


Inductive red : forall {Γ A} {t : Tm Γ A}, RTm t -> RTm t -> Set :=
  | red_beta {Γ A B} {t : Tm (Γ,,A) B} {u : Tm Γ A} (t' t'' : RTm t) (u' u'' : RTm u) :
      ((beta t u) # rapp (rlam t') u') ⤳ (rsub_tm u'' t'')

  | red_lam {Γ A B} {t : Tm (Γ,,A) B} (t' : RTm t) (t'' : RTm t) :
      t' ⤳ t'' -> (rlam t') ⤳ (rlam t'')

  | red_app {Γ A B} {t : Tm Γ (A → B)} {u : Tm Γ A} (t' t'' : RTm t) (u' u'' : RTm u) :
      t' ⤳ t'' -> u' ⤳ u'' -> (rapp t' u') ⤳ (rapp t'' u'')

  where "t ⤳ u" := (red t u).

Inductive clos_red {Γ A} {t : Tm Γ A} : RTm t -> RTm t -> Set :=
  | red_refl t' : t' ⤳* t'
  | red_trans (t1 t2 t3 : RTm t) : (t1 ⤳ t2) -> (t2 ⤳* t3) -> (t1 ⤳* t3)
  where "t ⤳* u" := (clos_red t u).

Definition join {Γ A} {t : Tm Γ A} (t' t'' : RTm t) :=
  {u & (t' ⤳* u) * (t'' ⤳* u)}.


Conjecture completeness : forall Γ A (t : Tm Γ A) (t' t'' : RTm t), join t' t''.


Module Export Quotient.

  Section Domain.

    Context {A : Type} (R : A -> A -> Type).

    Private Inductive quotient (R : A -> A -> Type) : Type :=
    | class_of : A -> quotient R.

    (** The path constructors. *)
    Axiom related_classes_eq
    : forall {x y : A}, R x y ->
                        class_of R x = class_of R y.

    Arguments class_of {_} _.

    Axiom quotient_set : forall x y : quotient R, forall p q : x = y, p = q.

    Definition quotient_ind (P : quotient R -> Type)
               (dclass : forall x, P (class_of x))
               (dequiv : (forall x y (H : R x y), (related_classes_eq H) # (dclass x) = dclass y))
    : forall q, P q
      := fun q => match q with class_of a => fun _ => dclass a end dequiv.

    Definition quotient_ind_compute {P} dclass dequiv x
    : @quotient_ind P dclass dequiv (class_of x) = dclass x.
    Proof.
      reflexivity.
    Defined.

  End Domain.

End Quotient.

Arguments class_of {_ _} _.

Definition QTm {Γ A} (t : Tm Γ A) := @quotient (RTm t) join.

Lemma quot_bind {A B} {R : A -> A -> Type} {R' : B -> B -> Type} (f : A -> quotient R') :
  (forall x y, R x y -> f x = f y) ->
  (quotient R -> quotient R').
Proof.
  intros Hf a.
  unshelve eapply quotient_ind.
  3: eassumption.
  all: try eassumption.
  intros ?? e.
  erewrite Hf.
  2: eassumption.
  now destruct (related_classes_eq R e).
Defined.

Conjecture rlam_join : forall {Γ A B} {t : Tm (Γ,,A) B} (t' t'' : RTm t), join t' t'' -> join (rlam t') (rlam t'').

Conjecture rapp_join_l : forall {Γ A B} {t : Tm Γ (A → B)} {u : Tm Γ A} (t' t'' : RTm t) (u' : RTm u),
  join t' t'' -> join (rapp t' u') (rapp t'' u').

Conjecture rapp_join_r : forall {Γ A B} {t : Tm Γ (A → B)} {u : Tm Γ A} (t' : RTm t) (u' u'' : RTm u),
  join u' u'' -> join (rapp t' u') (rapp t' u'').

Lemma beta_over {Γ A B} {t : Tm (Γ,,A) B} {u : Tm Γ A} {t' : RTm t} {u' : RTm u} :
  class_of (beta t u # (rapp (rlam t') u')) = class_of (rsub_tm u' t') :> QTm _.
Proof.
  apply related_classes_eq.
  econstructor.
  split.
  2: constructor.
  econstructor.
  2: constructor.
  constructor.
Qed.

Definition from_Tm {Γ A} (t : Tm Γ A) : QTm t.
Proof.
  revert Γ A t ; apply Tm_ind.
  - intros.
    exact (class_of (rvar v)).
  - intros.
    unshelve eapply quot_bind.
    5: eassumption.
    + intros t'.
      exact (class_of (rlam t')).
    + intros ; cbn.
      now apply related_classes_eq, rlam_join.
  - intros * t' ? u'.
    unshelve eapply quot_bind.
    5: exact t'.
    1: clear t' ; intros t' ; unshelve eapply quot_bind.
    5: exact u'.
    + clear u' ; intros u'.
      exact (class_of (rapp t' u')).
    + intros ; cbn.
      now apply related_classes_eq, rapp_join_r.
    + cbn.
      intros.
      pattern u'.
      unshelve eapply quotient_ind.
      * cbn.
        clear u' ; intros u'.
        now apply related_classes_eq, rapp_join_l.
      * cbn.
        intros.
        apply quotient_set.
  - intros.

