Require Import SimpleNBE.Syntax.
Require Import SimpleNBE.Typing.
Require Import SimpleNBE.TypedSem.
Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Notation Ty := (D -> D -> Prop).
Notation Ev := (Env -> Prop).

Notation "d ∈! T" := (T d d) (at level 80).

Generalizable All Variables.
Definition Top : Df -> Df -> Prop :=
  `(∀ n, ∃ w : Nf, (Rf n -- d ↘ w) ∧ (Rf n -- d' ↘ w)).
Arguments Top df df' /.

Definition Bot : Dn -> Dn -> Prop :=
  `(∀ n, ∃ u, (Re n -- e ↘ u) ∧ (Re n -- e' ↘ u)).
Arguments Bot Dn Dn /.

Lemma l_in_bot (x : nat) : Bot (dn_l x) (dn_l x).
Proof.
  do 3 econstructor.
Qed.  

Lemma app_in_bot : `(Bot e e' -> Top d d' -> Bot (dn_app e d) (dn_app e' d')).
Proof.
  intros.
  intro.
  destruct (H n) as [? [? ?]].
  destruct (H0 n) as [? [? ?]].
  exists (ne_app x x0).
  split;econstructor;auto.
Qed.  



Record app_equivalence (f f' : D) (e e' : Dn) (M T : Typ) : Prop := mk_app_equiv
{
  fe : D ;
  f'e' : D ;
  eval_fe : f ∘ (d_up M e) ↘ fe ;
  eval_f'e' : f' ∘ (d_up M e') ↘ f'e' ;
  fe_top_f'e' : Top (df_down T fe) (df_down T f'e') ;
}.
(*
Record app_equivalence_of_T (f f' a a' : D) (T : Ty) : Prop := mk_app_equiv_T
{
  fa : D ;
  f'a' : D ;
  eval_fa : f ∘ a ↘ fa ;
  eval_f'a' : f' ∘ a' ↘ f'a' ;
  fa_T_f'a' : (T fa f'a') ;
}.
*)
Inductive app_equivalence_of_T' (f f' a a' : D) (T : Ty) : Prop :=
| app_eq_t
    (fa f'a': D)
    (eval_fa : f ∘ a ↘ fa)
    (eval_f'a' : f' ∘ a' ↘ f'a')
    (fa_T_f'a' : T fa f'a').

Notation "f ∘ a ≡ f' ∘ a' ∈ T" := (app_equivalence_of_T' f f' a a' T) (at level 80, f' at next level, a' at next level).


Notation "f ∘ e ≡ f' ∘ e' ∈[ M ---> T ]" := (app_equivalence f f' e e' M T) (at level 80, f' at next level, e' at next level).

Disable Notation "'l'' T x".
Lemma f_in_top (f f' : D) (M T : Typ) (bot_to_fe : ∀ e e', Bot e e' -> (f ∘ e ≡ f' ∘ e' ∈[ M ---> T ])) : Top (df_down (M --> T) f) (df_down (M --> T) f').
Proof.
  intro.
  destruct (bot_to_fe _ _ (l_in_bot n)).
  destruct (fe_top_f'e' (S n)) as [? [? ?]].
  exists (nf_lam x).
  split.
  - eapply (Rlam _ _ _ _ _ _ eval_fe H).
  - eapply (Rlam _ _ _ _ _ _ eval_f'e' H0).  
Qed.

#[export]
Hint Resolve f_in_top l_in_bot app_in_bot : snbe.

Definition fun_equiv (f f' : D) (M T : Ty) : Prop :=
  (∀ a a', M a a' -> (f ∘ a ≡ f' ∘ a' ∈ T)).
Arguments fun_equiv f f' M T /.


Definition ty_fun (M : Ty) (T : Ty) : Ty := λ a b, (fun_equiv a b M T).

Notation "M ==> T" := (ty_fun M T) (at level 80).

Inductive equiv_bool : Ty :=
| true_equiv : equiv_bool d_true d_true
| false_equiv : equiv_bool d_false d_false
| up_bool : `(Bot e e' -> equiv_bool (d_up T e) (d_up T e'))
.
#[export]
Hint Constructors equiv_bool : snbe.

Notation "a ≡ b ∈Bool" := (equiv_bool a b) (at level 80).

Lemma Bool_sym : `(a ≡ b ∈Bool -> b ≡ a ∈Bool).
Proof.
  intros.
  induction H;econstructor.
  intro.
  destruct (H n) as [? [? ?]].
  exists x.
  split.
  - exact H1.
  - exact H0.
Qed.  

Lemma Bool_trans : `(a ≡ a' ∈Bool -> a' ≡ a'' ∈Bool -> a ≡ a'' ∈Bool).
Proof.
  intros.
  induction H;inversion H0;(try (econstructor;assumption)).
  subst.
  econstructor.
  intro.
  destruct (H n) as [? [ex e'x]].
  destruct (H4 n) as [? [e'x0 e'0x0]].
  rewrite <- (re_det _ _ _ _ e'x e'x0) in e'0x0.
  exists x.
  split;assumption.
Qed.  


Fixpoint interp_type (T: Typ) : Ty :=
  match T with
  | Bool => equiv_bool
  | M --> T => (interp_type M) ==> (interp_type T)
  end.

Notation "⟦ T ⟧T" := (interp_type T) (at level 80).


Lemma interp_sym (T : Typ) (a b : D) (ab : ⟦ T ⟧T a b) : ⟦ T ⟧T b a.
Proof.
  dependent induction T;simpl.
  - apply (Bool_sym _ _ ab).
  - simpl in ab.
    do 3 intro.
    destruct (ab _ _ (IHT1 _ _ H)).    
    econstructor.
    -- exact eval_f'a'.
    -- exact eval_fa.
    -- exact (IHT2 _ _ fa_T_f'a').   
Qed.  

Lemma interp_trans (T : Typ) : `(⟦ T ⟧T a b -> ⟦ T ⟧T b c -> ⟦ T ⟧T a c).
Proof.
  intros.
  dependent induction T;simpl.
  - apply (Bool_trans _ _ _ H H0).
  - simpl in *.
    do 3 intro.
    destruct (H _ _ H1).
    destruct (H0 _ _ H1).
    destruct (H _ _ (interp_sym _ _ _ H1)).
    destruct (H0 _ _ (interp_sym _ _ _ H1)).
    destruct (H _ _ (IHT1 _ _ _ H1 (interp_sym _ _ _ H1))).
    destruct (H0 _ _ (IHT1 _ _ _ H1 (interp_sym _ _ _ H1))).
    assert (f'a' = fa2) by eauto using ap_det;subst.
    assert (fa = fa3) by eauto using ap_det;subst.
    assert (fa0 = f'a'3) by eauto using ap_det;subst.
    assert (f'a'3 = f'a'1) by eauto using ap_det;subst.
    econstructor.
    -- exact eval_fa.
    -- exact eval_f'a'0.
    -- eapply IHT2.
       exact fa_T_f'a'3.
       exact fa_T_f'a'0.
Qed.  

Lemma interp_refl (T : Typ) : `(⟦ T ⟧T a b -> ⟦ T ⟧T a a).
Proof.
  intros.
  eapply (interp_trans _ _ _ _ H (interp_sym _ _ _ H)).
Qed.  

#[export]
Hint Resolve Bool_sym Bool_trans interp_sym interp_trans interp_refl : snbe.

Notation "a ≡ b ∈^ T" := (Top (df_down T a) (df_down T b)) (at level 70, b at next level, T at next level).

Notation "↑ e ≡↑ e' ∈! T" := (Bot e e') (at level 80).


Record typ_equiv_rel (T : Typ) (A : Ty) : Prop := mk_typ_equiv_rel
{
  bot_imp : `(Bot e e' -> A (d_up T e) (d_up T e')) ;
  imp_top : `(A a b -> a ≡ b ∈^ T);
}.

Notation "T ⊩ A" := (typ_equiv_rel T A) (at level 80).

Lemma fun_equiv_rel : `(M ⊩ A -> U ⊩ B -> (M --> U) ⊩ (A ==> B)).
Proof.
  intros.
  econstructor.
  - intros.
    econstructor.
    constructor.
    constructor.
    inversion H.
    inversion H0.
    eapply bot_imp1.
    eapply (app_in_bot _ _ _ _ H1).
    eapply (imp_top0 _ _ H2).
  - simpl in *.
    intros.
    inversion H.
    inversion H0.
    pose proof (H1 _ _ (bot_imp0 _ _ (l_in_bot n))).
    destruct H2.
    destruct (imp_top1 _ _ fa_T_f'a' (S n)) as [? [? ?]].
    econstructor.
    split;econstructor;eauto with snbe.
Qed.
    
Lemma bool_interp : Bool ⊩ ⟦ Bool ⟧T.
Proof.
  econstructor.
  - intros.
    now econstructor.
  - intros.
    simpl in H.
    induction H.
    1-2 : econstructor;(split;econstructor).
    intro.
    destruct (H n) as [? [? ?]].
    exists (nf_ne x).
    split;econstructor.
    -- exact H0.
    -- exact H1.
Qed.

Lemma type_interp (T : Typ) : T ⊩ ⟦ T ⟧T.
Proof.
  dependent induction T.
  - exact bool_interp.
  - apply (fun_equiv_rel _ _ _ _ IHT1 IHT2).
Qed.

Lemma interp_to_top (T : Typ) : `(⟦ T ⟧T a a' -> Top (df_down T a) (df_down T a')).
Proof.
  intros.
  exact (imp_top _ _ (type_interp T) a a' H).
Qed.


Lemma bot_to_interp (T : Typ) : `(Bot e e' -> ⟦ T ⟧T (d_up T e) (d_up T e')).
Proof.
  dependent induction T.
  - intros.
    now econstructor.
  - intros.
    econstructor.
    econstructor.
    econstructor.
    eapply IHT2.
    eapply (app_in_bot _ _ _ _ H).
    eapply (interp_to_top _ _ _ H0).
Qed.

Definition env_equiv (p p' : Env) (Γ : Ctx) : Prop :=
  `(x |: T ∈! Γ -> ⟦ T ⟧T (p x) (p' x)).

Notation "p ≡ p' ∈⟦ Γ ⟧" := (env_equiv p p' Γ) (at level 60, p' at next level, Γ at next level).


Lemma env_equiv_sym (p p' : Env) (Γ : Ctx) : p ≡ p' ∈⟦ Γ ⟧ -> p' ≡ p ∈⟦ Γ ⟧.
Proof.
  intros.
  intro.
  intros.
  eapply interp_sym.
  exact (H x T H0).
Qed.  

Lemma env_equiv_refl (p p' : Env) (Γ : Ctx) : p ≡ p' ∈⟦ Γ ⟧ -> p ≡ p ∈⟦ Γ ⟧.
Proof.
  intros.
  intro.
  intros.
  eapply interp_refl.
  exact (H x T H0).
Qed.  


Lemma ctx_ext (p p' : Env) (Γ : Ctx) (p_eq : p ≡ p' ∈⟦ Γ ⟧) (a b : D)  (T : Typ) (aTb : ⟦ T ⟧T a b ) : (p ↦ a) ≡ (p' ↦ b) ∈⟦ T :: Γ ⟧.
Proof.
  generalize dependent T.
  intros.
  intro.
  intros.
  induction x.
  - simp extend.
    inversion H;subst.
    exact aTb.
  - simp extend.
    inversion H;subst.
    exact (p_eq x T0 H3).
Qed.

#[export]
Hint Resolve ctx_ext env_equiv_refl env_equiv_sym type_interp bot_to_interp interp_to_top : snbe.


Record interpreted_equivalent (s t : Exp) (p p' : Env) (T : Typ) : Prop := mk_interpreted_equivalent
{
  interp_s : D ;
  interp_t : D ;
  eval_s : ⟦ s ⟧ p ↘ interp_s ;
  eval_t : ⟦ t ⟧ p' ↘ interp_t ;
  equiv_T : ⟦ T ⟧T interp_s interp_t ;
}.

Notation "⟦ s ⟧ p ≡⟦ t ⟧ p' ∈ T" := (interpreted_equivalent s t p p' T) (at level 80).

Record interpreted_equivalent_sub (σ τ : Subst) (p p' : Env) (Γ : Ctx) : Prop := mk_interpreted_equivalent_sub
{
  interp_σ : Env;
  interp_τ : Env;
  eval_σ : ⟦ σ ⟧s p ↘ interp_σ;
  eval_τ : ⟦ τ ⟧s p' ↘ interp_τ;
  equiv_Γ : interp_σ ≡ interp_τ ∈⟦ Γ ⟧ ;
}.

Notation "⟦ σ ⟧ p ≡⟦ τ ⟧ p' ∈s Γ" := (interpreted_equivalent_sub σ τ p p' Γ) (at level 80).

Definition sem_tm_eq (Γ : Ctx) (t t' : Exp) (T : Typ) : Prop :=
  `(p ≡ p' ∈⟦ Γ ⟧ -> ⟦ t ⟧ p ≡⟦ t' ⟧ p' ∈ T).
Arguments sem_tm_eq Γ t t' T /. 

Notation "Γ ⊨ t ≈ t' : T" := (sem_tm_eq Γ t t' T) (at level 80, t at next level, t' at next level).

Notation "Γ ⊨ t : T" := (sem_tm_eq Γ t t T) (at level 80, t at next level).

Definition sem_sub_eq (Γ : Ctx) (σ τ : Subst) (Δ : Ctx) : Prop :=
  `(p ≡ p' ∈⟦ Γ ⟧ -> ⟦ σ ⟧ p ≡⟦ τ ⟧ p' ∈s Δ).
Arguments sem_sub_eq Γ σ τ Δ /.

Notation "Γ ⊨s σ ≈ τ : Δ" := (sem_sub_eq Γ σ τ Δ) (at level 80, σ at next level, τ at next level, Δ at next level).
Notation "Γ ⊨s σ : Δ" := (sem_sub_eq Γ σ σ Δ) (at level 80, σ at next level, Δ at next level).

Lemma tm_eq_sym (Γ : Ctx) (t t' : Exp) (T : Typ) : (Γ ⊨ t ≈ t' : T -> Γ ⊨ t' ≈ t : T).
Proof.
  simpl.
  intros.  
  destruct (H p' p (env_equiv_sym _ _ _ H0)).
  econstructor.
  3 : exact (interp_sym _ _ _ equiv_T).
  1-2: assumption.
Qed.  

Lemma tm_eq_trans (Γ : Ctx) (t t' t'' : Exp) (T : Typ) :  Γ ⊨ t ≈ t' : T -> Γ ⊨ t' ≈ t'' : T -> Γ ⊨ t ≈ t'' : T.
Proof.
  simpl.
  intros.
  destruct (H _ _  (env_equiv_refl _ _ _ H1)).
  destruct (H0 _ _ H1).
  rewrite (tm_det _ _ _ _ eval_t eval_s0) in *.
  econstructor;eauto with snbe.
Qed.  

Lemma initial_refl (Γ : Ctx) : InitialEnv Γ ≡ InitialEnv Γ ∈⟦ Γ ⟧.
Proof.
  intro.
  intros.
  induction H.
  - simp InitialEnv.
    eapply bot_to_interp.
    eapply l_in_bot.
  - simp InitialEnv.
Qed.
  
#[export]
Hint Resolve tm_eq_trans tm_eq_sym initial_refl : snbe.

#[export]
Hint Extern 4 (Top _ _) => intro;intros : snbe.
#[export]
Hint Extern 4 (Bot _ _) => intro;intros : snbe.
#[export]
Hint Extern 4 (env_equiv _ _ _) => intro;intros : snbe.
#[export]
Hint Extern 4 (sem_tm_eq _ _ _ _) => intro;intros : snbe.



