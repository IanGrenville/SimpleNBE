Require Import List.
Require Import SimpleNBE.Syntax.

From Equations Require Import Equations.


Inductive D : Set :=
| d_true : D
| d_false : D
| d_lam : Exp -> (nat -> D) -> D
| d_up : Typ -> Dn -> D
with Dn : Set :=
| dn_l : nat -> Dn
| dn_app : Dn -> Df -> Dn
with Df : Set :=
| df_down : Typ -> D -> Df
.


Notation Env := (nat -> D).

Equations extend : Env -> D -> Env :=
  (extend p d) 0 := d;
  (extend p d) (S x) := p x;
.

Notation "p ↦ a" := (extend p a) (at level 80).
                        
Equations drop : Env -> Env :=
  (drop p n) := p (S n).

Notation "'l'' T x" := (d_up T (dn_l x)) (at level 80).
Notation "[ T ] x $' y" := (d_up T (dn_app x y)) (at level 80).


Reserved Notation "A ∘ B ↘ C" (at level 80, B at next level, C at next level). 
Reserved Notation "⟦ A ⟧ B ↘ C" (at level 80, B at next level, C at next level).
Reserved Notation "⟦ A ⟧s B ↘ C" (at level 80, B at next level, C at next level).

Generalizable All Variables.                  

Inductive app_eval : D -> D -> D -> Prop :=
| app_lam : `(⟦ t ⟧ (p ↦ a) ↘ b ->
              (d_lam t p) ∘ a ↘ b)
| app_app : `(d_up (M --> T) e ∘ a ↘ d_up T (dn_app e (df_down M a)))
where "A ∘ B ↘ C" := (app_eval A B C)
with tm_eval : Exp -> Env -> D -> Prop :=
| eval_var : `(⟦ var n ⟧ p ↘ p n)
| eval_true : `(⟦ true ⟧ p ↘ d_true)
| eval_false : `(⟦ false ⟧ p ↘ d_false)
| eval_lam : `(⟦ lam t ⟧ p ↘ d_lam t p)
| eval_app : `(⟦ r ⟧ p ↘ f ->
               ⟦ s ⟧ p ↘ a ->
               f ∘ a ↘ b ->
               ⟦ r $ s ⟧ p ↘ b)
| eval_sub : `(⟦ σ ⟧s p ↘ p' ->
               ⟦ t ⟧ p' ↘ a ->
               ⟦ t [ σ ] ⟧ p ↘ a)
where "⟦ A ⟧ B ↘ C" := (tm_eval A B C)
with sub_eval : Subst -> Env -> Env -> Prop :=
| eval_wk : `(⟦ wk ⟧s p ↘ drop p)
| eval_id : `(⟦ id ⟧s p ↘ p)
| eval_comp : `(⟦ τ ⟧s p ↘ p' ->
                ⟦ σ ⟧s p' ↘ p'' ->
                ⟦ (σ ∙ τ) ⟧s p ↘ p'')
| eval_ext : `( ⟦ σ ⟧s p ↘ p' ->
                ⟦ t ⟧ p ↘ a ->
                ⟦ σ ,, t ⟧s p ↘ (p' ↦ a))
where "⟦ A ⟧s B ↘ C" := (sub_eval A B C)  
.

Lemma ap_det (f a b b': D) (ev_b : f ∘ a ↘ b) (ev_b' : f ∘ a ↘ b') : b = b'
with tm_det (t : Exp) (p : Env) (a a' : D) `(ev_a : ⟦ t ⟧ p ↘ a) (ev_a' : ⟦ t ⟧ p ↘ a') : a = a'
with sub_det (σ : Subst) (p p' p'' : Env) (eval_p' : ⟦ σ ⟧s p ↘ p') (eval_p'' : ⟦ σ ⟧s p ↘ p'') : p' = p''.
Proof.
  - inversion ev_b;inversion ev_b';subst.
    -- inversion H4;subst.
       exact (tm_det _ _ _ _ H H3).
    -- inversion H3.
    -- inversion H3.
    -- inversion H2;subst.
       reflexivity.
  - inversion ev_a;inversion ev_a';subst;
      (try ((first [inversion H2 | inversion H5 | inversion H4]);congruence)). 
    -- inversion H8;subst.
       rewrite <- (tm_det _ _ _ _ H H5) in H7.
       rewrite <- (tm_det _ _ _ _ H0 H6) in H7.
       exact (ap_det _ _ _ _ H1 H7).
    -- inversion H6;subst.
       rewrite (sub_det _ _ _ _ H H4) in H0.
       exact (tm_det _ _ _ _ H0 H5).
  - inversion eval_p';inversion eval_p'';subst;
      (try (first [reflexivity | congruence | inversion H2])).
    -- inversion H6;subst.
       rewrite (sub_det _ _ _ _ H H4) in H0.
       exact (sub_det _ _ _ _ H0 H5).
    -- inversion H6;subst.
       rewrite (tm_det _ _ _ _ H0 H5).
       rewrite (sub_det _ _ _ _ H H4).
       reflexivity.
Qed.

Reserved Notation "'Rf' A -- B ↘ C" (at level 90, B at next level, C at next level).
Reserved Notation "'Re' A -- B ↘ C" (at level 90, B at next level, C at next level).

Inductive rf_eval : nat -> Df -> Nf -> Prop :=
| Rtrue : `(Rf n -- (df_down Bool d_true) ↘ nf_true)
| Rfalse: `(Rf n -- (df_down Bool d_false) ↘ nf_false)
| Rlam : `(f ∘ (d_up M (dn_l n)) ↘ a ->
           Rf (S n) -- (df_down T a) ↘ w ->
           Rf n -- (df_down (M --> T) f) ↘ nf_lam w)
| Rne : `( Re n -- e ↘ u ->
          Rf n -- df_down Bool (d_up T e) ↘ nf_ne u)
where "'Rf' A -- B ↘ C" := (rf_eval A B C)
with re_eval : nat -> Dn -> Ne -> Prop :=
| Rl : `(Re n -- dn_l x ↘ ne_var (n - x - 1))
| Rapp : `(Re n -- e ↘ u ->
           Rf n -- d ↘ w ->
           Re n -- (dn_app e d) ↘ (ne_app u w))
where "'Re' A -- B ↘ C" := (re_eval A B C).  


Lemma rf_det (n : nat) (d : Df) (w w' : Nf) (rf_w : Rf n -- d ↘ w ) (rf_w' : Rf n -- d ↘ w') : w = w'
with re_det (n : nat) (d : Dn) (u u' : Ne) (re_u : Re n -- d ↘ u) (re_u' : Re n -- d ↘ u' ) : u = u'.
Proof.
  - inversion rf_w;inversion rf_w';subst;
      (try (first [reflexivity | congruence])).
    -- inversion H7;subst.
       rewrite (ap_det _ _ _ _ H H4) in H0.
       rewrite (rf_det _ _ _ _ H0 H5).
       reflexivity.
    -- inversion H5;subst.
       rewrite (re_det _ _ _ _ H H3).
       reflexivity.
  - inversion re_u;inversion re_u';subst;
      (try (first [reflexivity | congruence])).
    -- inversion H7;subst.
       rewrite (re_det _ _ _ _ H H4).
       rewrite (rf_det _ _ _ _ H0 H5).
       reflexivity.   
Qed.

Record NBE (n : nat) (p : Env) (t : Exp) (T : Typ) (w : Nf) : Prop := mk_nbe
{
  val_t : D ;
  eval_t : ⟦ t ⟧ p ↘ val_t ;
  down_t : Rf n -- (df_down T val_t) ↘ w
}.
Equations InitialEnv : Ctx -> Env :=
  InitialEnv nil i := d_true ;
  InitialEnv (T :: Γ) 0 := d_up T (dn_l (List.length Γ)) ;
  InitialEnv (T :: Γ) (S i) := InitialEnv Γ i;
.
                               
#[export]
  Hint Constructors app_eval tm_eval sub_eval rf_eval re_eval: snbe.

#[export]
Hint Resolve ap_det tm_det sub_det re_det rf_det : snbe. 
