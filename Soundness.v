Require Import SimpleNBE.Syntax.
Require Import SimpleNBE.Typing.
Require Import SimpleNBE.TypedSem.
Require Import SimpleNBE.PER.
Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.
Require Import Lia.
From Equations Require Import Equations.

Generalizable All Variables.

Fixpoint weaken (Γ : Ctx) : Subst :=
  match Γ with
  | nil => id
  | T :: Γ => (weaken Γ ∙ wk)
  end.

Fixpoint weaken_proof (Γ Δ : Ctx) : (Δ ++ Γ) ⊢s weaken Δ : Γ.
Proof.
  induction Δ.
  econstructor.
  econstructor.
  2 : exact IHΔ.
  econstructor.
Qed.  
Fixpoint weaken_comp (Γ Δ Δ' : Ctx) : (Δ' ++ Δ ++ Γ) ⊢s weaken Δ ∙ weaken Δ' ≈ weaken (Δ' ++ Δ) : Γ.
Proof.
  induction Δ'.
  - simpl.
    econstructor.
    eapply weaken_proof.
  - eapply eq_trans.
    -- eapply eq_sym.
       eapply eq_comp_assoc;try eapply weaken_proof.
       econstructor.
    -- eapply eq_comp_cong.
       --- econstructor.
       --- eapply IHΔ'.    
Qed.    
Notation Pred := (Exp -> D -> Prop).

Notation DPred := (Ctx -> Pred).
#[export]
Hint Resolve weaken_proof weaken_comp : snbe.

Inductive TopPred (Δ : Ctx) (σ : Subst) (t : Exp) (a : D) (T : Typ) : Prop :=
| top_pred (nf : Nf)
    (eval_nf : Rf (length Δ) -- df_down T a ↘ nf)
    (equiv_nf : Δ ⊢ t [ σ ] ≈ (NfToExp nf) : T).

Inductive Top (T : Typ) (Γ : Ctx) (t : Exp) (a : D) : Prop :=
| top (t_typed : Γ ⊢ t : T)
    (krip : ∀ Δ, TopPred (Δ ++ Γ) (weaken Δ) t a T).

Inductive BotPred (Δ : Ctx) (σ : Subst) (t : Exp) (e : Dn) (T : Typ) : Prop :=
| bot_pred (ne : Ne)
    (eval_ne : Re (length Δ) -- e ↘ ne)
    (equiv_ne : Δ ⊢ t [ σ ] ≈ (NeToExp ne) : T).

Inductive Bot (T : Typ) (Γ : Ctx) (t : Exp) (a : Dn) : Prop :=
| bot (t_typed : Γ ⊢ t : T)
      (krip : ∀ Δ, BotPred (Δ ++ Γ) (weaken Δ) t a T).


Inductive FunPred (B : DPred) (Δ : Ctx) (σ : Subst) (t s: Exp) (f a : D) : Prop :=
| funpred (fa : D) (eval_fa : app_eval f a fa) (app_B : B Δ (t [ σ ] $ s) fa).

Inductive FunInterp (Γ : Ctx) (M : Typ) (A : DPred) (T : Typ) (B : DPred) (t : Exp) (f : D) : Prop :=
| funinterp (t_fun : Γ ⊢ t : (M --> T)) (krip : ∀ Δ s a, A (Δ ++ Γ) s a -> FunPred B (Δ ++ Γ) (weaken Δ) t s f a).

Notation "⦃ Γ ⊨[ M ] A =>[ T ] B ⦄" := (FunInterp Γ M A T B).

Definition FunDPred (M : Typ) (A : DPred) (T : Typ) (B : DPred) : DPred :=
  λ Γ, ⦃ Γ ⊨[ M ] A =>[ T ] B ⦄.

Notation "[ M ] A =>[ T ] B" := (FunDPred M A T B) (at level 80).


Fixpoint TypeInterp (T : Typ) : DPred :=
  match T with
  | Bool => Top Bool
  | M --> T => [ M ] (TypeInterp M) =>[ T ] (TypeInterp T)
  end.

Notation "⟦ T ⟧" := (TypeInterp T) (at level 90).

Lemma Interp_to_wf : `(⟦ T ⟧ Γ t e -> Γ ⊢ t : T).
Proof.
  intros.
  induction T;destruct H;eauto.
Qed.

Lemma Bot_to_Top_Bool : `(Bot Bool Γ t e -> Top Bool Γ t (d_up Bool e)).
Proof.
  intros.
  inversion H.
  econstructor;eauto.
  intros.
  destruct (krip Δ).
  econstructor.
  econstructor;eauto.
  exact equiv_ne.
Qed.  

Lemma var_Bot_helper (Δ : Ctx) : `(Δ ++ M :: Γ ⊢ var 0 [ weaken Δ ] ≈ var (length (Δ ++ M :: Γ) - (length Γ) - 1) : M).
Proof.
  intros.
  dependent induction Δ.
  
  1-2 : simpl weaken.
  eapply trans.

  { eapply sub_id.
    econstructor.
    econstructor.
  }
  simpl app.
  enough (length (M :: Γ) - length Γ = 1).
  rewrite H.
  assert (1-1 = 0) by lia.
  rewrite H0.
  econstructor;econstructor.
  simpl.
  induction (length Γ).
  reflexivity.
  lia.

  
  eapply trans.
  eapply sub_comp;eauto with snbe.
  econstructor.
  econstructor;econstructor.
  eapply trans.
  eapply sub_cong.
  econstructor.
  eapply IHΔ.
  eapply trans.
  eapply wk_lookup.
  admit.
  
Admitted.

Lemma var_Bot : `(Bot M (M :: Γ) (var 0) (dn_l (length Γ))).
Proof.
  intros.
  do 4 econstructor.
  eapply var_Bot_helper.
Qed.

Lemma Bot_to_interp : `(Bot T Γ t e -> ⟦ T ⟧ Γ t (d_up T e))
with Top_to_interp : `(⟦ T ⟧ Γ t a -> Top T Γ t a).
Proof.
  - intros.
    inversion H.
    dependent induction T;simpl.
    econstructor;eauto.
    intro. 
    destruct (krip Δ).
    econstructor;eauto with snbe.
    econstructor;eauto with snbe.
    intros.
    destruct ((Top_to_interp _ _ _ _ H0)).
    econstructor;eauto with snbe.
    eapply IHT2.
    econstructor;eauto with snbe.
    econstructor;eauto with snbe.
    econstructor;eauto with snbe.
    
    intros.
    destruct (krip (Δ0 ++ Δ)).
    destruct (krip0 Δ0).
    econstructor.
    econstructor.
    
    assert ((Δ0 ++ Δ) ++ Γ = Δ0 ++ Δ ++ Γ) by eauto using app_assoc.
    rewrite <- H1.
    exact eval_ne.

    exact eval_nf.
    assert ((Δ0 ++ Δ) ++ Γ = Δ0 ++ Δ ++ Γ) by eauto using app_assoc.
    rewrite <- H1.
    simpl.
    eapply trans.
    eapply app_sub.
    rewrite -> H1.
    eapply weaken_proof.
    econstructor;eauto with snbe.
     eauto.
    eapply app_cong.
    eapply trans.
    eapply sym.
    eapply sub_comp;eauto with snbe.
    rewrite  H1.
    eapply weaken_proof.
    eapply trans.
    2 : exact equiv_ne.
    eapply sub_cong.
    rewrite H1.
    eapply weaken_comp.
    eapply term_eq_refl;eauto.
    rewrite H1.
    exact equiv_nf.
    econstructor;eauto with snbe.
    econstructor;eauto with snbe.

    intro.
    assert ((Δ0 ++ Δ) ++ Γ = Δ0 ++ Δ ++ Γ) by eauto using app_assoc.
    destruct (krip (Δ0 ++ Δ)).
    destruct (krip0 Δ0).
    econstructor.
    econstructor;eauto with snbe.
    rewrite <- H1.
    exact eval_ne.
     eapply trans.
    eapply app_sub.
    eapply weaken_proof.
    econstructor;eauto with snbe.
    eauto.
    eapply app_cong.
    eapply trans.
    eapply sym.
    eapply sub_comp;eauto with snbe.
    
    eapply trans.
    2 : rewrite <- H1.
    2 : exact equiv_ne.
    eapply sub_cong.
    eapply weaken_comp.
    eapply (term_eq_refl _ _ _ t_typed). 
    exact equiv_nf.
  - intros.
    dependent induction T.
    -- destruct H.
       clear Top_to_interp.
       econstructor;eauto with snbe.
    -- destruct H.
       econstructor;eauto with snbe.
       intro.
       pose proof (Bot_to_interp _ _ _ _ (var_Bot T1 (Δ ++ Γ))).
       assert (T1 :: Δ ++ Γ = (T1 :: Δ) ++ Γ) by eauto using app_assoc.
       rewrite H0 in H.
       destruct (krip _ _ _ H).
       destruct (IHT2 _ _ _ app_B).
       destruct (krip0 nil).
       simpl in equiv_nf, eval_nf.
       
       econstructor;eauto with snbe.

       simpl.
       eapply trans.
       eapply lam_eta.
       econstructor;eauto with snbe.
 
       eapply lam_cong.
       eapply trans.
       2 : exact equiv_nf.
       eapply trans.
       2: eapply sym;eapply sub_id.
       eapply app_cong.
       eapply sym.
       eapply sub_comp.
       econstructor.
       eapply weaken_proof.
       exact t_fun.
       econstructor.
       econstructor.
       econstructor.
       econstructor;eauto with snbe.
       econstructor;eauto with snbe.
       econstructor.
        econstructor.
       econstructor.
Qed.

Lemma eq_sep : `(Γ ⊢ t ≈ t' : T -> Γ ⊢ t : T ∧ Γ ⊢ t' : T) with sub_eq_sep : `(Γ ⊢s σ ≈ σ' : Δ -> Γ ⊢s σ : Δ ∧ Γ ⊢s σ' : Δ).
Proof.
  - intros.
    induction H;split;
      try econstructor;
      try destruct (IHwf_term_eq);
      try destruct (IHwf_term_eq1);
      try destruct (IHwf_term_eq2);
      try destruct (sub_eq_sep _ _ _ _ H);
      eauto with snbe;
      try econstructor;
      eauto with snbe.
    all: econstructor;do 2 (try econstructor);eauto.
  - intros.
    induction H;split;
      try econstructor;
      try destruct (IHwf_sub_eq);
      try destruct (IHwf_sub_eq1);
      try destruct (IHwf_sub_eq2);
      try destruct (eq_sep _ _ _ _ H0);
      eauto with snbe;
      try econstructor;
      eauto with snbe.
    all: econstructor;econstructor;eauto.
Qed.

Lemma interp_respects_trans : `(⟦ T ⟧ Γ t a -> Γ ⊢ t' ≈ t : T -> ⟦ T ⟧ Γ t' a).
Proof.
  intros.
  dependent induction T.
  - econstructor.
    -- destruct (eq_sep _ _ _ _ H0).
       exact H1.
    -- destruct H. intro.
       destruct (krip Δ).
       econstructor;eauto with snbe.
       eapply trans.
       2: exact equiv_nf.
       eapply sub_cong.
       2 : exact H0.
       eapply sub_eq_refl;eauto with snbe.
  - econstructor.
    -- destruct (eq_sep _ _ _ _ H0).
       exact H1.
    -- intros.
       destruct H.
       destruct (krip _ _ _ H1).
       econstructor;eauto with snbe.
       eapply IHT2.
       exact app_B.
       eapply app_cong.
       eapply sub_cong.
       eapply sub_eq_refl;eauto with snbe.
       exact H0.
       eapply term_eq_refl.
       eapply (Interp_to_wf _ _ _ _ H1).
Qed.
#[export]
Hint Resolve Top_to_interp Bot_to_interp var_Bot Interp_to_wf weaken_comp weaken_proof : snbe.

Inductive sub_env_equiv (σ : Subst) (p : Env) (Γ Δ : Ctx) : Prop :=
| sub_env_eq (wf_sub : Δ ⊢s σ : Γ) (lkup : ∀ x T, x |: T ∈! Γ -> ⟦ T ⟧ Δ (var x [ σ ]) (p x)).

Notation "σ ~ p ∈⟦ Γ ⟧ Δ" := (sub_env_equiv σ p Γ Δ) (at level 80).


Lemma interp_weaken : `(⟦ T ⟧ Γ t a -> ⟦ T ⟧ (Δ ++ Γ) (t [ weaken Δ ]) a).
Proof.
  intros.
  dependent induction T.
  - destruct H.
    destruct (krip Δ).
    econstructor.
    econstructor;eauto with snbe.
    intros.
    assert ((Δ0 ++ Δ) ++ Γ = Δ0 ++ Δ ++ Γ) by eauto using app_assoc.
    destruct (krip (Δ0 ++ Δ)).
    rewrite H in *.
    econstructor;eauto with snbe.
    eapply trans.
    2: exact equiv_nf0.
    eapply trans.
    eapply sym.
    eapply sub_comp.
    eapply weaken_proof.
    eapply weaken_proof.
    exact t_typed.
    eapply sub_cong.
    2: eapply (term_eq_refl _ _ _ t_typed).
    eapply weaken_comp.
  - destruct H.
    econstructor.
    econstructor;eauto with snbe.
    intros.
    assert ((Δ0 ++ Δ) ++ Γ = Δ0 ++ Δ ++ Γ) by eauto using app_assoc.
    rewrite <- H0 in H.
    destruct (krip _ _ _ H).
    econstructor;eauto with snbe.
    eapply interp_respects_trans.
    rewrite H0 in app_B.
    exact app_B.
    eapply app_cong.
    2: { eapply (term_eq_refl).
         rewrite <- H0.
         eapply (Interp_to_wf _ _ _ _ H).
       }  
    eapply trans.
    eapply sym.
    eapply sub_comp.
    eapply weaken_proof.
    eapply weaken_proof.
    exact t_fun.
    eapply sub_cong.
    eapply weaken_comp.
    eapply (term_eq_refl _ _ _ t_fun).
Qed.

Lemma senv_extend : `((σ ~ p ∈⟦ Γ ⟧ Δ) -> (⟦ T ⟧ (Δ' ++ Δ) t a) -> (((σ ∙ weaken Δ'),, t) ~ (p ↦ a) ∈⟦ T :: Γ ⟧ Δ' ++ Δ)).
Proof.
  intros.
  inversion H.
  econstructor.
  econstructor;eauto with snbe.
  econstructor;eauto with snbe.
  intros.
  inversion H1;subst.
  eapply interp_respects_trans.
  simp extend.
  econstructor.
  econstructor;eauto using weaken_proof with snbe.
  eapply (Interp_to_wf _ _ _ _ H0).
  simp extend.
  eapply interp_respects_trans.
  eapply interp_weaken.
  eapply (lkup _ _ H5).
  eapply trans.
  2 : {
      eapply sub_comp;
      eauto using weaken_proof with snbe.
      econstructor; exact H5.
  }
  eapply ext_var_s;try econstructor;eauto using weaken_proof with snbe.  
Qed.  

Record Intp (Δ : Ctx) (σ : Subst) (p : Env) (t : Exp) (T : Typ) : Prop := mk_intp
{
  val_t : D ;
  eval_t : tm_eval t p val_t (* ⟦ t ⟧ p ↘ val_t *) ;
  tT : ⟦ T ⟧ Δ (t [ σ ]) val_t ;
}.

Definition tm_sem (Γ : Ctx) (t : Exp) (T : Typ) : Prop :=
  ∀ σ p Δ, σ ~ p ∈⟦ Γ ⟧ Δ -> Intp Δ σ p t T.

Notation "Γ ⊨ t : T" := (tm_sem Γ t T).

Record Intps (Δ' : Ctx) (σ' : Subst) (p : Env) (σ : Subst) (Δ : Ctx) : Prop := mk_intps
{ 
  val_σ : Env ;
  eval_σ : sub_eval σ p val_σ ;
  asso : (σ ∙ σ') ~ val_σ ∈⟦ Δ ⟧ Δ' ;
}.

Definition sub_sem (Γ : Ctx) (σ : Subst) (Δ : Ctx) : Prop :=
  ∀ σ' p Δ',  σ' ~ p ∈⟦ Γ ⟧ Δ' -> Intps Δ' σ' p σ Δ.

Notation "Γ ⊨s σ : Δ" := (sub_sem Γ σ Δ).


Lemma id_init (Γ : Ctx) : id ~ InitialEnv Γ ∈⟦ Γ ⟧ Γ.
Proof.
  dependent induction Γ.
  - econstructor.
    -- econstructor.
    -- intros.
       inversion H.
  - econstructor.
    -- econstructor.
    -- intros.
       destruct IHΓ.
       inversion H;subst.
       --- eapply interp_respects_trans.
           simp InitialEnv.
           eapply Bot_to_interp.
           eapply var_Bot.
           econstructor;econstructor;auto.  
       --- eapply interp_respects_trans.  
           simp InitialEnv.
           exact (interp_weaken _ _ _ _ (a :: nil) (lkup _ _ H3)).
           simpl weaken.
           eapply trans.
           2 : {
             eapply sub_comp;econstructor;try econstructor.
             exact H3.
           }
           eapply trans.
           eapply sym.
           eapply trans.
           2 : { eapply sym. eapply sub_id.
                 econstructor;econstructor. exact H3.
           }
           eapply (wk_lookup _ _ _ _ H3).
           eapply sub_cong.
           2 : eapply term_eq_refl;econstructor;eauto.
           eapply eq_trans.
           2 : {eapply eq_sym. eapply eq_id_comp_l. econstructor;eauto with snbe. econstructor. }
           eapply eq_sym.
           eapply eq_id_comp_l.
           econstructor.           
Qed.

Lemma sem_to_tm : `(Γ ⊨ t : T ->
                    Γ ⊢ t : T).
Proof.
  intros.
  destruct (H _ _ _ (id_init Γ )).
  eapply Interp_to_wf.
  eapply interp_respects_trans.
  exact tT.
  eapply sym.
  pose proof (Interp_to_wf _ _ _ _ tT).
  inversion H0;subst.
  inversion H6;subst.
  eapply sub_id.
  exact H4.
Qed.

Lemma sem_to_sub : `(Γ ⊨s σ : Δ ->
                     Γ ⊢s σ : Δ).         
Proof.
  intros.
  destruct (H id (InitialEnv Γ) _ (id_init _)).
  destruct asso.
  inversion wf_sub;subst.
  inversion H3;subst.
  exact H5.
Qed.  


Lemma tm_var : `(x |: T ∈! Γ ->
                 Γ ⊨ var x : T).
Proof.
  intros.
  econstructor.
  1-2 : inversion H0;subst.
  - econstructor.
  - eapply (lkup _ _ H).
Qed.  

Lemma tm_true : `(Γ ⊨ true : Bool).
Proof.
  intros.
  econstructor;econstructor.
  - inversion H.
    econstructor;eauto with snbe.
    econstructor.
  - intro. econstructor.
    -- econstructor.
    -- simpl.
       destruct H.
       eapply trans.
       eapply sym.
       eapply sub_comp.
       eapply weaken_proof.
       exact wf_sub.
       econstructor.
       econstructor.
       econstructor;eauto using weaken_proof with snbe.
Qed.  

Lemma tm_false : `(Γ ⊨ false : Bool).
Proof.
  intros.
  econstructor;econstructor.
  - inversion H.
    econstructor;eauto with snbe.
    econstructor.
  - intro. econstructor.
    -- econstructor.
    -- simpl.
       destruct H.
       eapply trans.
       eapply sym.
       eapply sub_comp.
       eapply weaken_proof.
       exact wf_sub.
       econstructor.
       econstructor.
       econstructor;eauto using weaken_proof with snbe.
Qed.

Lemma ext_sub_lemma : `(Γ ⊢s σ : Γ' -> Γ' ⊢s σ' : Γ'' -> Γ' ⊢ t : T -> Γ ⊢s ((σ' ,, t) ∙ σ) ≈ ((σ' ∙ σ) ,, (t [ σ ])) : T :: Γ'').
Proof.
  intros.
  enough (Γ ⊢s ((σ' ,, t) ∙ σ) ≈
            ((wk ∙ ((σ' ,, t) ∙ σ)) ,, (var 0 [ (σ' ,, t) ∙ σ ])) : T :: Γ'').
  enough (Γ ⊢s ((wk ∙ ((σ' ,, t) ∙ σ)) ,, (var 0 [ (σ' ,, t) ∙ σ ])) ≈ ( (wk ∙ (σ' ,, t) ∙ σ) ,, (var 0 [σ' ,, t] [σ])) : T :: Γ'').
  enough (Γ ⊢s ((wk ∙ (σ' ,, t) ∙ σ) ,, (var 0 [σ' ,, t] [σ])) ≈ ((σ' ∙ σ) ,, (t [ σ ])) : T :: Γ'').
  eapply eq_trans.
  exact H2.
  eapply eq_trans.
  exact H3.
  eapply eq_trans.
  exact H4.
  eapply sub_eq_refl.
  econstructor;econstructor;eauto with snbe.

  - eapply eq_ext_cong.
    eapply eq_comp_cong.
    eapply (sub_eq_refl _ _ _ H).
    econstructor;eauto with snbe.
    econstructor.
    eapply (sub_eq_refl _ _ _ H).
    econstructor;eauto.
  - eapply eq_ext_cong.
    eapply eq_sym.
    eapply eq_comp_assoc;try econstructor;eauto.
    eapply sub_comp;try econstructor;eauto with snbe.
    econstructor.
  - eapply eq_ext_var.
    do 2 try econstructor;eauto with snbe.
Qed.  

Lemma tm_lam : `(M :: Γ ⊨ t : T ->
                             Γ ⊨ lam t : (M --> T)).
Proof.
  intros.
  econstructor;econstructor.
  inversion H0.
  pose proof (sem_to_tm _ _ _ H).
  econstructor;try econstructor;eauto with snbe.

  intros.
  destruct (H _ _ _ (senv_extend _ _ _ _ _ _ _ _ H0 H1)).
  econstructor.
  econstructor;try econstructor;eauto with snbe.
  eapply (interp_respects_trans _ _ _ _ _ tT).

  destruct (Top_to_interp _ _ _ _ H1).
  destruct (Top_to_interp _ _ _ _ tT).
  destruct (krip nil).
  destruct (krip0 nil).
  inversion H0;subst.
  pose proof (sem_to_tm _ _ _ H).
  simpl in *.
  
  eapply trans.
  eapply app_cong.
  eapply sym.
  eapply sub_comp;try econstructor;eauto with snbe.
  now eapply term_eq_refl.

  eapply trans.
  eapply app_cong.
  2 : eapply term_eq_refl;eauto.
  eapply lam_sub;try econstructor;eauto with snbe.

  eapply trans.
  eapply lam_beta;do 4 (try econstructor);eauto with snbe.

  eapply trans.
  eapply sym.
  eapply sub_comp;do 3 (try econstructor);eauto with snbe.

  eapply sub_cong.
  2 : eapply term_eq_refl;eauto.
  eapply eq_trans.

  eapply ext_sub_lemma;do 3 (try econstructor);eauto with snbe.

  eapply eq_ext_cong.
  eapply eq_trans.
  eapply eq_comp_assoc;do 2 (try econstructor);eauto with snbe.
  eapply eq_trans.
  eapply eq_comp_cong.
  eapply eq_wk_ext.
  1-3 : try econstructor;eauto with snbe.
  1-2 : eapply sub_eq_refl;eauto with snbe.
  eapply eq_id_comp_r;econstructor;eauto with snbe.
  econstructor;eauto with snbe.
  econstructor.
Qed.

Lemma tm_app : `(Γ ⊨ r : (M --> T) ->
                 Γ ⊨ m : M ->
                 Γ ⊨ (r $ m) : T).                
Proof.
  intros.
  intro.
  intros.
  destruct (H _ _ _ H1).
  destruct (H0 _ _ _ H1).
  destruct tT.
  destruct (krip nil _ _ tT0).
  inversion H1;subst.
  econstructor.
  eapply (eval_app _ _ _ _ _ _ eval_t eval_t0 eval_fa).
  eapply (interp_respects_trans _ _ _ _ _ app_B).
  simpl.
  eapply trans.
  eapply app_sub.
  exact wf_sub.
  exact (sem_to_tm _ _ _ H).
  exact (sem_to_tm _ _ _ H0).
  eapply app_cong.
  2 : eapply term_eq_refl;
      econstructor;
      eauto using sem_to_tm with snbe.
  eapply trans.
  2: eapply sub_comp;eauto with snbe.
  eapply sub_cong.
  econstructor.
  econstructor;eauto with snbe.
  eapply term_eq_refl.
  1,3: exact (sem_to_tm _ _ _ H).
  econstructor.
Qed.

Lemma tm_sub : `(Δ ⊨ t : T ->
                 Γ ⊨s σ : Δ ->        
                 Γ ⊨ (t [ σ ]) : T).        
Proof.
  intros.
  intro;intros.
  destruct (H0 _ _ _ H1).
  destruct (H _ _ _ asso).
  inversion H1;subst.
  pose proof (sem_to_tm _ _ _ H).
  pose proof (sem_to_sub _ _ _ H0).
  econstructor;eauto with snbe.
  eapply (interp_respects_trans _ _ _ _ _ tT).
  eapply sym.
  eapply (sub_comp _ _ _ _ _ _ _ wf_sub H3 H2).
Qed.  

Lemma sem_sub_id : `(Γ ⊨s id : Γ).
Proof.
  intros.
  intro;intros.
  inversion H;subst.
  econstructor;eauto with snbe.
  econstructor.
  econstructor;eauto with snbe.
  econstructor.

  intros.
  eapply (interp_respects_trans _ _ _ _ _ (lkup _ _ H0)).
  eapply sub_cong.
  econstructor.
  exact wf_sub.
  econstructor.
  exact H0.
Qed.  

Lemma sem_sub_wk : `(M :: Γ ⊨s wk : Γ).
Proof.
  intros;intro;intros.
  inversion H;subst.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eauto.
  econstructor.

  intros.
  eapply interp_respects_trans.
  simp drop.
  eapply lkup.
  econstructor;eauto.
  eapply trans.
  eapply sub_comp;eauto with snbe;try (econstructor;eauto).
  eapply sub_cong.
  eapply (sub_eq_refl _ _ _ wf_sub).
  econstructor.
  exact H0.
Qed.

Lemma sem_sub_comp : `(Γ ⊨s τ : Γ' ->
                   Γ' ⊨s σ : Γ'' ->
                   Γ ⊨s (σ ∙ τ) : Γ''                  
                     ).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ _ H1).
  destruct (H0 _ _ _ asso).
  inversion H1;inversion asso;inversion asso0;subst.
  pose proof (sem_to_sub _ _ _ H).
  pose proof (sem_to_sub _ _ _ H0).
  econstructor.
  econstructor;eauto with snbe.
  econstructor.
  econstructor;try econstructor;eauto with snbe.
  intros.
  eapply interp_respects_trans.
  eapply (lkup1 _ _ H4).
  eapply sub_cong.
  2 : econstructor;eauto.
  eapply eq_comp_assoc;eauto.
Qed.  
Lemma sem_sub_extend : `(Γ ⊨s σ : Δ ->
                     Γ ⊨ m : M ->
                     Γ ⊨s (σ ,, m) : M :: Δ).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ _ H1).
  destruct (H0 _ _ _ H1).
  pose proof (sem_to_sub _ _ _ H).
  pose proof (sem_to_tm _ _ _ H0).
  inversion H1;inversion asso;subst.
  econstructor.
  econstructor;eauto with snbe.
  econstructor.
  econstructor;eauto with snbe.
  econstructor;eauto with snbe.
  intros.
  inversion H4;subst.
  1-2 : simp extend.
  eapply interp_respects_trans.
  exact tT.
  eapply trans.
  eapply sub_comp;try econstructor;eauto with snbe.
  eapply sub_cong.
  eapply (sub_eq_refl _ _ _ wf_sub).
  econstructor;eauto.

  eapply interp_respects_trans.
  eapply (lkup0 _ _ H8).
  eapply trans.
  2 : eapply trans.
  eapply sub_comp;try econstructor;eauto with snbe.
  2 : eapply sym;eapply sub_comp;try econstructor;eauto with snbe.
  eapply sub_cong.
  eapply (sub_eq_refl _ _ _ wf_sub).
  eapply ext_var_s;eauto.
Qed.
#[local]
Hint Resolve sem_to_tm sem_to_sub tm_var tm_true tm_false tm_lam tm_app tm_sub sem_sub_id sem_sub_wk sem_sub_extend sem_sub_comp : snbe. 

Lemma fundamental : `(Γ ⊢ t : T -> Γ ⊨ t : T)
with fundamental_sub : `(Γ ⊢s σ : Δ -> Γ ⊨s σ : Δ).
Proof.
  - intros.
    clear fundamental.
    induction H;eauto with snbe.    
  - intros.
    clear fundamental_sub.
    induction H;eauto with snbe.
Qed.    
  

Record Soundness (Γ : Ctx) (p : Env) (t : Exp) (T : Typ) : Prop := mk_soundness
{
  nf : Nf ;
  nbe : NBE (length Γ) p t T nf ;
  eq_nf : Γ ⊢ t ≈ (NfToExp nf) : T ;
}.

Lemma soundness :`(Γ ⊢ t : T -> Soundness Γ (InitialEnv Γ) t T).
Proof.
  intros.
  pose proof (fundamental _ _ _ H).
  destruct (H0 _ _ _ (id_init _ )).
  destruct (Top_to_interp _ _ _ _ tT).
  destruct (krip nil).
  simpl in *.
  econstructor;try econstructor;eauto with snbe.
  eapply sym;eapply trans.
  2 : exact equiv_nf.
  eapply sym.
  eapply trans;
  eapply sub_id;eauto with snbe.
Qed.  

Lemma nbe_comp : `(Γ ⊢ t : T -> ∃ w, NBE (length Γ) (InitialEnv Γ) t T w).
Proof.
  intros.
  pose proof (fundamental _ _ _ H).
  destruct (H0 _ _ _ (id_init _ )).
  destruct (Top_to_interp _ _ _ _ tT).
  destruct (krip nil).
  simpl in *.
  econstructor;econstructor;eauto with snbe.
Qed.  


