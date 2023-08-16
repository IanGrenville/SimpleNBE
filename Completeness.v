Require Import SimpleNBE.Syntax.
Require Import SimpleNBE.Typing.
Require Import SimpleNBE.TypedSem.
Require Import SimpleNBE.PER.
Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
From Equations Require Import Equations.

Generalizable All Variables.

Lemma sem_var_eq : `(x |: T ∈! Γ -> Γ ⊨ var x ≈ var x : T).
Proof.
  intros.
  intro.
  intros.
  econstructor;try econstructor.  
  exact (H0 _ _ H).
Qed.  

Lemma sem_true_eq : `(Γ ⊨ true ≈ true : Bool).
Proof.
  intros.
  repeat econstructor.
Qed.  
Lemma sem_false_eq : `(Γ ⊨ false ≈ false : Bool).
Proof.
  intros.
  repeat econstructor.
Qed.  
Lemma sem_lam_cong : `(M :: Γ ⊨ t ≈ t' : T ->
                       Γ ⊨ lam t ≈ lam t' : (M --> T)).
Proof.
  intros.
  econstructor;try constructor.
  intro.
  intro.
  intro.
  assert ((p ↦ a) ≡ (p' ↦ a') ∈⟦ M :: Γ ⟧).
  {
    intro.
    intros.
    dependent induction x.
    - inversion H2;subst.
      simp extend.
    - inversion H2;subst.
      simp extend.
      eapply (H0 _ _ H6).
  }
  destruct (H _ _ H2).
  econstructor;eauto with snbe. 
Qed.

Lemma sem_app_cong : `(Γ ⊨ r ≈ r' : (M --> T) ->
                       Γ ⊨ m ≈ m' : M ->             
                       Γ ⊨ (r $ m) ≈ (r' $ m') : T).
Proof.
  intros.
  intro.
  intros.
  
  pose proof (H _ _ H1).
  pose proof (H0 _ _ H1).
  destruct H2.
  destruct H3.
  simpl in *.
  pose proof (equiv_T interp_s0 interp_t0 equiv_T0).
  inversion H2.
  econstructor; eauto with snbe.
Qed.  
Lemma sem_lam_beta : `(M :: Γ ⊨ t : T ->
                 Γ ⊨ m : M ->
                 Γ ⊨ lam t $ m ≈ (t [ id ,, m ]) : T).
Proof.
  simpl.
  intros.
  destruct (H0 _ _ H1).
  assert ((p ↦ interp_s) ≡ (p' ↦ interp_t) ∈⟦ (M :: Γ) ⟧).
  {
    intro;intros.
    inversion H2;subst.
    simp extend.
    simp extend.
    eapply (H1 _ _ H6).
  }    
  destruct (H (p ↦ interp_s) (p' ↦ interp_t) H2).  
  econstructor;eauto with snbe.
Qed.  
Lemma sem_lam_eta : `(Γ ⊨ t : (M --> T) ->
              Γ ⊨ t ≈ lam (t [ wk ] $ var 0) : (M --> T)).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ H0).
  simpl in *.
  econstructor;eauto with snbe.
  intro;intros.
  destruct (equiv_T _ _ H1).
  econstructor;eauto with snbe.
Qed.  
Lemma sem_sub_id : `(Γ ⊨ t : T ->
             Γ ⊨ t [ id ] ≈ t : T).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ H0).
  simpl in *.
  econstructor;eauto with snbe.
Qed.  
Lemma sem_wk_lookup : `(x |: T ∈! Γ ->
                M :: Γ ⊨ var x [ wk ] ≈ var (S x) : T).
Proof.
  intros.
  intro;intros.
  pose proof (sem_var_eq _ _ _ H).
  inversion H;subst.
  econstructor;eauto with snbe.
  2: econstructor;eauto with snbe.
  1-2: simp drop.
  1-2: eapply H0.
  1-2: econstructor;eauto with snbe.
Qed.  
Lemma sem_sub_comp : `(Γ ⊨s τ : Γ' ->
                 Γ' ⊨s σ : Γ'' ->
                 Γ'' ⊨ t : T ->
                 Γ ⊨ t [ σ ∙ τ ] ≈ (t [ σ ] [ τ ]) : T).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ H2).
  destruct (H0 _ _ equiv_Γ).
  destruct (H1 _ _ equiv_Γ0).
  econstructor;eauto with snbe.
Qed.

Lemma sem_sub_cong : `(Γ ⊨s σ ≈ τ : Δ ->
                       Δ ⊨ t ≈ t' : T ->
                       Γ ⊨ (t [ σ ]) ≈ (t' [ τ ]) : T).
Proof.
  simpl.
  intros.
  destruct (H _ _ H1).
  destruct (H0 _ _ equiv_Γ).
  econstructor;eauto with snbe.
Qed.
  
Lemma sem_ext_var_z : `(Γ ⊨s σ : Δ ->
                 Γ ⊨ m : M ->
                 Γ ⊨ var 0 [ σ ,, m ] ≈ m : M).
Proof.
  simpl.
  intros.
  destruct (H _ _ H1).
  destruct (H0 _ _ H1).
  econstructor;eauto with snbe.
Qed.  
Lemma sem_ext_var_s : `(Γ ⊨s σ : Δ ->
                 Γ ⊨ m : M ->
                 x |: T ∈! Δ ->
                 Γ ⊨ var (S x) [ σ ,, m ] ≈ (var x [ σ ]) : T).
Proof.  
  simpl.
  intros.
  destruct (H _ _ H2).
  destruct (H0 _ _ H2).
  econstructor;eauto with snbe.
  simp extend.
  eauto with snbe.
Qed.

Lemma sem_app_sub : `(Γ ⊨s σ : Δ ->
                      Δ ⊨ r : (M --> T) ->
                      Δ ⊨ m : M ->
                      Γ ⊨ ((r $ m) [σ]) ≈ ((r [σ]) $ (m [σ])) : T).
Proof.
  intros.
  intro;intros.
  destruct (H _ _ H2).
  destruct (H0 _ _ equiv_Γ).
  destruct (H1 _ _ equiv_Γ).
  destruct (equiv_T _ _ equiv_T0).
  econstructor;eauto with snbe.
Qed.  


Lemma sem_sub_eq_wk : `(M :: Γ ⊨s wk ≈ wk : Γ).
Proof.
  intros.
  econstructor;eauto with snbe.
  intro;intros.
  simp drop.
  eapply H.
  econstructor;eauto.
Qed.  
Lemma sem_sub_eq_id : `(Γ ⊨s id ≈ id : Γ).
Proof.
  intros.
  econstructor;eauto with snbe.
Qed.  
Lemma sem_sub_eq_comp_cong : `(Γ ⊨s τ ≈ τ' : Γ' ->
                  Γ' ⊨s σ ≈ σ' : Γ'' ->
                  Γ ⊨s (σ ∙ τ) ≈ (σ' ∙ τ') : Γ'').
Proof.
  intros.
  intro;intros.
  destruct (H _ _ H1).
  destruct (H0 _ _ equiv_Γ).
  econstructor;eauto with snbe.
Qed.  

Lemma sem_sub_eq_ext_cong : `(Γ ⊨s σ ≈ σ' : Δ ->
                  Γ ⊨ m ≈ m' : M ->
                  Γ ⊨s σ ,, m ≈ (σ' ,, m') : M :: Δ).
Proof.
  simpl.
  intros.
  destruct (H _ _ H1).
  destruct (H0 _ _ H1).
  econstructor;eauto with snbe.
Qed.

Lemma sem_sub_eq_wk_ext : `( Γ ⊨s σ : Δ ->
                  Γ ⊨ m : M ->
                  Γ ⊨s wk ∙ (σ ,, m) ≈ σ : Δ).
Proof.
  simpl.
  intros.
  destruct (H _ _ H1).
  destruct (H0 _ _ H1).
  econstructor;eauto with snbe.
Qed.

Lemma sem_sub_eq_id_comp_l : `(Γ ⊨s σ : Δ ->
                  Γ ⊨s id ∙ σ ≈ σ : Δ).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  econstructor;eauto with snbe.
Qed.  

Lemma sem_sub_eq_id_comp_r : `(Γ ⊨s σ : Δ ->
                  Γ ⊨s σ ∙ id ≈ σ : Δ).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  econstructor;eauto with snbe.
Qed.  

Lemma sem_sub_eq_comp_assoc : `(Γ' ⊨s σ : Γ ->
                  Γ''  ⊨s σ' : Γ' ->
                  Γ'''  ⊨s σ'' : Γ'' ->
                  Γ''' ⊨s σ ∙ σ' ∙ σ'' ≈ (σ ∙ (σ' ∙ σ'')) : Γ).
Proof.
  simpl.
  intros.
  destruct (H1 _ _ H2).
  destruct (H0 _ _ equiv_Γ).
  destruct (H _ _ equiv_Γ0).
  econstructor;eauto with snbe.
Qed.  

Lemma sem_sub_eq_ext_var : `(Γ ⊨s σ : M :: Δ ->
                  Γ ⊨s σ ≈ ((wk ∙ σ) ,, (var 0 [ σ ])) : M :: Δ).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  econstructor;eauto with snbe.
  intro;intros.
  inversion H1;subst.
  1-2: simp extend drop;eauto with snbe.
Qed.

Lemma sem_true_sub_eq : `(Γ ⊨s σ : Δ ->
                          Γ ⊨ true [ σ ] ≈ true : Bool).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  econstructor;eauto with snbe.
  constructor.
Qed.  
Lemma sem_false_sub_eq : `(Γ ⊨s σ : Δ ->
                           Γ ⊨ false [ σ ] ≈ false : Bool).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  econstructor;eauto with snbe.
  constructor.
Qed.  
                            

Record Completeness' (n : nat) (p p' : Env) (s t : Exp) (T : Typ) : Prop := mk_completeness_alt
{
  nf : Nf ;
  nbs : NBE n p s T nf ;
  nbt : NBE n p' t T nf;
}. 

Definition Completeness (n : nat) (p : Env) (s t :Exp) (T : Typ) : Prop := Completeness' n p p s t T.

Arguments Completeness n p s t T /.

Lemma sat_consequence : `(Γ ⊨ s ≈ t : T -> forall n, p ≡ p' ∈⟦ Γ ⟧ -> Completeness' n p p' s t T).
Proof.
  simpl.
  intros.
  destruct (H _ _ H0).
  dependent induction T.
  simpl in *.
  - induction interp_s;inversion equiv_T;subst.
    3 : destruct (H4 n) as [? [? ?]].
    1-3 : econstructor.
    1-3 : econstructor;eauto with snbe.
    1-3 : econstructor;eauto with snbe.
  - simpl in *.
    pose proof (l_in_bot n).
    destruct (equiv_T (d_up T1 (dn_l n)) (d_up T1 (dn_l n)) (bot_to_interp _ _ _ H1)).
    assert (Top (df_down (T1 --> T2) interp_s) (df_down (T1 --> T2) interp_t)).
    {
      eapply f_in_top.
      intros.
      destruct (equiv_T (d_up T1 e) (d_up T1 e') (bot_to_interp _ _ _ H2)).
      econstructor;eauto with snbe.
    }
    destruct (H2 n) as [? [? ?]].
    econstructor;econstructor;eauto with snbe.
Qed.

Lemma sem_sound : `(Γ ⊢ t : T -> Γ ⊨ t : T)
  with sem_s_sound :`( Γ ⊢s σ : Δ -> Γ ⊨s σ : Δ).
Proof.
  - intros.
    induction H.
    -- eapply (sem_var_eq _ _ _ H).
    -- eapply (sem_true_eq).
    -- eapply (sem_false_eq).
    -- eapply (sem_lam_cong _ _ _ _ _ IHwf_term).
    -- eapply (sem_app_cong _ _ _ _ _ _ _ IHwf_term1 IHwf_term2).
    -- pose proof (sem_s_sound _ _ _ H0).
       eapply (sem_sub_cong _ _ _ _ _ _ _ H1 IHwf_term).
  - intros.
    induction H.
    -- eapply (sem_sub_eq_wk).
    -- eapply (sem_sub_eq_id).
    -- eapply (sem_sub_eq_comp_cong _ _ _ _ _ _ _ IHwf_sub1 IHwf_sub2).
    -- eapply (sem_sub_eq_ext_cong _ _ _ _ _ _ _ IHwf_sub (sem_sound _ _ _ H0)).   
Qed.  

Lemma Completeness0 : `(Γ ⊢ t : T -> Completeness (length Γ) (InitialEnv Γ) t t T).
Proof.
  intros.
  pose proof (sem_sound _ _ _ H).
  simpl in *.
  destruct (H0 (InitialEnv Γ) (InitialEnv Γ) (initial_refl _)).
  destruct (interp_to_top _ _ _ equiv_T (length Γ)) as [? [? ?]].
  econstructor;econstructor;eauto with snbe.    
Qed.  

Lemma nbe_comp : `(Γ ⊢ t : T -> exists w, NBE (length Γ) (InitialEnv Γ) t T w).
Proof.
  intros.
  pose proof (sem_sound _ _ _ H).
  destruct (H0 _ _ (initial_refl Γ)).
  destruct (interp_to_top _ _ _ equiv_T (length Γ)) as [? [? ?]].
  exists x.
  econstructor;eauto with snbe.
Qed.  

Lemma equivsem_sound : `(Γ ⊢ s ≈ t : T -> Γ ⊨ s ≈ t : T)
with equivsem_sub_sound : `(Γ ⊢s σ ≈ τ : Δ -> Γ ⊨s σ ≈ τ : Δ).
Proof.
  - intros.
    induction H.
    -- eapply (sem_var_eq _ _ _ H).
    -- eapply (sem_true_eq).
    -- eapply (sem_false_eq).
    -- eapply (sem_lam_cong _ _ _ _ _ IHwf_term_eq).
    -- eapply (sem_app_cong _ _ _ _ _ _ _ IHwf_term_eq1 IHwf_term_eq2).
    -- eapply (sem_sub_cong _ _ _ _ _ _ _  (equivsem_sub_sound _ _ _ _ H) IHwf_term_eq).
    -- eapply (sem_true_sub_eq _ _ _ (sem_s_sound _ _ _ H)).       
    -- eapply (sem_false_sub_eq _ _ _ (sem_s_sound _ _ _ H)).
    -- eapply (sem_app_sub _ _ _ _ _ _ _ (sem_s_sound _ _ _ H) (sem_sound _ _ _ H0) (sem_sound _ _ _ H1)).
    -- eapply (sem_lam_beta _ _ _ _ _ (sem_sound _ _ _ H) (sem_sound _ _ _ H0)).
    -- eapply (sem_lam_eta _ _ _ _ (sem_sound _ _ _ H)).
    -- eapply (sem_sub_id _ _ _ (sem_sound _ _ _ H)).
    -- eapply (sem_wk_lookup _ _ _ _ H).
    -- eapply (sem_sub_comp _ _ _ _ _ _ _ (sem_s_sound _ _ _ H) (sem_s_sound _ _ _ H0) (sem_sound _ _ _ H1)).
    -- eapply (sem_ext_var_z _ _ _ _ _  (sem_s_sound _ _ _ H) (sem_sound _ _ _ H0)).

    -- eapply (sem_ext_var_s _ _ _ _ _ _ _ (sem_s_sound _ _ _ H) (sem_sound _ _ _ H0) H1).
    -- eapply (tm_eq_sym _ _ _ _ IHwf_term_eq).
    -- eapply (tm_eq_trans _ _ _ _ _ IHwf_term_eq1 IHwf_term_eq2).

  - intros.  
    induction H.
    -- eapply (sem_sub_eq_wk).
    -- eapply (sem_sub_eq_id).
    -- eapply (sem_sub_eq_comp_cong _ _ _ _ _ _ _ IHwf_sub_eq1 IHwf_sub_eq2).
    -- eapply (sem_sub_eq_ext_cong _ _ _ _ _ _ _ IHwf_sub_eq (equivsem_sound _ _ _ _ H0)).
    -- eapply (sem_sub_eq_wk_ext _ _ _ _ _ (sem_s_sound _ _ _ H) (sem_sound _ _ _ H0)).
    -- eapply (sem_sub_eq_id_comp_l _ _ _ (sem_s_sound _ _ _ H)).
    -- eapply (sem_sub_eq_id_comp_r _ _ _ (sem_s_sound _ _ _ H)).
    -- pose proof (sem_s_sound _ _ _ H).
       pose proof (sem_s_sound _ _ _ H0).
       pose proof (sem_s_sound _ _ _ H1).
       eapply (sem_sub_eq_comp_assoc _ _ _ _ _ _ _ H2 H3 H4).
    -- eapply (sem_sub_eq_ext_var _ _ _ _ (sem_s_sound _ _ _ H)).
    -- simpl in *.
       intros.
       destruct (IHwf_sub_eq _ _ (env_equiv_sym _ _ _ H0)).
       econstructor;eauto with snbe.
    -- simpl in *.
       intros.
       pose proof (env_equiv_refl _ _ _ H1).
       pose proof (env_equiv_sym _ _ _ H1).
       pose proof (env_equiv_refl _ _ _ H3).
       destruct (IHwf_sub_eq1 _ _ H1).
       destruct (IHwf_sub_eq2 _ _ H4).
       rewrite (sub_det _ _ _ _ eval_τ eval_σ0) in *.
       econstructor;eauto with snbe.
Qed.

Lemma completeness : `(Γ ⊢ s ≈ t : T -> Completeness (length Γ) (InitialEnv Γ) s t T).
Proof.
  intros.
  eapply (sat_consequence _ _ _ _ _ _ (equivsem_sound _ _ _ _ H) _ (initial_refl _)).
Qed.  
  
