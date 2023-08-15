Require Import List.
Require Import Unicode.Utf8_core.
Require Import SimpleNBE.Syntax.
Require Import Coq.Program.Equality.

Generalizable All Variables.

Reserved Notation "Γ ⊢ A ≈ B : T" (at level 80, A at next level, B at next level).
Reserved Notation "Γ ⊢ t : T" (no associativity, at level 80, t at next level).
Reserved Notation "Γ ⊢s σ : Δ" (no associativity, at level 80, σ at next level).
Reserved Notation "Γ ⊢s S1 ≈ S2 : Δ" (no associativity, at level 80, S1 at next level, S2 at next level).
Reserved Notation "x |: T ∈! Γ" (no associativity, at level 80, T at next level).

Inductive ctx_lookup : nat -> Typ -> Ctx -> Prop :=
  | here : `( 0 |: T ∈! (T :: Γ))
  | there : `( n |: T ∈! Γ -> (S n) |: T ∈! (M :: Γ))              
where "x |: T ∈! Γ" := (ctx_lookup x T Γ).



Inductive wf_term : Ctx -> Exp -> Typ -> Prop :=
| vlookup : `(
                x |: T ∈! Γ ->  
                Γ ⊢ var x : T)
| true_intro : `(Γ ⊢ true : Bool)
| false_intro : `(Γ ⊢ false : Bool)
| lam_intro : `(
                  M :: Γ ⊢ t : T ->
                  Γ ⊢ lam t : (M --> T))
| lam_elim : `(
                 Γ ⊢ r : (M --> T) ->
                 Γ ⊢ m : M ->        
                 Γ ⊢ (r $ m) : T)
| term_sub : `(
                 Δ ⊢ t : T ->
                 Γ ⊢s σ : Δ ->
                 Γ ⊢ (t [ σ ]) : T)
where "Γ ⊢ t : T" := (wf_term Γ t T)                            
with wf_sub : Ctx -> Subst -> Ctx -> Prop :=
| sb_wk : `(M :: Γ ⊢s wk : Γ)
| sb_id : `(Γ ⊢s id : Γ)
| sb_comp : `(
              Γ ⊢s τ : Γ' ->
              Γ' ⊢s σ : Γ'' ->
               Γ ⊢s (σ ∙ τ) : Γ'')
| sb_ext : `(
              Γ ⊢s σ : Δ ->
              Γ ⊢ m : M ->          
              Γ ⊢s (σ ,, m) : M :: Δ)        
where "Γ ⊢s σ : Δ" := (wf_sub Γ σ Δ).


Inductive wf_term_eq : Ctx -> Exp -> Exp -> Typ -> Prop :=
| var_eq : `(
               x |: T ∈! Γ ->
               Γ ⊢ var x ≈ var x : T)    
| true_eq : `(Γ ⊢ true ≈ true : Bool)
| false_eq : `(Γ ⊢ false ≈ false : Bool)
| lam_cong : `(
               M :: Γ ⊢ t ≈ t' : T ->
               Γ ⊢ lam t ≈ lam t' : (M --> T))
| app_cong : `(Γ ⊢ r ≈ r' : (M --> T) ->
               Γ ⊢ m ≈ m' : M ->             
               Γ ⊢ (r $ m) ≈ (r' $ m') : T)
| sub_cong : `(
                 Γ ⊢s σ ≈ σ' : Δ ->
                 Δ ⊢ t ≈ t' : T ->
                 Γ ⊢ (t [ σ ]) ≈ (t' [ σ' ]) : T)             
| true_sub : `(Γ ⊢s σ : Δ -> Γ ⊢ true [ σ ] ≈ true : Bool) 
| false_sub : `(Γ ⊢s σ : Δ -> Γ ⊢ false [ σ ] ≈ false : Bool)
| app_sub : `(Γ ⊢s σ : Δ →
                 Δ ⊢ r : (M --> T) →
                 Δ ⊢ m : M →
                 Γ ⊢ (r $ m) [ σ ] ≈ ((r [ σ ]) $ (m [ σ ])) : T)
| lam_beta : `(M :: Γ ⊢ t : T →
                 Γ ⊢ m : M →
                 Γ ⊢ lam t $ m ≈ (t [ id ,, m ]) : T)
| lam_eta : `(Γ ⊢ t : (M --> T) →
              Γ ⊢ t ≈ lam (t [ wk ] $ var 0) : (M --> T))
| sub_id : `(Γ ⊢ t : T →
             Γ ⊢ t [ id ] ≈ t : T)
| wk_lookup : `(x |: T ∈! Γ →
                M :: Γ ⊢ var x [ wk ] ≈ var (S x) : T)
| sub_comp : `(Γ ⊢s τ : Γ' →
                 Γ' ⊢s σ : Γ'' →
                 Γ'' ⊢ t : T →
                 Γ ⊢ t [ σ ∙ τ ] ≈ (t [ σ ] [ τ ]) : T)
| ext_var_z : `(Γ ⊢s σ : Δ →
                 Γ ⊢ m : M →
                 Γ ⊢ var 0 [ σ ,, m ] ≈ m : M)
| ext_var_s : `(Γ ⊢s σ : Δ →
                 Γ ⊢ m : M →
                 x |: T ∈! Δ →
                 Γ ⊢ var (S x) [ σ ,, m ] ≈ (var x [ σ ]) : T)
| sym : `(Γ ⊢ t ≈ t' : T -> Γ ⊢ t' ≈ t : T)
| trans : `(Γ ⊢ t ≈ t' : T →
                 Γ ⊢ t' ≈ t'' : T →
                 Γ ⊢ t ≈ t'' : T)
where "Γ ⊢ t ≈ t' : T" := (wf_term_eq Γ t t' T)
with wf_sub_eq : Ctx -> Subst -> Subst -> Ctx -> Prop :=
| eq_wk : `(M :: Γ ⊢s wk ≈ wk : Γ)
| eq_id : `(Γ ⊢s id ≈ id : Γ)
| eq_comp_cong : `(Γ ⊢s τ ≈ τ' : Γ' →
                  Γ' ⊢s σ ≈ σ' : Γ'' →
                  Γ ⊢s (σ ∙ τ) ≈ (σ' ∙ τ') : Γ'')

| eq_ext_cong : `(Γ ⊢s σ ≈ σ' : Δ →
                  Γ ⊢ m ≈ m' : M →
                  Γ ⊢s σ ,, m ≈ (σ' ,, m') : M :: Δ)

| eq_wk_ext : `( Γ ⊢s σ : Δ →
                  Γ ⊢ m : M →
                  Γ ⊢s wk ∙ (σ ,, m) ≈ σ : Δ)

| eq_id_comp_l : `(Γ ⊢s σ : Δ →
                  Γ ⊢s id ∙ σ ≈ σ : Δ)

| eq_id_comp_r : `(Γ ⊢s σ : Δ →
                  Γ ⊢s σ ∙ id ≈ σ : Δ)

| eq_comp_assoc : `(Γ' ⊢s σ : Γ →
                  Γ''  ⊢s σ' : Γ' →
                  Γ'''  ⊢s σ'' : Γ'' →
                  Γ''' ⊢s σ ∙ σ' ∙ σ'' ≈ (σ ∙ (σ' ∙ σ'')) : Γ)

| eq_ext_var : `(Γ ⊢s σ : M :: Δ →
                  Γ ⊢s σ ≈ ((wk ∙ σ) ,, (var 0 [ σ ])) : M :: Δ)

| eq_sym : `(Γ ⊢s σ ≈ σ' : Δ →
             Γ ⊢s σ' ≈ σ : Δ)

| eq_trans : `(
                 Γ ⊢s σ ≈ σ' : Δ →
                 Γ ⊢s σ' ≈ σ'' : Δ →
                                 Γ ⊢s σ ≈ σ'' : Δ)
where "Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Γ σ σ' Δ).


Lemma term_eq_refl (Γ : Ctx) (t : Exp) (T : Typ) : Γ ⊢ t : T -> Γ ⊢ t ≈ t : T
with sub_eq_refl (Γ Δ : Ctx) (σ : Subst) : Γ ⊢s σ : Δ -> Γ ⊢s σ ≈ σ : Δ.
Proof.
 - intros.
   dependent induction t;(inversion H;subst);(try (econstructor;auto)).
   -- eapply (term_eq_refl _ _ _ H3).
   -- exact (term_eq_refl _ _ _ H5).
   -- exact (sub_eq_refl _ _ _ H5).
   -- exact (term_eq_refl _ _ _ H3).
 - intros.
    dependent induction σ;(inversion H;subst);(try (econstructor;auto)).
      -- exact (sub_eq_refl _ _ _ H3).
      -- exact (sub_eq_refl _ _ _ H5).
Qed.   
