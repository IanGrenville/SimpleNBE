Require Import List.
From Equations Require Import Equations.

Create HintDb snbe.

Inductive Typ : Set :=
| Bool : Typ
| Arr : Typ -> Typ -> Typ.

Notation Ctx := (list Typ).
Notation "A --> B" := (Arr A B) (at level 80).

Inductive Exp : Set :=
| var : nat -> Exp
| true : Exp
| false : Exp
| lam : Exp -> Exp
| app : Exp -> Exp -> Exp
| sub : Exp -> Subst -> Exp
with Subst : Set :=
| wk : Subst
| id : Subst
| comp : Subst -> Subst -> Subst
| ext : Subst -> Exp -> Subst
.
#[export]
Hint Constructors Typ Exp : snbe.

Notation "A $ B" := (app A B) (at level 80).
Notation "A [ σ ]" := (sub A σ) (at level 80).
Notation "σ ∙ τ" := (comp σ τ) (at level 80).
Notation "σ ,, s" := (ext σ s) (at level 80).
Notation "'q' σ" := (ext (comp σ wk) (var 0)) (at level 80).

Generalizable All Variables.

Inductive Weaken : Ctx -> Ctx -> Set :=
| I : `(Weaken Γ Γ)
| P : `(Weaken Γ Δ -> Weaken (T :: Γ) Δ)
| Q : `(Weaken Γ Δ -> Weaken (T :: Γ) (T :: Δ))
.

Equations weak_comp : `(Weaken Γ' Δ -> Weaken Γ Γ' -> Weaken Γ Δ) :=
  weak_comp _ _ _ σ (I _) := σ;
  weak_comp _ _ _ σ (P _ _ T δ) := P _ _ T (weak_comp _ _ _ σ δ);
  weak_comp _ _ _ (I _) (Q _ _ T δ) := Q _ _ T δ;
  weak_comp _ _ _ (P _ _ T σ) (Q _ _ T δ) := P _ _ T (weak_comp _ _ _ σ δ);
  weak_comp _ _ _ (Q _ _ T σ) (Q _ _ T δ) := Q _ _ T (weak_comp _ _ _ σ δ);
.
  
Equations Weaken_to_Subst : `(Weaken Γ Δ -> Subst) :=
  Weaken_to_Subst  _ _ (I _) := id;
  Weaken_to_Subst _ _ (P _ _ T σ) := (Weaken_to_Subst _ _ σ) ∙ wk;
  Weaken_to_Subst _ _ (Q _ _ T σ) := q (Weaken_to_Subst _ _ σ)
.


Inductive Ne : Set :=
| ne_var : nat -> Ne
| ne_app : Ne -> Nf -> Ne
with Nf : Set :=
| nf_ne : Ne -> Nf
| nf_true : Nf
| nf_false : Nf
| nf_lam : Nf -> Nf.

Fixpoint NeToExp (ne : Ne) : Exp :=
  match ne with
  | ne_var n => var n
  | ne_app f v => (NeToExp f) $ (NfToExp v)
  end
with NfToExp (nf : Nf) : Exp :=
  match nf with
  | nf_ne ne => NeToExp ne
  | nf_true => true
  | nf_false => false
  | nf_lam w => lam (NfToExp w)
  end.

                        
