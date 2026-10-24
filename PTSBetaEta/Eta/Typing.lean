module

public import PTSBetaEta.Eta.Basic
public import PTSBetaEta.Beta.Normalization

@[expose] public section

/-!
# Pure type systems with βη-conversion

`HasTypeBE` has the seven rules of `HasType`, except that its conversion rule uses βη-conversion.
This file defines βη-conversion, the typing relation, legal terms, and weak and strong βη-normalization of a whole system.
It also shows that every derivation with β-conversion is a derivation with βη-conversion.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

def ConvertsBE (M N : Expr S) : Prop := EqvGen BetaEta M N

/-- Typing with βη-conversion.
The seven rules are those of `HasType`, except that the conversion rule uses βη-conversion. -/
inductive HasTypeBE {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeBE P [] (.sort s) (.sort t)
  | var {Γ A s} : HasTypeBE P Γ A (.sort s) →
      HasTypeBE P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasTypeBE P Γ M B → HasTypeBE P Γ A (.sort s) →
      HasTypeBE P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasTypeBE P Γ A (.sort s₁) →
      HasTypeBE P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeBE P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasTypeBE P (A :: Γ) b B →
      HasTypeBE P Γ (.pi A B) (.sort s) →
      HasTypeBE P Γ (.lam A b) (.pi A B)
  | application {Γ f a A B} : HasTypeBE P Γ f (.pi A B) →
      HasTypeBE P Γ a A → HasTypeBE P Γ (.app f a) (B.instantiate a)
  | conversion {Γ M A B s} : HasTypeBE P Γ M A → HasTypeBE P Γ B (.sort s) →
      ConvertsBE A B → HasTypeBE P Γ M B

inductive ValidContextBE {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContextBE P []
  | cons {Γ A s} : ValidContextBE P Γ → HasTypeBE P Γ A (.sort s) →
      ValidContextBE P (A :: Γ)

def LegalBE (P : Specification S) (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ A, HasTypeBE P Γ M A ∨ HasTypeBE P Γ A M

def NormalBE (M : Expr S) : Prop := ∀ N, ¬ BetaEta M N

def WeaklyNormalizingBE (M : Expr S) : Prop :=
  ∃ N, ReflTransGen BetaEta M N ∧ NormalBE N

def SystemWeaklyNormalizingBE (P : Specification S) : Prop :=
  ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → WeaklyNormalizingBE M

def SystemStronglyNormalizingBE (P : Specification S) : Prop :=
  ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → StronglyNormalizingBetaEta M

/-! ## From β-conversion to βη-conversion -/

theorem ConvertsBE.of_converts {M N : Expr S} (h : Converts M N) : ConvertsBE M N := by
  induction h with
  | rel a b h => exact .rel _ _ (Or.inl h)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem HasTypeBE.of_hasType {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) : HasTypeBE P Γ M A := by
  induction h with
  | ax h => exact .ax h
  | var _ ih => exact .var ih
  | weaken _ _ ih₁ ih₂ => exact .weaken ih₁ ih₂
  | product _ _ hr ih₁ ih₂ => exact .product ih₁ ih₂ hr
  | abstraction _ _ ih₁ ih₂ => exact .abstraction ih₁ ih₂
  | application _ _ ih₁ ih₂ => exact .application ih₁ ih₂
  | conversion _ _ hc ih₁ ih₂ => exact .conversion ih₁ ih₂ (.of_converts hc)

theorem ValidContextBE.of_validContext {P : Specification S} {Γ : List (Expr S)}
    (h : ValidContext P Γ) : ValidContextBE P Γ := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (.of_hasType hA)

theorem LegalBE.of_legal {P : Specification S} {Γ : List (Expr S)} {M : Expr S}
    (h : Legal P Γ M) : LegalBE P Γ M := by
  obtain ⟨A, hA | hA⟩ := h
  · exact ⟨A, .inl (.of_hasType hA)⟩
  · exact ⟨A, .inr (.of_hasType hA)⟩

/-- βη-reduction preserves strong β-normalization. -/
theorem StronglyNormalizing.of_betaEta_star {M N : Expr S} (h : StronglyNormalizing M)
    (hr : ReflTransGen BetaEta M N) : StronglyNormalizing N := by
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    rcases hs with hb | he
    · exact ih.inv hb
    · obtain ⟨n, hn⟩ := ih.bounded
      exact stronglyNormalizing_of_bounded (hn.of_eta he)

/-! ## The variant with β-conversion in typing and βη-reduction -/

/-- Every legal term of the system with β-conversion is weakly βη-normalizing. -/
def SystemWeaklyNormalizingBetaEta (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → WeaklyNormalizingBE M

def SystemStronglyNormalizingBetaEta (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → StronglyNormalizingBetaEta M

end PureTypeSystem
