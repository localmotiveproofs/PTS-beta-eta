module

public import PTSBetaEta.Eta.Confluence
public import PTSBetaEta.Eta.Typing

@[expose] public section


namespace PureTypeSystem

universe u

/-! This file adapts OpenAI's `Typing.lean` (`PTSBetaEta.Beta.Typing`) to typing with βη-conversion (`HasTypeBE`).
The proofs are OpenAI's, except for the lemmas about conversion.
Those use injectivity of products and of sorts from `PTSBetaEta.Eta.Confluence`.
`Lookup` and `Neutral` are reused from OpenAI's library. -/

namespace HasTypeBE

variable {S : Type u} {P : Specification S}

theorem valid {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    ValidContextBE P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

/-- Every derivation contains a sort, namely the sort of one of its axiom leaves. -/
theorem sort_exists {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    Nonempty S := by
  induction h with
  | @ax s _ _ => exact ⟨s⟩
  | var _ ih => exact ih
  | weaken _ _ ih _ => exact ih
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ ih _ => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContextBE P Γ)
    {s t : S} (hst : P.axioms s t) : HasTypeBE P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- If a product `Π A. B` has a type, then `A` has a sort as its type.
This is proved directly by induction on the derivation.
It comes before the substitution theorem and needs no exchange or context-substitution lemma. -/
theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeBE P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasTypeBE P Γ A (.sort s) := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM

end HasTypeBE

namespace ConvertsBE

variable {S : Type u} {M N : Expr S}

theorem subst (h : ConvertsBE M N) (σ : Nat → Expr S) :
    ConvertsBE (M.subst σ) (N.subst σ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.elim (fun h => .inl (h.subst σ)) (fun h => .inr (h.subst σ)))
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename (h : ConvertsBE M N) (ρ : Nat → Nat) :
    ConvertsBE (M.rename ρ) (N.rename ρ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.elim (fun h => .inl (h.rename ρ)) (fun h => .inr (h.rename ρ)))
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end ConvertsBE

/-- A simultaneous substitution `σ` from `Γ` to `Δ` is typed when each `σ n` has, in `Δ`, the declared type of `n` in `Γ` after substitution.
Only the substitution theorem assumes this, and the main theorems do not. -/
def TypedSubstitutionBE {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasTypeBE P Δ (σ n) (A.subst σ)

namespace TypedSubstitutionBE

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitutionBE P (A :: Γ) Δ σ) :
    TypedSubstitutionBE P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitutionBE P Γ Δ σ)
    (hA : HasTypeBE P Δ (A.subst σ) (.sort s)) :
    TypedSubstitutionBE P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasTypeBE.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasTypeBE.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitutionBE

namespace HasTypeBE

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem subst (h : HasTypeBE P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitutionBE P Γ Δ σ) :
    HasTypeBE P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasTypeBE.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)

end HasTypeBE

namespace HasTypeBE

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContextBE P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasTypeBE P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

end HasTypeBE

namespace TypedSubstitutionBE

variable {S : Type u} {P : Specification S}

theorem identity {Γ : List (Expr S)} (hΓ : ValidContextBE P Γ) :
    TypedSubstitutionBE P Γ Γ Expr.var := by
  intro n A hn
  simpa only [Expr.subst_var] using HasTypeBE.lookup hΓ hn

theorem weaken {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) :
    TypedSubstitutionBE P Γ (A :: Γ) (Expr.var ∘ Nat.succ) := by
  intro n B hn
  simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
    (HasTypeBE.weaken (HasTypeBE.lookup hA.valid hn) hA)

theorem single {Γ : List (Expr S)} {a A : Expr S} (ha : HasTypeBE P Γ a A) :
    TypedSubstitutionBE P (A :: Γ) Γ (Expr.single a) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single, Expr.subst_lift_single] using HasTypeBE.lookup ha.valid hn

end TypedSubstitutionBE

namespace HasTypeBE

section

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem rename {M A : Expr S} (h : HasTypeBE P Γ M A)
    (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasTypeBE P Δ (.var (ρ n)) (B.rename ρ)) :
    HasTypeBE P Δ (M.rename ρ) (A.rename ρ) := by
  have hσ : TypedSubstitutionBE P Γ Δ (Expr.var ∘ ρ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ

theorem instantiate {A b B a : Expr S}
    (hb : HasTypeBE P (A :: Γ) b B) (ha : HasTypeBE P Γ a A) :
    HasTypeBE P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TypedSubstitutionBE.single ha)

theorem weaken_under {A D b B : Expr S} {s t : S}
    (hb : HasTypeBE P (A :: Γ) b B) (hA : HasTypeBE P Γ A (.sort s))
    (hD : HasTypeBE P Γ D (.sort t)) :
    HasTypeBE P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasTypeBE P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasTypeBE.weaken hA hD
  have hσ := (TypedSubstitutionBE.weaken hD).lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

theorem context_head_conversion {A A' b B : Expr S} {s t : S}
    (hb : HasTypeBE P (A :: Γ) b B) (hA : HasTypeBE P Γ A (.sort s))
    (hA' : HasTypeBE P Γ A' (.sort t)) (hc : ConvertsBE A A') :
    HasTypeBE P (A' :: Γ) b B := by
  have hσ : TypedSubstitutionBE P (A :: Γ) (A' :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ

end

variable {S : Type u} {P : Specification S}

/-- The generation lemma for typing with βη-conversion.
Each case describes the type of a term up to βη-conversion, and no functionality is assumed. -/
def GenerationBE (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ ConvertsBE T A
  | .sort s => ∃ t, P.axioms s t ∧ ConvertsBE T (.sort t)
  | .app f a => ∃ A B, HasTypeBE P Γ f (.pi A B) ∧ HasTypeBE P Γ a A ∧
      ConvertsBE T (B.instantiate a)
  | .lam A b => ∃ B s, HasTypeBE P (A :: Γ) b B ∧
      HasTypeBE P Γ (.pi A B) (.sort s) ∧ ConvertsBE T (.pi A B)
  | .pi A B => ∃ s₁ s₂ s₃, HasTypeBE P Γ A (.sort s₁) ∧
      HasTypeBE P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      ConvertsBE T (.sort s₃)

theorem generation {Γ : List (Expr S)} {M T : Expr S}
    (h : HasTypeBE P Γ M T) : GenerationBE P Γ M T := by
  induction h with
  | ax h => exact ⟨_, h, .refl _⟩
  | var h ih => exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A, hA, hc⟩ := ihM
          exact ⟨_, .succ D hA, hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t', ht, hc⟩ := ihM
          exact ⟨t', ht, hc.rename Nat.succ⟩
      | app f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi A B =>
          obtain ⟨t₁, t₂, t₃, hA, hB, hr, hc⟩ := ihM
          exact ⟨t₁, t₂, t₃, .weaken hA hD, hB.weaken_under hA hD,
            hr, hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_, _, hb, hPi, .refl _⟩
  | application hf ha ihf iha => exact ⟨_, _, hf, ha, .refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D, hD, hd⟩ := ihM
          exact ⟨D, hD, .trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r, hr, hd⟩ := ihM
          exact ⟨r, hr, .trans _ _ _ (.symm _ _ hc) hd⟩
      | app f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasTypeBE P Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃, HasTypeBE P Γ A (.sort s₁) ∧
      HasTypeBE P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      ConvertsBE T (.sort s₃) := h.generation

theorem generation_lam {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasTypeBE P Γ (.lam A b) T) :
    ∃ B s, HasTypeBE P (A :: Γ) b B ∧ HasTypeBE P Γ (.pi A B) (.sort s) ∧
      ConvertsBE T (.pi A B) := h.generation

theorem generation_app {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasTypeBE P Γ (.app f a) T) :
    ∃ A B, HasTypeBE P Γ f (.pi A B) ∧ HasTypeBE P Γ a A ∧
      ConvertsBE T (B.instantiate a) := h.generation

/-- **Correctness of types.**
If `M` has type `A`, then either `A` is a sort or `A` has a sort as its type.
The first case is needed because a sort need not have a type itself. -/
theorem regularity {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    (∃ s, A = .sort s) ∨ (∃ s, HasTypeBE P Γ A (.sort s)) := by
  induction h with
  | ax h => exact .inl ⟨_, rfl⟩
  | var h ih => exact .inr ⟨_, .weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := ihM
      · exact .inl ⟨s, rfl⟩
      · exact .inr ⟨s, .weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_, rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_, hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s, heq⟩ | ⟨s, hPi⟩ := ihf
      · cases heq
      · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
        exact .inr ⟨s₂, hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_, hA⟩

theorem product_type_sorted {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasTypeBE P Γ M (.pi A B)) : ∃ s, HasTypeBE P Γ (.pi A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasTypeBE

namespace ConvertsBE

variable {S : Type u}

theorem pi {A A' B B' : Expr S} (hA : ConvertsBE A A') (hB : ConvertsBE B B') :
    ConvertsBE (.pi A B) (.pi A' B') :=
  .trans _ _ _
    (eqv_lift (c := fun x => .pi x B) (fun h => h.elim (fun h => .inl (.pi_domain h))
      (fun h => .inr (.pi_domain h))) hA)
    (eqv_lift (c := fun x => .pi A' x) (fun h => h.elim (fun h => .inl (.pi_body h))
      (fun h => .inr (.pi_body h))) hB)

theorem pi_not_sort {A B : Expr S} {s : S} : ¬ ConvertsBE (.pi A B) (.sort s) :=
  convertsBE_pi_not_sort

theorem sort_inj {s t : S} (h : ConvertsBE (Expr.sort s) (.sort t)) : s = t :=
  convertsBE_sort_inj h

/-- **Injectivity of products** for βη-conversion.
The sort `z` is only used to erase λ-domains in the proof. -/
theorem product_compatibility (z : S) {A B A' B' : Expr S}
    (h : ConvertsBE (.pi A B) (.pi A' B')) : ConvertsBE A A' ∧ ConvertsBE B B' :=
  convertsBE_pi_inj z h

theorem instantiate_right {a a' : Expr S} (h : ConvertsBE a a') (B : Expr S) :
    ConvertsBE (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      rcases h with h | h
      · exact reduces_convertsBE
          (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces
      · exact etaStar_convertsBE (eta_instantiate_arg B h)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end ConvertsBE

namespace HasTypeBE

variable {S : Type u} {P : Specification S}

theorem application_type_sorted_aux {Γ : List (Expr S)} {M T : Expr S}
    (h : HasTypeBE P Γ M T) :
    ∀ f a, M = .app f a → ∃ s, HasTypeBE P Γ T (.sort s) := by
  induction h with
  | ax h => intro f a heq; cases heq
  | var h ih => intro f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam A b => cases heq
      | pi A B => cases heq
      | app g b =>
          obtain ⟨r, hr⟩ := ihM g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro f a heq; cases heq
  | application hf ha ihf iha =>
      intro f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasTypeBE P Γ (.app f a) T) : ∃ s, HasTypeBE P Γ T (.sort s) :=
  h.application_type_sorted_aux f a rfl

theorem abstraction_type_sorted {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasTypeBE P Γ (.lam A b) T) : ∃ s, HasTypeBE P Γ T (.sort s) := by
  obtain ⟨s, hT⟩ | hs := h.regularity
  · obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
    subst T
    exact False.elim (ConvertsBE.pi_not_sort (.symm _ _ hc))
  · exact hs

/-- A term whose type is a sort can be given back any type `T` that is convertible to that sort, as long as `T` is itself a sort or has a sort as its type.
This avoids asking for a type of a sort that has none. -/
theorem conversion_from_sort {Γ : List (Expr S)} {M T : Expr S} {s : S}
    (h : HasTypeBE P Γ M (.sort s))
    (hT : (∃ t, T = .sort t) ∨ ∃ t, HasTypeBE P Γ T (.sort t))
    (hc : ConvertsBE T (.sort s)) : HasTypeBE P Γ M T := by
  obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hT
  · have heq := hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)

/-- **Subject reduction for β-steps.**
A β-step keeps the exact type of a term, including β-steps inside binder domains. -/
theorem subject_reduction {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasTypeBE P Γ M T) (hr : Beta M N) : HasTypeBE P Γ N T := by
  induction hr generalizing Γ T with
  | head A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨hDA, hEB⟩ := hp.product_compatibility s
      obtain ⟨t, hA⟩ := hPi.product_domain A B rfl
      have haA := HasTypeBE.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show ConvertsBE a a' from .rel _ _ (.inl hr)).instantiate_right B))
        (.symm _ _ hc))
  | @lam_domain A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : ConvertsBE A A' := .rel _ _ (.inl hr)
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasTypeBE.product hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      have hA' := ih hA
      have hB' := hB.context_head_conversion hA hA' (.rel _ _ (.inl hr))
      exact (HasTypeBE.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      exact (HasTypeBE.product hA (ih hB) hrule).conversion_from_sort h.regularity hc

theorem subject_reduces {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasTypeBE P Γ M T) (hr : Reduces M N) : HasTypeBE P Γ N T := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.subject_reduction hr

end HasTypeBE
namespace HasTypeBE

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem sort_cannot_have_product_type {s : S} {A B : Expr S}
    (h : HasTypeBE P Γ (.sort s) (.pi A B)) : False := by
  obtain ⟨t, ht, hc⟩ := h.generation
  exact ConvertsBE.pi_not_sort hc

theorem product_cannot_have_product_type {A B D E : Expr S}
    (h : HasTypeBE P Γ (.pi A B) (.pi D E)) : False := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
  exact ConvertsBE.pi_not_sort hc

theorem lambda_cannot_have_sort_type {A b : Expr S} {s : S}
    (h : HasTypeBE P Γ (.lam A b) (.sort s)) : False := by
  obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
  exact ConvertsBE.pi_not_sort (.symm _ _ hc)

/-- **Uniqueness of types for neutral terms**, up to βη-conversion.
No functionality is needed for this.
The declaration of the head variable fixes the type of the head, and injectivity of products fixes each later codomain. -/
theorem neutral_unique {M A B : Expr S} (hn : Neutral M)
    (hA : HasTypeBE P Γ M A) (hB : HasTypeBE P Γ M B) : ConvertsBE A B := by
  induction hn generalizing A B with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hA.generation
      obtain ⟨E, hE, hcE⟩ := hB.generation
      have heq : D = E := by
        clear hA hB hcD hcE
        induction hD generalizing E with
        | zero A Γ => cases hE; rfl
        | succ C hD ih =>
            cases hE with
            | succ _ hE => exact congrArg (Expr.rename Nat.succ) (ih _ hE)
      subst E
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | @app f a hn ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := hA.generation_app
      obtain ⟨D', E', hf', ha', hc'⟩ := hB.generation_app
      obtain ⟨z⟩ := hA.sort_exists
      have he := ((ih hf hf').product_compatibility z).2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))

theorem normal_shape {M T : Expr S} (h : HasTypeBE P Γ M T) (hn : Normal M) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b, M = .lam A b) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s, rfl⟩
  | lam A b ihA ihb => exact .inr (.inr (.inr ⟨A, b, rfl⟩))
  | pi A B ihA ihB => exact .inr (.inr (.inl ⟨A, B, rfl⟩))
  | app f a ihf iha =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, rfl⟩ | hnf | ⟨A, B, rfl⟩ | ⟨A, b, rfl⟩ := ihf hf hn.app_left
      · exact False.elim hf.sort_cannot_have_product_type
      · exact .inr (.inl (.app hnf))
      · exact False.elim hf.product_cannot_have_product_type
      · exact False.elim (hn _ (.head A b a))

theorem sorted_normal_shape {M : Expr S} {s : S}
    (h : HasTypeBE P Γ M (.sort s)) (hn : Normal M) :
    (∃ t, M = .sort t) ∨ Neutral M ∨ (∃ A B, M = .pi A B) := by
  obtain h | h | h | ⟨A, b, rfl⟩ := h.normal_shape hn
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact False.elim h.lambda_cannot_have_sort_type

end HasTypeBE
