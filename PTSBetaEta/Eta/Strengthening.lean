module

public import PTSBetaEta.Eta.Confluence
public import PTSBetaEta.Beta.Profiles

@[expose] public section

/-!
# Strengthening for arbitrary pure type systems

This file proves strengthening for `HasType`, with no functionality assumption.
It follows van Benthem Jutting, McKinna and Pollack, *Checking algorithms for Pure Type Systems* (TYPES'93), Sections 4 and 5, adapted to the de Bruijn syntax of OpenAI's library.

* `HasTypeO` is their liberal and nearly syntax-directed relation `⊢o`. It has no conversion rule, and its λ-rule does not check that the product is typed. Here the application rule uses the substituted codomain, so no π-reduction is needed.
* The file proves that `⊢o` is complete for `⊢`, and it proves their approximate substitution and weak closure lemmas.
* The Key Theorem is their Theorem 46. Its second alternative is the inductive `KeyAlt`, which replaces their explicit telescopes.
* `HasTypeN` is a nearly syntax-directed system, their `⊢nsdtp` with `⊢o` in the premise of the λ-rule. It is sound and complete for `⊢`, and strengthening holds for it directly. This gives strengthening for `⊢`, which is their Theorem 63.

The file starts with β-reduction under injective renamings, and with renaming and its inversion for `⊢o`.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

/-! ## β-reduction under injective renamings -/

theorem Beta.rename_inv : ∀ (X : Expr S) {ρ : Nat → Nat}, Function.Injective ρ →
    ∀ {Y : Expr S}, Beta (X.rename ρ) Y → ∃ X', Y = X'.rename ρ ∧ Beta X X' := by
  intro X
  induction X with
  | var n => intro ρ hρ Y h; cases h
  | sort s => intro ρ hρ Y h; cases h
  | pi A B ihA ihB =>
    intro ρ hρ Y h
    cases h with
    | pi_domain h =>
      obtain ⟨A', rfl, hA⟩ := ihA hρ h
      exact ⟨.pi A' B, rfl, .pi_domain hA⟩
    | pi_body h =>
      obtain ⟨B', rfl, hB⟩ := ihB (liftRen_injective hρ) h
      exact ⟨.pi A B', rfl, .pi_body hB⟩
  | lam A b ihA ihb =>
    intro ρ hρ Y h
    cases h with
    | lam_domain h =>
      obtain ⟨A', rfl, hA⟩ := ihA hρ h
      exact ⟨.lam A' b, rfl, .lam_domain hA⟩
    | lam_body h =>
      obtain ⟨b', rfl, hb⟩ := ihb (liftRen_injective hρ) h
      exact ⟨.lam A b', rfl, .lam_body hb⟩
  | app f a ihf iha =>
    intro ρ hρ Y h
    have congr_left : ∀ {f'}, Beta (f.rename ρ) f' →
        ∃ X', Expr.app f' (a.rename ρ) = X'.rename ρ ∧ Beta (.app f a) X' := by
      intro f' hf
      obtain ⟨f₁, rfl, pf⟩ := ihf hρ hf
      exact ⟨.app f₁ a, rfl, .app_left pf⟩
    have congr_right : ∀ {a'}, Beta (a.rename ρ) a' →
        ∃ X', Expr.app (f.rename ρ) a' = X'.rename ρ ∧ Beta (.app f a) X' := by
      intro a' ha
      obtain ⟨a₁, rfl, pa⟩ := iha hρ ha
      exact ⟨.app f a₁, rfl, .app_right pa⟩
    cases f with
    | lam A b =>
      simp only [Expr.rename] at h congr_left congr_right
      cases h with
      | head _ _ _ => exact ⟨_, (Expr.instantiate_rename b a ρ), .head A b a⟩
      | app_left hf => exact congr_left hf
      | app_right ha => exact congr_right ha
    | var n =>
      simp only [Expr.rename] at h congr_left congr_right
      cases h with
      | app_left hf => exact congr_left hf
      | app_right ha => exact congr_right ha
    | sort s =>
      simp only [Expr.rename] at h congr_left congr_right
      cases h with
      | app_left hf => exact congr_left hf
      | app_right ha => exact congr_right ha
    | app g c =>
      simp only [Expr.rename] at h congr_left congr_right
      cases h with
      | app_left hf => exact congr_left hf
      | app_right ha => exact congr_right ha
    | pi C D =>
      simp only [Expr.rename] at h congr_left congr_right
      cases h with
      | app_left hf => exact congr_left hf
      | app_right ha => exact congr_right ha

theorem Reduces.rename_inv {ρ : Nat → Nat} (hρ : Function.Injective ρ) {X Y : Expr S}
    (h : Reduces (X.rename ρ) Y) : ∃ X', Y = X'.rename ρ ∧ Reduces X X' := by
  induction h with
  | refl => exact ⟨X, rfl, .refl⟩
  | tail _ hb ih =>
    obtain ⟨X', rfl, hX⟩ := ih
    obtain ⟨X'', rfl, hb'⟩ := Beta.rename_inv X' hρ hb
    exact ⟨X'', rfl, hX.tail hb'⟩

theorem Converts.rename_inv {ρ : Nat → Nat} (hρ : Function.Injective ρ) {X Y : Expr S}
    (h : Converts (X.rename ρ) (Y.rename ρ)) : Converts X Y := by
  obtain ⟨Z, hX, hY⟩ := h.join
  obtain ⟨X', rfl, hX'⟩ := Reduces.rename_inv hρ hX
  obtain ⟨Y', he, hY'⟩ := Reduces.rename_inv hρ hY
  have := Expr.rename_inj X' hρ he
  subst this
  exact .trans _ _ _ hX'.converts (.symm _ _ hY'.converts)

theorem Converts.ttrans {a b c : Expr S} (h₁ : Converts a b) (h₂ : Converts b c) :
    Converts a c := Relation.EqvGen.trans _ _ _ h₁ h₂

theorem Reduces.sort_inv {s : S} {X : Expr S} (h : Reduces (.sort s) X) : X = .sort s :=
  ((Normal.sort s).reduces_eq h).symm

theorem Converts.reduces_sort {s : S} {X : Expr S} (h : Converts X (.sort s)) :
    Reduces X (.sort s) := by
  obtain ⟨Z, hX, hs⟩ := h.join
  rw [Reduces.sort_inv hs] at hX
  exact hX

theorem Reduces.sort_unique {s t : S} {X : Expr S} (h₁ : Reduces X (.sort s))
    (h₂ : Reduces X (.sort t)) : s = t :=
  Converts.sort_inj (.trans _ _ _ (.symm _ _ h₁.converts) h₂.converts)

theorem Reduces.not_sort_pi {s : S} {X D E : Expr S} (h₁ : Reduces X (.sort s))
    (h₂ : Reduces X (.pi D E)) : False :=
  Converts.pi_not_sort (.trans _ _ _ (.symm _ _ h₂.converts) h₁.converts)

/-- If a term reduces both to a product and to `Y`, then `Y` also reduces to a product.
The domain and codomain of that product are reducts of those of the first product. -/
theorem Reduces.join_pi {X Y D E : Expr S} (h₁ : Reduces X (.pi D E)) (h₂ : Reduces X Y) :
    ∃ D' E', Reduces Y (.pi D' E') ∧ Reduces D D' ∧ Reduces E E' := by
  obtain ⟨Z, hZ₁, hZ₂⟩ := Reduces.confluent h₁ h₂
  obtain ⟨D', E', rfl, hD, hE⟩ := Reduces.pi_inv hZ₁
  exact ⟨D', E', hZ₂, hD, hE⟩

/-- If a term is β-convertible to a product, then it reduces to a product.
The domain and codomain of that product are reducts of those of the given product. -/
theorem Converts.join_pi {X D E : Expr S} (h : Converts X (.pi D E)) :
    ∃ D' E', Reduces X (.pi D' E') ∧ Reduces D D' ∧ Reduces E E' := by
  obtain ⟨Z, hX, hZ⟩ := h.join
  obtain ⟨D', E', rfl, hD, hE⟩ := Reduces.pi_inv hZ
  exact ⟨D', E', hX, hD, hE⟩

theorem Lookup.unique {Γ : List (Expr S)} {n : Nat} {A B : Expr S}
    (hA : Lookup Γ n A) (hB : Lookup Γ n B) : A = B := by
  induction hA generalizing B with
  | zero A Γ => cases hB; rfl
  | succ C _ ih =>
    cases hB with
    | succ _ hB => exact congrArg (Expr.rename Nat.succ) (ih hB)

/-! ## The liberal relation `⊢o` -/

/-- The liberal and nearly syntax-directed typing relation `⊢o`.
It has no conversion rule, no premises about valid contexts, and no check in the λ-rule that the product is typed. -/
inductive HasTypeO {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | sort {Γ s t} : P.axioms s t → HasTypeO P Γ (.sort s) (.sort t)
  | var {Γ n A} : Lookup Γ n A → HasTypeO P Γ (.var n) A
  | pi {Γ A B TA TB s₁ s₂ s₃} : HasTypeO P Γ A TA → Reduces TA (.sort s₁) →
      HasTypeO P (A :: Γ) B TB → Reduces TB (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeO P Γ (.pi A B) (.sort s₃)
  | lam {Γ A b B} : HasTypeO P (A :: Γ) b B → HasTypeO P Γ (.lam A b) (.pi A B)
  | app {Γ f a T U D E} : HasTypeO P Γ f T → Reduces T (.pi D E) →
      HasTypeO P Γ a U → Reduces U D → HasTypeO P Γ (.app f a) (E.instantiate a)

/-- `DeclRenamingInv Γ Δ ρ` says that `ρ` reflects declarations from `Δ` to `Γ`.
Every declaration of `Δ` at an index `ρ n` is the renaming by `ρ` of the declaration of `n` in `Γ`. -/
def DeclRenamingInv (Γ Δ : List (Expr S)) (ρ : Nat → Nat) : Prop :=
  ∀ n A, Lookup Δ (ρ n) A → ∃ A₀, Lookup Γ n A₀ ∧ A = A₀.rename ρ

namespace DeclRenamingInv

variable {Γ Δ : List (Expr S)} {ρ : Nat → Nat}

theorem lift (h : DeclRenamingInv Γ Δ ρ) (A : Expr S) :
    DeclRenamingInv (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ) := by
  intro n B hn
  cases n with
  | zero =>
    cases hn
    refine ⟨_, .zero A Γ, ?_⟩
    rw [Expr.rename_comp, Expr.rename_comp]
    rfl
  | succ n =>
    cases hn with
    | succ _ hn =>
      obtain ⟨B₀, hB₀, rfl⟩ := h n _ hn
      refine ⟨_, .succ A hB₀, ?_⟩
      rw [Expr.rename_comp, Expr.rename_comp]
      rfl

theorem weaken (C : Expr S) : DeclRenamingInv Γ (C :: Γ) Nat.succ := by
  intro n A hn
  cases hn with
  | succ _ hn => exact ⟨_, hn, rfl⟩

end DeclRenamingInv

namespace HasTypeO

variable {P : Specification S}

theorem rename {M T : Expr S} {Γ : List (Expr S)} (h : HasTypeO P Γ M T) :
    ∀ {Δ : List (Expr S)} {ρ : Nat → Nat}, TypingTree.DeclRenaming Γ Δ ρ →
      HasTypeO P Δ (M.rename ρ) (T.rename ρ) := by
  induction h with
  | sort h => intro Δ ρ _; exact .sort h
  | var h => intro Δ ρ hρ; exact .var (hρ _ _ h)
  | pi _ hTA _ hTB hr ihA ihB =>
    intro Δ ρ hρ
    exact .pi (ihA hρ) (hTA.rename ρ) (ihB (hρ.lift _)) (hTB.rename (Expr.liftRen ρ)) hr
  | lam _ ih => intro Δ ρ hρ; exact .lam (ih (hρ.lift _))
  | @app Γ f a T U D E _ hT _ hU ihf iha =>
    intro Δ ρ hρ
    rw [← Expr.instantiate_rename]
    exact HasTypeO.app (ihf hρ) (hT.rename ρ) (iha hρ) (hU.rename ρ)

/-- Strengthening for `⊢o`.
A typing of a renamed term comes from a typing of the original term. -/
theorem rename_inv : ∀ (M : Expr S) {Γ Δ : List (Expr S)} {ρ : Nat → Nat} {T : Expr S},
    Function.Injective ρ → DeclRenamingInv Γ Δ ρ → HasTypeO P Δ (M.rename ρ) T →
      ∃ T₀, HasTypeO P Γ M T₀ ∧ T = T₀.rename ρ := by
  intro M
  induction M with
  | var n =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | var h =>
      obtain ⟨A₀, hA₀, rfl⟩ := hinv n _ h
      exact ⟨A₀, .var hA₀, rfl⟩
  | sort s =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | sort h => exact ⟨_, .sort h, rfl⟩
  | pi A B ihA ihB =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | pi hA hTA hB hTB hr =>
      obtain ⟨TA₀, hA₀, rfl⟩ := ihA hρ hinv hA
      obtain ⟨TB₀, hB₀, rfl⟩ := ihB (liftRen_injective hρ) (hinv.lift A) hB
      obtain ⟨X, hX, hTA₀⟩ := Reduces.rename_inv hρ hTA
      obtain ⟨Y, hY, hTB₀⟩ := Reduces.rename_inv (liftRen_injective hρ) hTB
      cases X <;> simp [Expr.rename] at hX
      cases Y <;> simp [Expr.rename] at hY
      subst hX hY
      exact ⟨_, .pi hA₀ hTA₀ hB₀ hTB₀ hr, rfl⟩
  | lam A b ihA ihb =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | lam hb =>
      obtain ⟨B₀, hb₀, rfl⟩ := ihb (liftRen_injective hρ) (hinv.lift A) hb
      exact ⟨_, .lam hb₀, rfl⟩
  | app f a ihf iha =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | app hf hT ha hU =>
      obtain ⟨T₀, hf₀, rfl⟩ := ihf hρ hinv hf
      obtain ⟨U₀, ha₀, rfl⟩ := iha hρ hinv ha
      obtain ⟨X, hX, hT₀⟩ := Reduces.rename_inv hρ hT
      cases X with
      | pi D₀ E₀ =>
        simp only [Expr.rename, Expr.pi.injEq] at hX
        obtain ⟨rfl, rfl⟩ := hX
        obtain ⟨Y, hY, hU₀⟩ := Reduces.rename_inv hρ hU
        have := Expr.rename_inj Y hρ hY.symm
        subst this
        exact ⟨_, .app hf₀ hT₀ ha₀ hU₀, Expr.instantiate_rename E₀ a ρ⟩
      | _ => simp [Expr.rename] at hX

/-! ### Approximate substitution, their Lemma 42 up to conversion -/

/-- A substitution that is typed in `⊢o` up to conversion. -/
def TypedSubstO (P : Specification S) (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → ∃ A', HasTypeO P Δ (σ n) A' ∧ Converts A' (A.subst σ)

theorem TypedSubstO.lift {Γ Δ : List (Expr S)} {σ : Nat → Expr S}
    (hσ : TypedSubstO P Γ Δ σ) (A : Expr S) :
    TypedSubstO P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
    refine ⟨_, .var (.zero _ _), ?_⟩
    rw [Expr.rename_succ_liftSub]
    exact .refl _
  | succ _ hn =>
    obtain ⟨B', hB', hc⟩ := hσ _ _ hn
    refine ⟨_, hB'.rename (TypingTree.DeclRenaming.weaken _), ?_⟩
    rw [Expr.rename_succ_liftSub]
    exact hc.rename Nat.succ

theorem subst {M T : Expr S} {Γ : List (Expr S)} (h : HasTypeO P Γ M T) :
    ∀ {Δ : List (Expr S)} {σ : Nat → Expr S}, TypedSubstO P Γ Δ σ →
      ∃ T', HasTypeO P Δ (M.subst σ) T' ∧ Converts T' (T.subst σ) := by
  induction h with
  | sort h => intro Δ σ _; exact ⟨_, .sort h, .refl _⟩
  | var h => intro Δ σ hσ; exact hσ _ _ h
  | pi _ hTA _ hTB hr ihA ihB =>
    intro Δ σ hσ
    obtain ⟨TA', hA', cA⟩ := ihA hσ
    obtain ⟨TB', hB', cB⟩ := ihB (hσ.lift _)
    have rA : Reduces TA' (.sort _) :=
      Converts.reduces_sort (.trans _ _ _ cA (hTA.subst σ).converts)
    have rB : Reduces TB' (.sort _) :=
      Converts.reduces_sort (.trans _ _ _ cB (hTB.subst _).converts)
    exact ⟨_, .pi hA' rA hB' rB hr, .refl _⟩
  | lam _ ih =>
    intro Δ σ hσ
    obtain ⟨B', hb', cb⟩ := ih (hσ.lift _)
    exact ⟨_, .lam hb', Converts.pi (.refl _) cb⟩
  | @app Γ f a T U D E _ hT _ hU ihf iha =>
    intro Δ σ hσ
    obtain ⟨T', hf', cf⟩ := ihf hσ
    obtain ⟨U', ha', ca⟩ := iha hσ
    obtain ⟨D', E', hT', hD, hE⟩ :=
      Converts.join_pi (.trans _ _ _ cf (hT.subst σ).converts)
    obtain ⟨D'', hU'', hD''⟩ := (Converts.ttrans ca
      (Reduces.converts ((hU.subst σ).trans hD))).join
    have hT'' : Reduces T' (.pi D'' E') := hT'.trans (Reduces.pi hD'' .refl)
    refine ⟨_, .app hf' hT'' ha' hU'', ?_⟩
    rw [← Expr.instantiate_subst]
    exact .symm _ _ (hE.subst (Expr.single (a.subst σ))).converts

/-! ### Reduction of contexts and weak closure, their Lemmas 43 to 45 -/

theorem lookup_forall₂ {Γ₁ Γ₂ : List (Expr S)} (hc : List.Forall₂ Reduces Γ₁ Γ₂) :
    ∀ {n A}, Lookup Γ₁ n A → ∃ A₂, Lookup Γ₂ n A₂ ∧ Reduces A A₂ := by
  induction hc with
  | nil => intro n A h; cases h
  | cons hab _ ih =>
    intro n A h
    cases h with
    | zero => exact ⟨_, .zero _ _, hab.rename Nat.succ⟩
    | succ _ h =>
      obtain ⟨A₂, h₂, r⟩ := ih h
      exact ⟨_, .succ _ h₂, r.rename Nat.succ⟩

theorem _root_.PureTypeSystem.Reduces.to_sort_of_reduces {X Y : Expr S} {s : S} (h₁ : Reduces X (.sort s))
    (h₂ : Reduces X Y) : Reduces Y (.sort s) := by
  obtain ⟨Z, hs, hY⟩ := Reduces.confluent h₁ h₂
  rw [Reduces.sort_inv hs] at hY
  exact hY

theorem ctx_reduce {M T : Expr S} {Γ₁ : List (Expr S)} (h : HasTypeO P Γ₁ M T) :
    ∀ {Γ₂}, List.Forall₂ Reduces Γ₁ Γ₂ → ∃ T₂, HasTypeO P Γ₂ M T₂ ∧ Reduces T T₂ := by
  induction h with
  | sort h => intro Γ₂ _; exact ⟨_, .sort h, .refl⟩
  | var h =>
    intro Γ₂ hc
    obtain ⟨A₂, h₂, r⟩ := lookup_forall₂ hc h
    exact ⟨_, .var h₂, r⟩
  | pi _ hTA _ hTB hr ihA ihB =>
    intro Γ₂ hc
    obtain ⟨TA₂, hA, rA⟩ := ihA hc
    obtain ⟨TB₂, hB, rB⟩ := ihB (.cons .refl hc)
    exact ⟨_, .pi hA (Reduces.to_sort_of_reduces hTA rA) hB
      (Reduces.to_sort_of_reduces hTB rB) hr, .refl⟩
  | lam _ ih =>
    intro Γ₂ hc
    obtain ⟨B₂, hb, rb⟩ := ih (.cons .refl hc)
    exact ⟨_, .lam hb, Reduces.pi .refl rb⟩
  | @app Γ f a T U D E _ hT _ hU ihf iha =>
    intro Γ₂ hc
    obtain ⟨T₂, hf, rT⟩ := ihf hc
    obtain ⟨U₂, ha, rU⟩ := iha hc
    obtain ⟨D', E', hT₂, hD, hE⟩ := Reduces.join_pi hT rT
    obtain ⟨D'', hD'', hU₂⟩ := Reduces.confluent (hU.trans hD) rU
    exact ⟨_, .app hf (hT₂.trans (Reduces.pi hD'' .refl)) ha hU₂,
      hE.subst (Expr.single a)⟩

theorem lam_inv {Γ : List (Expr S)} {C c T : Expr S} (h : HasTypeO P Γ (.lam C c) T) :
    ∃ B, T = .pi C B ∧ HasTypeO P (C :: Γ) c B := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

theorem step_closure {M T : Expr S} {Γ : List (Expr S)} (h : HasTypeO P Γ M T) :
    ∀ {N}, Beta M N → ∃ T', HasTypeO P Γ N T' ∧ Converts T' T := by
  induction h with
  | sort _ => intro N hb; cases hb
  | var _ => intro N hb; cases hb
  | @pi Γ A B TA TB s₁ s₂ s₃ hA hTA hB hTB hr ihA ihB =>
    intro N hb
    cases hb with
    | pi_domain hb =>
      obtain ⟨TA', hA', cA⟩ := ihA hb
      obtain ⟨TB₂, hB₂, rB⟩ := hB.ctx_reduce (.cons (.single hb) (List.forall₂_refl _ ))
      exact ⟨_, .pi hA' (Converts.reduces_sort (.trans _ _ _ cA hTA.converts)) hB₂
        (Reduces.to_sort_of_reduces hTB rB) hr, .refl _⟩
    | pi_body hb =>
      obtain ⟨TB', hB', cB⟩ := ihB hb
      exact ⟨_, .pi hA hTA hB' (Converts.reduces_sort (.trans _ _ _ cB hTB.converts)) hr,
        .refl _⟩
  | @lam Γ A b B hb ih =>
    intro N hs
    cases hs with
    | lam_domain hs =>
      obtain ⟨B₂, hb₂, rB⟩ := hb.ctx_reduce (.cons (.single hs) (List.forall₂_refl _))
      exact ⟨_, .lam hb₂, .symm _ _ (Converts.pi (Reduces.converts (.single hs))
        rB.converts)⟩
    | lam_body hs =>
      obtain ⟨B', hb', cB⟩ := ih hs
      exact ⟨_, .lam hb', Converts.pi (.refl _) cB⟩
  | @app Γ f a T U D E hf hT ha hU ihf iha =>
    intro N hs
    cases hs with
    | head C c _ =>
      obtain ⟨B₁, rfl, hc⟩ := lam_inv hf
      obtain ⟨D', E', he, hCD, hBE⟩ := Reduces.pi_inv hT
      simp only [Expr.pi.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hσ : TypedSubstO P (C :: Γ) Γ (Expr.single a) := by
        intro n A hn
        cases hn with
        | zero =>
          refine ⟨U, ha, ?_⟩
          rw [Expr.subst_lift_single]
          exact .trans _ _ _ hU.converts (.symm _ _ hCD.converts)
        | succ _ hn =>
          refine ⟨_, .var hn, ?_⟩
          rw [Expr.subst_lift_single]
          exact .refl _
      obtain ⟨T', hT', cT⟩ := hc.subst hσ
      exact ⟨T', hT', .trans _ _ _ cT (hBE.subst (Expr.single a)).converts⟩
    | app_left hs =>
      obtain ⟨T', hf', cT⟩ := ihf hs
      obtain ⟨D', E', hT', hD, hE⟩ := Converts.join_pi (.trans _ _ _ cT hT.converts)
      exact ⟨_, .app hf' hT' ha (hU.trans hD), .symm _ _ (hE.subst (Expr.single a)).converts⟩
    | @app_right _ _ a' hs =>
      obtain ⟨U', ha', cU⟩ := iha hs
      obtain ⟨D'', hU'', hD''⟩ := (Converts.ttrans cU hU.converts).join
      exact ⟨_, .app hf (hT.trans (Reduces.pi hD'' .refl)) ha' hU'',
        .symm _ _ ((show Converts a a' from Reduces.converts (.single hs)).instantiate_right E)⟩

theorem closure {M N T : Expr S} {Γ : List (Expr S)} (h : HasTypeO P Γ M T)
    (hr : Reduces M N) : ∃ T', HasTypeO P Γ N T' ∧ Converts T' T := by
  induction hr with
  | refl => exact ⟨T, h, .refl _⟩
  | tail _ hb ih =>
    obtain ⟨T₁, h₁, c₁⟩ := ih
    obtain ⟨T₂, h₂, c₂⟩ := h₁.step_closure hb
    exact ⟨T₂, h₂, .trans _ _ _ c₂ c₁⟩

end HasTypeO

/-! ### Completeness of `⊢o` for `⊢`, their Lemma 39 -/

theorem HasType.toO {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) : ∃ A₀, HasTypeO P Γ M A₀ ∧ Converts A₀ A := by
  induction h with
  | ax h => exact ⟨_, .sort h, .refl _⟩
  | var _ _ => exact ⟨_, .var (.zero _ _), .refl _⟩
  | weaken _ _ ih _ =>
    obtain ⟨A₀, h₀, c₀⟩ := ih
    exact ⟨_, h₀.rename (TypingTree.DeclRenaming.weaken _), c₀.rename Nat.succ⟩
  | product _ _ hr ihA ihB =>
    obtain ⟨TA, hA, cA⟩ := ihA
    obtain ⟨TB, hB, cB⟩ := ihB
    exact ⟨_, .pi hA (Converts.reduces_sort cA) hB (Converts.reduces_sort cB) hr, .refl _⟩
  | abstraction _ _ ihb _ =>
    obtain ⟨B₀, hb, cb⟩ := ihb
    exact ⟨_, .lam hb, Converts.pi (.refl _) cb⟩
  | @application Γ f a A B _ _ ihf iha =>
    obtain ⟨T, hf, cf⟩ := ihf
    obtain ⟨U, ha, ca⟩ := iha
    obtain ⟨A', B', hT, hA, hB⟩ := Converts.join_pi cf
    obtain ⟨D, hU, hD⟩ := (Converts.ttrans ca hA.converts).join
    exact ⟨_, .app hf (hT.trans (Reduces.pi hD .refl)) ha hU,
      .symm _ _ (hB.subst (Expr.single a)).converts⟩
  | conversion _ _ hc ih _ =>
    obtain ⟨A₀, h₀, c₀⟩ := ih
    exact ⟨A₀, h₀, .trans _ _ _ c₀ hc⟩

/-! ## The Key Theorem, their Theorem 46 -/

/-- The second alternative of the Key Theorem, written as an inductive telescope.
The `⊢o`-type reduces to `Π x⃗:C⃗. s`, the term reduces to `λ x⃗:C⃗. a₀`, and the body `a₀` has type `s` in the extended context. -/
inductive KeyAlt {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | base {Γ a A a' s} : Reduces A (.sort s) → Reduces a a' → HasType P Γ a' (.sort s) →
      KeyAlt P Γ a A
  | step {Γ a A C A' a' s} : Reduces A (.pi C A') → Reduces a (.lam C a') →
      HasType P Γ C (.sort s) → KeyAlt P (C :: Γ) a' A' → KeyAlt P Γ a A

namespace KeyAlt

variable {P : Specification S}

theorem pre {Γ : List (Expr S)} {a A a₀ A₀ : Expr S} (h : KeyAlt P Γ a A)
    (hA : Reduces A₀ A) (ha : Reduces a₀ a) : KeyAlt P Γ a₀ A₀ := by
  cases h with
  | base h₁ h₂ h₃ => exact .base (hA.trans h₁) (ha.trans h₂) h₃
  | step h₁ h₂ h₃ h₄ => exact .step (hA.trans h₁) (ha.trans h₂) h₃ h₄

theorem sort_inv {Γ : List (Expr S)} {a A : Expr S} {s : S} (h : KeyAlt P Γ a A)
    (hA : Reduces A (.sort s)) : ∃ a', Reduces a a' ∧ HasType P Γ a' (.sort s) := by
  cases h with
  | base h₁ h₂ h₃ =>
    have := Reduces.sort_unique h₁ hA
    subst this
    exact ⟨_, h₂, h₃⟩
  | step h₁ _ _ _ => exact (Reduces.not_sort_pi hA h₁).elim

theorem subst {Γ : List (Expr S)} {a A : Expr S} (h : KeyAlt P Γ a A) :
    ∀ {Δ σ}, ValidContext P Δ → TypedSubstitution P Γ Δ σ →
      KeyAlt P Δ (a.subst σ) (A.subst σ) := by
  induction h with
  | base h₁ h₂ h₃ =>
    intro Δ σ hΔ hσ
    exact .base (h₁.subst σ) (h₂.subst σ) (h₃.subst hΔ σ hσ)
  | step h₁ h₂ h₃ _ ih =>
    intro Δ σ hΔ hσ
    have hC := h₃.subst hΔ σ hσ
    exact .step (h₁.subst σ) (h₂.subst σ) hC (ih (.cons hΔ hC) (hσ.lift hC))

theorem instantiate {Γ : List (Expr S)} {C a A c : Expr S} (h : KeyAlt P (C :: Γ) a A)
    (hc : HasType P Γ c C) : KeyAlt P Γ (a.instantiate c) (A.instantiate c) :=
  h.subst hc.valid (TypedSubstitution.single hc)

theorem weaken {Γ : List (Expr S)} {a A C : Expr S} {s : S} (h : KeyAlt P Γ a A)
    (hC : HasType P Γ C (.sort s)) :
    KeyAlt P (C :: Γ) (a.rename Nat.succ) (A.rename Nat.succ) := by
  have := h.subst (.cons hC.valid hC) (TypedSubstitution.weaken hC)
  simpa only [Expr.subst_var_rename] using this

theorem head_conversion {Γ : List (Expr S)} {C C₂ a A : Expr S} {s t : S}
    (h : KeyAlt P (C :: Γ) a A) (hC : HasType P Γ C (.sort s))
    (hC₂ : HasType P Γ C₂ (.sort t)) (hc : Converts C C₂) : KeyAlt P (C₂ :: Γ) a A := by
  have hσ : TypedSubstitution P (C :: Γ) (C₂ :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hC₂) (.weaken hC hC₂) (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (HasType.lookup hC.valid hn) hC₂
  simpa only [Expr.subst_var] using h.subst (.cons hC₂.valid hC₂) hσ

/-- The second alternative of the Key Theorem is preserved when the `⊢o`-type is reduced. -/
theorem type_reduce {Γ : List (Expr S)} {a A : Expr S} (h : KeyAlt P Γ a A) :
    ∀ {A₂}, Reduces A A₂ → KeyAlt P Γ a A₂ := by
  induction h with
  | base h₁ h₂ h₃ =>
    intro A₂ hr
    exact .base (Reduces.to_sort_of_reduces h₁ hr) h₂ h₃
  | step h₁ h₂ h₃ _ ih =>
    intro A₂ hr
    obtain ⟨C₂, A₃, hA₂, hC, hA'⟩ := Reduces.join_pi h₁ hr
    have hC₂ := h₃.subject_reduces hC
    exact .step hA₂ (h₂.trans (Reduces.lam hC .refl)) hC₂
      ((ih hA').head_conversion h₃ hC₂ hC.converts)

end KeyAlt

/-- **Key Theorem for `⊢o`.**
Let `a` be a well-typed term with a `⊢o`-type `A₁`.
Then either `A₁` is convertible to the type of `a`, or `A₁` reduces to a telescope ending in a sort, and a reduct of `a` realises that telescope. -/
theorem HasType.key {P : Specification S} {Γ : List (Expr S)} {a A₀ : Expr S}
    (h : HasType P Γ a A₀) :
    ∀ {A₁}, HasTypeO P Γ a A₁ → Converts A₁ A₀ ∨ KeyAlt P Γ a A₁ := by
  classical
  induction h with
  | @ax s t hst =>
    intro A₁ ho
    cases ho with
    | @sort _ _ t' h' =>
      by_cases ht : t' = t
      · subst ht; exact .inl (.refl _)
      · exact .inr (.base .refl .refl (.ax h'))
  | var _ _ =>
    intro A₁ ho
    cases ho with
    | var h' => rw [Lookup.unique h' (.zero _ _)]; exact .inl (.refl _)
  | @weaken Γ M B C s hM hC ihM _ =>
    intro A₁ ho
    obtain ⟨T₀, h₀, rfl⟩ :=
      HasTypeO.rename_inv M Nat.succ_injective (DeclRenamingInv.weaken C) ho
    rcases ihM h₀ with c | k
    · exact .inl (c.rename Nat.succ)
    · exact .inr (k.weaken hC)
  | @product Γ A B s₁ s₂ s₃ hA hB hr ihA ihB =>
    intro A₁ ho
    cases ho with
    | @pi _ _ _ TA TB sA sB s hA₀ hTA hB₀ hTB hr' =>
      by_cases hs : s = s₃
      · subst hs; exact .inl (.refl _)
      · right
        -- Some reduct of `A` has the sort `sA` as its type.
        have hCA : ∃ C, Reduces A C ∧ HasType P Γ C (.sort sA) := by
          rcases ihA hA₀ with c | k
          · have := Reduces.sort_unique hTA (Converts.reduces_sort c)
            subst this
            exact ⟨A, .refl, hA⟩
          · exact k.sort_inv hTA
        have hDB : ∃ D, Reduces B D ∧ HasType P (A :: Γ) D (.sort sB) := by
          rcases ihB hB₀ with c | k
          · have := Reduces.sort_unique hTB (Converts.reduces_sort c)
            subst this
            exact ⟨B, .refl, hB⟩
          · exact k.sort_inv hTB
        obtain ⟨C, hAC, hC⟩ := hCA
        obtain ⟨D, hBD, hD⟩ := hDB
        have hD' := hD.context_head_conversion hA hC hAC.converts
        exact .base .refl (Reduces.pi hAC hBD) (.product hC hD' hr')
  | abstraction hb hPi ihb _ =>
    intro A₁ ho
    cases ho with
    | lam hb₀ =>
      rcases ihb hb₀ with c | k
      · exact .inl (Converts.pi (.refl _) c)
      · obtain ⟨s₁, s₂, s₃, hA, _, _, _⟩ := hPi.generation_pi
        exact .inr (.step .refl .refl hA k)
  | @application Γ f a A B hf ha ihf _ =>
    intro A₁ ho
    cases ho with
    | @app _ _ _ T U D E hf₀ hT ha₀ hU =>
      rcases ihf hf₀ with c | k
      · obtain ⟨_, hE⟩ := (Converts.ttrans (.symm _ _ hT.converts) c).product_compatibility
        exact .inl (hE.subst (Expr.single a))
      · cases k with
        | base h₁ _ _ => exact (Reduces.not_sort_pi h₁ hT).elim
        | @step _ _ _ C T₁ f₁ s h₁ h₂ hC k₁ =>
          obtain ⟨Z, hZ₁, hZ₂⟩ := Reduces.confluent h₁ hT
          obtain ⟨C₂, T₂, rfl, hCC, hTT⟩ := Reduces.pi_inv hZ₁
          obtain ⟨D₂, E₂, he, hDD, hEE⟩ := Reduces.pi_inv hZ₂
          simp only [Expr.pi.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hlam := hf.subject_reduces h₂
          obtain ⟨B', t, _, _, hpc⟩ := hlam.generation_lam
          obtain ⟨hAC, _⟩ := hpc.product_compatibility
          have haC : HasType P Γ a C := .conversion ha hC hAC
          have k₂ := (k₁.type_reduce hTT).instantiate haC
          exact .inr (k₂.pre (hEE.subst (Expr.single a))
            ((Reduces.app h₂ .refl).tail (.head _ _ _)))
  | conversion _ _ hc ihM _ =>
    intro A₁ ho
    rcases ihM ho with c | k
    · exact .inl (.trans _ _ _ c hc)
    · exact .inr k

/-- Their Corollary 47.
If `⊢o` gives `a` a type that reduces to a sort `s`, then some reduct of `a` has type `s`. -/
theorem HasType.sort_of_O {P : Specification S} {Γ : List (Expr S)} {a A D : Expr S} {s : S}
    (h : HasType P Γ a A) (ho : HasTypeO P Γ a D) (hD : Reduces D (.sort s)) :
    ∃ a', Reduces a a' ∧ HasType P Γ a' (.sort s) := by
  rcases h.key ho with c | k
  · have hA : Reduces A (.sort s) :=
      Converts.reduces_sort (.trans _ _ _ (.symm _ _ c) hD.converts)
    refine ⟨a, .refl, ?_⟩
    obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := h.regularity
    · rw [Reduces.sort_inv hA]
      exact h
    · exact .conversion h (ht.subject_reduces hA) hA.converts
  · exact k.sort_inv hD

/-! ## The nearly syntax-directed system, their Definition 56 -/

/-- If `M` has type `A` and `A` reduces to `A'`, then `M` also has type `A'`. -/
theorem HasType.type_reduce {P : Specification S} {Γ : List (Expr S)} {M A A' : Expr S}
    (h : HasType P Γ M A) (hr : Reduces A A') : HasType P Γ M A' := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · rw [Reduces.sort_inv hr]; exact h
  · exact .conversion h (hA.subject_reduces hr) hr.converts

/-- Corollary 47, extended to terms that are sorts. -/
theorem HasType.sort_of_O' {P : Specification S} {Γ : List (Expr S)} {a D : Expr S} {s : S}
    (hΓ : ValidContext P Γ) (h : (∃ t, a = .sort t) ∨ ∃ t, HasType P Γ a (.sort t))
    (ho : HasTypeO P Γ a D) (hD : Reduces D (.sort s)) :
    ∃ a', Reduces a a' ∧ HasType P Γ a' (.sort s) := by
  rcases h with ⟨t, rfl⟩ | ⟨t, ht⟩
  · cases ho with
    | sort hax =>
      refine ⟨_, .refl, ?_⟩
      rw [Reduces.sort_inv hD]
      exact HasType.sort_of_valid hΓ hax
  · exact ht.sort_of_O ho hD

/-- The relation `⊢nsdtp`, with `⊢o` in the side condition of the λ-rule.
Variables are typed through `Lookup`, there are no premises about contexts, and there is no conversion rule. -/
inductive HasTypeN {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | sort {Γ s t} : P.axioms s t → HasTypeN P Γ (.sort s) (.sort t)
  | var {Γ n A} : Lookup Γ n A → HasTypeN P Γ (.var n) A
  | pi {Γ A B TA TB s₁ s₂ s₃} : HasTypeN P Γ A TA → Reduces TA (.sort s₁) →
      HasTypeN P (A :: Γ) B TB → Reduces TB (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeN P Γ (.pi A B) (.sort s₃)
  | lam {Γ A b TA B' B D s₁ s₂ s₃} : HasTypeN P Γ A TA → Reduces TA (.sort s₁) →
      HasTypeN P (A :: Γ) b B' → Reduces B' B →
      HasTypeO P (A :: Γ) B D → Reduces D (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeN P Γ (.lam A b) (.pi A B)
  | app {Γ f a T U D E} : HasTypeN P Γ f T → Reduces T (.pi D E) →
      HasTypeN P Γ a U → Converts U D → HasTypeN P Γ (.app f a) (E.instantiate a)

namespace HasTypeN

variable {P : Specification S}

theorem rename {M T : Expr S} {Γ : List (Expr S)} (h : HasTypeN P Γ M T) :
    ∀ {Δ : List (Expr S)} {ρ : Nat → Nat}, TypingTree.DeclRenaming Γ Δ ρ →
      HasTypeN P Δ (M.rename ρ) (T.rename ρ) := by
  induction h with
  | sort h => intro Δ ρ _; exact .sort h
  | var h => intro Δ ρ hρ; exact .var (hρ _ _ h)
  | pi _ hTA _ hTB hr ihA ihB =>
    intro Δ ρ hρ
    exact .pi (ihA hρ) (hTA.rename ρ) (ihB (hρ.lift _)) (hTB.rename (Expr.liftRen ρ)) hr
  | lam _ hTA _ hB hBo hD hr ihA ihb =>
    intro Δ ρ hρ
    exact .lam (ihA hρ) (hTA.rename ρ) (ihb (hρ.lift _)) (hB.rename (Expr.liftRen ρ))
      (hBo.rename (hρ.lift _)) (hD.rename (Expr.liftRen ρ)) hr
  | app _ hT _ hU ihf iha =>
    intro Δ ρ hρ
    rw [← Expr.instantiate_rename]
    exact .app (ihf hρ) (hT.rename ρ) (iha hρ) (hU.rename ρ)

/-- Strengthening for `⊢nsdtp`, their Lemma 67.
Since there is no conversion rule, a typing of a renamed term comes from a typing of the original term. -/
theorem rename_inv : ∀ (M : Expr S) {Γ Δ : List (Expr S)} {ρ : Nat → Nat} {T : Expr S},
    Function.Injective ρ → DeclRenamingInv Γ Δ ρ → HasTypeN P Δ (M.rename ρ) T →
      ∃ T₀, HasTypeN P Γ M T₀ ∧ T = T₀.rename ρ := by
  intro M
  induction M with
  | var n =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | var h =>
      obtain ⟨A₀, hA₀, rfl⟩ := hinv n _ h
      exact ⟨A₀, .var hA₀, rfl⟩
  | sort s =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | sort h => exact ⟨_, .sort h, rfl⟩
  | pi A B ihA ihB =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | pi hA hTA hB hTB hr =>
      obtain ⟨TA₀, hA₀, rfl⟩ := ihA hρ hinv hA
      obtain ⟨TB₀, hB₀, rfl⟩ := ihB (liftRen_injective hρ) (hinv.lift A) hB
      obtain ⟨X, hX, hTA₀⟩ := Reduces.rename_inv hρ hTA
      obtain ⟨Y, hY, hTB₀⟩ := Reduces.rename_inv (liftRen_injective hρ) hTB
      cases X <;> simp [Expr.rename] at hX
      cases Y <;> simp [Expr.rename] at hY
      subst hX hY
      exact ⟨_, .pi hA₀ hTA₀ hB₀ hTB₀ hr, rfl⟩
  | lam A b ihA ihb =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | lam hA hTA hb hB hBo hD hr =>
      obtain ⟨TA₀, hA₀, rfl⟩ := ihA hρ hinv hA
      obtain ⟨X, hX, hTA₀⟩ := Reduces.rename_inv hρ hTA
      cases X <;> simp [Expr.rename] at hX
      subst hX
      obtain ⟨B'₀, hb₀, rfl⟩ := ihb (liftRen_injective hρ) (hinv.lift A) hb
      obtain ⟨B₀, rfl, hB₀⟩ := Reduces.rename_inv (liftRen_injective hρ) hB
      obtain ⟨D₀, hBo₀, rfl⟩ :=
        HasTypeO.rename_inv B₀ (liftRen_injective hρ) (hinv.lift A) hBo
      obtain ⟨Y, hY, hD₀⟩ := Reduces.rename_inv (liftRen_injective hρ) hD
      cases Y <;> simp [Expr.rename] at hY
      subst hY
      exact ⟨_, .lam hA₀ hTA₀ hb₀ hB₀ hBo₀ hD₀ hr, rfl⟩
  | app f a ihf iha =>
    intro Γ Δ ρ T hρ hinv h
    cases h with
    | app hf hT ha hU =>
      obtain ⟨T₀, hf₀, rfl⟩ := ihf hρ hinv hf
      obtain ⟨U₀, ha₀, rfl⟩ := iha hρ hinv ha
      obtain ⟨X, hX, hT₀⟩ := Reduces.rename_inv hρ hT
      cases X with
      | pi D₀ E₀ =>
        simp only [Expr.rename, Expr.pi.injEq] at hX
        obtain ⟨rfl, rfl⟩ := hX
        exact ⟨_, .app hf₀ hT₀ ha₀ (Converts.rename_inv hρ hU), Expr.instantiate_rename E₀ a ρ⟩
      | _ => simp [Expr.rename] at hX

/-- Every `⊢nsdtp` typing is a `⊢o` typing up to conversion, their Lemma 57 (i). -/
theorem toO {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeN P Γ M T) :
    ∃ T₀, HasTypeO P Γ M T₀ ∧ Converts T₀ T := by
  induction h with
  | sort h => exact ⟨_, .sort h, .refl _⟩
  | var h => exact ⟨_, .var h, .refl _⟩
  | pi _ hTA _ hTB hr ihA ihB =>
    obtain ⟨TA₀, hA₀, cA⟩ := ihA
    obtain ⟨TB₀, hB₀, cB⟩ := ihB
    exact ⟨_, .pi hA₀ (Converts.reduces_sort (.trans _ _ _ cA hTA.converts)) hB₀
      (Converts.reduces_sort (.trans _ _ _ cB hTB.converts)) hr, .refl _⟩
  | lam _ _ _ hB _ _ _ _ ihb =>
    obtain ⟨B₀, hb₀, cb⟩ := ihb
    exact ⟨_, .lam hb₀, Converts.pi (.refl _) (.trans _ _ _ cb hB.converts)⟩
  | @app Γ f a T U D E _ hT _ hU ihf iha =>
    obtain ⟨T₀, hf₀, cf⟩ := ihf
    obtain ⟨D', E', hT₀, hD, hE⟩ := Converts.join_pi (.trans _ _ _ cf hT.converts)
    obtain ⟨U₀, ha₀, ca⟩ := iha
    obtain ⟨D'', hU'', hD''⟩ := (Converts.ttrans (Converts.ttrans ca hU) hD.converts).join
    exact ⟨_, .app hf₀ (hT₀.trans (Reduces.pi hD'' .refl)) ha₀ hU'',
      .symm _ _ (hE.subst (Expr.single a)).converts⟩

/-- Soundness of `⊢nsdtp`, their Lemma 59. -/
theorem sound {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeN P Γ M T) :
    ValidContext P Γ → ∃ T₀, Reduces T T₀ ∧ HasType P Γ M T₀ := by
  induction h with
  | sort hax => intro hΓ; exact ⟨_, .refl, HasType.sort_of_valid hΓ hax⟩
  | var hn => intro hΓ; exact ⟨_, .refl, HasType.lookup hΓ hn⟩
  | pi _ hTA _ hTB hr ihA ihB =>
    intro hΓ
    obtain ⟨A₁, rA, hA₁⟩ := ihA hΓ
    have hAs := hA₁.type_reduce (Reduces.to_sort_of_reduces hTA rA)
    obtain ⟨B₁, rB, hB₁⟩ := ihB (.cons hΓ hAs)
    have hBs := hB₁.type_reduce (Reduces.to_sort_of_reduces hTB rB)
    exact ⟨_, .refl, .product hAs hBs hr⟩
  | lam _ hTA _ hB hBo hD hr ihA ihb =>
    intro hΓ
    obtain ⟨A₁, rA, hA₁⟩ := ihA hΓ
    have hAs := hA₁.type_reduce (Reduces.to_sort_of_reduces hTA rA)
    have hΓ' : ValidContext P _ := .cons hΓ hAs
    obtain ⟨B₁, rB₁, hb₁⟩ := ihb hΓ'
    obtain ⟨B₄, h₄B, h₄B₁⟩ := Reduces.confluent hB rB₁
    have hb₄ := hb₁.type_reduce h₄B₁
    obtain ⟨D₄, hD₄, cD₄⟩ := hBo.closure h₄B
    have rD₄ := Converts.reduces_sort (.trans _ _ _ cD₄ hD.converts)
    obtain ⟨B₅, r₅, hB₅⟩ := HasType.sort_of_O' hΓ' hb₄.regularity hD₄ rD₄
    exact ⟨_, Reduces.pi .refl (h₄B.trans r₅),
      .abstraction (hb₄.type_reduce r₅) (.product hAs hB₅ hr)⟩
  | @app Γ f a T U D E _ hT _ hU ihf iha =>
    intro hΓ
    obtain ⟨T₁, rT, hf₁⟩ := ihf hΓ
    obtain ⟨D₂, E₂, hT₁, hDD, hEE⟩ := Reduces.join_pi hT rT
    obtain ⟨U₁, rU, ha₁⟩ := iha hΓ
    have c : Converts U₁ D₂ :=
      .trans _ _ _ (.symm _ _ rU.converts) (.trans _ _ _ hU hDD.converts)
    obtain ⟨D₃, hU₃, hD₃⟩ := c.join
    exact ⟨_, hEE.subst (Expr.single a),
      .application ((hf₁.type_reduce hT₁).type_reduce (Reduces.pi hD₃ .refl))
        (ha₁.type_reduce hU₃)⟩

end HasTypeN

/-- Completeness of `⊢nsdtp`, their Lemma 58. -/
theorem HasType.toN {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) : ∃ A₀, HasTypeN P Γ M A₀ ∧ Converts A₀ A := by
  induction h with
  | ax h => exact ⟨_, .sort h, .refl _⟩
  | var _ _ => exact ⟨_, .var (.zero _ _), .refl _⟩
  | weaken _ _ ih _ =>
    obtain ⟨A₀, h₀, c₀⟩ := ih
    exact ⟨_, h₀.rename (TypingTree.DeclRenaming.weaken _), c₀.rename Nat.succ⟩
  | product _ _ hr ihA ihB =>
    obtain ⟨TA, hA, cA⟩ := ihA
    obtain ⟨TB, hB, cB⟩ := ihB
    exact ⟨_, .pi hA (Converts.reduces_sort cA) hB (Converts.reduces_sort cB) hr, .refl _⟩
  | abstraction _ _ ihb ihPi =>
    obtain ⟨B₀, hb₀, cb⟩ := ihb
    obtain ⟨P₀, hP₀, cP⟩ := ihPi
    cases hP₀ with
    | pi hA hTA hB hTB hr =>
      obtain ⟨TB₀, hBo, cB⟩ := hB.toO
      obtain ⟨B₁, hB₀B₁, hBB₁⟩ := cb.join
      obtain ⟨D₁, hD₁, cD₁⟩ := hBo.closure hBB₁
      have rD₁ : Reduces D₁ (.sort _) :=
        Converts.reduces_sort (.trans _ _ _ cD₁ (.trans _ _ _ cB hTB.converts))
      exact ⟨_, .lam hA hTA hb₀ hB₀B₁ hD₁ rD₁ hr,
        Converts.pi (.refl _) (.symm _ _ hBB₁.converts)⟩
  | @application Γ f a A B _ _ ihf iha =>
    obtain ⟨T, hf₀, cf⟩ := ihf
    obtain ⟨A', B', hT, hA, hB⟩ := Converts.join_pi cf
    obtain ⟨U, ha₀, ca⟩ := iha
    exact ⟨_, .app hf₀ hT ha₀ (Converts.ttrans ca hA.converts),
      .symm _ _ (hB.subst (Expr.single a)).converts⟩
  | conversion _ _ hc ih _ =>
    obtain ⟨A₀, h₀, c₀⟩ := ih
    exact ⟨A₀, h₀, .trans _ _ _ c₀ hc⟩

/-! ## Strengthening, their Theorem 63 -/

/-- **Strengthening for arbitrary PTSs.**
Suppose a renamed term is typed in a context that only adds unused declarations.
Then the original term is typed in the smaller context, at a type `T₀` such that the old type reduces to the renaming of `T₀`. -/
theorem HasType.strengthen {P : Specification S} {Γ Δ : List (Expr S)} {ρ : Nat → Nat}
    {M T : Expr S} (hρ : Function.Injective ρ) (hinv : DeclRenamingInv Γ Δ ρ)
    (hΓ : ValidContext P Γ) (h : HasType P Δ (M.rename ρ) T) :
    ∃ T₀, HasType P Γ M T₀ ∧ Reduces T (T₀.rename ρ) := by
  obtain ⟨A₀, hN, c⟩ := h.toN
  obtain ⟨A₁, hN₁, rfl⟩ := HasTypeN.rename_inv M hρ hinv hN
  obtain ⟨A₂, r₂, h₂⟩ := hN₁.sound hΓ
  obtain ⟨Z, hTZ, hAZ⟩ := (Converts.ttrans (.symm _ _ c) (r₂.rename ρ).converts).join
  obtain ⟨Z₀, rfl, hA₂Z₀⟩ := Reduces.rename_inv hρ hAZ
  exact ⟨Z₀, h₂.type_reduce hA₂Z₀, hTZ⟩

/-- Strengthening that removes the innermost declaration. -/
theorem HasType.strengthen_succ {P : Specification S} {Γ : List (Expr S)} {C M T : Expr S}
    (h : HasType P (C :: Γ) (M.rename Nat.succ) T) :
    ∃ T₀, HasType P Γ M T₀ ∧ Reduces T (T₀.rename Nat.succ) := by
  have hv := h.valid
  cases hv with
  | cons hΓ _ => exact h.strengthen Nat.succ_injective (DeclRenamingInv.weaken C) hΓ

/-- **Subject reduction for an η-step at the root**, for typing with β-conversion and any specification. -/
theorem HasType.eta_head {P : Specification S} {Γ : List (Expr S)} {D F C : Expr S}
    (h : HasType P Γ (.lam D (.app (F.rename Nat.succ) (.var 0))) C) : HasType P Γ F C := by
  obtain ⟨B, s, hb, _, cC⟩ := h.generation_lam
  obtain ⟨A', B', hF, hx, cB⟩ := hb.generation_app
  obtain ⟨T₀, hF₀, rT⟩ := hF.strengthen_succ
  obtain ⟨A'', B'', hT, hA'', hB''⟩ := Reduces.pi_inv rT
  cases T₀ <;> simp only [Expr.rename, reduceCtorEq] at hT
  rename_i P₀ Q₀
  simp only [Expr.pi.injEq] at hT
  obtain ⟨rfl, rfl⟩ := hT
  obtain ⟨A₀, hl, cA⟩ := hx.generation
  cases hl
  have hDP : Converts D P₀ :=
    Converts.rename_inv Nat.succ_injective (.trans _ _ _ (.symm _ _ cA) hA''.converts)
  have hBQ : Converts B Q₀ := by
    have := hB''.subst (Expr.single (.var 0))
    change Reduces (B'.instantiate (.var 0))
      ((Q₀.rename (Expr.liftRen Nat.succ)).instantiate (.var 0)) at this
    rw [Expr.instantiate_liftRen_succ_var] at this
    exact .trans _ _ _ cB this.converts
  have hc : Converts (.pi P₀ Q₀) C := .symm _ _ (.trans _ _ _ cC (Converts.pi hDP hBQ))
  obtain ⟨t, rfl⟩ | ⟨t, hC⟩ := h.regularity
  · exact (Converts.pi_not_sort hc).elim
  · exact .conversion hF₀ hC hc

end PureTypeSystem
