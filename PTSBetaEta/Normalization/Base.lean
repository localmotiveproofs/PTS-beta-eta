module

public import PTSBetaEta.Eta.Metatheory
public import PTSBetaEta.Eta.Paradox

@[expose] public section

/-!
# Foundations for typing with βη-conversion

Typing here is `HasTypeBE`, whose conversion rule uses βη-conversion.
The standing hypothesis is `SystemENormalizing z P`, which follows from weak βη-normalization of this system.
It says that every legal term has a β-reduct with no β-redex outside its λ-domains.

βη-conversion ignores λ-domains (`convertsBE_erase`), and it is confluent on erased terms (`convertsBE_join`).
This file proves the following facts.

* Erased βη-reduction of neutral spines can be inverted.
* Two neutral terms that are βη-convertible have βη-convertible types.
* An erasure-normal type that has a sort as its type is a sort, a neutral spine or a product.
* The sorts of such a type do not change under βη-conversion.
* Reduct profiles are invariant under βη-conversion.
* Each reduct profile has a normal witness typed with β-conversion, so reduct profiles are feasible in OpenAI's profile graph, which is reused unchanged.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

/-! ## βη-normal forms on erased terms -/

theorem NormalBE.normal {M : Expr S} (h : NormalBE M) : Normal M := fun N hN => h N (.inl hN)

theorem ParEta.eq_of_normalBE {M N : Expr S} (h : NormalBE M) (p : ParEta M N) : N = M := by
  rcases (ParEta.eta_star p).cases_head with e | ⟨c, hc, _⟩
  · exact e.symm
  · exact (h c (.inr hc)).elim

theorem Parallel.eq_of_normalBE {M N : Expr S} (h : NormalBE M) (p : Parallel M N) : N = M :=
  (Normal.reduces_eq h.normal p.reduces).symm

theorem StepE.eq_of_normalBE {z : S} {M N : Expr S} (h : NormalBE M) (p : StepE z M N) :
    N = M := by
  rcases p with ⟨_, p | p⟩
  · exact Parallel.eq_of_normalBE h p
  · exact ParEta.eq_of_normalBE h p

theorem stepE_star_eq_of_normalBE {z : S} {M N : Expr S} (h : NormalBE M)
    (p : ReflTransGen (StepE z) M N) : N = M := by
  induction p with
  | refl => rfl
  | tail _ hs ih => subst ih; exact StepE.eq_of_normalBE h hs

/-- Two erased βη-normal terms that are βη-convertible are equal. -/
theorem eq_of_convertsBE_normalBE (z : S) {X Y : Expr S} (eX : X.erase z = X)
    (eY : Y.erase z = Y) (hX : NormalBE X) (hY : NormalBE Y) (h : ConvertsBE X Y) : X = Y := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  rw [eX] at h₁
  rw [eY] at h₂
  exact (stepE_star_eq_of_normalBE hX h₁).symm.trans (stepE_star_eq_of_normalBE hY h₂)

/-! ## Shapes of erasures -/

theorem Neutral.erase (z : S) {M : Expr S} (h : Neutral M) : Neutral (M.erase z) := by
  induction h with
  | var n => exact .var n
  | app _ ih => exact .app ih

theorem erase_eq_sort (z : S) {X : Expr S} {s : S} (h : X.erase z = .sort s) : X = .sort s := by
  cases X <;> simp [Expr.erase] at h
  subst h; rfl

theorem erase_eq_pi (z : S) {X A B : Expr S} (h : X.erase z = .pi A B) :
    ∃ A' B', X = .pi A' B' ∧ A'.erase z = A ∧ B'.erase z = B := by
  cases X <;> simp [Expr.erase] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem erase_eq_var (z : S) {X : Expr S} {n : Nat} (h : X.erase z = .var n) : X = .var n := by
  cases X <;> simp [Expr.erase] at h
  subst h; rfl

theorem erase_eq_app (z : S) {X f a : Expr S} (h : X.erase z = .app f a) :
    ∃ f' a', X = .app f' a' ∧ f'.erase z = f ∧ a'.erase z = a := by
  cases X <;> simp [Expr.erase] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem Neutral.parallel {f g : Expr S} (hf : Neutral f) (h : Parallel f g) : Neutral g := by
  induction hf generalizing g with
  | var n => rw [Parallel.var_inv h]; exact .var n
  | @app f a hf ih =>
    rcases Parallel.app_inv h with ⟨f', a', rfl, pf, _⟩ | ⟨A, b, b', a', rfl, _, _, _⟩
    · exact .app (ih pf)
    · cases hf

theorem Neutral.parEta {f g : Expr S} (hf : Neutral f) (h : ParEta f g) : Neutral g := by
  induction hf generalizing g with
  | var n => rw [ParEta.var_inv h]; exact .var n
  | @app f a hf ih =>
    obtain ⟨f', a', rfl, pf, _⟩ := ParEta.app_inv h
    exact .app (ih pf)

theorem stepE_star_var_inv {z : S} {n : Nat} {W : Expr S}
    (h : ReflTransGen (StepE z) (.var n) W) : W = .var n := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    rcases hs with ⟨_, hs | hs⟩
    · exact Parallel.var_inv hs
    · exact ParEta.var_inv hs

/-- Erased βη-reduction of a neutral application gives a neutral application. -/
theorem stepE_star_app_neutral {z : S} {f a W : Expr S} (hf : Neutral f)
    (h : ReflTransGen (StepE z) (.app f a) W) :
    ∃ f' a', W = .app f' a' ∧ Neutral f' ∧ ReflTransGen (StepE z) f f' ∧
      ReflTransGen (StepE z) a a' := by
  induction h with
  | refl => exact ⟨f, a, rfl, hf, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨f', a', rfl, hf', h1, h2⟩ := ih
    obtain ⟨hE, hs⟩ := hs
    obtain ⟨ef, ea⟩ := hE.app
    rcases hs with hs | hs
    · rcases Parallel.app_inv hs with ⟨f'', a'', rfl, pf, pa⟩ | ⟨A, b, b', a'', rfl, _, _, _⟩
      · exact ⟨f'', a'', rfl, hf'.parallel pf, h1.tail ⟨ef, .inl pf⟩, h2.tail ⟨ea, .inl pa⟩⟩
      · cases hf'
    · obtain ⟨f'', a'', rfl, pf, pa⟩ := ParEta.app_inv hs
      exact ⟨f'', a'', rfl, hf'.parEta pf, h1.tail ⟨ef, .inr pf⟩, h2.tail ⟨ea, .inr pa⟩⟩

theorem stepE_star_neutral_erase {z : S} {M W : Expr S} (hM : Neutral M)
    (h : ReflTransGen (StepE z) (M.erase z) W) : Neutral W := by
  cases hM with
  | var n => rw [stepE_star_var_inv h]; exact .var n
  | @app f a hf =>
    obtain ⟨f', a', rfl, hf', _, _⟩ := stepE_star_app_neutral (hf.erase z) h
    exact .app hf'

/-- A neutral term that is βη-convertible to a variable is that variable. -/
theorem convertsBE_var_neutral (z : S) {n : Nat} {N : Expr S} (hN : Neutral N)
    (h : ConvertsBE (.var n) N) : N = .var n := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  have hW : W = .var n := stepE_star_var_inv h₁
  subst hW
  cases hN with
  | var m =>
    have := stepE_star_var_inv h₂
    simp only [Expr.var.injEq] at this
    rw [this]
  | @app g b hg =>
    obtain ⟨g', b', he, _⟩ := stepE_star_app_neutral (hg.erase z) h₂
    cases he

/-- If two neutral applications are βη-convertible, then their heads are βη-convertible and their arguments are βη-convertible. -/
theorem convertsBE_app_neutral (z : S) {f a N : Expr S} (hf : Neutral f) (hN : Neutral N)
    (h : ConvertsBE (.app f a) N) :
    ∃ g b, N = .app g b ∧ Neutral g ∧ ConvertsBE f g ∧ ConvertsBE a b := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  obtain ⟨f₁, a₁, rfl, _, hf₁, ha₁⟩ := stepE_star_app_neutral (hf.erase z) h₁
  cases hN with
  | var m =>
    have := stepE_star_var_inv h₂
    cases this
  | @app g b hg =>
    obtain ⟨g₁, b₁, he, _, hg₁, hb₁⟩ := stepE_star_app_neutral (hg.erase z) h₂
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨g, b, rfl, hg, ?_, ?_⟩
    · exact .trans _ _ _ (convertsBE_erase z f) (.trans _ _ _ (stepE_star_convertsBE z hf₁)
        (.trans _ _ _ (.symm _ _ (stepE_star_convertsBE z hg₁)) (.symm _ _ (convertsBE_erase z g))))
    · exact .trans _ _ _ (convertsBE_erase z a) (.trans _ _ _ (stepE_star_convertsBE z ha₁)
        (.trans _ _ _ (.symm _ _ (stepE_star_convertsBE z hb₁)) (.symm _ _ (convertsBE_erase z b))))

/-! ## Types of neutral terms up to βη-conversion -/

namespace HasTypeBE

variable {P : Specification S} {Γ : List (Expr S)}

/-- **Uniqueness of types for convertible neutral terms.**
If two neutral terms are βη-convertible, then their types are βη-convertible.
No functionality is assumed. -/
theorem neutral_unique_conv (z : S) : ∀ {M N A B : Expr S}, Neutral M → Neutral N →
    ConvertsBE M N → HasTypeBE P Γ M A → HasTypeBE P Γ N B → ConvertsBE A B := by
  intro M N A B hM
  induction hM generalizing N A B with
  | var n =>
    intro hN hc hA hB
    have := convertsBE_var_neutral z hN hc
    subst this
    exact HasTypeBE.neutral_unique (.var n) hA hB
  | @app f a hf ih =>
    intro hN hc hA hB
    obtain ⟨g, b, rfl, hg, cfg, cab⟩ := convertsBE_app_neutral z hf hN hc
    obtain ⟨D, E, hf1, _, c1⟩ := hA.generation_app
    obtain ⟨D', E', hg1, _, c2⟩ := hB.generation_app
    have cpi := ih hg cfg hf1 hg1
    obtain ⟨_, cE⟩ := cpi.product_compatibility z
    exact .trans _ _ _ c1 (.trans _ _ _ (cE.subst (Expr.single a))
      (.trans _ _ _ (cab.instantiate_right E') (.symm _ _ c2)))

theorem lookup_sorted (hΓ : ValidContextBE P Γ) {n : Nat} {A : Expr S}
    (hn : Lookup Γ n A) : ∃ s, HasTypeBE P Γ A (.sort s) := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact ⟨_, .weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨s, hs⟩ := ih hn
          exact ⟨s, .weaken hs hB⟩

end HasTypeBE

/-! ## Shapes of erasure-normal terms -/

/-- An erasure-normal term with a product type that is not an abstraction is a neutral spine. -/
theorem neutral_of_enormalBE (z : S) {P : Specification S} : ∀ (f : Expr S)
    {Γ : List (Expr S)} {D E : Expr S}, HasTypeBE P Γ f (.pi D E) → ENormal z f →
      (∀ A b, f ≠ .lam A b) → Neutral f := by
  intro f
  induction f with
  | var n => intro _ _ _ _ _ _; exact .var n
  | sort s => intro _ _ _ h _ _; exact h.sort_cannot_have_product_type.elim
  | pi A B _ _ => intro _ _ _ h _ _; exact h.product_cannot_have_product_type.elim
  | lam A b _ _ => intro _ _ _ _ _ hnl; exact (hnl A b rfl).elim
  | app g c ihg _ =>
    intro Γ D E h he _
    obtain ⟨D', E', hg, _, _⟩ := h.generation_app
    obtain ⟨eg, _, gnl⟩ := he.app
    exact .app (ihg hg eg gnl)

/-- An erasure-normal type that has a sort as its type is a sort, a neutral spine or a product. -/
theorem HasTypeBE.enormal_sorted_shape (z : S) {P : Specification S} {Γ : List (Expr S)}
    {M : Expr S} {s : S} (h : HasTypeBE P Γ M (.sort s)) (hn : ENormal z M) :
    (∃ t, M = .sort t) ∨ Neutral M ∨ ∃ A B, M = .pi A B := by
  cases M with
  | var n => exact .inr (.inl (.var n))
  | sort t => exact .inl ⟨t, rfl⟩
  | pi A B => exact .inr (.inr ⟨A, B, rfl⟩)
  | lam A b => exact h.lambda_cannot_have_sort_type.elim
  | app f a =>
    obtain ⟨D, E, hf, _, _⟩ := h.generation_app
    obtain ⟨ef, _, fnl⟩ := hn.app
    exact .inr (.inl (.app (neutral_of_enormalBE z f hf ef fnl)))

/-- Two erasure-normal types that have sorts as their types and are βη-convertible have the same outer shape.
They may live in different contexts. -/
theorem convertsBE_sorted_shape (z : S) {P : Specification S} {Γ Δ : List (Expr S)}
    {A B : Expr S} {s t : S} (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Δ B (.sort t))
    (eA : ENormal z A) (eB : ENormal z B) (hc : ConvertsBE A B) :
    (∃ u, A = .sort u ∧ B = .sort u) ∨ (∃ A₁ A₂ B₁ B₂, A = .pi A₁ A₂ ∧ B = .pi B₁ B₂) ∨
      (Neutral A ∧ Neutral B) := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z hc
  rcases hA.enormal_sorted_shape z eA with ⟨u, rfl⟩ | nA | ⟨A₁, A₂, rfl⟩ <;>
  rcases hB.enormal_sorted_shape z eB with ⟨u', rfl⟩ | nB | ⟨B₁, B₂, rfl⟩
  · exact .inl ⟨u, rfl, by rw [convertsBE_sort_inj hc]⟩
  · exfalso
    have hW : W = .sort u := stepE_star_sort_inv z h₁
    have := stepE_star_neutral_erase nB h₂
    rw [hW] at this; cases this
  · exact (convertsBE_pi_not_sort (.symm _ _ hc)).elim
  · exfalso
    have hW : W = .sort u' := stepE_star_sort_inv z h₂
    have := stepE_star_neutral_erase nA h₁
    rw [hW] at this; cases this
  · exact .inr (.inr ⟨nA, nB⟩)
  · exfalso
    obtain ⟨X, Y, rfl, _, _⟩ := stepE_star_pi_inv z h₂
    have := stepE_star_neutral_erase nA h₁
    cases this
  · exact (convertsBE_pi_not_sort hc).elim
  · exfalso
    obtain ⟨X, Y, rfl, _, _⟩ := stepE_star_pi_inv z h₁
    have := stepE_star_neutral_erase nB h₂
    cases this
  · exact .inr (.inl ⟨_, _, _, _, rfl, rfl⟩)

theorem ENormal.eq_sort_of_convertsBE (z : S) {P : Specification S} {Γ : List (Expr S)}
    {X : Expr S} {s t : S} (hX : HasTypeBE P Γ X (.sort s)) (eX : ENormal z X)
    (h : ConvertsBE X (.sort t)) : X = .sort t := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  have hW : W = .sort t := stepE_star_sort_inv z h₂
  subst hW
  rcases hX.enormal_sorted_shape z eX with ⟨u, rfl⟩ | nX | ⟨A, B, rfl⟩
  · rw [convertsBE_sort_inj h]
  · have := stepE_star_neutral_erase nX h₁
    cases this
  · obtain ⟨X', Y', he, _, _⟩ := stepE_star_pi_inv z h₁
    cases he

/-- An erasure-normal type that has a sort as its type and is βη-convertible to a product is itself a product. -/
theorem ENormal.pi_of_convertsBE (z : S) {P : Specification S} {Γ : List (Expr S)}
    {X C D : Expr S} {s : S} (hX : HasTypeBE P Γ X (.sort s)) (eX : ENormal z X)
    (h : ConvertsBE X (.pi C D)) : ∃ X₁ X₂, X = .pi X₁ X₂ := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  obtain ⟨Y₁, Y₂, rfl, _, _⟩ := stepE_star_pi_inv z h₂
  rcases hX.enormal_sorted_shape z eX with ⟨u, rfl⟩ | nX | ⟨A, B, rfl⟩
  · have := stepE_star_sort_inv z h₁
    cases this
  · have := stepE_star_neutral_erase nX h₁
    cases this
  · exact ⟨A, B, rfl⟩

/-! ## Erasure-normal reducts -/

variable (z : S)

/-- Every legal term has a β-reduct with no β-redex outside its λ-domains. -/
def SystemENormalizing (P : Specification S) : Prop :=
  ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → ∃ M', Reduces M M' ∧ ENormal z M'

theorem SystemWeaklyNormalizingBE.eNormalizing {P : Specification S}
    (h : SystemWeaklyNormalizingBE P) : SystemENormalizing z P :=
  fun Γ hΓ M hM => erasure_normalizes_of_betaEta z (h Γ hΓ M hM)

variable {z}

/-- A legal type that is βη-convertible to a sort β-reduces to that sort. -/
theorem HasTypeBE.reduces_sort_of_convertsBE {P : Specification S} (hE : SystemENormalizing z P)
    {Γ : List (Expr S)} {X : Expr S} {s t : S} (hX : HasTypeBE P Γ X (.sort s))
    (h : ConvertsBE X (.sort t)) : Reduces X (.sort t) := by
  obtain ⟨X₁, r₁, e₁⟩ := hE Γ hX.valid X ⟨_, .inl hX⟩
  have hX₁ := hX.subject_reduces r₁
  have c : ConvertsBE X₁ (.sort t) := .trans _ _ _ (.symm _ _ (reduces_convertsBE r₁)) h
  rw [← ENormal.eq_sort_of_convertsBE z hX₁ e₁ c]
  exact r₁

theorem HasTypeBE.neutral_type_sorted {P : Specification S} (hE : SystemENormalizing z P)
    {Γ : List (Expr S)} {M A : Expr S} (hn : Neutral M) (ht : HasTypeBE P Γ M A) :
    ∃ s, HasTypeBE P Γ A (.sort s) := by
  cases hn with
  | var n =>
      obtain ⟨D, hD, hc⟩ := ht.generation
      obtain ⟨s, hs⟩ := HasTypeBE.lookup_sorted ht.valid hD
      obtain ⟨t, rfl⟩ | hA := ht.regularity
      · exact ⟨s, hs.subject_reduces (hs.reduces_sort_of_convertsBE hE (.symm _ _ hc))⟩
      · exact hA
  | app _ => exact ht.application_type_sorted

theorem HasTypeBE.neutral_axiom {P : Specification S} (hE : SystemENormalizing z P)
    {Γ : List (Expr S)} {M : Expr S} {s : S} (hne : Neutral M)
    (ht : HasTypeBE P Γ M (.sort s)) : (AxProfile P s).Nonempty := by
  obtain ⟨t, ht⟩ := ht.neutral_type_sorted hE hne
  obtain ⟨u, hu, _⟩ := ht.generation
  exact ⟨u, hu⟩

/-! ## The sorts of erasure-normal types are invariant under βη-conversion -/

variable (z) in
theorem sorts_iff_of_convertsBE {P : Specification S} : ∀ (A : Expr S) {Γ : List (Expr S)}
    {B : Expr S} {s t : S}, HasTypeBE P Γ A (.sort s) → HasTypeBE P Γ B (.sort t) →
    ENormal z A → ENormal z B → ConvertsBE A B →
      ∀ r, HasTypeBE P Γ A (.sort r) ↔ HasTypeBE P Γ B (.sort r) := by
  intro A
  have neutral_case : ∀ {Γ : List (Expr S)} {A B : Expr S} {s t : S}, Neutral A → Neutral B →
      HasTypeBE P Γ A (.sort s) → HasTypeBE P Γ B (.sort t) → ConvertsBE A B →
      ∀ r, HasTypeBE P Γ A (.sort r) ↔ HasTypeBE P Γ B (.sort r) := by
    intro Γ A B s t nA nB hA hB hc r
    have hst : s = t := (HasTypeBE.neutral_unique_conv z nA nB hc hA hB).sort_inj
    subst hst
    constructor
    · intro h
      have := (HasTypeBE.neutral_unique nA h hA).sort_inj; subst this; exact hB
    · intro h
      have := (HasTypeBE.neutral_unique nB h hB).sort_inj; subst this; exact hA
  induction A with
  | sort u =>
    intro Γ B s t hA hB eA eB hc r
    rcases convertsBE_sorted_shape z hA hB eA eB hc with ⟨u', e1, rfl⟩ | ⟨_, _, _, _, e1, _⟩ |
      ⟨n1, _⟩
    · cases e1; exact Iff.rfl
    · cases e1
    · cases n1
  | lam _ _ _ _ => intro _ _ _ _ hA; exact hA.lambda_cannot_have_sort_type.elim
  | pi A₁ A₂ ih₁ ih₂ =>
    intro Γ B s t hA hB eA eB hc r
    rcases convertsBE_sorted_shape z hA hB eA eB hc with ⟨u', e1, _⟩ |
      ⟨A₁', A₂', B₁, B₂, e1, rfl⟩ | ⟨n1, _⟩
    · cases e1
    · cases e1
      obtain ⟨c₁, c₂⟩ := hc.product_compatibility z
      obtain ⟨a, b, _, hA₁, hA₂, _, _⟩ := hA.generation_pi
      obtain ⟨a', b', _, hB₁, hB₂, _, _⟩ := hB.generation_pi
      have h₁ := ih₁ hA₁ hB₁ eA.pi.1 eB.pi.1 c₁
      have hB₂' := hB₂.context_head_conversion hB₁ hA₁ (.symm _ _ c₁)
      have h₂ := ih₂ hA₂ hB₂' eA.pi.2 eB.pi.2 c₂
      have ctx : ∀ q, HasTypeBE P (A₁ :: Γ) B₂ (.sort q) ↔ HasTypeBE P (B₁ :: Γ) B₂ (.sort q) :=
        fun q => ⟨fun h => h.context_head_conversion hA₁ hB₁ c₁,
          fun h => h.context_head_conversion hB₁ hA₁ (.symm _ _ c₁)⟩
      constructor
      · intro h
        obtain ⟨x, y, w, hx, hy, hr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((h₁ x).1 hx) ((ctx y).1 ((h₂ y).1 hy)) hr
      · intro h
        obtain ⟨x, y, w, hx, hy, hr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((h₁ x).2 hx) ((h₂ y).2 ((ctx y).2 hy)) hr
    · cases n1
  | var n =>
    intro Γ B s t hA hB eA eB hc r
    rcases convertsBE_sorted_shape z hA hB eA eB hc with ⟨u', e1, _⟩ |
      ⟨_, _, _, _, e1, _⟩ | ⟨n1, n2⟩
    · cases e1
    · cases e1
    · exact neutral_case n1 n2 hA hB hc r
  | app f a _ _ =>
    intro Γ B s t hA hB eA eB hc r
    rcases convertsBE_sorted_shape z hA hB eA eB hc with ⟨u', e1, _⟩ |
      ⟨_, _, _, _, e1, _⟩ | ⟨n1, n2⟩
    · cases e1
    · cases e1
    · exact neutral_case n1 n2 hA hB hc r

/-! ## Reduct profiles -/

/-- The reduct profile of `T` is the set of sorts that some β-reduct of `T` has as its type, for typing with βη-conversion. -/
def ProfileR (P : Specification S) (Γ : List (Expr S)) (T : Expr S) : Set S :=
  {s | ∃ T', Reduces T T' ∧ HasTypeBE P Γ T' (.sort s)}

namespace ProfileR

variable {P : Specification S} {Γ Δ : List (Expr S)}

theorem of_type {T : Expr S} {s : S} (h : HasTypeBE P Γ T (.sort s)) : s ∈ ProfileR P Γ T :=
  ⟨T, .refl, h⟩

theorem nonempty {T : Expr S} {s : S} (h : HasTypeBE P Γ T (.sort s)) :
    (ProfileR P Γ T).Nonempty := ⟨s, of_type h⟩

/-- The reduct profile of a type is the set of sorts of any of its erasure-normal reducts. -/
theorem eq_of_enormal (hE : SystemENormalizing z P) {T T₁ : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hr : Reduces T T₁) (hn : ENormal z T₁) :
    ProfileR P Γ T = {r | HasTypeBE P Γ T₁ (.sort r)} := by
  ext r
  constructor
  · rintro ⟨T', hT', hr'⟩
    obtain ⟨T₂, h₂, e₂⟩ := hE Γ hr'.valid T' ⟨_, .inl hr'⟩
    have hT₁ := hT.subject_reduces hr
    have c : ConvertsBE T₂ T₁ :=
      .trans _ _ _ (.symm _ _ (reduces_convertsBE (hT'.trans h₂))) (reduces_convertsBE hr)
    exact (sorts_iff_of_convertsBE z T₂ (hr'.subject_reduces h₂) hT₁ e₂ hn c r).1
      (hr'.subject_reduces h₂)
  · intro h; exact ⟨T₁, hr, h⟩

theorem reduces {T T' : Expr S} (hE : SystemENormalizing z P) {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hr : Reduces T T') :
    ProfileR P Γ T' = ProfileR P Γ T := by
  obtain ⟨T₁, h₁, e₁⟩ := hE Γ hT.valid T' ⟨_, .inl (hT.subject_reduces hr)⟩
  rw [eq_of_enormal hE (hT.subject_reduces hr) h₁ e₁, eq_of_enormal hE hT (hr.trans h₁) e₁]

/-- Two legal types that are βη-convertible have the same reduct profile. -/
theorem converts (hE : SystemENormalizing z P) {A B : Expr S} {s t : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Γ B (.sort t)) (hc : ConvertsBE A B) :
    ProfileR P Γ A = ProfileR P Γ B := by
  obtain ⟨A₁, rA, eA⟩ := hE Γ hA.valid A ⟨_, .inl hA⟩
  obtain ⟨B₁, rB, eB⟩ := hE Γ hB.valid B ⟨_, .inl hB⟩
  rw [eq_of_enormal hE hA rA eA, eq_of_enormal hE hB rB eB]
  ext r
  exact sorts_iff_of_convertsBE z A₁ (hA.subject_reduces rA) (hB.subject_reduces rB) eA eB
    (.trans _ _ _ (.symm _ _ (reduces_convertsBE rA)) (.trans _ _ _ hc (reduces_convertsBE rB))) r

theorem sort (hΓ : ValidContextBE P Γ) (s : S) : ProfileR P Γ (.sort s) = AxProfile P s := by
  ext t
  constructor
  · rintro ⟨T', hr, ht⟩
    rw [Reduces.sort_inv hr] at ht
    obtain ⟨u, hu, hc⟩ := ht.generation
    have := hc.sort_inj; subst this; exact hu
  · intro h; exact ⟨_, .refl, HasTypeBE.sort_of_valid hΓ h⟩

/-- Substitution can only enlarge a reduct profile. -/
theorem growth {T : Expr S} (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitutionBE P Γ Δ σ) : ProfileR P Γ T ⊆ ProfileR P Δ (T.subst σ) := by
  rintro s ⟨T', hr, ht⟩
  exact ⟨T'.subst σ, hr.subst σ, ht.subst hΔ σ hσ⟩

theorem context_head_conversion {A A' M : Expr S} {s t : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hA' : HasTypeBE P Γ A' (.sort t))
    (hc : ConvertsBE A A') : ProfileR P (A :: Γ) M = ProfileR P (A' :: Γ) M := by
  ext r
  exact ⟨fun ⟨T', hr, h⟩ => ⟨T', hr, h.context_head_conversion hA hA' hc⟩,
    fun ⟨T', hr, h⟩ => ⟨T', hr, h.context_head_conversion hA' hA (.symm _ _ hc)⟩⟩

/-- The reduct profile of a product is the output of the reduct profiles of its domain and codomain. -/
theorem pi {D E : Expr S} {s : S}
    (h : HasTypeBE P Γ (.pi D E) (.sort s)) :
    ProfileR P Γ (.pi D E) = OutProfile P (ProfileR P Γ D) (ProfileR P (D :: Γ) E) := by
  obtain ⟨a₀, b₀, c₀, hD, hE', _, _⟩ := h.generation_pi
  ext c
  constructor
  · rintro ⟨X, hr, hX⟩
    obtain ⟨D', E', rfl, hDD, hEE⟩ := Reduces.pi_inv hr
    obtain ⟨a, b, w, hD', hE'', hrule, hcw⟩ := hX.generation_pi
    have := hcw.sort_inj; subst this
    refine ⟨a, ⟨D', hDD, hD'⟩, b, ⟨E', hEE, ?_⟩, hrule⟩
    exact hE''.context_head_conversion hD' hD (.symm _ _ (reduces_convertsBE hDD))
  · rintro ⟨a, ⟨D', hDD, hD'⟩, b, ⟨E', hEE, hE''⟩, hrule⟩
    refine ⟨.pi D' E', Reduces.pi hDD hEE, .product hD' ?_ hrule⟩
    exact hE''.context_head_conversion hD hD' (reduces_convertsBE hDD)

end ProfileR

/-! ## Normal witnesses typed with β-conversion, and feasibility of reduct profiles -/

theorem sorts_weaken_iff_beta {P : Specification S} {Γ : List (Expr S)} {T C : Expr S} {t : S}
    (hC : HasType P Γ C (.sort t)) (r : S) :
    HasType P (C :: Γ) (T.rename Nat.succ) (.sort r) ↔ HasType P Γ T (.sort r) := by
  constructor
  · intro h
    obtain ⟨T₀, hT₀, hred⟩ := h.strengthen_succ
    have hs : T₀.rename Nat.succ = .sort r := Reduces.sort_inv hred
    cases T₀ <;> simp [Expr.rename] at hs
    subst hs; exact hT₀
  · intro h; exact .weaken h hC

theorem sorts_weaken_list_iff_beta {P : Specification S} : ∀ (Δ : List (Expr S))
    {Γ : List (Expr S)} {T : Expr S}, ValidContext P (Δ ++ Γ) → ∀ r,
    HasType P (Δ ++ Γ) (T.rename (· + Δ.length)) (.sort r) ↔ HasType P Γ T (.sort r)
  | [], Γ, T, _, r => by
      have e : T.rename (· + ([] : List (Expr S)).length) = T := by
        rw [show (· + ([] : List (Expr S)).length) = (id : Nat → Nat) from funext fun _ => rfl,
          Expr.rename_id]
      rw [e]; rfl
  | C :: Δ, Γ, T, hv, r => by
      have hv0 : ValidContext P (C :: (Δ ++ Γ)) := hv
      cases hv0 with
      | cons hv' hC =>
        have e : T.rename (· + (C :: Δ).length) = (T.rename (· + Δ.length)).rename Nat.succ := by
          rw [Expr.rename_comp]; congr 1
        rw [List.cons_append, e, sorts_weaken_iff_beta hC]
        exact sorts_weaken_list_iff_beta Δ hv' r

variable (z) in
/-- Every erasure-normal type that has a sort as its type has a normal witness typed with β-conversion.
The witness has the same sorts as its types, and it lives in an extension of any given valid context. -/
theorem skeleton {P : Specification S} (hE : SystemENormalizing z P) :
    ∀ (T : Expr S) {Γ : List (Expr S)} {s : S},
    HasTypeBE P Γ T (.sort s) → ENormal z T → ∀ {Γ₀ : List (Expr S)}, ValidContext P Γ₀ →
    ∃ Δ T₀, ValidContext P (Δ ++ Γ₀) ∧ Normal T₀ ∧
      ∀ r, HasType P (Δ ++ Γ₀) T₀ (.sort r) ↔ HasTypeBE P Γ T (.sort r) := by
  intro T
  have neutral_case : ∀ {Γ Γ₀ : List (Expr S)} {T : Expr S} {s : S}, Neutral T →
      HasTypeBE P Γ T (.sort s) → ValidContext P Γ₀ →
      ∃ Δ T₀, ValidContext P (Δ ++ Γ₀) ∧ Normal T₀ ∧
        ∀ r, HasType P (Δ ++ Γ₀) T₀ (.sort r) ↔ HasTypeBE P Γ T (.sort r) := by
    intro Γ Γ₀ T s hn hT hΓ₀
    obtain ⟨t, ht⟩ := hT.neutral_axiom hE hn
    have hs : HasType P Γ₀ (.sort s) (.sort t) := HasType.sort_of_valid hΓ₀ ht
    have hv : HasType P (.sort s :: Γ₀) (.var 0) (.sort s) := .var hs
    refine ⟨[.sort s], .var 0, .cons hΓ₀ hs, Normal.var 0, fun r => ?_⟩
    simp only [List.singleton_append]
    constructor
    · intro h
      have := (HasType.neutral_unique (.var 0) h hv).sort_inj; subst this; exact hT
    · intro h
      have := (HasTypeBE.neutral_unique hn h hT).sort_inj; subst this; exact hv
  induction T with
  | sort u =>
    intro Γ s hT _ Γ₀ hΓ₀
    refine ⟨[], .sort u, hΓ₀, Normal.sort u, fun r => ?_⟩
    constructor
    · intro h
      obtain ⟨v, hv, hc⟩ := h.generation
      have := hc.sort_inj; subst this
      exact HasTypeBE.sort_of_valid hT.valid hv
    · intro h
      obtain ⟨v, hv, hc⟩ := h.generation
      have := hc.sort_inj; subst this
      exact HasType.sort_of_valid hΓ₀ hv
  | lam _ _ _ _ => intro _ _ hT; exact hT.lambda_cannot_have_sort_type.elim
  | pi A B ihA ihB =>
    intro Γ s hT eT Γ₀ hΓ₀
    obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
    obtain ⟨ΔA, A₀, hvA, nA, sA⟩ := ihA hA eT.pi.1 hΓ₀
    obtain ⟨ΔB, B₀, hvB, nB, sB⟩ := ihB hB eT.pi.2 hvA
    let Γ₂ := ΔB ++ (ΔA ++ Γ₀)
    let A₀' := A₀.rename (· + ΔB.length)
    have sA' : ∀ r, HasType P Γ₂ A₀' (.sort r) ↔ HasTypeBE P Γ A (.sort r) := fun r =>
      (sorts_weaken_list_iff_beta ΔB hvB r).trans (sA r)
    have hA₀' : HasType P Γ₂ A₀' (.sort a) := (sA' a).2 hA
    have sB' : ∀ r, HasType P (A₀' :: Γ₂) (B₀.rename Nat.succ) (.sort r) ↔
        HasTypeBE P (A :: Γ) B (.sort r) := fun r =>
      (sorts_weaken_iff_beta hA₀' r).trans (sB r)
    refine ⟨ΔB ++ ΔA, .pi A₀' (B₀.rename Nat.succ), ?_, nA.rename _ |>.pi (nB.rename _), ?_⟩
    · rw [List.append_assoc]; exact hvB
    · intro r
      rw [List.append_assoc]
      constructor
      · intro h
        obtain ⟨x, y, w, hx, hy, hr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((sA' x).1 hx) ((sB' y).1 hy) hr
      · intro h
        obtain ⟨x, y, w, hx, hy, hr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((sA' x).2 hx) ((sB' y).2 hy) hr
  | var n =>
    intro Γ s hT _ Γ₀ hΓ₀
    exact neutral_case (.var n) hT hΓ₀
  | app f a _ _ =>
    intro Γ s hT eT Γ₀ hΓ₀
    obtain ⟨D, E, hf, _, _⟩ := hT.generation_app
    obtain ⟨ef, _, fnl⟩ := eT.app
    exact neutral_case (.app (neutral_of_enormalBE z f hf ef fnl)) hT hΓ₀

/-- **Every reduct profile is feasible** in OpenAI's profile graph. -/
theorem ProfileR.feasible {P : Specification S} (hE : SystemENormalizing z P)
    {Γ : List (Expr S)} {T : Expr S} {s : S} (hT : HasTypeBE P Γ T (.sort s)) :
    FeasibleProfile P (ProfileR P Γ T) := by
  obtain ⟨T₁, r₁, e₁⟩ := hE Γ hT.valid T ⟨_, .inl hT⟩
  obtain ⟨Δ, T₀, hv, n₀, h₀⟩ := skeleton z hE T₁ (hT.subject_reduces r₁) e₁ (Γ₀ := []) .nil
  refine ⟨ProfileR.nonempty hT, Δ ++ [], T₀, hv, n₀, ?_⟩
  rw [Profile.of_normal n₀, ProfileR.eq_of_enormal hE hT r₁ e₁]
  ext r
  exact h₀ r

/-- The reduct profiles of the domain, the codomain and the whole of a product form a profile triple in OpenAI's sense. -/
theorem ProfileR.triple {P : Specification S} (hE : SystemENormalizing z P)
    {Γ : List (Expr S)} {D E : Expr S} {s : S} (h : HasTypeBE P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (ProfileR P Γ D) (ProfileR P (D :: Γ) E) (ProfileR P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE', _, _⟩ := h.generation_pi
  exact ⟨ProfileR.feasible hE hD, ProfileR.feasible hE hE', ProfileR.feasible hE h,
    ProfileR.pi h⟩

end PureTypeSystem
