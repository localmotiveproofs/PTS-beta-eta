/- Adapted to typing with βη-conversion from OpenAI's `Potential.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Candidates

@[expose] public section

/-!
# Profile paths and potentials

This file adapts OpenAI's `Potential.lean` (`PTSBetaEta.Beta.Potential`) to typing with βη-conversion.
Profiles in plain contexts are the reduct profiles `ProfileR`, and a normal type is now an erasure-normal legal type.
OpenAI's argument about neutral leaves works for any reduct of a substituted neutral leaf.
The lemmas that only concern the graph are reused from OpenAI's library.
These are `ObservationLayers`, `ActiveLayer`, interpolation for `IsComponent`, and `ContextEquivalentBE`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PureTypeSystem

universe u

variable {S : Type u} [Nonempty S]

open Relation

theorem Neutral.sort_unique {P : Specification S} {Γ : List (Expr S)} {M : Expr S} {r s : S}
    (hn : Neutral M) (h : HasTypeBE P Γ M (.sort r)) (h' : HasTypeBE P Γ M (.sort s)) : r = s :=
  (HasTypeBE.neutral_unique hn h h').sort_inj

namespace ProfileR

variable {P : Specification S} {Γ Δ : List (Expr S)}

theorem nonempty_of_sorted (hw : SystemENormalizing' P) {M : Expr S} {s : S}
    (h : HasTypeBE P Γ M (.sort s)) : (ProfileR P Γ M).Nonempty := nonempty h

theorem feasible' (hw : SystemENormalizing' P) {T : Expr S} {s : S}
    (h : HasTypeBE P Γ T (.sort s)) : FeasibleProfile P (ProfileR P Γ T) :=
  ProfileR.feasible hw h

theorem triple' (hw : SystemENormalizing' P) {D E : Expr S} {s : S}
    (h : HasTypeBE P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (ProfileR P Γ D) (ProfileR P (D :: Γ) E) (ProfileR P Γ (.pi D E)) :=
  ProfileR.triple hw h

theorem growth_path (hw : SystemENormalizing' P) {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitutionBE P Γ Δ σ) :
    PositivePath (PrimaryEdge P) (ProfileR P Δ (T.subst σ)) (ProfileR P Γ T) :=
  Profile.inclusion_path (feasible' hw (hT.subst hΔ σ hσ)) (feasible' hw hT)
    (growth hΔ σ hσ)

theorem instantiate_product_path (hw : SystemENormalizing' P)
    {D E n : Expr S} {s : S} (h : HasTypeBE P Γ (.pi D E) (.sort s))
    (hn : HasTypeBE P Γ n D) :
    PositivePath (PrimaryEdge P) (ProfileR P Γ (E.instantiate n))
      (ProfileR P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have hp := growth_path hw hE hn.valid _ (TypedSubstitutionBE.single hn)
  exact hp.trans (.single (.codomain (triple' hw h)))

/-- The reduct profile of an erasure-normal neutral type has exactly one element. -/
theorem neutral_enormal (hw : SystemENormalizing' P) {M : Expr S} {s : S}
    (hn : ENormal dz M) (hne : Neutral M) (ht : HasTypeBE P Γ M (.sort s)) :
    ProfileR P Γ M = {s} := by
  rw [eq_of_enormal hw ht .refl hn]
  ext t
  constructor
  · intro h; exact (ht.neutral_unique hne h).sort_inj.symm
  · intro h; have he : t = s := h; subst t; exact ht

theorem context_equiv {M : Expr S} (h : ContextEquivalentBE P Γ Δ) :
    ProfileR P Γ M = ProfileR P Δ M := by
  ext s
  exact ⟨fun ⟨T', hr, ht⟩ => ⟨T', hr, (h.typing _ _).1 ht⟩,
    fun ⟨T', hr, ht⟩ => ⟨T', hr, (h.typing _ _).2 ht⟩⟩

end ProfileR

namespace HasTypeBE

variable {P : Specification S} {Γ : List (Expr S)}

theorem neutral_profileR_ascent (hw : SystemENormalizing' P)
    {M T : Expr S} (hn : Neutral M) (h : HasTypeBE P Γ M T) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (ProfileR P Γ T) (ProfileR P Γ D) := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      refine ⟨n, D, rfl, hD, ?_⟩
      obtain ⟨t, hT⟩ := h.neutral_type_sorted hw (.var n)
      obtain ⟨u, hDs⟩ := HasTypeBE.lookup_sorted h.valid hD
      rw [ProfileR.converts hw hT hDs hc]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, hp⟩ := hf.product_type_sorted
      obtain ⟨n, A, hh, hl, hr⟩ := ih hf
      refine ⟨n, A, hh, hl, ?_⟩
      obtain ⟨t, hT⟩ := h.neutral_type_sorted hw (.app hnf)
      obtain ⟨_, _, _, _, hE, _, _⟩ := hp.generation_pi
      have hEn := hE.instantiate ha
      rw [ProfileR.converts hw hT hEn hc]
      exact (ProfileR.instantiate_product_path hw hp ha).trans hr

theorem neutral_profileR_seed (hw : SystemENormalizing' P)
    {M : Expr S} {s : S} (hn : Neutral M) (hM : ENormal dz M)
    (h : HasTypeBE P Γ M (.sort s)) :
    ProfileR P Γ M = {s} ∧ (AxProfile P s).Nonempty ∧
      ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
        PositivePath (PrimaryEdge P) (AxProfile P s) (ProfileR P Γ D) := by
  refine ⟨ProfileR.neutral_enormal hw hM hn h, h.neutral_axiom hw hn, ?_⟩
  simpa only [ProfileR.sort h.valid] using neutral_profileR_ascent hw hn h

end HasTypeBE

namespace ProfileR

variable {P : Specification S}

/-- Typed renamings preserve the sorts of erasure-normal types. -/
theorem sorts_rename_enormal {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hn : ENormal dz T)
    (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasTypeBE P Δ (.var (ρ n)) (B.rename ρ)) (r : S) :
    HasTypeBE P Δ (T.rename ρ) (.sort r) ↔ HasTypeBE P Γ T (.sort r) := by
  have hT' := hT.rename hΔ ρ hρ
  have neutral_case (hne : Neutral T) :
      HasTypeBE P Δ (T.rename ρ) (.sort r) ↔ HasTypeBE P Γ T (.sort r) := by
    constructor
    · intro h
      have := ((hne.rename ρ).sort_unique h hT').symm; subst this; exact hT
    · intro h
      have := (hne.sort_unique h hT).symm; subst this; exact hT'
  induction T generalizing Γ Δ s ρ r with
  | var n => exact neutral_case (.var n)
  | app f a ihf iha =>
      obtain ⟨t, he⟩ | h | ⟨D, E, he⟩ := hT.enormal_sorted_shape dz hn
      · cases he
      · exact neutral_case h
      · cases he
  | sort t =>
      constructor
      · intro h
        obtain ⟨v, hv, hc⟩ := h.generation
        have := hc.sort_inj; subst this
        exact HasTypeBE.sort_of_valid hT.valid hv
      · intro h
        obtain ⟨v, hv, hc⟩ := h.generation
        have := hc.sort_inj; subst this
        exact HasTypeBE.sort_of_valid hΔ hv
  | lam A b ihA ihb => exact False.elim hT.lambda_cannot_have_sort_type
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n D, Lookup (A :: Γ) n D →
          HasTypeBE P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (D.rename (Expr.liftRen ρ)) := by
        intro n D hD
        cases hD with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasTypeBE.var hA'
        | succ _ hD =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasTypeBE.weaken (hρ _ _ hD) hA'
      have enA : ENormal dz A := (show ENormal dz (.pi A B) from hn).pi.1
      have enB : ENormal dz B := (show ENormal dz (.pi A B) from hn).pi.2
      have eA := fun q => ihA hA enA hΔ ρ hρ q (hA.rename hΔ ρ hρ) (fun hne => by
        constructor
        · intro h; have := ((hne.rename ρ).sort_unique h (hA.rename hΔ ρ hρ)).symm; subst this; exact hA
        · intro h; have := (hne.sort_unique h hA).symm; subst this; exact hA.rename hΔ ρ hρ)
      have eB := fun q => ihB hB enB (.cons hΔ hA') _ hr q (hB.rename (.cons hΔ hA') _ hr) (fun hne => by
        constructor
        · intro h; have := ((hne.rename _).sort_unique h (hB.rename (.cons hΔ hA') _ hr)).symm
          subst this; exact hB
        · intro h; have := (hne.sort_unique h hB).symm; subst this; exact hB.rename (.cons hΔ hA') _ hr)
      show HasTypeBE P Δ (.pi (A.rename ρ) (B.rename (Expr.liftRen ρ))) (.sort r) ↔ _
      constructor
      · intro h
        obtain ⟨x, y, w, hx, hy, hrr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((eA x).1 hx) ((eB y).1 hy) hrr
      · intro h
        obtain ⟨x, y, w, hx, hy, hrr, hcw⟩ := h.generation_pi
        have := hcw.sort_inj; subst this
        exact .product ((eA x).2 hx) ((eB y).2 hy) hrr

/-- Typed renamings preserve the reduct profiles of erasure-normal types. -/
theorem rename_enormal (hw : SystemENormalizing' P) {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hn : ENormal dz T)
    (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasTypeBE P Δ (.var (ρ n)) (B.rename ρ)) :
    ProfileR P Δ (T.rename ρ) = ProfileR P Γ T := by
  have hn' : ENormal dz (T.rename ρ) := by
    unfold ENormal at hn ⊢; rw [Expr.erase_rename]; exact hn.rename ρ
  have hT' := hT.rename hΔ ρ hρ
  rw [eq_of_enormal hw hT' .refl hn', eq_of_enormal hw hT .refl hn]
  ext r
  exact sorts_rename_enormal hT hn hΔ ρ hρ r

theorem rename (hw : SystemENormalizing' P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasTypeBE P Δ (.var (ρ n)) (B.rename ρ)) :
    ProfileR P Δ (T.rename ρ) = ProfileR P Γ T := by
  obtain ⟨T₁, r₁, e₁⟩ := hw Γ hT.valid T ⟨_, .inl hT⟩
  have hT₁ := hT.subject_reduces r₁
  rw [← reduces hw hT r₁, ← reduces hw (hT.rename hΔ ρ hρ) (r₁.rename ρ)]
  exact rename_enormal hw hT₁ e₁ hΔ ρ hρ

theorem weaken' (hw : SystemENormalizing' P) {Γ : List (Expr S)}
    {T D : Expr S} {s t : S} (hT : HasTypeBE P Γ T (.sort s))
    (hD : HasTypeBE P Γ D (.sort t)) :
    ProfileR P (D :: Γ) (T.rename Nat.succ) = ProfileR P Γ T :=
  rename hw hT (.cons hD.valid hD) Nat.succ
    (fun _ _ hB => .weaken (HasTypeBE.lookup hD.valid hB) hD)

end ProfileR

/-- Every image that can replace a neutral head comes from the chosen profile of the outer binder. -/
def SingleSourceR {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (σ : Nat → Expr S) (I : Set S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → ProfileR P Γ D = I

namespace SingleSourceR
variable {P : Specification S} {Γ : List (Expr S)} {σ : Nat → Expr S} {I : Set S}

theorem single (hw : SystemENormalizing' P) {D q : Expr S} {s : S}
    (hD : HasTypeBE P Γ D (.sort s)) :
    SingleSourceR P (D :: Γ) (Expr.single q) (ProfileR P Γ D) := by
  intro n A hn hbad
  cases hn with
  | zero => exact ProfileR.weaken' hw hD hD
  | succ _ _ => exact False.elim (hbad (.var _))

theorem lift (hw : SystemENormalizing' P) (h : SingleSourceR P Γ σ I)
    {D : Expr S} {s : S} (hD : HasTypeBE P Γ D (.sort s)) :
    SingleSourceR P (D :: Γ) (Expr.liftSub σ) I := by
  intro n A hn hbad
  cases hn with
  | zero => exact False.elim (hbad (.var 0))
  | succ _ hn =>
      obtain ⟨u, hu⟩ := HasTypeBE.lookup_sorted hD.valid hn
      rw [ProfileR.weaken' hw hu hD]
      exact h _ _ hn (fun hh => hbad (hh.rename Nat.succ))
end SingleSourceR

namespace ForbiddenConfiguration
variable {P : Specification S} {C D : Set (Set S)}

/-- OpenAI's argument about neutral leaves.
No erasure-normal neutral leaf of the component can reduce to a product when the outer binder is substituted. -/
theorem of_neutral_expansionR (hw : SystemENormalizing' P)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitutionBE P Γ Δ σ) (hsrc : SingleSourceR P Γ σ I)
    {M A B : Expr S} {s : S} (h : HasTypeBE P Γ M (.sort s))
    (hn : ENormal dz M) (hne : Neutral M) (hM : ProfileR P Γ M ∈ D)
    (he : Reduces (M.subst σ) (.pi A B)) : ForbiddenConfiguration P C := by
  obtain ⟨hp, hax, n, F, hh, hf, hpath⟩ := h.neutral_profileR_seed hw hne hn
  have hbad : ¬ Neutral (σ n) := by
    intro hs
    have hM' := hne.subst_of_head σ (by
      intro m hm
      have heq : m = n := by simpa only [hh, Expr.var.injEq] using hm.symm
      exact heq.symm ▸ hs)
    have hnorm := hM'.reduces he
    cases hnorm
  have hF := hsrc n F hf hbad
  rw [hF] at hpath
  exact ⟨D, hD, hplain, hneg, I, J, K, s, htr, hJ, hK, hp ▸ hM, hax, hpath⟩
end ForbiddenConfiguration

namespace PlainObservationsR
open Classical
/-- OpenAI's potential on syntax trees, computed with reduct profiles. -/
noncomputable def potential (P : Specification S) (C D : Set (Set S))
    (Γ : List (Expr S)) : Expr S → Nat
  | .pi A B => by
      classical
      exact 1 +
      (if ProfileR P Γ A ∈ D ∧ ActiveLayer P C (ProfileR P (A :: Γ) B)
       then potential P C D Γ A else 0) +
      (if ProfileR P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B else 0)
  | _ => 1

variable {P : Specification S} {C D : Set (Set S)}

theorem potential_context {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (h : ContextEquivalentBE P Γ Δ) :
    potential P C D Γ T = potential P C D Δ T := by
  induction T generalizing Γ Δ s with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      simp only [potential]
      rw [ProfileR.context_equiv (M := A) h, ProfileR.context_equiv (M := B) (h.cons hA),
        ihA hA h, ihB hB (h.cons hA)]

/-- Two erasure-normal legal types that are βη-convertible have the same potential. -/
theorem potential_converts (hw : SystemENormalizing' P) {Γ : List (Expr S)} :
    ∀ (T : Expr S) {T' : Expr S} {s t : S}, HasTypeBE P Γ T (.sort s) →
      HasTypeBE P Γ T' (.sort t) → ENormal dz T → ENormal dz T' → ConvertsBE T T' →
      potential P C D Γ T = potential P C D Γ T' := by
  intro T
  induction T generalizing Γ with
  | pi A B ihA ihB =>
      intro T' s t hT hT' eT eT' hc
      rcases convertsBE_sorted_shape dz hT hT' eT eT' hc with ⟨u, e1, _⟩ |
        ⟨A₀, B₀, A', B', e1, rfl⟩ | ⟨n1, _⟩
      · cases e1
      · obtain ⟨cA, cB⟩ := hc.product_compatibility dz
        obtain ⟨a, b, _, hA, hB, _, _⟩ := hT.generation_pi
        obtain ⟨a', b', _, hA', hB', _, _⟩ := hT'.generation_pi
        have ctx := ContextEquivalentBE.head_conversion hA hA' cA
        have hB'' := (ctx.typing _ _).2 hB'
        simp only [potential]
        rw [ProfileR.converts hw hA hA' cA, ihA hA hA' eT.pi.1 eT'.pi.1 cA,
          ProfileR.converts hw hB hB'' cB, ProfileR.context_equiv (M := B') ctx,
          ihB hB hB'' eT.pi.2 eT'.pi.2 cB, potential_context hB' ctx.symm]
      · cases n1
  | var n | sort u | app f a | lam A b =>
      intro T' s t hT hT' eT eT' hc
      rcases convertsBE_sorted_shape dz hT hT' eT eT' hc with ⟨u, _, rfl⟩ |
        ⟨_, _, _, _, e1, _⟩ | ⟨_, n2⟩
      · rfl
      · cases e1
      · cases T' with
        | pi A' B' => cases n2
        | _ => rfl

theorem potential_pos (Γ : List (Expr S)) (T : Expr S) : 0 < potential P C D Γ T := by
  cases T <;> simp only [potential] <;> omega

/-- The potential inequality for any erasure-normal reduct of a substituted erasure-normal type. -/
theorem potential_subst_le (hw : SystemENormalizing' P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitutionBE P Γ Δ σ) (hsrc : SingleSourceR P Γ σ I)
    {T : Expr S} {s : S} (hT : HasTypeBE P Γ T (.sort s)) (hn : ENormal dz T)
    (hTC : ProfileR P Γ T ∈ D) {X : Expr S} (hX : Reduces (T.subst σ) X)
    (hXn : ENormal dz X) :
    potential P C D Δ X ≤ potential P C D Γ T := by
  classical
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  have leaf {Γ Δ : List (Expr S)} {σ : Nat → Expr S} {M : Expr S} {s : S}
      (hΔ : ValidContextBE P Δ) (hσ : TypedSubstitutionBE P Γ Δ σ)
      (hsrc : SingleSourceR P Γ σ I) (hM : HasTypeBE P Γ M (.sort s))
      (hn : ENormal dz M) (hne : Neutral M) (hMC : ProfileR P Γ M ∈ D)
      {X : Expr S} (hX : Reduces (M.subst σ) X) :
      potential P C D Δ X = 1 := by
    cases X with
    | pi A B =>
        exact False.elim (hno (ForbiddenConfiguration.of_neutral_expansionR hw hD hplain hneg
          htr hJ hK hΔ hσ hsrc hM hn hne hMC hX))
    | var n | sort t | app f a | lam A b => rfl
  induction T generalizing Γ Δ σ s X with
  | var n => exact le_of_eq (leaf hΔ hσ hsrc hT hn (.var n) hTC hX)
  | sort t =>
      rw [show X = .sort t from (Reduces.sort_inv hX)]
      simp only [potential, le_refl]
  | lam A b => exact False.elim hT.lambda_cannot_have_sort_type
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨A, B, he⟩ := hT.enormal_sorted_shape dz hn
        · cases he
        · exact h
        · cases he
      exact le_of_eq (leaf hΔ hσ hsrc hT hn hneutral hTC hX)
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.subst hΔ σ hσ
      have hΔ' : ValidContextBE P (A.subst σ :: Δ) := .cons hΔ hA'
      have hσ' := hσ.lift hA'
      have hB' := hB.subst hΔ' _ hσ'
      have htr' := ProfileR.triple' hw hT
      have hAp := ProfileR.growth_path hw hA hΔ σ hσ
      have hBp := ProfileR.growth_path hw hB hΔ' _ hσ'
      obtain ⟨A₁, B₁, rfl, rA, rB⟩ := Reduces.pi_inv hX
      have eA₁ : ENormal dz A₁ := (show ENormal dz (.pi A₁ B₁) from hXn).pi.1
      have eB₁ : ENormal dz B₁ := (show ENormal dz (.pi A₁ B₁) from hXn).pi.2
      have hA₁ := hA'.subject_reduces rA
      have ctx := ContextEquivalentBE.head_conversion hA' hA₁ (reduces_convertsBE rA)
      have hB₁ := (ctx.typing _ _).1 (hB'.subject_reduces rB)
      have pA : ProfileR P Δ A₁ = ProfileR P Δ (A.subst σ) := ProfileR.reduces hw hA' rA
      have pB : ProfileR P (A₁ :: Δ) B₁ = ProfileR P (A.subst σ :: Δ) (B.subst (Expr.liftSub σ)) := by
        rw [← ProfileR.context_equiv (M := B₁) ctx]
        exact ProfileR.reduces hw hB' rB
      have potB : potential P C D (A₁ :: Δ) B₁ = potential P C D (A.subst σ :: Δ) B₁ :=
        potential_context hB₁ ctx.symm
      have enA : ENormal dz A := (show ENormal dz (.pi A B) from hn).pi.1
      have enB : ENormal dz B := (show ENormal dz (.pi A B) from hn).pi.2
      simp only [potential]
      rw [pA, pB, potB]
      apply Nat.add_le_add
      · apply Nat.add_le_add_left
        split_ifs with hc hc'
        · exact ihA hΔ hσ hsrc hA enA hc'.1 rA eA₁
        · obtain ⟨hAC, hBa⟩ := hD.domain_interpolation hl ha htr' hTC hc.1 hc.2 hAp hBp
          exact False.elim (hc' ⟨hAC, hBa⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · split_ifs with hc hc'
        · exact ihB hΔ' hσ' (hsrc.lift hw hA) hB enB hc' rB eB₁
        · exact False.elim (hc' (hD.codomain_interpolation hl htr' hTC hc hBp))
        · exact Nat.zero_le _
        · exact le_rfl

/-- The potential drops along a legal frame, in a plain component with an internal negative edge. -/
theorem frame_potential_drop (hw : SystemENormalizing' P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {Γ : List (Expr S)} {A B n : Expr S} {s : S}
    (hT : HasTypeBE P Γ (.pi A B) (.sort s)) (hnT : ENormal dz (.pi A B))
    (hn : HasTypeBE P Γ n A) (hK : ProfileR P Γ (.pi A B) ∈ D)
    (hL : ProfileR P Γ (B.instantiate n) ∈ D) {X : Expr S}
    (hX : Reduces (B.instantiate n) X) (hXn : ENormal dz X) :
    potential P C D Γ X ≤ potential P C D (A :: Γ) B ∧
      potential P C D (A :: Γ) B < potential P C D Γ (.pi A B) := by
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have htr := ProfileR.triple' hw hT
  have hp := ProfileR.growth_path hw hB hn.valid _ (TypedSubstitutionBE.single hn)
  have hJ := hD.codomain_interpolation hl htr hK hL hp
  refine ⟨potential_subst_le hw hno hD hplain hneg htr hJ hK hn.valid
    (TypedSubstitutionBE.single hn) (SingleSourceR.single hw hA) hB hnT.pi.2 hJ hX hXn, ?_⟩
  simp only [potential, ite_eq_left hJ]
  omega

theorem frame_domain_drop (hplain : ∀ I ∈ D, PlainLayer P C I)
    {Γ : List (Expr S)} {A B : Expr S}
    (hI : ProfileR P Γ A ∈ D) (hJ : ProfileR P (A :: Γ) B ∈ D) :
    potential P C D Γ A < potential P C D Γ (.pi A B) := by
  have hc : ProfileR P Γ A ∈ D ∧ ActiveLayer P C (ProfileR P (A :: Γ) B) :=
    ⟨hI, (hplain _ hJ).active⟩
  simp only [potential, ite_eq_left hc, ite_eq_left hJ]
  omega

/-- The potential counts positions, so a valid thinning does not change it. -/
theorem potential_rename (hw : SystemENormalizing' P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasTypeBE P Γ T (.sort s)) (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasTypeBE P Δ (.var (ρ n)) (B.rename ρ)) :
    potential P C D Δ (T.rename ρ) = potential P C D Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n E, Lookup (A :: Γ) n E →
          HasTypeBE P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (E.rename (Expr.liftRen ρ)) := by
        intro n E hE
        cases hE with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasTypeBE.var hA'
        | succ _ hE =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasTypeBE.weaken (hρ _ _ hE) hA'
      simp only [Expr.rename, potential]
      rw [ProfileR.rename hw hA hΔ ρ hρ,
        ProfileR.rename hw hB (.cons hΔ hA') _ hr,
        ihA hA hΔ ρ hρ, ihB hB (.cons hΔ hA') _ hr]

end PlainObservationsR

/-! ## The tower level: key profiles and key potentials -/

namespace ContextTowerBE

section
open Classical
variable {P : Specification S} (Ω : ContextTowerBE P)

theorem profileR_at_next (hw : SystemENormalizing' P) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasTypeBE P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    ProfileR P (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      ProfileR P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨D, t, hD, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact ProfileR.weaken' hw ht hD

theorem profileR_at_mono (hw : SystemENormalizing' P) {n m : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasTypeBE P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    ProfileR P (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      ProfileR P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih => exact (Ω.profileR_at_next hw (Ω.at_mono (A := .sort s) ht h)).trans ih

variable [hE : Fact (SystemENormalizing' P)]

/-- A typing up to keys at a sort is realized by a typing in the tower. -/
theorem KHasTypeBE.sorted_witness {T : Expr S} {s : S} (h : Ω.KHasTypeBE T (.sort s)) :
    ∃ T₀, Ω.HasTypeBE T₀ (.sort s) ∧ T₀.knf = T.knf := by
  obtain ⟨T₀, S₀, h₀, hT, hS⟩ := h
  rw [Expr.knf_sort] at hS
  refine ⟨T₀, ?_, hT⟩
  rcases h₀.regularity with ⟨u, rfl⟩ | ⟨u, hU⟩
  · rw [Expr.knf_sort] at hS; cases hS; exact h₀
  · have c := converts_sort_of_knf (hU.kwn_both hE.out).1 hS
    have hs : Ω.HasTypeBE (.sort s) (.sort u) := hU.subject_reduces (hU.reduces_sort hE.out c)
    exact h₀.conversion hs c

theorem kprofile_at (hw : SystemENormalizing' P) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasTypeBE P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.kprofile T = ProfileR P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hT : Ω.HasTypeBE T (.sort s) := ⟨n, ht⟩
  ext r
  constructor
  · intro h
    obtain ⟨T₀, h₀, hk⟩ := KHasTypeBE.sorted_witness Ω h
    have c := converts_of_knf_eq hE.out h₀ hT hk
    obtain ⟨m, h₀m, hTm⟩ := h₀.common hT
    obtain ⟨k, hk1, hk2⟩ : ∃ k, m ≤ k ∧ n ≤ k := ⟨max m n, le_max_left _ _, le_max_right _ _⟩
    have h₀k := Ω.at_mono (A := .sort r) h₀m hk1
    have hTk := Ω.at_mono (A := .sort s) ht hk2
    have e := ProfileR.converts hE.out hTk h₀k (.symm _ _ (c.rename _))
    rw [← Ω.profileR_at_mono hw ht hk2, e]
    exact ProfileR.of_type h₀k
  · rintro ⟨X, hr, hX⟩
    obtain ⟨X₀, rfl, hX₀⟩ := Reduces.rename_inv (reverseIndex_injective n) hr
    have hX₀t : Ω.HasTypeBE X₀ (.sort r) := ⟨n, hX⟩
    have wT := (hT.kwn_both hE.out).1
    have wX := (hX₀t.kwn_both hE.out).1
    exact ⟨X₀, _, hX₀t, Expr.knf_converts wX wT (.symm _ _ hX₀.k.converts), rfl⟩

theorem kprofile_knf (T : Expr S) : Ω.kprofile T.knf = Ω.kprofile T := by
  ext r
  exact ⟨fun h => h.of_knf_eq (Expr.knf_idem T) rfl,
    fun h => h.of_knf_eq (Expr.knf_idem T).symm rfl⟩

theorem kprofile_of_knf_eq {T T' : Expr S} (h : T.knf = T'.knf) : Ω.kprofile T = Ω.kprofile T' := by
  ext r
  exact ⟨fun k => k.of_knf_eq h rfl, fun k => k.of_knf_eq h.symm rfl⟩

theorem kprofile_nonempty (hw : SystemENormalizing' P) {T : Expr S} {s : S}
    (ht : Ω.KHasTypeBE T (.sort s)) : (Ω.kprofile T).Nonempty := ⟨s, ht⟩

theorem kprofile_feasible (hw : SystemENormalizing' P) {T : Expr S} {s : S}
    (ht : Ω.KHasTypeBE T (.sort s)) : FeasibleProfile P (Ω.kprofile T) := by
  obtain ⟨T₀, ⟨n, hn⟩, hk⟩ := KHasTypeBE.sorted_witness Ω ht
  rw [← Ω.kprofile_of_knf_eq hk, Ω.kprofile_at hw hn]
  exact ProfileR.feasible' hw hn

theorem kprofile_subst_growth (hw : SystemENormalizing' P) {Γ : List (Expr S)}
    {T : Expr S} {s : S} {σ : Nat → Expr S} (ht : PureTypeSystem.HasTypeBE P Γ T (.sort s))
    (hσ : Ω.KTypedSubstitutionBE Γ σ) : ProfileR P Γ T ⊆ Ω.kprofile (T.subst σ) := by
  rintro r ⟨T', hr, hT'⟩
  have h := KHasTypeBE.subst hT' hσ
  have w := h.kwn hE.out
  have w' : KWN (T.subst σ) := KWN.of_kconverts (hr.subst σ).k.converts w
  exact h.of_knf_eq (Expr.knf_converts w w' (.symm _ _ (hr.subst σ).k.converts)) rfl

/-- A typing up to keys of a product at a sort is realized by a typing in the tower of an erasure-normal product at the same sort.
The domain and codomain of that product have the same keys as those of the given product. -/
theorem KHasTypeBE.pi_type_witness {A B : Expr S} {s : S} (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) :
    ∃ A₁ B₁, Ω.HasTypeBE (.pi A₁ B₁) (.sort s) ∧ A₁.knf = A.knf ∧ B₁.knf = B.knf ∧
      ENormal dz A₁ ∧ ENormal dz B₁ := by
  obtain ⟨T₀, h₀, hk⟩ := KHasTypeBE.sorted_witness Ω hT
  have wT := (h₀.kwn_both hE.out).1
  have wP : KWN (.pi A B) := KWN.of_knf_eq hk.symm wT
  obtain ⟨T₁, hr, hn⟩ := h₀.enormal_reduct hE.out
  have hT₁ := h₀.subject_reduces hr
  have c : ConvertsBE T₁ (.pi A B) :=
    .trans _ _ _ (.symm _ _ (reduces_convertsBE hr)) ((convertsBE_iff_knf_eq wT wP).2 hk)
  obtain ⟨A₁, B₁, rfl⟩ := hT₁.pi_shape hE.out hn c
  have w₁ := (hT₁.kwn_both hE.out).1
  obtain ⟨cA, cB⟩ := c.product_compatibility dz
  have eA : ENormal dz A₁ := (show ENormal dz (.pi A₁ B₁) from hn).pi.1
  have eB : ENormal dz B₁ := (show ENormal dz (.pi A₁ B₁) from hn).pi.2
  exact ⟨A₁, B₁, hT₁, (convertsBE_iff_knf_eq w₁.pi_domain wP.pi_domain).1 cA,
    (convertsBE_iff_knf_eq w₁.pi_body wP.pi_body).1 cB, eA, eB⟩

omit hE in
theorem kdomain_sorted_of {A B : Expr S} {s : S}
    (hT : Ω.HasTypeBE (.pi A B) (.sort s)) : ∃ a, Ω.HasTypeBE A (.sort a) := Ω.domain_sorted hT

theorem kdomain_sorted {A B : Expr S} {s : S}
    (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) : ∃ a, Ω.KHasTypeBE A (.sort a) := by
  obtain ⟨A₁, B₁, h, hA, _, _, _⟩ := KHasTypeBE.pi_type_witness Ω hT
  obtain ⟨a, ha⟩ := Ω.domain_sorted h
  exact ⟨a, (KHasTypeBE.of ha).of_knf_eq hA rfl⟩

/-- The frame data for a product and an argument that are typed up to keys, realized in a single finite prefix of the tower. -/
theorem frame_data {A B q : Expr S} {s : S}
    (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) (hq : Ω.KHasTypeBE q A) :
    ∃ (n : Nat) (A₁ B₁ q₀ : Expr S) (a b c : S),
      ENormal dz A₁ ∧ ENormal dz B₁ ∧ A₁.knf = A.knf ∧ B₁.knf = B.knf ∧
      q₀.knf = q.knf ∧
      PureTypeSystem.HasTypeBE P (Ω.context n)
        (.pi (A₁.rename (Expr.reverseIndex n)) (B₁.rename (Expr.liftRen (Expr.reverseIndex n))))
        (.sort s) ∧
      PureTypeSystem.HasTypeBE P (Ω.context n) (A₁.rename (Expr.reverseIndex n)) (.sort a) ∧
      PureTypeSystem.HasTypeBE P (A₁.rename (Expr.reverseIndex n) :: Ω.context n)
        (B₁.rename (Expr.liftRen (Expr.reverseIndex n))) (.sort b) ∧
      P.rule a b c ∧
      PureTypeSystem.HasTypeBE P (Ω.context n) (q₀.rename (Expr.reverseIndex n))
        (A₁.rename (Expr.reverseIndex n)) := by
  obtain ⟨A₁, B₁, hP, hA, hB, eA, eB⟩ := KHasTypeBE.pi_type_witness Ω hT
  obtain ⟨a', hA₁⟩ := Ω.domain_sorted hP
  obtain ⟨q₀, U₀, hq₀, hqk, hUk⟩ := hq
  have hq₁ : Ω.HasTypeBE q₀ A₁ := hq₀.retype hE.out hA₁ (hUk.trans hA.symm)
  obtain ⟨n, hPn, hqn⟩ := hP.common hq₁
  obtain ⟨a, b, c, hAn, hBn, hr, _⟩ := hPn.generation_pi
  exact ⟨n, A₁, B₁, q₀, a, b, c, eA, eB, hA, hB, hqk, hPn, hAn, hBn, hr, hqn⟩

theorem kframe_target_sorted {A B q : Expr S} {s : S}
    (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) (hq : Ω.KHasTypeBE q A) :
    ∃ b, Ω.KHasTypeBE (B.instantiate q) (.sort b) := by
  obtain ⟨n, A₁, B₁, q₀, a, b, c, eA, eB, hA, hB, hqk, hPn, hAn, hBn, hr, hqn⟩ :=
    Ω.frame_data hT hq
  have hQ := hBn.instantiate hqn
  rw [Expr.instantiate_rename] at hQ
  have hQt : Ω.HasTypeBE (B₁.instantiate q₀) (.sort b) := ⟨n, hQ⟩
  have w := (hQt.kwn_both hE.out).1
  have wB₁ : KWN B₁ := (KWN.pi_body ((show Ω.HasTypeBE (.pi A₁ B₁) (.sort s) from ⟨n, hPn⟩).kwn_both
    hE.out).1)
  have wq₀ : KWN q₀ := (show Ω.HasTypeBE q₀ A₁ from ⟨n, hqn⟩).kwn_both hE.out |>.1
  have c1 : KConverts (B₁.instantiate q₀) (B.instantiate q) := by
    unfold KConverts
    rw [Expr.erase_instantiate, Expr.erase_instantiate]
    have cB : KConverts B₁ B := KConverts.of_knf_eq wB₁ (KWN.of_knf_eq hB.symm wB₁) hB
    have cq : KConverts q₀ q := KConverts.of_knf_eq wq₀ (KWN.of_knf_eq hqk.symm wq₀) hqk
    exact .trans _ _ _ (ConvertsBE.subst cB _) (cq.instantiate_right _)
  exact ⟨b, (KHasTypeBE.of hQt).of_knf_eq
    (Expr.knf_converts w (KWN.of_kconverts (.symm _ _ c1) w) c1) rfl⟩

/-- The formation data for a frame that is typed up to keys, as in OpenAI's `frame_profiles`. -/
theorem kframe_profiles (hw : SystemENormalizing' P) {A B q : Expr S} {s : S}
    (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) (hq : Ω.KHasTypeBE q A) :
    ∃ J, ProfileTriple P (Ω.kprofile A) J (Ω.kprofile (.pi A B)) ∧
      PositivePath (PrimaryEdge P) (Ω.kprofile (B.instantiate q)) J := by
  obtain ⟨n, A₁, B₁, q₀, a, b, c, eA, eB, hA, hB, hqk, hPn, hAn, hBn, hr, hqn⟩ :=
    Ω.frame_data hT hq
  have hQ := hBn.instantiate hqn
  rw [Expr.instantiate_rename] at hQ
  have htr := ProfileR.triple' hw hPn
  have hp := ProfileR.growth_path hw hBn hqn.valid _ (TypedSubstitutionBE.single hqn)
  change PositivePath (PrimaryEdge P)
    (ProfileR P (Ω.context n) ((B₁.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q₀.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename] at hp
  have wP := (show Ω.HasTypeBE (.pi A₁ B₁) (.sort s) from ⟨n, hPn⟩).kwn_both hE.out
  have kA : Ω.kprofile A = Ω.kprofile A₁ := Ω.kprofile_of_knf_eq hA.symm
  have kP : Ω.kprofile (.pi A B) = Ω.kprofile (.pi A₁ B₁) := Ω.kprofile_of_knf_eq (by
    rw [Expr.knf_pi wP.1.pi_domain wP.1.pi_body, hA, hB,
      ← Expr.knf_pi (KWN.of_knf_eq hA.symm wP.1.pi_domain) (KWN.of_knf_eq hB.symm wP.1.pi_body)])
  obtain ⟨b', hQk⟩ := Ω.kframe_target_sorted hT hq
  have hQt : Ω.HasTypeBE (B₁.instantiate q₀) (.sort b) := ⟨n, hQ⟩
  have kQ : Ω.kprofile (B.instantiate q) = Ω.kprofile (B₁.instantiate q₀) := by
    obtain ⟨_, _, hQk', hk1, _⟩ := hQk
    have w := (hQt.kwn_both hE.out).1
    have wB₁ : KWN B₁ := wP.1.pi_body
    have wq₀ : KWN q₀ := (show Ω.HasTypeBE q₀ A₁ from ⟨n, hqn⟩).kwn_both hE.out |>.1
    apply Ω.kprofile_of_knf_eq
    have c1 : KConverts (B₁.instantiate q₀) (B.instantiate q) := by
      unfold KConverts
      rw [Expr.erase_instantiate, Expr.erase_instantiate]
      have cB : KConverts B₁ B := KConverts.of_knf_eq wB₁ (KWN.of_knf_eq hB.symm wB₁) hB
      have cq : KConverts q₀ q := KConverts.of_knf_eq wq₀ (KWN.of_knf_eq hqk.symm wq₀) hqk
      exact .trans _ _ _ (ConvertsBE.subst cB _) (cq.instantiate_right _)
    exact (Expr.knf_converts w (KWN.of_kconverts (.symm _ _ c1) w) c1).symm
  refine ⟨ProfileR P (A₁.rename (Expr.reverseIndex n) :: Ω.context n)
    (B₁.rename (Expr.liftRen (Expr.reverseIndex n))), ?_, ?_⟩
  · rw [kA, kP, Ω.kprofile_at hw hAn, Ω.kprofile_at hw (T := .pi A₁ B₁) hPn]
    exact htr
  · rw [kQ, Ω.kprofile_at hw hQ]
    exact hp

/-! ### Key potentials -/

theorem potentialR_at_next (hw : SystemENormalizing' P) (C D : Set (Set S)) {n : Nat}
    {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasTypeBE P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    PlainObservationsR.potential P C D (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      PlainObservationsR.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨A, t, hA, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact PlainObservationsR.potential_rename hw ht (.cons hA.valid hA) Nat.succ
    (fun _ _ hn => .weaken (PureTypeSystem.HasTypeBE.lookup hA.valid hn) hA)

theorem potentialR_at_mono (hw : SystemENormalizing' P) (C D : Set (Set S)) {n m : Nat}
    {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasTypeBE P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    PlainObservationsR.potential P C D (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      PlainObservationsR.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (Ω.potentialR_at_next hw C D (Ω.at_mono (A := .sort s) ht h)).trans ih

/-- A legal erasure-normal representative in the tower with the given key. -/
def KRep (T T₀ : Expr S) (n : Nat) (s : S) : Prop :=
  PureTypeSystem.HasTypeBE P (Ω.context n) (T₀.rename (Expr.reverseIndex n)) (.sort s) ∧
    ENormal dz T₀ ∧ T₀.knf = T.knf

/-- The potential of a key class, computed on any legal erasure-normal representative. -/
noncomputable def kpotential (C D : Set (Set S)) (T : Expr S) : Nat :=
  if h : ∃ T₀ n s, Ω.KRep T T₀ n s
  then PlainObservationsR.potential P C D (Ω.context h.choose_spec.choose)
    (h.choose.rename (Expr.reverseIndex h.choose_spec.choose))
  else 1

theorem kpotential_at (hw : SystemENormalizing' P) (C D : Set (Set S)) {T T₀ : Expr S}
    {n : Nat} {s : S} (hr : Ω.KRep T T₀ n s) :
    Ω.kpotential C D T =
      PlainObservationsR.potential P C D (Ω.context n) (T₀.rename (Expr.reverseIndex n)) := by
  have h : ∃ T₀ n s, Ω.KRep T T₀ n s := ⟨T₀, n, s, hr⟩
  rw [kpotential, dif_pos h]
  obtain ⟨t, ⟨hT₁, e₁, k₁⟩⟩ := h.choose_spec.choose_spec
  set T₁ := h.choose
  set m := h.choose_spec.choose
  obtain ⟨hT₀, e₀, k₀⟩ := hr
  let k := max m n
  have hm : m ≤ k := le_max_left _ _
  have hn : n ≤ k := le_max_right _ _
  rw [← Ω.potentialR_at_mono hw C D hT₁ hm, ← Ω.potentialR_at_mono hw C D hT₀ hn]
  have a1 := Ω.at_mono (A := .sort t) hT₁ hm
  have a0 := Ω.at_mono (A := .sort s) hT₀ hn
  have c : ConvertsBE T₁ T₀ := converts_of_knf_eq hE.out (s := t) (t := s) ⟨k, a1⟩ ⟨k, a0⟩
    (k₁.trans k₀.symm)
  have en : ∀ X : Expr S, ENormal dz X → ENormal dz (X.rename (Expr.reverseIndex k)) := by
    intro X hX; unfold ENormal at hX ⊢; rw [Expr.erase_rename]; exact hX.rename _
  exact PlainObservationsR.potential_converts hw _ a1 a0 (en _ e₁) (en _ e₀) (c.rename _)

theorem kpotential_of_knf_eq (C D : Set (Set S)) {T T' : Expr S} (h : T.knf = T'.knf) :
    Ω.kpotential C D T = Ω.kpotential C D T' := by
  have he : ∀ T₀ n s, Ω.KRep T T₀ n s ↔ Ω.KRep T' T₀ n s := fun T₀ n s =>
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.trans h⟩, fun ⟨a, b, c⟩ => ⟨a, b, c.trans h.symm⟩⟩
  unfold kpotential
  by_cases h1 : ∃ T₀ n s, Ω.KRep T T₀ n s
  · have h2 : ∃ T₀ n s, Ω.KRep T' T₀ n s := by
      obtain ⟨T₀, n, s, hr⟩ := h1; exact ⟨T₀, n, s, (he _ _ _).1 hr⟩
    obtain ⟨T₀, n, s, hr⟩ := h1
    rw [← kpotential, ← kpotential, Ω.kpotential_at hE.out C D hr,
      Ω.kpotential_at hE.out C D ((he _ _ _).1 hr)]
  · have h2 : ¬ ∃ T₀ n s, Ω.KRep T' T₀ n s := by
      rintro ⟨T₀, n, s, hr⟩; exact h1 ⟨T₀, n, s, (he _ _ _).2 hr⟩
    rw [dif_neg h1, dif_neg h2]

/-- The potential of the target drops strictly along a frame that is typed up to keys, as in OpenAI's `frame_target_drop`. -/
theorem kframe_target_drop (hw : SystemENormalizing' P) {C D : Set (Set S)}
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {A B q : Expr S} {s : S} (hT : Ω.KHasTypeBE (.pi A B) (.sort s))
    (hN : KNormal (.pi A B)) (hq : Ω.KHasTypeBE q A)
    (hK : Ω.kprofile (.pi A B) ∈ D) (hL : Ω.kprofile (B.instantiate q) ∈ D) :
    Ω.kpotential C D (B.instantiate q).knf < Ω.kpotential C D (.pi A B) := by
  obtain ⟨n, A₁, B₁, q₀, a, b, c, eA, eB, hA, hB, hqk, hPn, hAn, hBn, hr, hqn⟩ :=
    Ω.frame_data hT hq
  have hPt : Ω.HasTypeBE (.pi A₁ B₁) (.sort s) := ⟨n, hPn⟩
  have wP := hPt.kwn_both hE.out
  have kPeq : (Expr.pi A₁ B₁).knf = (Expr.pi A B).knf := by
    rw [Expr.knf_pi wP.1.pi_domain wP.1.pi_body, hA, hB,
      ← Expr.knf_pi (KWN.of_knf_eq hA.symm wP.1.pi_domain) (KWN.of_knf_eq hB.symm wP.1.pi_body)]
  have ePi : ENormal dz (.pi A₁ B₁) := by
    unfold ENormal at eA eB ⊢; exact Normal.pi eA eB
  have en : ∀ X : Expr S, ENormal dz X → ENormal dz (X.rename (Expr.reverseIndex n)) := by
    intro X hX; unfold ENormal at hX ⊢; rw [Expr.erase_rename]; exact hX.rename _
  have hQ := hBn.instantiate hqn
  rw [Expr.instantiate_rename] at hQ
  obtain ⟨X', rX', eX'⟩ := hE.out _ hQ.valid _ ⟨_, .inl hQ⟩
  obtain ⟨X, rfl, rX⟩ := Reduces.rename_inv (reverseIndex_injective n) rX'
  have eX : ENormal dz X := by
    unfold ENormal at eX' ⊢; rw [Expr.erase_rename] at eX'; exact Normal.of_rename _ eX'
  have hQt : Ω.HasTypeBE (B₁.instantiate q₀) (.sort b) := ⟨n, hQ⟩
  have wQ := (hQt.kwn_both hE.out).1
  have kQ : (B₁.instantiate q₀).knf = (B.instantiate q).knf := by
    have wB₁ : KWN B₁ := wP.1.pi_body
    have wq₀ : KWN q₀ := (show Ω.HasTypeBE q₀ A₁ from ⟨n, hqn⟩).kwn_both hE.out |>.1
    have c1 : KConverts (B₁.instantiate q₀) (B.instantiate q) := by
      unfold KConverts
      rw [Expr.erase_instantiate, Expr.erase_instantiate]
      have cB : KConverts B₁ B := KConverts.of_knf_eq wB₁ (KWN.of_knf_eq hB.symm wB₁) hB
      have cq : KConverts q₀ q := KConverts.of_knf_eq wq₀ (KWN.of_knf_eq hqk.symm wq₀) hqk
      exact .trans _ _ _ (ConvertsBE.subst cB _) (cq.instantiate_right _)
    exact Expr.knf_converts wQ (KWN.of_kconverts (.symm _ _ c1) wQ) c1
  have kX : X.knf = ((B.instantiate q).knf).knf := by
    rw [Expr.knf_idem, ← kQ]
    exact Expr.knf_converts (KWN.of_kconverts (.symm _ _ rX.k.converts) wQ) wQ
      (.symm _ _ rX.k.converts)
  have repX : Ω.KRep ((B.instantiate q).knf) X n b :=
    ⟨hQ.subject_reduces rX', eX, kX⟩
  have repP : Ω.KRep (.pi A B) (.pi A₁ B₁) n s := ⟨hPn, ePi, kPeq⟩
  rw [Ω.kpotential_at hw C D repX, Ω.kpotential_at hw C D repP]
  rw [← Ω.kprofile_of_knf_eq kPeq, Ω.kprofile_at hw (T := .pi A₁ B₁) hPn] at hK
  rw [← Ω.kprofile_of_knf_eq kQ, Ω.kprofile_at hw hQ, ← Expr.instantiate_rename] at hL
  have hXr : Reduces ((B₁.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q₀.rename (Expr.reverseIndex n))) (X.rename (Expr.reverseIndex n)) := by
    rw [Expr.instantiate_rename]; exact rX'
  have hh := PlainObservationsR.frame_potential_drop hw hno hD hplain hneg hPn
    (en _ ePi) hqn hK hL hXr (en _ eX)
  exact lt_of_le_of_lt hh.1 hh.2

/-- Every active domain in the same component is counted, as in OpenAI's `frame_domain_drop`. -/
theorem kframe_domain_drop (hw : SystemENormalizing' P) {C D : Set (Set S)}
    {A B q : Expr S} {s : S} (hT : Ω.KHasTypeBE (.pi A B) (.sort s)) (hq : Ω.KHasTypeBE q A)
    (hK : ActiveLayer P C (Ω.kprofile (.pi A B)))
    (hL : ActiveLayer P C (Ω.kprofile (B.instantiate q)))
    (hI : Ω.kprofile A ∈ D) :
    Ω.kpotential C D A < Ω.kpotential C D (.pi A B) := by
  obtain ⟨n, A₁, B₁, q₀, a, b, c, eA, eB, hA, hB, hqk, hPn, hAn, hBn, hr, hqn⟩ :=
    Ω.frame_data hT hq
  have hPt : Ω.HasTypeBE (.pi A₁ B₁) (.sort s) := ⟨n, hPn⟩
  have wP := hPt.kwn_both hE.out
  have kPeq : (Expr.pi A₁ B₁).knf = (Expr.pi A B).knf := by
    rw [Expr.knf_pi wP.1.pi_domain wP.1.pi_body, hA, hB,
      ← Expr.knf_pi (KWN.of_knf_eq hA.symm wP.1.pi_domain) (KWN.of_knf_eq hB.symm wP.1.pi_body)]
  have ePi : ENormal dz (.pi A₁ B₁) := by
    unfold ENormal at eA eB ⊢; exact Normal.pi eA eB
  have en : ∀ X : Expr S, ENormal dz X → ENormal dz (X.rename (Expr.reverseIndex n)) := by
    intro X hX; unfold ENormal at hX ⊢; rw [Expr.erase_rename]; exact hX.rename _
  have repA : Ω.KRep A A₁ n a := ⟨hAn, eA, hA⟩
  have repP : Ω.KRep (.pi A B) (.pi A₁ B₁) n s := ⟨hPn, ePi, kPeq⟩
  have htrn := ProfileR.triple' hw hPn
  have kA : Ω.kprofile A = ProfileR P (Ω.context n) (A₁.rename (Expr.reverseIndex n)) := by
    rw [← Ω.kprofile_at hw hAn]; exact Ω.kprofile_of_knf_eq hA.symm
  have kP : Ω.kprofile (.pi A B) =
      ProfileR P (Ω.context n) ((Expr.pi A₁ B₁).rename (Expr.reverseIndex n)) := by
    rw [← Ω.kprofile_at hw (T := .pi A₁ B₁) hPn]; exact Ω.kprofile_of_knf_eq kPeq.symm
  have hQ := hBn.instantiate hqn
  rw [Expr.instantiate_rename] at hQ
  have hQt : Ω.HasTypeBE (B₁.instantiate q₀) (.sort b) := ⟨n, hQ⟩
  have kQ : Ω.kprofile (B.instantiate q) =
      ProfileR P (Ω.context n) ((B₁.instantiate q₀).rename (Expr.reverseIndex n)) := by
    rw [← Ω.kprofile_at hw hQ]
    apply Ω.kprofile_of_knf_eq
    have w := (hQt.kwn_both hE.out).1
    have wB₁ : KWN B₁ := wP.1.pi_body
    have wq₀ : KWN q₀ := (show Ω.HasTypeBE q₀ A₁ from ⟨n, hqn⟩).kwn_both hE.out |>.1
    have c1 : KConverts (B₁.instantiate q₀) (B.instantiate q) := by
      unfold KConverts
      rw [Expr.erase_instantiate, Expr.erase_instantiate]
      have cB : KConverts B₁ B := KConverts.of_knf_eq wB₁ (KWN.of_knf_eq hB.symm wB₁) hB
      have cq : KConverts q₀ q := KConverts.of_knf_eq wq₀ (KWN.of_knf_eq hqk.symm wq₀) hqk
      exact .trans _ _ _ (ConvertsBE.subst cB _) (cq.instantiate_right _)
    exact (Expr.knf_converts w (KWN.of_kconverts (.symm _ _ c1) w) c1).symm
  have hp := ProfileR.growth_path hw hBn hqn.valid _ (TypedSubstitutionBE.single hqn)
  change PositivePath (PrimaryEdge P)
    (ProfileR P (Ω.context n) ((B₁.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q₀.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename, ← kQ] at hp
  rw [kP] at hK
  have hJH := ObservationLayers.positive hL.layer hp
  have hJ := hK.predecessor (Reach.single (SecondaryEdge.positive hJH hK.layer
    (.codomain htrn)))
  have hc : ProfileR P (Ω.context n) (A₁.rename (Expr.reverseIndex n)) ∈ D ∧
      ActiveLayer P C (ProfileR P (A₁.rename (Expr.reverseIndex n) :: Ω.context n)
        (B₁.rename (Expr.liftRen (Expr.reverseIndex n)))) := ⟨kA ▸ hI, hJ⟩
  rw [Ω.kpotential_at hw C D repA, Ω.kpotential_at hw C D repP]
  simp only [Expr.rename, PlainObservationsR.potential, ite_eq_left hc]
  omega

end

end ContextTowerBE

end PureTypeSystem
