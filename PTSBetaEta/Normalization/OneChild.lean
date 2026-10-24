/- Adapted to typing with βη-conversion from OpenAI's `OneChild.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Components

@[expose] public section

/-!
# Case 2 for typing with βη-conversion, using erasure-normal reducts

This file adapts OpenAI's `OneChild.lean` (`PTSBetaEta.Beta.OneChild`) to typing with βη-conversion.
Types in plain contexts are replaced by a chosen erasure-normal reduct `rnf`.
The lemma `eval_converts` shows that `eval` gives the same result for any two erasure-normal legal representatives.
It takes the place of uniqueness of normal forms.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem

universe u

/-- A chosen erasure-normal β-reduct of `M`, or `M` itself if there is none. -/
noncomputable def Expr.rnf {S : Type u} [Nonempty S] (M : Expr S) : Expr S := by
  classical
  exact if h : ∃ M', Reduces M M' ∧ ENormal dz M' then h.choose else M

theorem Expr.rnf_spec {S : Type u} [Nonempty S] {M : Expr S}
    (h : ∃ M', Reduces M M' ∧ ENormal dz M') : Reduces M M.rnf ∧ ENormal dz M.rnf := by
  classical
  unfold Expr.rnf; rw [dif_pos h]; exact h.choose_spec

theorem Expr.rnf_sort {S : Type u} [Nonempty S] (s : S) : (Expr.sort s).rnf = .sort s := by
  have h : ∃ M', Reduces (Expr.sort s) M' ∧ ENormal dz M' :=
    ⟨_, .refl, show Normal (Expr.sort s) from Normal.sort s⟩
  exact Reduces.sort_inv (Expr.rnf_spec h).1

theorem HasTypeBE.rnf_spec {S : Type u} [Nonempty S] {P : Specification S}
    (hw : SystemENormalizing' P) {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    Reduces M M.rnf ∧ ENormal dz M.rnf :=
  Expr.rnf_spec (hw Γ h.valid M ⟨A, .inl h⟩)

end PureTypeSystem

namespace PureTypeSystem.KP.OneChildInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))

abbrev Bits := Nat → Bool

def extendBit (θ : Bits) (b : Bool) : Bits
  | 0 => b
  | n+1 => θ n

def head : Expr S → Option Nat
  | .var n => some n
  | .app f _ => head f
  | _ => none

noncomputable def eval (Γ : List (Expr S)) (A : Expr S) (σ : Nat → Expr S) (θ : Bits) : Set (Expr S) :=
  if ProfileR P Γ A ∈ C ∧ Ω.kprofile (A.subst σ) ∈ C then
    match A with
    | .pi D E => RawProduct Ω D E σ (eval Γ D σ θ)
        (fun n b => eval (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
    | A => match head A with
      | none => Top Ω (A.subst σ).knf
      | some i => if θ i then Top Ω (A.subst σ).knf else Bottom Ω (A.subst σ).knf
  else Top Ω (A.subst σ).knf

@[simp] theorem head_rename (A : Expr S) (ρ : Nat → Nat) :
    head (A.rename ρ) = (head A).map ρ := by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl

theorem head_subst {A : Expr S} {i : Nat} (hi : head A = some i) (σ : Nat → Expr S) :
    head (A.subst σ) = head (σ i) := by
  induction A with
  | var j => cases hi; rfl
  | app f n ihf ihn => exact ihf hi
  | sort s => cases hi
  | pi D E ihD ihE => cases hi
  | lam D m ihD ihm => cases hi

theorem head_beta {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Beta A B) :
    head B = some i := by
  induction hr with
  | head D m n => cases hi
  | app_left hr ih => exact ih hi
  | app_right hr ih => exact hi
  | lam_domain hr ih => cases hi
  | lam_body hr ih => cases hi
  | pi_domain hr ih => cases hi
  | pi_body hr ih => cases hi

theorem head_reduces {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Reduces A B) :
    head B = some i := by
  induction hr with
  | refl => exact hi
  | tail hr hs ih => exact head_beta ih hs

theorem head_erase (A : Expr S) : head (A.erase dz) = head A := by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl

theorem eval_pi (Γ : List (Expr S)) (D E : Expr S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.pi D E) σ θ =
      if ProfileR P Γ (.pi D E) ∈ C ∧ Ω.kprofile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D σ θ)
          (fun n b => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).knf := rfl

theorem eval_head {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits} {i : Nat}
    (hg : ProfileR P Γ A ∈ C) (ha : Ω.kprofile (A.subst σ) ∈ C) (hi : head A = some i) :
    eval Ω C Γ A σ θ = if θ i then Top Ω (A.subst σ).knf else Bottom Ω (A.subst σ).knf := by
  cases A <;> simp only [eval,ite_eq_left (And.intro hg ha)]
  all_goals first | (cases hi <;> rfl) | (rw [hi])

theorem eval_sort (Γ : List (Expr S)) (s : S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.sort s) σ θ = Top Ω (.sort s) := by
  simp only [eval,head,ite_self,Expr.subst,Expr.knf_of_normal (KNormal.sort s)]

variable (hw : SystemENormalizing' P)
include hw

theorem eval_candidate {Γ : List (Expr S)} {A : Expr S} {s : S}
    {σ : Nat → Expr S} (hA : HasTypeBE P Γ A (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ) (θ : Bits) :
    IsCandidate Ω (A.subst σ).knf (eval Ω C Γ A σ θ) := by
  induction A generalizing Γ s σ θ with
  | pi D E ihD ihE =>
    rw [eval]
    split
    · obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
      have hX := ihD hD hσ θ
      apply rawProduct_candidate hw hA hσ hX
      intro n hn bit
      have hrawD := ContextTowerBE.THasTypeBE.subst hD hσ
      have ht := (hX.upper hn).1.conversion hrawD
        (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
      exact ihE hE (hσ.cons ht) (extendBit θ bit)
    · exact top_candidate
  | var i =>
    simp only [eval,head]
    split
    · split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate
  | sort s => simp only [eval,head,ite_self]; exact top_candidate
  | lam D m ihD ihm => simp only [eval,head,ite_self]; exact top_candidate
  | app f n ihf ihn =>
    simp only [eval]
    split
    · cases hh : head (.app f n) with
      | none => exact top_candidate
      | some i =>
        change IsCandidate Ω (Expr.subst σ (.app f n)).knf
          (if θ i then Top Ω (Expr.subst σ (.app f n)).knf else Bottom Ω (Expr.subst σ (.app f n)).knf)
        split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate

omit hw in
theorem eval_outside {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits}
    (ho : ProfileR P Γ A ∉ C ∨ Ω.kprofile (A.subst σ) ∉ C) :
    eval Ω C Γ A σ θ = Top Ω (A.subst σ).knf := by
  have hn : ¬ (ProfileR P Γ A ∈ C ∧ Ω.kprofile (A.subst σ) ∈ C) :=
    fun h => ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
  cases A <;> simp only [eval,ite_eq_right hn]

def dropSupport : Option (Nat × Bool) → Option (Nat × Bool)
  | some (0,_) => none
  | some (n+1,p) => some (n,p)
  | none => none

def flipSupport : Option (Nat × Bool) → Option (Nat × Bool) :=
  Option.map (fun (n,p) => (n,!p))

noncomputable def support (Γ : List (Expr S)) (A : Expr S) : Option (Nat × Bool) :=
  if ProfileR P Γ A ∈ C then
    match A with
    | .pi D E => if ProfileR P Γ D ∈ C then flipSupport (support Γ D)
        else dropSupport (support (D :: Γ) E)
    | A => (head A).map (fun i => (i,false))
  else none

structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TTypedSubstitutionBE Γ images
  bits : Bits

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  eval Ω C Γ A.rnf e.images e.bits

theorem rnf_typed {Γ : List (Expr S)} {A : Expr S} {s : S} (hA : HasTypeBE P Γ A (.sort s)) :
    HasTypeBE P Γ A.rnf (.sort s) := hA.subject_reduces (hA.rnf_spec hw).1

theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S}
    (hA : ExpectedBE P Γ A) (e : Environment Ω Γ) :
    (A.rnf.subst e.images).knf = (A.subst e.images).knf := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.rnf_sort]
  · have hr := (hA.rnf_spec hw).1.subst e.images
    have w := (ContextTowerBE.THasTypeBE.subst hA e.typed).kwn hw
    exact (Expr.knf_converts w (KWN.of_kconverts (.symm _ _ hr.k.converts) w) hr.k.converts).symm

theorem R_candidate {Γ : List (Expr S)} {A : Expr S} (hA : ExpectedBE P Γ A) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.images).knf (R Ω C A e) := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · simp only [R,Expr.rnf_sort,eval_sort,Expr.subst,Expr.knf_of_normal (KNormal.sort s)]
    exact top_candidate
  · rw [← normal_subst_eq Ω hw (.sorted hA) e]
    exact eval_candidate Ω C hw (rnf_typed hw hA) e.typed e.bits

end

section
universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))
variable (hw : SystemENormalizing' P)

theorem eval_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hc : ContextEquivalentBE P Γ Δ)
    (σ : Nat → Expr S) (θ : Bits) : eval Ω C Γ A σ θ = eval Ω C Δ A σ θ := by
  induction A generalizing Γ Δ s σ θ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp : ProfileR P Γ (.pi D E) = ProfileR P Δ (.pi D E) := ProfileR.context_equiv hc
    rw [eval_pi,eval_pi,hp]
    congr 1
    apply congrArg₂ (RawProduct Ω D E σ) (ihD hD hc σ θ)
    funext n bit
    exact ihE hE (hc.cons hD) _ _
  | var i =>
    have hp : ProfileR P Γ (.var i) = ProfileR P Δ (.var i) := ProfileR.context_equiv hc
    simp only [eval,hp]
  | sort s => rw [eval_sort,eval_sort]
  | app f n ihf ihn =>
    have hp : ProfileR P Γ (.app f n) = ProfileR P Δ (.app f n) := ProfileR.context_equiv hc
    simp only [eval,hp]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type

omit [Fact (SystemENormalizing' P)] in
/-- Two neutral spines that are βη-convertible have the same head variable. -/
theorem head_eq_of_convertsBE {T : Expr S} (n1 : Neutral T) :
    ∀ {T' : Expr S}, Neutral T' → ConvertsBE T T' → head T = head T' := by
  induction n1 with
  | var n => intro T' n2 hc; rw [convertsBE_var_neutral dz n2 hc]
  | @app f a hf ih =>
    intro T' n2 hc
    obtain ⟨g, b, rfl, hg, cfg, _⟩ := convertsBE_app_neutral dz hf n2 hc
    have h := ih hg cfg
    exact h

/-- `eval` does not depend on the choice of erasure-normal representative. -/
theorem eval_converts : ∀ (T : Expr S) {Γ : List (Expr S)} {T' : Expr S} {s t : S}
    {σ : Nat → Expr S} (θ : Bits), HasTypeBE P Γ T (.sort s) → HasTypeBE P Γ T' (.sort t) →
    ENormal dz T → ENormal dz T' → ConvertsBE T T' → Ω.TTypedSubstitutionBE Γ σ →
    eval Ω C Γ T σ θ = eval Ω C Γ T' σ θ := by
  intro T
  induction T with
  | pi A B ihA ihB =>
    intro Γ T' s t σ θ hT hT' eT eT' hc hσ
    obtain ⟨A', B', rfl⟩ : ∃ A' B', T' = .pi A' B' := by
      rcases convertsBE_sorted_shape dz hT hT' eT eT' hc with ⟨u, e1, _⟩ |
        ⟨_, _, A', B', _, e2⟩ | ⟨n1, _⟩
      · cases e1
      · exact ⟨A', B', e2⟩
      · cases n1
    obtain ⟨cA, cB⟩ := hc.product_compatibility dz
    obtain ⟨a, b, _, hA, hB, _, _⟩ := hT.generation_pi
    obtain ⟨a', b', _, hA', hB', _, _⟩ := hT'.generation_pi
    have ctx := ContextEquivalentBE.head_conversion hA hA' cA
    have hB'' := (ctx.typing _ _).2 hB'
    have wT := (ContextTowerBE.THasTypeBE.subst hT hσ).kwn Fact.out
    have wT' := (ContextTowerBE.THasTypeBE.subst hT' hσ).kwn Fact.out
    have kk : ((Expr.pi A B).subst σ).knf = ((Expr.pi A' B').subst σ).knf :=
      Expr.knf_converts wT wT' (hc.subst σ).k
    rw [eval_pi, eval_pi, ProfileR.converts (Fact.out : SystemENormalizing' P) hT hT' hc, Ω.kprofile_of_knf_eq kk]
    split
    · ext h
      have hX := ihA θ hA hA' eT.pi.1 eT'.pi.1 cA hσ
      unfold RawProduct
      rw [kk, hX]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hn bit => ?_⟩
        have hnC := (eval_candidate Ω C Fact.out hA' hσ θ).upper hn
        have hrawD := ContextTowerBE.THasTypeBE.subst hA' hσ
        have hnr := hnC.1.conversion hrawD (.symm _ _ (Expr.knf_spec (hrawD.kwn Fact.out)).1.converts)
        have hrawD0 := ContextTowerBE.THasTypeBE.subst hA hσ
        have hnr0 : Ω.THasTypeBE n (A.subst σ) := hnr.conversion hrawD0 (cA.subst σ).k.symm
        have hY := ihB (extendBit θ bit) hB hB'' eT.pi.2 eT'.pi.2 cB
          (σ := Expr.extend σ n) (hσ.cons hnr0)
        have hrc := eval_recontext Ω C hB' ctx.symm (Expr.extend σ n) (extendBit θ bit)
        have := h2 n hn bit
        dsimp only at this ⊢
        rw [hY] at this
        rw [hrc]
        exact this
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hn bit => ?_⟩
        have hnC := (eval_candidate Ω C Fact.out hA' hσ θ).upper hn
        have hrawD := ContextTowerBE.THasTypeBE.subst hA' hσ
        have hnr := hnC.1.conversion hrawD (.symm _ _ (Expr.knf_spec (hrawD.kwn Fact.out)).1.converts)
        have hrawD0 := ContextTowerBE.THasTypeBE.subst hA hσ
        have hnr0 : Ω.THasTypeBE n (A.subst σ) := hnr.conversion hrawD0 (cA.subst σ).k.symm
        have hY := ihB (extendBit θ bit) hB hB'' eT.pi.2 eT'.pi.2 cB
          (σ := Expr.extend σ n) (hσ.cons hnr0)
        have hrc := eval_recontext Ω C hB' ctx.symm (Expr.extend σ n) (extendBit θ bit)
        have := h2 n hn bit
        dsimp only at this ⊢
        rw [hrc] at this
        rw [hY]
        exact this
    · rw [kk]
  | lam _ _ _ _ => intro _ _ _ _ _ _ hT; exact hT.lambda_cannot_have_sort_type.elim
  | sort u =>
    intro Γ T' s t σ θ hT hT' eT eT' hc hσ
    rw [ENormal.eq_sort_of_convertsBE dz hT' eT' (.symm _ _ hc)]
  | var i =>
    intro Γ T' s t σ θ hT hT' eT eT' hc hσ
    exact neutral_case _ hT hT' eT eT' hc hσ θ
  | app f a _ _ =>
    intro Γ T' s t σ θ hT hT' eT eT' hc hσ
    exact neutral_case _ hT hT' eT eT' hc hσ θ
where
  neutral_case (T : Expr S) {Γ : List (Expr S)} {T' : Expr S} {s t : S} {σ : Nat → Expr S}
      (hT : HasTypeBE P Γ T (.sort s)) (hT' : HasTypeBE P Γ T' (.sort t))
      (eT : ENormal dz T) (eT' : ENormal dz T') (hc : ConvertsBE T T')
      (hσ : Ω.TTypedSubstitutionBE Γ σ) (θ : Bits) (hnp : ∀ A B, T ≠ .pi A B := by
        intro A B h; cases h) :
      eval Ω C Γ T σ θ = eval Ω C Γ T' σ θ := by
    have hnp' : ∀ A B, T' ≠ .pi A B := by
      rintro A B rfl
      rcases convertsBE_sorted_shape dz hT hT' eT eT' hc with ⟨u, _, e2⟩ |
        ⟨A₁, A₂, _, _, e1, _⟩ | ⟨_, n2⟩
      · cases e2
      · exact hnp _ _ e1
      · cases n2
    have hh : head T = head T' := by
      rcases convertsBE_sorted_shape dz hT hT' eT eT' hc with ⟨u, rfl, rfl⟩ |
        ⟨A₁, A₂, _, _, e1, _⟩ | ⟨n1, n2⟩
      · rfl
      · exact (hnp _ _ e1).elim
      · exact head_eq_of_convertsBE n1 n2 hc
    have wT := (ContextTowerBE.THasTypeBE.subst hT hσ).kwn Fact.out
    have wT' := (ContextTowerBE.THasTypeBE.subst hT' hσ).kwn Fact.out
    have kk : (T.subst σ).knf = (T'.subst σ).knf := Expr.knf_converts wT wT' (hc.subst σ).k
    have hp := ProfileR.converts (Fact.out : SystemENormalizing' P) hT hT' hc
    have hk := Ω.kprofile_of_knf_eq kk
    unfold eval
    rw [hp, hk]
    split
    · cases T with
      | pi A B => exact (hnp A B rfl).elim
      | _ =>
        cases T' with
        | pi A B => exact (hnp' A B rfl).elim
        | _ => simp only [hh, kk]
    · rw [kk]

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : ExpectedBE P Γ A) (hB : ExpectedBE P Γ B) (hc : ConvertsBE A B) (e : Environment Ω Γ) :
    R Ω C A e = R Ω C B e := by
  unfold R
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩ <;> rcases hB with ⟨t,rfl⟩ | ⟨t,hB⟩
  · rw [hc.sort_inj]
  · have hr := (hB.rnf_spec Fact.out)
    have hBs := hB.subject_reduces hr.1
    rw [Expr.rnf_sort]
    have : B.rnf = .sort s := ENormal.eq_sort_of_convertsBE dz hBs hr.2
      (.trans _ _ _ (.symm _ _ (reduces_convertsBE hr.1)) (.symm _ _ hc))
    rw [this]
  · have hr := (hA.rnf_spec Fact.out)
    rw [Expr.rnf_sort]
    have : A.rnf = .sort t := ENormal.eq_sort_of_convertsBE dz (hA.subject_reduces hr.1) hr.2
      (.trans _ _ _ (.symm _ _ (reduces_convertsBE hr.1)) hc)
    rw [this]
  · have rA := hA.rnf_spec Fact.out
    have rB := hB.rnf_spec Fact.out
    exact eval_converts Ω C _ e.bits (hA.subject_reduces rA.1) (hB.subject_reduces rB.1) rA.2 rB.2
      (.trans _ _ _ (.symm _ _ (reduces_convertsBE rA.1))
        (.trans _ _ _ hc (reduces_convertsBE rB.1))) e.typed

include hw in
theorem eval_rename {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hΔ : ValidContextBE P Δ)
    (ρ : Nat → Nat) (hρ : TypingTreeBE.DeclRenaming Γ Δ ρ)
    (σ τ : Nat → Expr S) (θ ψ : Bits) (hσ : τ ∘ ρ = σ) (hθ : ψ ∘ ρ = θ) :
    eval Ω C Γ A σ θ = eval Ω C Δ (A.rename ρ) τ ψ := by
  induction A generalizing Γ Δ s ρ σ τ θ ψ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp := ProfileR.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he (M : Expr S) : (M.rename ρ).subst τ = M.subst σ := by rw [Expr.subst_rename,hσ]
    rw [eval_pi]
    change _ = eval Ω C Δ (.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) τ ψ
    rw [eval_pi]
    have hraw : (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))).subst τ = (Expr.pi D E).subst σ := he (.pi D E)
    have hX := ihD hD hΔ ρ hρ σ τ θ ψ hσ hθ
    have hY : (fun n bit => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ bit)) =
        (fun n bit => eval Ω C (D.rename ρ :: Δ) (E.rename (Expr.liftRen ρ))
          (Expr.extend τ n) (extendBit ψ bit)) := by
      funext n bit
      apply ihE hE (.cons hΔ (hD.rename hΔ ρ (hρ.typed hΔ))) _ (hρ.lift D)
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hσ i
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hθ i
    change ProfileR P Δ (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) = _ at hp
    rw [hp,hraw]
    congr 1
    unfold RawProduct
    rw [hraw,hX,hY]
  | sort s => rw [eval_sort,Expr.rename,eval_sort]
  | var i =>
    have hp := ProfileR.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : (.var (ρ i) : Expr S).subst τ = Expr.subst σ (.var i) := congrFun hσ i
    change ProfileR P Δ (.var (ρ i)) = _ at hp
    simp only [eval,Expr.rename,hp,he,head]
    rw [show ψ (ρ i) = θ i from congrFun hθ i]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | app f n ihf ihn =>
    have hp := ProfileR.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : ((Expr.app f n).rename ρ).subst τ = (Expr.app f n).subst σ := by rw [Expr.subst_rename,hσ]
    simp only [Expr.rename] at hp he ⊢
    simp only [eval,hp,he,head,head_rename]
    cases hh : head f with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [show ψ (ρ i) = θ i from congrFun hθ i]

namespace Environment
variable {Ω}
def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment Ω Γ) (f : Environment Ω (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.bits (i+1) = e.bits i
end Environment

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω C (.sort s) e = Top Ω (.sort s) := by
  rw [R,Expr.rnf_sort,eval_sort]

include hw in
theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasTypeBE P Γ D (.sort s)) (hA : ExpectedBE P Γ A) (he : e.Ext f n) :
    R Ω C (A.rename Nat.succ) f = R Ω C A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω C a f).trans (R_sort Ω C a e).symm
  · have hAw : HasTypeBE P (D :: Γ) (A.rename Nat.succ) (.sort a) := .weaken hA hD
    have rA := hA.rnf_spec hw
    have rAw := hAw.rnf_spec hw
    have hA₁ := hA.subject_reduces rA.1
    have hA₁w : HasTypeBE P (D :: Γ) (A.rnf.rename Nat.succ) (.sort a) := .weaken hA₁ hD
    have en : ENormal dz (A.rnf.rename Nat.succ) := by
      unfold ENormal at rA ⊢; rw [Expr.erase_rename]; exact rA.2.rename _
    have c : ConvertsBE (A.rename Nat.succ).rnf (A.rnf.rename Nat.succ) :=
      .trans _ _ _ (.symm _ _ (reduces_convertsBE rAw.1))
        (reduces_convertsBE (rA.1.rename Nat.succ))
    rw [R, R, eval_converts Ω C _ f.bits (hAw.subject_reduces rAw.1) hA₁w rAw.2 en c f.typed]
    symm
    apply eval_rename Ω C hw hA₁ (.cons hD.valid hD) Nat.succ (TypingTreeBE.DeclRenaming.weaken D)
    · rw [he.1]; rfl
    · exact funext (fun i => he.2 i)

end

section
universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))
variable (hw : SystemENormalizing' P)
include hw

theorem normal_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (σ : Nat → Expr S)
    (hσ : Ω.TTypedSubstitutionBE Γ σ) (θ : Bits) :
    eval Ω C Γ (Expr.pi D E).rnf σ θ =
      if ProfileR P Γ (.pi D E) ∈ C ∧ Ω.kprofile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D.rnf σ θ)
          (fun n b => eval Ω C (D :: Γ) E.rnf (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).knf := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have rP := hp.rnf_spec hw
  obtain ⟨D', E', heq, rD', rE'⟩ := Reduces.pi_inv rP.1
  have eP : ENormal dz (Expr.pi D' E') := heq ▸ rP.2
  have eD' : ENormal dz D' := eP.pi.1
  have eE' : ENormal dz E' := eP.pi.2
  rw [heq, eval_pi]
  have hP' : HasTypeBE P Γ (.pi D' E') (.sort s) := heq ▸ hp.subject_reduces rP.1
  obtain ⟨a',b',c',hD',hE'',_,_⟩ := hP'.generation_pi
  have rD := hD.rnf_spec hw
  have rE := hE.rnf_spec hw
  have hDn := hD.subject_reduces rD.1
  have ctxD := ContextEquivalentBE.head_conversion hD hD' (reduces_convertsBE rD')
  have hEn := hE.subject_reduces rE.1
  have hEn' := (ctxD.typing _ _).1 hEn
  have hp1 : ProfileR P Γ (.pi D' E') = ProfileR P Γ (.pi D E) := by
    rw [← heq]; exact ProfileR.reduces hw hp rP.1
  have wraw := (ContextTowerBE.THasTypeBE.subst hp hσ).kwn hw
  have wraw' := (ContextTowerBE.THasTypeBE.subst hP' hσ).kwn hw
  have hrr : Reduces ((Expr.pi D E).subst σ) ((Expr.pi D' E').subst σ) := by
    rw [← heq]; exact rP.1.subst σ
  have kk : ((Expr.pi D' E').subst σ).knf = ((Expr.pi D E).subst σ).knf :=
    Expr.knf_converts wraw' wraw (.symm _ _ hrr.k.converts)
  rw [hp1, Ω.kprofile_of_knf_eq kk]
  split
  · ext h
    unfold RawProduct
    rw [kk]
    have hX : eval Ω C Γ D' σ θ = eval Ω C Γ D.rnf σ θ :=
      eval_converts Ω C _ θ hD' hDn eD' rD.2
        (.trans _ _ _ (.symm _ _ (reduces_convertsBE rD')) (reduces_convertsBE rD.1)) hσ
    rw [hX]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun n hn bit => ?_⟩
      have hnC := (eval_candidate Ω C hw hDn hσ θ).upper hn
      have hrawD := ContextTowerBE.THasTypeBE.subst hDn hσ
      have hnr := hnC.1.conversion hrawD (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
      have hrawD' := ContextTowerBE.THasTypeBE.subst hD' hσ
      have hnr' : Ω.THasTypeBE n (D'.subst σ) := hnr.conversion hrawD'
        (ConvertsBE.subst (Relation.EqvGen.trans _ _ _ (.symm _ _ (reduces_convertsBE rD.1)) (reduces_convertsBE rD')) σ).k
      have hY := eval_converts Ω C _ (extendBit θ bit) hE'' hEn' eE' rE.2
        (.trans _ _ _ (.symm _ _ (reduces_convertsBE rE')) (reduces_convertsBE rE.1)) (σ := Expr.extend σ n)
        (hσ.cons hnr')
      have hrc := eval_recontext Ω C hEn ctxD (Expr.extend σ n) (extendBit θ bit)
      have := h2 n hn bit
      dsimp only at this ⊢
      rw [hY, ← hrc] at this
      exact this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun n hn bit => ?_⟩
      have hnC := (eval_candidate Ω C hw hDn hσ θ).upper hn
      have hrawD := ContextTowerBE.THasTypeBE.subst hDn hσ
      have hnr := hnC.1.conversion hrawD (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
      have hrawD' := ContextTowerBE.THasTypeBE.subst hD' hσ
      have hnr' : Ω.THasTypeBE n (D'.subst σ) := hnr.conversion hrawD'
        (ConvertsBE.subst (Relation.EqvGen.trans _ _ _ (.symm _ _ (reduces_convertsBE rD.1)) (reduces_convertsBE rD')) σ).k
      have hY := eval_converts Ω C _ (extendBit θ bit) hE'' hEn' eE' rE.2
        (.trans _ _ _ (.symm _ _ (reduces_convertsBE rE')) (reduces_convertsBE rE.1)) (σ := Expr.extend σ n)
        (hσ.cons hnr')
      have hrc := eval_recontext Ω C hEn ctxD (Expr.extend σ n) (extendBit θ bit)
      have := h2 n hn bit
      dsimp only at this ⊢
      rw [hY, ← hrc]
      exact this
  · rw [kk]

theorem R_outside {Γ : List (Expr S)} {A : Expr S} (hA : ExpectedBE P Γ A)
    (e : Environment Ω Γ) (ho : ProfileR P Γ A ∉ C ∨ Ω.kprofile (A.subst e.images) ∉ C) :
    R Ω C A e = Top Ω (A.subst e.images).knf := by
  have hnf := normal_subst_eq Ω hw hA e
  rw [R,eval_outside Ω C,hnf]
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rcases ho with ho | ho
    · exact .inl (by rwa [Expr.rnf_sort])
    · exact .inr (by rwa [Expr.rnf_sort])
  · rcases ho with ho | ho
    · exact .inl (by rwa [ProfileR.reduces hw hA (hA.rnf_spec hw).1])
    · exact .inr (by
        rw [Ω.kprofile_of_knf_eq hnf]
        exact ho)

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hg : ProfileR P Γ (.pi D E) ∈ C)
    (e : Environment Ω Γ) (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C (.pi D E) e ↔
      h ∈ Top Ω ((Expr.pi D E).subst e.images).knf ∧
      ∀ n, n ∈ R Ω C D e → ∀ f : Environment Ω (D :: Γ), e.Ext f n → Expr.app h n ∈ R Ω C E f := by
  rw [R,normal_product Ω C hw hp e.images e.typed e.bits,ite_eq_left ⟨hg,ha⟩]
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn f he
    have hb : f.bits = extendBit e.bits (f.bits 0) := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact he.2 i
    change Expr.app h n ∈ eval Ω C (D :: Γ) E.rnf f.images f.bits
    rw [he.1,hb]
    exact hbody n hn (f.bits 0)
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn bit
    have hrawD := ContextTowerBE.THasTypeBE.subst hD e.typed
    have hnt := ((R_candidate Ω C hw (.sorted hD) e).upper hn).1.conversion hrawD
      (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
    let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
    exact hbody n hn f ⟨rfl,fun _ => rfl⟩

end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (C : Set (Set S))

def CompatibleBits (r : Option (Nat × Bool)) (dir : Bool) (σ : Nat → Expr S) (θ ψ : Bits) : Prop :=
  ∀ i p, r = some (i,p) → (∃ j, σ i = .var j ∧ θ i = ψ j) ∨ θ i = Bool.xor dir p

def Below {α : Type*} (dir : Bool) (X Y : Set α) : Prop := if dir then Y ⊆ X else X ⊆ Y

theorem support_outside {Γ : List (Expr S)} {A : Expr S} (h : ProfileR P Γ A ∉ C) :
    support (P := P) C Γ A = none := by cases A <;> simp only [support,ite_eq_right h]

theorem support_head {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (hg : ProfileR P Γ A ∈ C) (hi : head A = some i) : support (P := P) C Γ A = some (i,false) := by
  cases A <;> simp only [support,ite_eq_left hg]
  all_goals first | (cases hi <;> rfl) | (rw [hi]; rfl)

theorem bits_domain {Γ : List (Expr S)} {D E : Expr S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hg : ProfileR P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) :
    CompatibleBits (support (P := P) C Γ D) (!dir) σ θ ψ := by
  intro i p hi
  by_cases hd : ProfileR P Γ D ∈ C
  · have hp : support (P := P) C Γ (.pi D E) = some (i,!p) := by
      rw [support,ite_eq_left hg,ite_eq_left hd,flipSupport,hi]; rfl
    rcases hb i (!p) hp with h | h
    · exact .inl h
    · right
      have he : Bool.xor dir (!p) = Bool.xor (!dir) p := by cases dir <;> cases p <;> rfl
      exact h.trans he
  · rw [support_outside C hd] at hi
    cases hi

theorem bits_body (hw : SystemENormalizing' P)
    (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
    {Γ : List (Expr S)} {D E : Expr S} {s : S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hg : ProfileR P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) (bit : Bool) :
    CompatibleBits (support (P := P) C (D :: Γ) E) dir (Expr.liftSub σ) (extendBit θ bit) (extendBit ψ bit) := by
  intro i p hi
  by_cases hd : ProfileR P Γ D ∈ C
  · have he : ProfileR P (D :: Γ) E ∉ C := fun he => hno (ProfileR.triple' hw hp) hd he hg
    rw [support_outside C he] at hi
    cases hi
  · cases i with
    | zero => exact .inl ⟨0,rfl,rfl⟩
    | succ i =>
      have hh : support (P := P) C Γ (.pi D E) = some (i,p) := by
        rw [support,ite_eq_left hg,ite_eq_right hd,hi]; rfl
      rcases hb i p hh with ⟨j,hj,he⟩ | he
      · left
        exact ⟨j+1,by rw [Expr.liftSub_succ,hj]; rfl,he⟩
      · exact .inr he

noncomputable def chosenBit (Γ : List (Expr S)) (A : Expr S) : Bool :=
  match support (P := P) C Γ A with
  | some (0,p) => p
  | _ => true

theorem bits_single (Γ : List (Expr S)) (A N : Expr S) (θ : Bits) :
    CompatibleBits (support (P := P) C Γ A) false (Expr.single N) (extendBit θ (chosenBit (P := P) C Γ A)) θ := by
  intro i p hi
  cases i with
  | zero =>
    right
    simp only [extendBit,chosenBit,hi,Bool.false_xor]
  | succ i => exact .inl ⟨i,rfl,rfl⟩

end

section
universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))
variable (hw : SystemENormalizing' P)
include hw

theorem neutral_compare {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hΔ : ValidContextBE P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitutionBE P Γ Δ δ) (e : Environment Ω Δ) (θ : Bits) (dir : Bool) {i : Nat}
    (hi : head A = some i) (hg : ProfileR P Γ A ∈ C)
    (hp : ProfileR P Δ (A.subst δ) ∈ C)
    (ha : Ω.kprofile (A.subst (fun i => (δ i).subst e.images)) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  have ht := hA.subst hΔ δ hδ
  have hcomp : ((A.subst δ).subst e.images) = A.subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
  have hc := R_candidate Ω C hw (.sorted ht) e
  rw [hcomp] at hc
  rw [eval_head Ω C hg ha hi]
  rcases hb i false (support_head C hg hi) with ⟨j,hj,hbit⟩ | hbit
  · have rt := ht.rnf_spec hw
    have hhead : head (A.subst δ).rnf = some j :=
      head_reduces (by rw [head_subst hi,hj]; rfl) rt.1
    have hnf := normal_subst_eq Ω hw (.sorted ht) e
    have ha' : Ω.kprofile (((A.subst δ).rnf).subst e.images) ∈ C := by
      rw [Ω.kprofile_of_knf_eq hnf, hcomp]
      exact ha
    have hg' : ProfileR P Δ (A.subst δ).rnf ∈ C := by
      rwa [ProfileR.reduces hw ht rt.1]
    have he : R Ω C (A.subst δ) e =
        if e.bits j then Top Ω (A.subst (fun i => (δ i).subst e.images)).knf
        else Bottom Ω (A.subst (fun i => (δ i).subst e.images)).knf := by
      rw [R,eval_head Ω C hg' ha' hhead,hnf,hcomp]
    rw [he,hbit]
    cases dir <;> exact Set.Subset.rfl
  · simp only [Bool.xor_false] at hbit
    rw [hbit]
    cases dir with
    | false => exact bottom_le hc
    | true => exact hc.upper

omit hw in
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : head (M.apps ns) = head M := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih _

omit hw in
theorem normal_app_head {Γ : List (Expr S)} {f n : Expr S} {s : S}
    (ht : HasTypeBE P Γ (.app f n) (.sort s)) (hn : ENormal dz (.app f n)) :
    ∃ i, head (.app f n) = some i := by
  have hneutral {M : Expr S} (h : Neutral M) : ∃ i, head M = some i := by
    induction h with
    | var i => exact ⟨i,rfl⟩
    | app h ih => exact ih
  obtain ⟨s,he⟩ | h | ⟨D,E,he⟩ := ht.enormal_sorted_shape dz hn
  · cases he
  · exact hneutral h
  · cases he

variable (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hC hno hw

/-- The one-child comparison of polarities at an arbitrary erasure-normal type. -/
theorem compare_subst {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hN : ENormal dz A)
    (hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P Γ A) K)
    (hΔ : ValidContextBE P Δ) (δ : Nat → Expr S) (hδ : TypedSubstitutionBE P Γ Δ δ)
    (e : Environment Ω Δ) (θ : Bits) (dir : Bool)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  induction A generalizing Γ Δ s δ θ dir with
  | var i =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.var i).subst δ).subst e.images) = (Expr.var i).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.kprofile_subst_path hw ht e.typed
    have hpg := ProfileR.growth_path hw hA hΔ δ hδ
    by_cases ha : Ω.kprofile ((Expr.var i).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : ProfileR P Γ (Expr.var i) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : ProfileR P Δ ((Expr.var i).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir rfl hg hp ha hb
  | app f n ihf ihn =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.app f n).subst δ).subst e.images) = (Expr.app f n).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.kprofile_subst_path hw ht e.typed
    have hpg := ProfileR.growth_path hw hA hΔ δ hδ
    by_cases ha : Ω.kprofile ((Expr.app f n).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : ProfileR P Γ (Expr.app f n) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : ProfileR P Δ ((Expr.app f n).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    obtain ⟨i,hi⟩ := normal_app_head hA hN
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir hi hg hp ha hb
  | sort a =>
    have ht := hA.subst hΔ δ hδ
    rw [eval_sort,Expr.subst,R_sort]
    cases dir <;> exact Set.Subset.rfl
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | pi D E ihD ihE =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.pi D E).subst δ).subst e.images) = (Expr.pi D E).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.kprofile_subst_path hw ht e.typed
    have hpg := ProfileR.growth_path hw hA hΔ δ hδ
    by_cases ha : Ω.kprofile ((Expr.pi D E).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : ProfileR P Γ (Expr.pi D E) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : ProfileR P Δ ((Expr.pi D E).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    obtain ⟨a,b,c,hD,hE,hr,_⟩ := hA.generation_pi
    have hDn : ENormal dz D := (show ENormal dz (.pi D E) from hN).pi.1
    have hEn : ENormal dz E := (show ENormal dz (.pi D E) from hN).pi.2
    have tr := ProfileR.triple' hw hA
    have relD : ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P Γ D) K := ⟨_,hg,.single (.domain tr)⟩
    have relE : ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P (D :: Γ) E) K := ⟨_,hg,.single (.codomain tr)⟩
    have hδD := hD.subst hΔ δ hδ
    have dom := ihD hD hDn relD hΔ δ hδ e θ (!dir) (bits_domain C hg hb)
    have body (n : Expr S) (hn : n ∈ R Ω C (D.subst δ) e) (bit : Bool) :
        Below dir (eval Ω C (D :: Γ) E (Expr.extend (fun i => (δ i).subst e.images) n) (extendBit θ bit))
          (eval Ω C (D.subst δ :: Δ) (E.subst (Expr.liftSub δ)).rnf
            (Expr.extend e.images n) (extendBit e.bits bit)) := by
      have hrawD := ContextTowerBE.THasTypeBE.subst hδD e.typed
      have hnt := ((R_candidate Ω C hw (.sorted hδD) e).upper hn).1.conversion hrawD
        (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
      let f : Environment Ω (D.subst δ :: Δ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
      have hbody := ihE hE hEn relE (.cons hΔ hδD) (Expr.liftSub δ) (hδ.lift hδD)
        f (extendBit θ bit) dir (bits_body C hw hno hA hg hb bit)
      have hei : (fun i => (Expr.liftSub δ i).subst f.images) = Expr.extend (fun i => (δ i).subst e.images) n := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact Expr.subst_raise_extend (δ i) n e.images
      rw [hei] at hbody
      exact hbody
    rw [eval_pi,ite_eq_left ⟨hg,ha⟩,R,Expr.subst,normal_product Ω C hw ht _ e.typed e.bits,
      ite_eq_left ⟨hp,by change Ω.kprofile (((Expr.pi D E).subst δ).subst e.images) ∈ C; rwa [he]⟩]
    change Below dir (RawProduct Ω D E _ _ _) (RawProduct Ω (D.subst δ) (E.subst (Expr.liftSub δ)) e.images _ _)
    have hraw : ((Expr.pi (D.subst δ) (E.subst (Expr.liftSub δ))).subst e.images).knf =
        ((Expr.pi D E).subst (fun i => (δ i).subst e.images)).knf := congrArg Expr.knf he
    have domR : eval Ω C Δ (D.subst δ).rnf e.images e.bits = R Ω C (D.subst δ) e := rfl
    cases dir with
    | false =>
      intro h hh
      refine ⟨hraw.symm ▸ hh.1,?_⟩
      intro n hn bit
      exact body n hn bit (hh.2 n (dom hn) bit)
    | true =>
      intro h hh
      refine ⟨hraw ▸ hh.1,?_⟩
      intro n hn bit
      exact body n (dom hn) bit (hh.2 n (dom hn) bit)

end

universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))
variable (hw : SystemENormalizing' P) (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hw hC hno

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hN : HasTypeBE P Γ N D) (hg : ProfileR P Γ (.pi D E) ∈ C)
    (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C (.pi D E) e) (hn : N.subst e.images ∈ R Ω C D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let bit := chosenBit (P := P) C (D :: Γ) E.rnf
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images (N.subst e.images),
    e.typed.cons (ContextTowerBE.THasTypeBE.subst hN e.typed),extendBit e.bits bit⟩
  have hm := ((product_iff Ω C hw hp hg e ha h).mp hh).2 (N.subst e.images) hn f ⟨rfl,fun _ => rfl⟩
  have rE := hE.rnf_spec hw
  have hEn := hE.subject_reduces rE.1
  have hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P (D :: Γ) E.rnf) K := by
    rw [ProfileR.reduces hw hE rE.1]
    exact ⟨_,hg,.single (.codomain (ProfileR.triple' hw hp))⟩
  have hc := compare_subst Ω C hw hC hno hEn rE.2 hrel hD.valid (Expr.single N)
    (TypedSubstitutionBE.single hN) e f.bits false (bits_single C (D :: Γ) E.rnf N e.bits)
  have he : (fun i => (Expr.single N i).subst e.images) = f.images := by
    funext i; cases i <;> rfl
  rw [he] at hc
  have hout := hc hm
  have ht := hE.instantiate hN
  have ht' := hEn.instantiate hN
  have cE := ConvertsBE.subst (reduces_convertsBE rE.1) (Expr.single N)
  exact (R_conversion Ω C (.sorted ht) (.sorted ht') cE e).symm ▸ hout

/-- One-child components need no relational exclusion. -/
noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨⟨σ,hσ,fun _ => false⟩,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ n hn := ⟨⟨Expr.extend e.images n,e.typed.cons hn,extendBit e.bits false⟩,rfl,fun _ => rfl⟩
  R := R Ω C
  candidate e hA := R_candidate Ω C hw hA e
  conversion e ha hb hc := R_conversion Ω C ha hb hc e
  outside e ht ho := R_outside Ω C hw ht e ho
  weakening hd he hx := R_weakening Ω C hw hd he hx
  product_intro e hp hg ha h ht hb := (product_iff Ω C hw hp hg e ha h).mpr ⟨ht,hb⟩
  specialization e hp hN hg ha h hh hn := specialization Ω C hw hC hno e hp hN hg ha h hh hn

end PureTypeSystem.KP.OneChildInterpretation

