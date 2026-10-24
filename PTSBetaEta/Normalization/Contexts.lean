/- Adapted to typing with βη-conversion from OpenAI's `Contexts.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Typing

@[expose] public section

/-! This file adapts OpenAI's saturated context tower to typing with βη-conversion. -/


namespace PureTypeSystem

universe u

namespace HasTypeBE

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem scope (h : HasTypeBE P Γ M A) : M.Scoped Γ.length ∧ A.Scoped Γ.length := by
  induction h with
  | ax _ => exact ⟨True.intro, True.intro⟩
  | var _ ih =>
      exact ⟨Nat.zero_lt_succ _, ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weaken _ _ ih _ =>
      exact ⟨ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi),
        ih.2.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, True.intro⟩
  | abstraction _ _ ihb ihPi => exact ⟨⟨ihPi.1.1, ihb.1⟩, ihPi.1⟩
  | application _ _ ihf iha => exact ⟨⟨ihf.1, iha.1⟩, ihf.2.2.instantiate iha.1⟩
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1, ihB.1⟩

end HasTypeBE

/-- A context tower is a sequence of valid contexts, each extending the previous one by a single declaration.
Outside a prefix, variables are named by their fixed levels.
The tower is saturated, which means that every type in fixed-level names is declared again arbitrarily late.
Bound variables stay de Bruijn indices and are never declared in the tower. -/
structure ContextTowerBE {S : Type u} (P : Specification S) where
  context : Nat → List (Expr S)
  valid : ∀ n, ValidContextBE P (context n)
  length : ∀ n, (context n).length = n
  step : ∀ n, ∃ A s, HasTypeBE P (context n) A (.sort s) ∧ context (n+1) = A :: context n
  saturated : ∀ (n : Nat) (A : Expr S) (s : S), HasTypeBE P (context n) (A.rename (Expr.reverseIndex n)) (.sort s) →
    ∀ lower, ∃ m, n ≤ m ∧ lower ≤ m ∧
      context (m+1) = A.rename (Expr.reverseIndex m) :: context m

namespace ContextTowerBEConstruction

variable {S : Type u} (P : Specification S)

structure Stage (n : Nat) where
  context : List (Expr S)
  valid : ValidContextBE P context
  length : context.length = n

variable [Countable S]

noncomputable def enumeration : Nat → Expr S := by
  letI : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose

theorem enumeration_surjective : Function.Surjective (enumeration (S := S)) := by
  let : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose_spec

noncomputable def scheduled (n : Nat) : Expr S := enumeration (Nat.unpair n).1

theorem scheduled_late (A : Expr S) (lower : Nat) :
    ∃ m, lower ≤ m ∧ scheduled m = A := by
  obtain ⟨k, hk⟩ := enumeration_surjective A
  exact ⟨Nat.pair k lower, Nat.right_le_pair _ _, by simpa only [scheduled, Nat.unpair_pair]⟩

variable {s₀ t₀ : S} (h₀ : P.axioms s₀ t₀)

noncomputable def next {n : Nat} (Γ : Stage P n) :
    {A : Expr S // ∃ s, HasTypeBE P Γ.context A (.sort s)} := by
  classical
  let A : Expr S := (scheduled n).rename (Expr.reverseIndex n)
  exact if ht : ∃ s, HasTypeBE P Γ.context A (.sort s) then ⟨A, ht⟩
    else ⟨.sort s₀, t₀, HasTypeBE.sort_of_valid Γ.valid h₀⟩

noncomputable def stages : (n : Nat) → Stage P n
  | 0 => ⟨[], .nil, rfl⟩
  | n+1 =>
      let Γ := stages n
      let A := next P h₀ Γ
      ⟨A.val :: Γ.context, .cons Γ.valid A.property.choose_spec,
        by simp only [List.length_cons, Γ.length]⟩

noncomputable def contexts (n : Nat) : List (Expr S) := (stages P h₀ n).context

theorem valid (n : Nat) : ValidContextBE P (contexts P h₀ n) := (stages P h₀ n).valid

theorem length (n : Nat) : (contexts P h₀ n).length = n := (stages P h₀ n).length

theorem step (n : Nat) : ∃ A s, HasTypeBE P (contexts P h₀ n) A (.sort s) ∧
    contexts P h₀ (n+1) = A :: contexts P h₀ n :=
  ⟨(next P h₀ (stages P h₀ n)).val, _, (next P h₀ (stages P h₀ n)).property.choose_spec, rfl⟩

theorem rename_next {n : Nat} {M A : Expr S}
    (h : HasTypeBE P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    HasTypeBE P (contexts P h₀ (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := step P h₀ n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem rename_mono {n m : Nat} {M A : Expr S}
    (h : HasTypeBE P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    HasTypeBE P (contexts P h₀ m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rename_next P h₀ ih

theorem at_scheduled {n : Nat} (s : S)
    (h : HasTypeBE P (contexts P h₀ n) ((scheduled n).rename (Expr.reverseIndex n)) (.sort s)) :
    contexts P h₀ (n+1) = (scheduled n).rename (Expr.reverseIndex n) :: contexts P h₀ n := by
  classical
  have ht : ∃ t, HasTypeBE P (stages P h₀ n).context
      ((scheduled n).rename (Expr.reverseIndex n)) (.sort t) := ⟨s,h⟩
  simp only [contexts, stages, next, dite_eq_left ht]

theorem saturated (n : Nat) (A : Expr S) (s : S)
    (h : HasTypeBE P (contexts P h₀ n) (A.rename (Expr.reverseIndex n)) (.sort s))
    (lower : Nat) : ∃ m, n ≤ m ∧ lower ≤ m ∧
      contexts P h₀ (m+1) = A.rename (Expr.reverseIndex m) :: contexts P h₀ m := by
  obtain ⟨m, hm, he⟩ := scheduled_late A (max n lower)
  have hnm : n ≤ m := (le_max_left _ _).trans hm
  have hlm : lower ≤ m := (le_max_right _ _).trans hm
  have ht : HasTypeBE P (contexts P h₀ m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    rename_mono P h₀ (A := .sort s) h hnm
  refine ⟨m, hnm, hlm, ?_⟩
  have hs : HasTypeBE P (contexts P h₀ m)
      ((scheduled m).rename (Expr.reverseIndex m)) (.sort s) := by
    rw [he]
    exact ht
  calc
    contexts P h₀ (m+1) = (scheduled m).rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      at_scheduled P h₀ s hs
    _ = A.rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      congrArg (fun B : Expr S => B.rename (Expr.reverseIndex m) :: contexts P h₀ m) he

noncomputable def tower : ContextTowerBE P where
  context := contexts P h₀
  valid := valid P h₀
  length := length P h₀
  step := step P h₀
  saturated := saturated P h₀

end ContextTowerBEConstruction

namespace ContextTowerBE

variable {S : Type u} {P : Specification S} (Ω : ContextTowerBE P)

/-- A global judgment of the tower holds in some finite prefix of it. -/
def HasTypeBE (M A : Expr S) : Prop :=
  ∃ n, PureTypeSystem.HasTypeBE P (Ω.context n) (M.rename (Expr.reverseIndex n))
    (A.rename (Expr.reverseIndex n))

theorem at_next {n : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasTypeBE P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    PureTypeSystem.HasTypeBE P (Ω.context (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := Ω.step n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem at_mono {n m : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasTypeBE P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    PureTypeSystem.HasTypeBE P (Ω.context m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Ω.at_next ih

namespace HasTypeBE

variable {Ω : ContextTowerBE P} {M A : Expr S}

theorem scope (h : Ω.HasTypeBE M A) : ∃ n, M.Scoped n ∧ A.Scoped n := by
  obtain ⟨n, ht⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  · have hh := ht.scope.2.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh


theorem common {N B : Expr S} (h : Ω.HasTypeBE M A) (k : Ω.HasTypeBE N B) :
    ∃ n, PureTypeSystem.HasTypeBE P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n)) ∧
      PureTypeSystem.HasTypeBE P (Ω.context n) (N.rename (Expr.reverseIndex n))
      (B.rename (Expr.reverseIndex n)) := by
  obtain ⟨n, ht⟩ := h
  obtain ⟨m, kt⟩ := k
  exact ⟨max n m, Ω.at_mono ht (le_max_left _ _), Ω.at_mono kt (le_max_right _ _)⟩

end HasTypeBE

theorem fresh_variable {A : Expr S} {s : S} (h : Ω.HasTypeBE A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.HasTypeBE (.var i) A := by
  obtain ⟨n, ht⟩ := h
  have hA : A.Scoped n := by
    have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  obtain ⟨m, hnm, hlm, he⟩ := Ω.saturated n A s ht lower
  have hAm := hA.mono hnm
  have hm : PureTypeSystem.HasTypeBE P (Ω.context m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    Ω.at_mono (A := .sort s) ht hnm
  refine ⟨m, hlm, m+1, ?_⟩
  rw [he, hAm.reverseIndex_succ]
  have hv := PureTypeSystem.HasTypeBE.var hm
  simpa only [Expr.rename, Expr.reverseIndex, Nat.lt_succ_self, ite_true,
    Nat.add_sub_cancel, Nat.sub_self] using hv

end ContextTowerBE

namespace ContextTowerBE.HasTypeBE

variable {S : Type u} {P : Specification S} {Ω : ContextTowerBE P}
variable {M N A B : Expr S}

theorem application (hf : Ω.HasTypeBE M (.pi A B)) (ha : Ω.HasTypeBE N A) :
    Ω.HasTypeBE (.app M N) (B.instantiate N) := by
  obtain ⟨n, hf, ha⟩ := hf.common ha
  refine ⟨n, ?_⟩
  simpa only [Expr.rename, Expr.instantiate_rename] using
    PureTypeSystem.HasTypeBE.application hf ha

theorem conversion {s : S} (hM : Ω.HasTypeBE M A) (hB : Ω.HasTypeBE B (.sort s))
    (hc : ConvertsBE A B) : Ω.HasTypeBE M B := by
  obtain ⟨n, hM, hB⟩ := hM.common hB
  exact ⟨n, .conversion hM hB (hc.rename _)⟩

theorem subject_reduces (h : Ω.HasTypeBE M A) (hr : Reduces M N) : Ω.HasTypeBE N A := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.subject_reduces (hr.rename _)⟩

theorem regularity (h : Ω.HasTypeBE M A) :
    (∃ s, A = .sort s) ∨ (∃ s, Ω.HasTypeBE A (.sort s)) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨s, he⟩ | ⟨s, hs⟩ := h.regularity
  · left
    refine ⟨s, ?_⟩
    have he' := congrArg (Expr.rename (Expr.reverseIndex n)) he
    simpa only [Expr.reverseIndex_twice, Expr.rename] using he'
  · exact .inr ⟨s, n, hs⟩


end ContextTowerBE.HasTypeBE

/-! The context of a typing judgment, before its variables are substituted, is called generic (OpenAI's term).
A finite generic context may be sent into the saturated tower by any typed substitution, and the images need not be normal.
Every such substitution is typed in a single finite prefix of the tower.
No normalization or strong normalization of the images is assumed. -/
namespace ContextTowerBE
variable {S : Type u} {P : Specification S} (Ω : ContextTowerBE P)

def TypedSubstitutionBE (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.HasTypeBE (σ n) (A.subst σ)

namespace TypedSubstitutionBE
variable {Ω} {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem tail {A : Expr S} (h : Ω.TypedSubstitutionBE (A :: Γ) σ) :
    Ω.TypedSubstitutionBE Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- One common finite prefix of the tower types the images of all declarations.
This holds although the substitution is given as a function on all indices. -/
theorem common_stage (h : Ω.TypedSubstitutionBE Γ σ) :
    ∃ k, ∀ n A, Lookup Γ n A →
      PureTypeSystem.HasTypeBE P (Ω.context k) ((σ n).rename (Expr.reverseIndex k))
        ((A.subst σ).rename (Expr.reverseIndex k)) := by
  induction Γ generalizing σ with
  | nil => exact ⟨0, fun _ _ hn => nomatch hn⟩
  | cons B Γ ih =>
      obtain ⟨k, hk⟩ := ih h.tail
      obtain ⟨m, hm⟩ := h 0 (B.rename Nat.succ) (.zero B Γ)
      refine ⟨max k m, ?_⟩
      intro n A hn
      cases hn with
      | zero => exact Ω.at_mono hm (le_max_right k m)
      | succ B hn =>
          have hh := Ω.at_mono (hk _ _ hn) (le_max_left k m)
          simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- A typed substitution can be extended by a typed term, not necessarily normal, for the new generic binder. -/
theorem cons {A a : Expr S} (h : Ω.TypedSubstitutionBE Γ σ)
    (ha : Ω.HasTypeBE a (A.subst σ)) : Ω.TypedSubstitutionBE (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn
end TypedSubstitutionBE

namespace HasTypeBE
variable {Ω} {Γ : List (Expr S)} {M A : Expr S} {σ : Nat → Expr S}

/-- A judgment in a finite generic context, followed by a typed substitution into the tower, gives a judgment of the tower. -/
theorem subst (h : PureTypeSystem.HasTypeBE P Γ M A) (hσ : Ω.TypedSubstitutionBE Γ σ) :
    Ω.HasTypeBE (M.subst σ) (A.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitutionBE.common_stage hσ
  refine ⟨k, ?_⟩
  have hh := h.subst (Ω.valid k) (fun n => (σ n).rename (Expr.reverseIndex k)) (fun n B hn => by
    simpa only [← Expr.rename_subst] using hk n B hn)
  simpa only [← Expr.rename_subst] using hh
end HasTypeBE

namespace TypedSubstitutionBE
variable {Ω} {Γ : List (Expr S)} {σ τ : Nat → Expr S}

theorem comp {Δ : List (Expr S)} (h : Ω.TypedSubstitutionBE Δ τ)
    (hσ : PureTypeSystem.TypedSubstitutionBE P Γ Δ σ) :
    Ω.TypedSubstitutionBE Γ (fun n => (σ n).subst τ) := by
  intro n A hn
  simpa only [Expr.subst_subst] using HasTypeBE.subst (hσ n A hn) h

/-- The identity environment of a finite prefix of the tower, written with global names. -/
theorem identity (n : Nat) : Ω.TypedSubstitutionBE (Ω.context n) (.var ∘ Expr.reverseIndex n) := by
  intro i A hi
  have ht := PureTypeSystem.HasTypeBE.lookup (Ω.valid n) hi
  refine ⟨n, ?_⟩
  simpa only [Expr.subst_var_rename, Expr.rename, Function.comp_apply,
    Expr.reverseIndex_involutive n i, Expr.reverseIndex_twice] using ht
end TypedSubstitutionBE

end ContextTowerBE

end PureTypeSystem

