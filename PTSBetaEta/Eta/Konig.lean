module

public import PTSBetaEta.Beta.Basic

@[expose] public section

/-!
# Strong normalization as a uniform bound

β-reduction is finitely branching.
Hence a term is strongly normalizing exactly when a single bound covers the lengths of all its reduction sequences.
This is the usual consequence of König's lemma.
Since `StronglyNormalizing` is defined as accessibility, the proof here is a well-founded induction over the finite list of one-step reducts, and König's lemma itself is not needed.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

namespace Expr

/-- The list of all one-step β-reducts of a term. -/
def reducts : Expr S → List (Expr S)
  | .var _ => []
  | .sort _ => []
  | .app f a =>
      (match f with
        | .lam _ b => [b.instantiate a]
        | _ => []) ++
      ((reducts f).map fun f' => .app f' a) ++ ((reducts a).map fun a' => .app f a')
  | .lam A b => ((reducts A).map fun A' => .lam A' b) ++ ((reducts b).map fun b' => .lam A b')
  | .pi A B => ((reducts A).map fun A' => .pi A' B) ++ ((reducts B).map fun B' => .pi A B')

end Expr

/-- β-reduction is finitely branching, since the β-reducts of `M` are exactly the members of `M.reducts`. -/
theorem beta_iff_mem_reducts {M N : Expr S} : Beta M N ↔ N ∈ M.reducts := by
  constructor
  · intro h
    induction h with
    | head A b a => simp [Expr.reducts]
    | app_left _ ih => simp [Expr.reducts, ih]
    | app_right _ ih => simp [Expr.reducts, ih]
    | lam_domain _ ih => simp [Expr.reducts, ih]
    | lam_body _ ih => simp [Expr.reducts, ih]
    | pi_domain _ ih => simp [Expr.reducts, ih]
    | pi_body _ ih => simp [Expr.reducts, ih]
  · induction M generalizing N with
    | var n => simp [Expr.reducts]
    | sort s => simp [Expr.reducts]
    | app f a ihf iha =>
      intro h
      simp only [Expr.reducts, List.mem_append, List.mem_map] at h
      rcases h with (h | ⟨f', hf', rfl⟩) | ⟨a', ha', rfl⟩
      · cases f <;> simp at h
        subst h
        exact .head _ _ _
      · exact .app_left (ihf hf')
      · exact .app_right (iha ha')
    | lam A b ihA ihb =>
      intro h
      simp only [Expr.reducts, List.mem_append, List.mem_map] at h
      rcases h with ⟨A', hA', rfl⟩ | ⟨b', hb', rfl⟩
      · exact .lam_domain (ihA hA')
      · exact .lam_body (ihb hb')
    | pi A B ihA ihB =>
      intro h
      simp only [Expr.reducts, List.mem_append, List.mem_map] at h
      rcases h with ⟨A', hA', rfl⟩ | ⟨B', hB', rfl⟩
      · exact .pi_domain (ihA hA')
      · exact .pi_body (ihB hB')

/-- `Steps n M N` says that `M` reduces to `N` in exactly `n` β-steps. -/
inductive Steps : Nat → Expr S → Expr S → Prop
  | refl (M : Expr S) : Steps 0 M M
  | step {k : Nat} {M N P : Expr S} : Beta M N → Steps k N P → Steps (k + 1) M P

/-- `BoundedBy M n` says that every β-reduction sequence from `M` has at most `n` steps. -/
def BoundedBy (M : Expr S) (n : Nat) : Prop :=
  ∀ k P, Steps k M P → k ≤ n

theorem BoundedBy.mono {M : Expr S} {n m : Nat} (h : BoundedBy M n) (hnm : n ≤ m) :
    BoundedBy M m :=
  fun k P hs => (h k P hs).trans hnm

/-- If each term of a finite list has a bound on its reductions, then one bound works for all of them. -/
theorem exists_common_bound (l : List (Expr S)) (h : ∀ N ∈ l, ∃ n, BoundedBy N n) :
    ∃ n, ∀ N ∈ l, BoundedBy N n := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons N l ih =>
    obtain ⟨n₁, h₁⟩ := h N (by simp)
    obtain ⟨n₂, h₂⟩ := ih fun N' hN' => h N' (by simp [hN'])
    refine ⟨max n₁ n₂, ?_⟩
    intro N' hN'
    rcases List.mem_cons.mp hN' with rfl | hN'
    · exact h₁.mono (le_max_left _ _)
    · exact (h₂ N' hN').mono (le_max_right _ _)

/-- A strongly normalizing term has a single bound on the lengths of its reduction sequences. -/
theorem StronglyNormalizing.bounded {M : Expr S} (h : StronglyNormalizing M) :
    ∃ n, BoundedBy M n := by
  induction h with
  | intro M _ ih =>
    obtain ⟨n, hn⟩ := exists_common_bound M.reducts fun N hN =>
      ih N (beta_iff_mem_reducts.mpr hN)
    refine ⟨n + 1, ?_⟩
    intro k P hs
    cases hs with
    | refl => exact Nat.zero_le _
    | step hb hs' =>
      exact Nat.succ_le_succ (hn _ (beta_iff_mem_reducts.mp hb) _ _ hs')

/-- A term with a bound on the lengths of its reduction sequences is strongly normalizing. -/
theorem stronglyNormalizing_of_bounded {M : Expr S} {n : Nat} (h : BoundedBy M n) :
    StronglyNormalizing M := by
  induction n generalizing M with
  | zero =>
    refine Acc.intro M fun N hb => ?_
    exact absurd (h 1 N (.step hb (.refl N))) (by omega)
  | succ n ih =>
    refine Acc.intro M fun N hb => ih fun k P hs => ?_
    have := h (k + 1) P (.step hb hs)
    omega

/-- **Strong normalization as a uniform bound.**
A term is strongly β-normalizing exactly when the lengths of its β-reduction sequences are bounded. -/
theorem stronglyNormalizing_iff_bounded {M : Expr S} :
    StronglyNormalizing M ↔ ∃ n, BoundedBy M n :=
  ⟨StronglyNormalizing.bounded, fun ⟨_, h⟩ => stronglyNormalizing_of_bounded h⟩

end PureTypeSystem
