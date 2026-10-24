module

public import PTSBetaEta.Eta.Postponement

@[expose] public section

/-!
# Domain erasure

`M.erase z` replaces every λ-domain of `M` by the sort `z` and keeps the domains of products.
A β-step or an η-step of `M` becomes at most one step of the erasure.
Conversely, every β-step of the erasure comes from a β-step of the original term.
Compare Proposition 4.4.14 of Geuvers's thesis, where erasure removes the domains altogether.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

namespace Expr

def erase (z : S) : Expr S → Expr S
  | .var n => .var n
  | .sort s => .sort s
  | .app f a => .app (f.erase z) (a.erase z)
  | .lam _ b => .lam (.sort z) (b.erase z)
  | .pi A B => .pi (A.erase z) (B.erase z)

variable (z : S)

theorem erase_rename (M : Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).erase z = (M.erase z).rename ρ := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename, erase, ihf, iha]
  | lam A b ihA ihb => simp [rename, erase, ihb]
  | pi A B ihA ihB => simp [rename, erase, ihA, ihB]

theorem erase_subst (M : Expr S) (σ : Nat → Expr S) :
    (M.subst σ).erase z = (M.erase z).subst (fun n => (σ n).erase z) := by
  have hlift (σ : Nat → Expr S) :
      (fun n => (liftSub σ n).erase z) = liftSub (fun n => (σ n).erase z) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => simp [liftSub, erase_rename]
  induction M generalizing σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [subst, erase, ihf, iha]
  | lam A b ihA ihb => simp [subst, erase, ihb, hlift]
  | pi A B ihA ihB => simp [subst, erase, ihA, ihB, hlift]

theorem erase_instantiate (b a : Expr S) :
    (b.instantiate a).erase z = (b.erase z).instantiate (a.erase z) := by
  unfold instantiate
  rw [erase_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem erase_idem (M : Expr S) : (M.erase z).erase z = M.erase z := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [erase, ihf, iha]
  | lam A b ihA ihb => simp [erase, ihb]
  | pi A B ihA ihB => simp [erase, ihA, ihB]

end Expr

variable (z : S)

theorem Beta.erase {M N : Expr S} (h : Beta M N) :
    Beta (M.erase z) (N.erase z) ∨ M.erase z = N.erase z := by
  induction h with
  | head A b a =>
    left
    rw [Expr.erase_instantiate]
    exact .head _ _ _
  | app_left _ ih =>
    rcases ih with h | h
    · exact .inl (.app_left h)
    · exact .inr (by simp [Expr.erase, h])
  | app_right _ ih =>
    rcases ih with h | h
    · exact .inl (.app_right h)
    · exact .inr (by simp [Expr.erase, h])
  | lam_domain _ _ => exact .inr rfl
  | lam_body _ ih =>
    rcases ih with h | h
    · exact .inl (.lam_body h)
    · exact .inr (by simp [Expr.erase, h])
  | pi_domain _ ih =>
    rcases ih with h | h
    · exact .inl (.pi_domain h)
    · exact .inr (by simp [Expr.erase, h])
  | pi_body _ ih =>
    rcases ih with h | h
    · exact .inl (.pi_body h)
    · exact .inr (by simp [Expr.erase, h])

theorem Eta.erase {M N : Expr S} (h : Eta M N) :
    Eta (M.erase z) (N.erase z) ∨ M.erase z = N.erase z := by
  induction h with
  | head A F =>
    left
    simp only [Expr.erase, Expr.erase_rename]
    exact .head _ _
  | app_left _ ih =>
    rcases ih with h | h
    · exact .inl (.app_left h)
    · exact .inr (by simp [Expr.erase, h])
  | app_right _ ih =>
    rcases ih with h | h
    · exact .inl (.app_right h)
    · exact .inr (by simp [Expr.erase, h])
  | lam_domain _ _ => exact .inr rfl
  | lam_body _ ih =>
    rcases ih with h | h
    · exact .inl (.lam_body h)
    · exact .inr (by simp [Expr.erase, h])
  | pi_domain _ ih =>
    rcases ih with h | h
    · exact .inl (.pi_domain h)
    · exact .inr (by simp [Expr.erase, h])
  | pi_body _ ih =>
    rcases ih with h | h
    · exact .inl (.pi_body h)
    · exact .inr (by simp [Expr.erase, h])

theorem betaEta_star_erase {M N : Expr S} (h : ReflTransGen BetaEta M N) :
    ReflTransGen BetaEta (M.erase z) (N.erase z) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hb | he
    · rcases hb.erase z with h | h
      · exact ih.tail (.inl h)
      · exact h ▸ ih
    · rcases he.erase z with h | h
      · exact ih.tail (.inr h)
      · exact h ▸ ih

/-- **Reflection.** A β-step of the erasure of `M` comes from a β-step of `M` itself. -/
theorem Beta.of_erase {M G : Expr S} (h : Beta (M.erase z) G) :
    ∃ N, Beta M N ∧ N.erase z = G := by
  induction M generalizing G with
  | var n => cases h
  | sort s => cases h
  | app f a ihf iha =>
    cases f with
    | lam A b =>
      cases h with
      | head _ _ _ => exact ⟨_, .head A b a, Expr.erase_instantiate z b a⟩
      | app_left h =>
        obtain ⟨N, hN, rfl⟩ := ihf h
        exact ⟨_, .app_left hN, rfl⟩
      | app_right h =>
        obtain ⟨N, hN, rfl⟩ := iha h
        exact ⟨_, .app_right hN, rfl⟩
    | var n =>
      cases h with
      | app_left h => cases h
      | app_right h =>
        obtain ⟨N, hN, rfl⟩ := iha h
        exact ⟨_, .app_right hN, rfl⟩
    | sort s =>
      cases h with
      | app_left h => cases h
      | app_right h =>
        obtain ⟨N, hN, rfl⟩ := iha h
        exact ⟨_, .app_right hN, rfl⟩
    | app g c =>
      cases h with
      | app_left h =>
        obtain ⟨N, hN, rfl⟩ := ihf h
        exact ⟨_, .app_left hN, rfl⟩
      | app_right h =>
        obtain ⟨N, hN, rfl⟩ := iha h
        exact ⟨_, .app_right hN, rfl⟩
    | pi A B =>
      cases h with
      | app_left h =>
        obtain ⟨N, hN, rfl⟩ := ihf h
        exact ⟨_, .app_left hN, rfl⟩
      | app_right h =>
        obtain ⟨N, hN, rfl⟩ := iha h
        exact ⟨_, .app_right hN, rfl⟩
  | lam A b ihA ihb =>
    cases h with
    | lam_domain h => cases h
    | lam_body h =>
      obtain ⟨N, hN, rfl⟩ := ihb h
      exact ⟨_, .lam_body hN, rfl⟩
  | pi A B ihA ihB =>
    cases h with
    | pi_domain h =>
      obtain ⟨N, hN, rfl⟩ := ihA h
      exact ⟨_, .pi_domain hN, rfl⟩
    | pi_body h =>
      obtain ⟨N, hN, rfl⟩ := ihB h
      exact ⟨_, .pi_body hN, rfl⟩

theorem reduces_of_erase {M G : Expr S} (h : Reduces (M.erase z) G) :
    ∃ N, Reduces M N ∧ N.erase z = G := by
  induction h with
  | refl => exact ⟨M, .refl, rfl⟩
  | tail _ hb ih =>
    obtain ⟨N, hN, rfl⟩ := ih
    obtain ⟨N', hN', rfl⟩ := Beta.of_erase z hb
    exact ⟨N', hN.tail hN', rfl⟩

/-- If a term is βη-normal, then its erasure is β-normal. -/
theorem normal_erase_of_normalBE {N : Expr S} (h : ∀ N', ¬ BetaEta N N') :
    Normal (N.erase z) := by
  intro G hG
  obtain ⟨N', hN', _⟩ := Beta.of_erase z hG
  exact h N' (.inl hN')

end PureTypeSystem
