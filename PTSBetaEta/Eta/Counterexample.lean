module

public import PTSBetaEta.Eta.Basic

@[expose] public section

/-!
# Weak βη-normalization does not imply weak β-normalization on annotated terms

Let `T = λx:Ω. f x`, which is `lam Ω (app (var 1) (var 0))` in de Bruijn form.
One η-step takes `T` to the normal term `f`.
The only β-redex of `T` is `Ω`, which sits in the domain annotation, and `Ω` only reduces to itself.
Hence `T` has no β-normal form.

So weak β-normalization cannot be derived from weak βη-normalization without using typing.
For legal terms the situation is different, because every annotation of a legal term is itself a legal type.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

namespace EtaCounterexample

/-- `ω = λy:D. y y`, where the annotation `D` is the variable `0` and so is normal. -/
def ω : Expr S := .lam (.var 0) (.app (.var 0) (.var 0))

/-- `Ω = ω ω`. -/
def Ω : Expr S := .app ω ω

/-- `T = λx:Ω. f x`, where `f` is the free variable `0`. -/
def T : Expr S := .lam Ω (.app (.var 1) (.var 0))

theorem ω_normal : Normal (ω : Expr S) := by
  intro N h
  cases h with
  | lam_domain h => cases h
  | lam_body h =>
    cases h with
    | app_left h => cases h
    | app_right h => cases h

theorem Ω_step {N : Expr S} (h : Beta Ω N) : N = Ω := by
  cases h with
  | head A b a => rfl
  | app_left h => exact absurd h (ω_normal _)
  | app_right h => exact absurd h (ω_normal _)

theorem T_step {N : Expr S} (h : Beta T N) : N = T := by
  cases h with
  | lam_domain h => rw [Ω_step h]; rfl
  | lam_body h =>
    cases h with
    | app_left h => cases h
    | app_right h => cases h

theorem T_reduces {N : Expr S} (h : Relation.ReflTransGen Beta T N) : N = T := by
  induction h with
  | refl => rfl
  | tail _ hb ih => subst ih; exact T_step hb

theorem T_not_normal : ¬ Normal (T : Expr S) := fun h =>
  h T (.lam_domain (.head _ _ _))

/-- `T` has no β-normal form. -/
theorem T_not_weaklyNormalizing : ¬ WeaklyNormalizing (T : Expr S) := by
  rintro ⟨N, hN, hn⟩
  rw [T_reduces hN] at hn
  exact T_not_normal hn

/-- One η-step takes `T` to the variable `f`. -/
theorem T_eta : Eta (T : Expr S) (.var 0) := Eta.head Ω (.var 0)

/-- The η-reduct `f` is βη-normal. -/
theorem var_betaEta_normal : ∀ N : Expr S, ¬ BetaEta (.var 0) N := by
  rintro N (h | h) <;> cases h

end EtaCounterexample

end PureTypeSystem
