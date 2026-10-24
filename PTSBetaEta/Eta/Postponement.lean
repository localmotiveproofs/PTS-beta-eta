module

public import PTSBetaEta.Eta.Basic
public import PTSBetaEta.Beta.Reduction

@[expose] public section

/-!
# η-postponement for whole reduction sequences

Every βη-reduction sequence on annotated pseudo-terms can be rearranged so that all β-steps come before all η-steps.
If `M` reduces to `N` by βη-steps, then `M` reduces by β-steps to some `L`, and `L` reduces to `N` by η-steps.

The method follows Takahashi.
Parallel η-reduction (`ParEta`) commutes with OpenAI's parallel β-reduction (`Parallel`), one parallel step for one parallel step.
For this reason the rearrangement needs no termination argument.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

/-- Parallel η-reduction, which may contract several nested η-redexes in one step. -/
inductive ParEta : Expr S → Expr S → Prop
  | var (n) : ParEta (.var n) (.var n)
  | sort (s) : ParEta (.sort s) (.sort s)
  | app {f f' a a'} : ParEta f f' → ParEta a a' → ParEta (.app f a) (.app f' a')
  | lam {A A' b b'} : ParEta A A' → ParEta b b' → ParEta (.lam A b) (.lam A' b')
  | pi {A A' B B'} : ParEta A A' → ParEta B B' → ParEta (.pi A B) (.pi A' B')
  | head (A : Expr S) {F F'} : ParEta F F' →
      ParEta (.lam A (.app (F.rename Nat.succ) (.var 0))) F'

namespace ParEta

variable {M N : Expr S}

theorem refl (M : Expr S) : ParEta M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem of_eta (h : Eta M N) : ParEta M N := by
  induction h with
  | head A F => exact .head A (refl F)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih

theorem rename (h : ParEta M N) (ρ : Nat → Nat) : ParEta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ ih =>
    simp only [Expr.rename, Expr.liftRen, Expr.rename_succ_liftRen]
    exact .head _ (ih ρ)

theorem subst (h : ParEta M N) (σ τ : Nat → Expr S) (hστ : ∀ n, ParEta (σ n) (τ n)) :
    ParEta (M.subst σ) (N.subst τ) := by
  have hlift (σ τ : Nat → Expr S) (hστ : ∀ n, ParEta (σ n) (τ n)) :
      ∀ n, ParEta (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hστ n).rename Nat.succ
  induction h generalizing σ τ with
  | var n => exact hστ n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app (ihf σ τ hστ) (iha σ τ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))
  | head A _ ih =>
    simp only [Expr.subst, Expr.liftSub_zero, Expr.rename_succ_liftSub]
    exact .head _ (ih σ τ hστ)

theorem instantiate {b b' a a' : Expr S} (hb : ParEta b b') (ha : ParEta a a') :
    ParEta (b.instantiate a) (b'.instantiate a') := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

/-- A parallel η-step is a sequence of ordinary η-steps. -/
theorem eta_star (h : ParEta M N) : ReflTransGen Eta M N := by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | @app f f' a a' _ _ ihf iha =>
    exact (ihf.lift (fun x => Expr.app x a) fun _ _ e => Eta.app_left e).trans
      (iha.lift (fun x => Expr.app f' x) fun _ _ e => Eta.app_right e)
  | @lam A A' b b' _ _ ihA ihb =>
    exact (ihA.lift (fun x => Expr.lam x b) fun _ _ e => Eta.lam_domain e).trans
      (ihb.lift (fun x => Expr.lam A' x) fun _ _ e => Eta.lam_body e)
  | @pi A A' B B' _ _ ihA ihB =>
    exact (ihA.lift (fun x => Expr.pi x B) fun _ _ e => Eta.pi_domain e).trans
      (ihB.lift (fun x => Expr.pi A' x) fun _ _ e => Eta.pi_body e)
  | @head A F F' _ ih =>
    have hin : ReflTransGen Eta (F.rename Nat.succ) (F'.rename Nat.succ) :=
      ih.lift (Expr.rename Nat.succ) fun _ _ e => e.rename _
    exact (hin.lift (fun x => Expr.lam A (.app x (.var 0)))
      fun _ _ e => Eta.lam_body (Eta.app_left e)).tail (.head A F')

end ParEta

namespace Expr

theorem instantiate_app_shift (G a : Expr S) :
    (Expr.app (G.rename Nat.succ) (.var 0)).instantiate a = .app G a := by
  change Expr.app ((G.rename Nat.succ).instantiate a) a = _
  rw [rename_succ_instantiate]

theorem instantiate_liftRen_succ_var (c : Expr S) :
    (c.rename (liftRen Nat.succ)).instantiate (.var 0) = c := by
  unfold instantiate
  rw [subst_rename]
  have : (single (Expr.var 0 : Expr S) ∘ liftRen Nat.succ) = Expr.var := by
    funext n
    cases n <;> rfl
  rw [this, subst_var]

end Expr

/-- If `G a` makes a parallel β-step to `P`, then so does its η-expansion `(λx:A. G x) a`. -/
theorem Parallel.eta_head {A G a P : Expr S} (h : Parallel (.app G a) P) :
    Parallel (.app (.lam A (.app (G.rename Nat.succ) (.var 0))) a) P := by
  cases h with
  | app hG ha =>
    have := Parallel.head A (Parallel.app (hG.rename Nat.succ) (.var 0)) ha
    rwa [Expr.instantiate_app_shift] at this
  | head C hc ha =>
    have hX : Parallel (Expr.app ((Expr.lam C _).rename Nat.succ) (.var 0))
        ((_ : Expr S).rename (Expr.liftRen Nat.succ) |>.instantiate (.var 0)) :=
      Parallel.head (C.rename Nat.succ) (hc.rename (Expr.liftRen Nat.succ)) (.var 0)
    have := Parallel.head A hX ha
    rwa [Expr.instantiate_liftRen_succ_var] at this

/-- **Takahashi's commutation.**
A parallel η-step followed by a parallel β-step can be replaced by a parallel β-step followed by a parallel η-step. -/
theorem parEta_parallel_commute : ∀ (n : Nat) (M : Expr S), M.size < n →
    ∀ N L, ParEta M N → Parallel N L → ∃ P, Parallel M P ∧ ParEta P L := by
  intro n
  induction n with
  | zero => intro M hM; omega
  | succ n IH =>
  intro M hM N L he hp
  cases he with
  | var k => cases hp; exact ⟨_, .var k, .var k⟩
  | sort s => cases hp; exact ⟨_, .sort s, .sort s⟩
  | pi hA hB =>
    cases hp with
    | pi pA pB =>
      simp only [Expr.size] at hM
      obtain ⟨QA, hQA, eA⟩ := IH _ (by omega) _ _ hA pA
      obtain ⟨QB, hQB, eB⟩ := IH _ (by omega) _ _ hB pB
      exact ⟨_, .pi hQA hQB, .pi eA eB⟩
  | lam hA hb =>
    cases hp with
    | lam pA pb =>
      simp only [Expr.size] at hM
      obtain ⟨QA, hQA, eA⟩ := IH _ (by omega) _ _ hA pA
      obtain ⟨Qb, hQb, eb⟩ := IH _ (by omega) _ _ hb pb
      exact ⟨_, .lam hQA hQb, .lam eA eb⟩
  | @head A F F' hF =>
    simp only [Expr.size, Expr.size_rename] at hM
    obtain ⟨Q, hQ, eQ⟩ := IH _ (by omega) _ _ hF hp
    exact ⟨_, .lam (Parallel.refl A) (.app (hQ.rename Nat.succ) (.var 0)), .head A eQ⟩
  | @app f f' a a' hf ha =>
    cases hp with
    | app pf pa =>
      simp only [Expr.size] at hM
      obtain ⟨Qf, hQf, ef⟩ := IH _ (by omega) _ _ hf pf
      obtain ⟨Qa, hQa, ea⟩ := IH _ (by omega) _ _ ha pa
      exact ⟨_, .app hQf hQa, .app ef ea⟩
    | @head b b' _ a'' B pb pa =>
      simp only [Expr.size] at hM
      obtain ⟨Qa, hQa, ea⟩ := IH _ (by omega) _ _ ha pa
      cases hf with
      | @lam B₀ _ b₀ _ hB hb =>
        simp only [Expr.size] at hM
        obtain ⟨Qb, hQb, eb⟩ := IH _ (by omega) _ _ hb pb
        exact ⟨_, .head B₀ hQb hQa, eb.instantiate ea⟩
      | @head A₀ G _ hG =>
        simp only [Expr.size, Expr.size_rename] at hM
        have hsmall : (Expr.app G a).size < n := by simp only [Expr.size]; omega
        obtain ⟨P', hP', eP'⟩ := IH _ hsmall _ _ (.app hG ha) (.head B pb pa)
        exact ⟨P', hP'.eta_head, eP'⟩

theorem ParEta.commute {M N L : Expr S} (he : ParEta M N) (hp : Parallel N L) :
    ∃ P, Parallel M P ∧ ParEta P L :=
  parEta_parallel_commute _ M (Nat.lt_succ_self _) N L he hp

theorem parEta_star_commute {M N L : Expr S} (he : ReflTransGen ParEta M N)
    (hp : Parallel N L) : ∃ P, Parallel M P ∧ ReflTransGen ParEta P L := by
  induction he generalizing L with
  | refl => exact ⟨L, hp, .refl⟩
  | tail _ he₁ ih =>
    obtain ⟨P₁, hP₁, eP₁⟩ := he₁.commute hp
    obtain ⟨P, hP, eP⟩ := ih hP₁
    exact ⟨P, hP, eP.tail eP₁⟩

theorem ParEta.star_eta_star {M N : Expr S} (h : ReflTransGen ParEta M N) :
    ReflTransGen Eta M N := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.trans e.eta_star

/-- **η-postponement** for reduction sequences on annotated pseudo-terms. -/
theorem eta_postponement {M N : Expr S} (h : ReflTransGen BetaEta M N) :
    ∃ L, Reduces M L ∧ ReflTransGen Eta L N := by
  suffices H : ∃ L, ReflTransGen Parallel M L ∧ ReflTransGen ParEta L N by
    obtain ⟨L, hL, eL⟩ := H
    exact ⟨L, Parallel.rtc_reduces hL, ParEta.star_eta_star eL⟩
  induction h with
  | refl => exact ⟨M, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨L₁, hL₁, eL₁⟩ := ih
    rcases hs with hb | he
    · obtain ⟨P, hP, eP⟩ := parEta_star_commute eL₁ (Parallel.of_beta hb)
      exact ⟨P, hL₁.tail hP, eP⟩
    · exact ⟨L₁, hL₁, eL₁.tail (.of_eta he)⟩

end PureTypeSystem
