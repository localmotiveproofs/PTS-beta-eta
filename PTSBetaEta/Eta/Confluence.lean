module

public import PTSBetaEta.Eta.Erasure

@[expose] public section

/-!
# βη-confluence up to domain erasure

βη-reduction is not confluent on annotated terms.
Nederpelt's example `λy:B. (λx:A. x) y` reduces to `λx:A. x` by an η-step and to `λy:B. y` by a β-step.
The two results differ in their domain and have no common reduct.
After the λ-domains are erased, this critical pair disappears.
This file proves the following facts.

* Parallel β-reduction and parallel η-reduction commute on erased terms, by Takahashi's method.
* Hence βη-reduction is confluent on erased terms, by the Hindley–Rosen lemma.
* Every term is βη-convertible to its erasure, by Geuvers's Domain Lemma.
* Hence βη-conversion is injective on products and on sorts, and no product is convertible to a sort.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

variable (z : S)

/-- A term is erased when every λ-domain in it is the sort `z`. -/
def Erased (M : Expr S) : Prop := M.erase z = M

namespace Erased

variable {z}

theorem erase_erased (M : Expr S) : Erased z (M.erase z) := Expr.erase_idem z M

theorem app {f a : Expr S} (h : Erased z (.app f a)) : Erased z f ∧ Erased z a := by
  simp only [Erased, Expr.erase, Expr.app.injEq] at h
  exact h

theorem lam {A b : Expr S} (h : Erased z (.lam A b)) : A = .sort z ∧ Erased z b := by
  simp only [Erased, Expr.erase, Expr.lam.injEq] at h
  exact ⟨h.1.symm, h.2⟩

theorem pi {A B : Expr S} (h : Erased z (.pi A B)) : Erased z A ∧ Erased z B := by
  simp only [Erased, Expr.erase, Expr.pi.injEq] at h
  exact h

theorem mk_app {f a : Expr S} (hf : Erased z f) (ha : Erased z a) : Erased z (.app f a) := by
  simp only [Erased, Expr.erase] at *; rw [hf, ha]

theorem mk_lam {b : Expr S} (hb : Erased z b) : Erased z (.lam (.sort z) b) := by
  simp only [Erased, Expr.erase] at *; rw [hb]

theorem rename {M : Expr S} (h : Erased z M) (ρ : Nat → Nat) : Erased z (M.rename ρ) := by
  unfold Erased at *; rw [Expr.erase_rename, h]

theorem subst {M : Expr S} (h : Erased z M) {σ : Nat → Expr S} (hσ : ∀ n, Erased z (σ n)) :
    Erased z (M.subst σ) := by
  unfold Erased at *
  rw [Expr.erase_subst, h]
  congr 1
  funext n
  exact hσ n

theorem instantiate {b a : Expr S} (hb : Erased z b) (ha : Erased z a) :
    Erased z (b.instantiate a) := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => rfl

end Erased

theorem liftRen_injective {ρ : Nat → Nat} (hρ : Function.Injective ρ) :
    Function.Injective (Expr.liftRen ρ) := by
  intro a b h
  cases a <;> cases b <;> simp [Expr.liftRen] at h ⊢
  exact hρ h

theorem Expr.rename_inj : ∀ (M : Expr S) {ρ : Nat → Nat}, Function.Injective ρ →
    ∀ {N : Expr S}, M.rename ρ = N.rename ρ → M = N
  | .var n, _, hρ, N, h => by cases N <;> simp [Expr.rename] at h ⊢; exact hρ h
  | .sort s, _, _, N, h => by cases N <;> simp [Expr.rename] at h ⊢; exact h
  | .app f a, _, hρ, N, h => by
    cases N <;> simp [Expr.rename] at h ⊢
    exact ⟨Expr.rename_inj f hρ h.1, Expr.rename_inj a hρ h.2⟩
  | .lam A b, _, hρ, N, h => by
    cases N <;> simp [Expr.rename] at h ⊢
    exact ⟨Expr.rename_inj A hρ h.1, Expr.rename_inj b (liftRen_injective hρ) h.2⟩
  | .pi A B, _, hρ, N, h => by
    cases N <;> simp [Expr.rename] at h ⊢
    exact ⟨Expr.rename_inj A hρ h.1, Expr.rename_inj B (liftRen_injective hρ) h.2⟩

theorem Expr.rename_injective_succ {M N : Expr S}
    (h : M.rename Nat.succ = N.rename Nat.succ) : M = N :=
  Expr.rename_inj M Nat.succ_injective h

theorem Parallel.erased {M N : Expr S} (h : Parallel M N) (hM : Erased z M) : Erased z N := by
  induction h with
  | var n => rfl
  | sort s => rfl
  | app _ _ ihf iha => exact Erased.mk_app (ihf hM.app.1) (iha hM.app.2)
  | lam hA _ ihA ihb =>
    obtain ⟨rfl, hb⟩ := hM.lam
    cases hA
    exact Erased.mk_lam (ihb hb)
  | pi _ _ ihA ihB =>
    obtain ⟨hA, hB⟩ := hM.pi
    have h1 := ihA hA
    have h2 := ihB hB
    unfold Erased at h1 h2 ⊢
    simp only [Expr.erase, h1, h2]
  | head A _ _ ihb iha =>
    obtain ⟨hl, ha⟩ := hM.app
    exact (ihb hl.lam.2).instantiate (iha ha)

theorem ParEta.erased {M N : Expr S} (h : ParEta M N) (hM : Erased z M) : Erased z N := by
  induction h with
  | var n => rfl
  | sort s => rfl
  | app _ _ ihf iha => exact Erased.mk_app (ihf hM.app.1) (iha hM.app.2)
  | lam hA _ ihA ihb =>
    obtain ⟨rfl, hb⟩ := hM.lam
    cases hA
    exact Erased.mk_lam (ihb hb)
  | pi _ _ ihA ihB =>
    obtain ⟨hA, hB⟩ := hM.pi
    have h1 := ihA hA
    have h2 := ihB hB
    unfold Erased at h1 h2 ⊢
    simp only [Expr.erase, h1, h2]
  | @head A F F' _ ih =>
    have hb := hM.lam.2
    have hF : Erased z (F.rename Nat.succ) := hb.app.1
    have : Erased z F := by
      unfold Erased at hF ⊢
      rw [Expr.erase_rename] at hF
      exact Expr.rename_injective_succ hF
    exact ih this

/-! ## Inverting the reductions of renamed terms -/

theorem Parallel.rename_inv : ∀ {ρ : Nat → Nat}, Function.Injective ρ →
    ∀ {F X : Expr S}, Parallel (F.rename ρ) X → ∃ F₁, X = F₁.rename ρ ∧ Parallel F F₁ := by
  intro ρ hρ F
  induction F generalizing ρ with
  | var n => intro X h; cases h; exact ⟨_, rfl, .var n⟩
  | sort s => intro X h; cases h; exact ⟨_, rfl, .sort s⟩
  | pi A B ihA ihB =>
    intro X h
    cases h with
    | pi hA hB =>
      obtain ⟨A₁, rfl, pA⟩ := ihA hρ hA
      obtain ⟨B₁, rfl, pB⟩ := ihB (liftRen_injective hρ) hB
      exact ⟨.pi A₁ B₁, rfl, .pi pA pB⟩
  | lam A b ihA ihb =>
    intro X h
    cases h with
    | lam hA hb =>
      obtain ⟨A₁, rfl, pA⟩ := ihA hρ hA
      obtain ⟨b₁, rfl, pb⟩ := ihb (liftRen_injective hρ) hb
      exact ⟨.lam A₁ b₁, rfl, .lam pA pb⟩
  | app f a ihf iha =>
    intro X h
    have congr_case : ∀ {f' a'}, Parallel (f.rename ρ) f' → Parallel (a.rename ρ) a' →
        ∃ F₁, Expr.app f' a' = F₁.rename ρ ∧ Parallel (.app f a) F₁ := by
      intro f' a' hf ha
      obtain ⟨f₁, rfl, pf⟩ := ihf hρ hf
      obtain ⟨a₁, rfl, pa⟩ := iha hρ ha
      exact ⟨.app f₁ a₁, rfl, .app pf pa⟩
    cases f with
    | lam A b =>
      simp only [Expr.rename] at h
      cases h with
      | app hf ha => exact congr_case hf ha
      | @head _ b₁' _ a₁' _ hb ha =>
        obtain ⟨a₁, rfl, pa⟩ := iha hρ ha
        have hlam : Parallel ((Expr.lam A b).rename ρ) (.lam (A.rename ρ) b₁') :=
          .lam (Parallel.refl _) hb
        obtain ⟨F₁, hF₁, pF⟩ := ihf hρ hlam
        cases pF with
        | lam pA pb =>
          simp only [Expr.rename, Expr.lam.injEq] at hF₁
          obtain ⟨_, rfl⟩ := hF₁
          exact ⟨_, Expr.instantiate_rename _ _ ρ, .head A pb pa⟩
    | var n =>
      simp only [Expr.rename] at h
      cases h with
      | app hf ha => exact congr_case hf ha
    | sort s =>
      simp only [Expr.rename] at h
      cases h with
      | app hf ha => exact congr_case hf ha
    | app g c =>
      simp only [Expr.rename] at h
      cases h with
      | app hf ha => exact congr_case hf ha
    | pi C D =>
      simp only [Expr.rename] at h
      cases h with
      | app hf ha => exact congr_case hf ha

/-! ## Free occurrences and unshifting -/

namespace Expr

/-- `Occurs k M` says that the index `k` occurs free in `M`. -/
def Occurs : Nat → Expr S → Prop
  | k, .var n => n = k
  | _, .sort _ => False
  | k, .app f a => Occurs k f ∨ Occurs k a
  | k, .lam A b => Occurs k A ∨ Occurs (k + 1) b
  | k, .pi A B => Occurs k A ∨ Occurs (k + 1) B

theorem rename_congr_on : ∀ (M : Expr S) {ρ ρ' : Nat → Nat},
    (∀ n, Occurs n M → ρ n = ρ' n) → M.rename ρ = M.rename ρ'
  | .var n, _, _, h => by simp [rename, h n rfl]
  | .sort s, _, _, _ => rfl
  | .app f a, _, _, h => by
    simp only [rename]
    rw [rename_congr_on f (fun n hn => h n (.inl hn)),
      rename_congr_on a (fun n hn => h n (.inr hn))]
  | .lam A b, ρ, ρ', h => by
    simp only [rename]
    rw [rename_congr_on A (fun n hn => h n (.inl hn)),
      rename_congr_on b (ρ := liftRen ρ) (ρ' := liftRen ρ') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [liftRen, h n (.inr hn)])]
  | .pi A B, ρ, ρ', h => by
    simp only [rename]
    rw [rename_congr_on A (fun n hn => h n (.inl hn)),
      rename_congr_on B (ρ := liftRen ρ) (ρ' := liftRen ρ') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [liftRen, h n (.inr hn)])]

theorem occurs_rename : ∀ (M : Expr S) (ρ : Nat → Nat) (k : Nat),
    Occurs k (M.rename ρ) → ∃ m, Occurs m M ∧ ρ m = k
  | .var n, ρ, k, h => ⟨n, rfl, h⟩
  | .sort s, _, _, h => h.elim
  | .app f a, ρ, k, h => by
    rcases h with h | h
    · obtain ⟨m, hm, e⟩ := occurs_rename f ρ k h; exact ⟨m, .inl hm, e⟩
    · obtain ⟨m, hm, e⟩ := occurs_rename a ρ k h; exact ⟨m, .inr hm, e⟩
  | .lam A b, ρ, k, h => by
    rcases h with h | h
    · obtain ⟨m, hm, e⟩ := occurs_rename A ρ k h; exact ⟨m, .inl hm, e⟩
    · obtain ⟨m, hm, e⟩ := occurs_rename b (liftRen ρ) (k + 1) h
      cases m with
      | zero => simp [liftRen] at e
      | succ m => exact ⟨m, .inr hm, by simpa [liftRen] using e⟩
  | .pi A B, ρ, k, h => by
    rcases h with h | h
    · obtain ⟨m, hm, e⟩ := occurs_rename A ρ k h; exact ⟨m, .inl hm, e⟩
    · obtain ⟨m, hm, e⟩ := occurs_rename B (liftRen ρ) (k + 1) h
      cases m with
      | zero => simp [liftRen] at e
      | succ m => exact ⟨m, .inr hm, by simpa [liftRen] using e⟩

theorem occurs_rename_of : ∀ (M : Expr S) (ρ : Nat → Nat) (m : Nat),
    Occurs m M → Occurs (ρ m) (M.rename ρ)
  | .var n, ρ, m, h => by simp only [Occurs] at h; subst h; rfl
  | .sort s, _, _, h => h.elim
  | .app f a, ρ, m, h => by
    rcases h with h | h
    · exact .inl (occurs_rename_of f ρ m h)
    · exact .inr (occurs_rename_of a ρ m h)
  | .lam A b, ρ, m, h => by
    rcases h with h | h
    · exact .inl (occurs_rename_of A ρ m h)
    · exact .inr (by simpa [liftRen] using occurs_rename_of b (liftRen ρ) (m + 1) h)
  | .pi A B, ρ, m, h => by
    rcases h with h | h
    · exact .inl (occurs_rename_of A ρ m h)
    · exact .inr (by simpa [liftRen] using occurs_rename_of B (liftRen ρ) (m + 1) h)

theorem not_occurs_zero_shift (N : Expr S) : ¬ Occurs 0 (N.rename Nat.succ) := by
  intro h
  obtain ⟨m, _, e⟩ := occurs_rename N Nat.succ 0 h
  exact Nat.succ_ne_zero m e

theorem unshift {M : Expr S} (h : ¬ Occurs 0 M) :
    M = (M.rename Nat.pred).rename Nat.succ := by
  rw [rename_comp]
  conv_lhs => rw [← rename_id M]
  apply rename_congr_on
  intro n hn
  cases n with
  | zero => exact absurd hn h
  | succ n => rfl

/-- Suppose `ρ` is injective and renaming `b` by the lift of `ρ` gives a shifted term.
Then `b` itself is a shifted term. -/
theorem shift_of_rename_liftRen {ρ : Nat → Nat} {b G : Expr S}
    (h : b.rename (liftRen ρ) = G.rename Nat.succ) :
    ∃ G₀ : Expr S, b = G₀.rename Nat.succ ∧ G₀.rename ρ = G := by
  have hno : ¬ Occurs 0 b := by
    intro h0
    have := occurs_rename_of b (liftRen ρ) 0 h0
    rw [h] at this
    exact not_occurs_zero_shift G (by simpa [liftRen] using this)
  refine ⟨b.rename Nat.pred, unshift hno, ?_⟩
  apply rename_injective_succ
  rw [← rename_succ_liftRen, ← unshift hno, h]

end Expr

theorem ParEta.lam_inv {A b X : Expr S} (h : ParEta (.lam A b) X) :
    (∃ A' b', X = .lam A' b' ∧ ParEta A A' ∧ ParEta b b') ∨
      (∃ F, b = .app (F.rename Nat.succ) (.var 0) ∧ ParEta F X) := by
  cases h with
  | lam hA hb => exact .inl ⟨_, _, rfl, hA, hb⟩
  | head _ hF => exact .inr ⟨_, rfl, hF⟩

theorem ParEta.rename_inv : ∀ (n : Nat) (F : Expr S), F.size < n → ∀ {ρ : Nat → Nat},
    Function.Injective ρ → ∀ {X : Expr S}, ParEta (F.rename ρ) X →
      ∃ F₁, X = F₁.rename ρ ∧ ParEta F F₁ := by
  intro n
  induction n with
  | zero => intro F hF; omega
  | succ n IH =>
  intro F hF ρ hρ X h
  cases F with
  | var k => cases h; exact ⟨_, rfl, .var k⟩
  | sort s => cases h; exact ⟨_, rfl, .sort s⟩
  | app f a =>
    simp only [Expr.size] at hF
    cases h with
    | app hf ha =>
      obtain ⟨f₁, rfl, pf⟩ := IH f (by omega) hρ hf
      obtain ⟨a₁, rfl, pa⟩ := IH a (by omega) hρ ha
      exact ⟨.app f₁ a₁, rfl, .app pf pa⟩
  | pi A B =>
    simp only [Expr.size] at hF
    cases h with
    | pi hA hB =>
      obtain ⟨A₁, rfl, pA⟩ := IH A (by omega) hρ hA
      obtain ⟨B₁, rfl, pB⟩ := IH B (by omega) (liftRen_injective hρ) hB
      exact ⟨.pi A₁ B₁, rfl, .pi pA pB⟩
  | lam A b =>
    simp only [Expr.size] at hF
    simp only [Expr.rename] at h
    rcases ParEta.lam_inv h with ⟨A', b', rfl, hA, hb⟩ | ⟨G, hbG, hG⟩
    · obtain ⟨A₁, rfl, pA⟩ := IH A (by omega) hρ hA
      obtain ⟨b₁, rfl, pb⟩ := IH b (by omega) (liftRen_injective hρ) hb
      exact ⟨.lam A₁ b₁, rfl, .lam pA pb⟩
    · cases b with
      | app b₁ b₂ =>
        simp only [Expr.rename, Expr.app.injEq] at hbG
        obtain ⟨e₁, e₂⟩ := hbG
        cases b₂ with
        | var m =>
          cases m with
          | zero =>
            obtain ⟨G₀, rfl, rfl⟩ := Expr.shift_of_rename_liftRen e₁
            simp only [Expr.size, Expr.size_rename] at hF
            obtain ⟨G₁, rfl, pG⟩ := IH G₀ (by omega) hρ hG
            exact ⟨G₁, rfl, .head A pG⟩
          | succ m => simp [Expr.rename, Expr.liftRen] at e₂
        | sort _ => simp [Expr.rename] at e₂
        | app _ _ => simp [Expr.rename] at e₂
        | lam _ _ => simp [Expr.rename] at e₂
        | pi _ _ => simp [Expr.rename] at e₂
      | var _ => simp [Expr.rename] at hbG
      | sort _ => simp [Expr.rename] at hbG
      | lam _ _ => simp [Expr.rename] at hbG
      | pi _ _ => simp [Expr.rename] at hbG

theorem ParEta.rename_inv' {ρ : Nat → Nat} (hρ : Function.Injective ρ) {F X : Expr S}
    (h : ParEta (F.rename ρ) X) : ∃ F₁, X = F₁.rename ρ ∧ ParEta F F₁ :=
  ParEta.rename_inv _ F (Nat.lt_succ_self _) hρ h

/-! ## Inversion lemmas -/

theorem ParEta.app_inv {f a X : Expr S} (h : ParEta (.app f a) X) :
    ∃ f' a', X = .app f' a' ∧ ParEta f f' ∧ ParEta a a' := by
  cases h with
  | app hf ha => exact ⟨_, _, rfl, hf, ha⟩

theorem Parallel.app_inv {f a X : Expr S} (h : Parallel (.app f a) X) :
    (∃ f' a', X = .app f' a' ∧ Parallel f f' ∧ Parallel a a') ∨
      (∃ A b b' a', f = .lam A b ∧ X = b'.instantiate a' ∧ Parallel b b' ∧ Parallel a a') := by
  cases h with
  | app hf ha => exact .inl ⟨_, _, rfl, hf, ha⟩
  | head A hb ha => exact .inr ⟨_, _, _, _, rfl, rfl, hb, ha⟩

theorem Parallel.var_inv {n : Nat} {X : Expr S} (h : Parallel (.var n) X) : X = .var n := by
  cases h; rfl

theorem Parallel.sort_inv {s : S} {X : Expr S} (h : Parallel (.sort s) X) : X = .sort s := by
  cases h; rfl

theorem ParEta.var_inv {n : Nat} {X : Expr S} (h : ParEta (.var n) X) : X = .var n := by
  cases h; rfl

theorem ParEta.sort_inv {s : S} {X : Expr S} (h : ParEta (.sort s) X) : X = .sort s := by
  cases h; rfl

/-- Inversion of a parallel β-step from the body `F x` of an η-redex, where `F` is shifted. -/
theorem Parallel.shift_app_var {F X : Expr S}
    (h : Parallel (.app (F.rename Nat.succ) (.var 0)) X) :
    (∃ F₁, X = .app (F₁.rename Nat.succ) (.var 0) ∧ Parallel F F₁) ∨
      (∃ C c c₁, F = .lam C c ∧ X = c₁ ∧ Parallel c c₁) := by
  rcases Parallel.app_inv h with ⟨f', a', rfl, hf, ha⟩ | ⟨A, b, b', a', hfe, rfl, hb, ha⟩
  · obtain ⟨F₁, rfl, pF⟩ := Parallel.rename_inv Nat.succ_injective hf
    rw [Parallel.var_inv ha]
    exact .inl ⟨F₁, rfl, pF⟩
  · cases F with
    | lam C c =>
      simp only [Expr.rename, Expr.lam.injEq] at hfe
      obtain ⟨_, rfl⟩ := hfe
      obtain ⟨c₁, rfl, pc⟩ := Parallel.rename_inv (liftRen_injective Nat.succ_injective) hb
      rw [Parallel.var_inv ha, Expr.instantiate_liftRen_succ_var]
      exact .inr ⟨C, c, c₁, rfl, rfl, pc⟩
    | var _ => simp [Expr.rename] at hfe
    | sort _ => simp [Expr.rename] at hfe
    | app _ _ => simp [Expr.rename] at hfe
    | pi _ _ => simp [Expr.rename] at hfe

/-! ## The diamond property of parallel η-reduction -/

theorem ParEta.diamond_aux : ∀ (n : Nat) (M : Expr S), M.size < n →
    ∀ {N₁ N₂ : Expr S}, ParEta M N₁ → ParEta M N₂ → ∃ P, ParEta N₁ P ∧ ParEta N₂ P := by
  intro n
  induction n with
  | zero => intro M hM; omega
  | succ n IH =>
  intro M hM N₁ N₂ h₁ h₂
  cases M with
  | var k => rw [ParEta.var_inv h₁, ParEta.var_inv h₂]; exact ⟨_, .var k, .var k⟩
  | sort s => rw [ParEta.sort_inv h₁, ParEta.sort_inv h₂]; exact ⟨_, .sort s, .sort s⟩
  | app f a =>
    simp only [Expr.size] at hM
    obtain ⟨f₁, a₁, rfl, hf₁, ha₁⟩ := ParEta.app_inv h₁
    obtain ⟨f₂, a₂, rfl, hf₂, ha₂⟩ := ParEta.app_inv h₂
    obtain ⟨Pf, e₁, e₂⟩ := IH f (by omega) hf₁ hf₂
    obtain ⟨Pa, e₃, e₄⟩ := IH a (by omega) ha₁ ha₂
    exact ⟨_, .app e₁ e₃, .app e₂ e₄⟩
  | pi A B =>
    simp only [Expr.size] at hM
    cases h₁ with
    | pi hA₁ hB₁ =>
      cases h₂ with
      | pi hA₂ hB₂ =>
        obtain ⟨PA, e₁, e₂⟩ := IH A (by omega) hA₁ hA₂
        obtain ⟨PB, e₃, e₄⟩ := IH B (by omega) hB₁ hB₂
        exact ⟨_, .pi e₁ e₃, .pi e₂ e₄⟩
  | lam A b =>
    simp only [Expr.size] at hM
    have side : ∀ {F N₁ A₂ b₂ : Expr S}, b = .app (F.rename Nat.succ) (.var 0) →
        ParEta F N₁ → ParEta b b₂ → ∃ P, ParEta N₁ P ∧ ParEta (.lam A₂ b₂) P := by
      intro F N₁ A₂ b₂ hb hF hb₂
      subst hb
      obtain ⟨X, Y, rfl, hX, hY⟩ := ParEta.app_inv hb₂
      rw [ParEta.var_inv hY]
      obtain ⟨F₂, rfl, pF₂⟩ := ParEta.rename_inv' Nat.succ_injective hX
      simp only [Expr.size, Expr.size_rename] at hM
      obtain ⟨Q, e₁, e₂⟩ := IH F (by omega) hF pF₂
      exact ⟨Q, e₁, .head _ e₂⟩
    rcases ParEta.lam_inv h₁ with ⟨A₁, b₁, rfl, hA₁, hb₁⟩ | ⟨F, hbF, hF⟩ <;>
      rcases ParEta.lam_inv h₂ with ⟨A₂, b₂, rfl, hA₂, hb₂⟩ | ⟨F', hbF', hF'⟩
    · obtain ⟨PA, e₁, e₂⟩ := IH A (by omega) hA₁ hA₂
      obtain ⟨Pb, e₃, e₄⟩ := IH b (by omega) hb₁ hb₂
      exact ⟨_, .lam e₁ e₃, .lam e₂ e₄⟩
    · obtain ⟨P, e₁, e₂⟩ := side hbF' hF' hb₁
      exact ⟨P, e₂, e₁⟩
    · exact side hbF hF hb₂
    · rw [hbF] at hbF'
      simp only [Expr.app.injEq] at hbF'
      have hFF : F = F' := Expr.rename_injective_succ hbF'.1
      subst hFF
      subst hbF
      simp only [Expr.size, Expr.size_rename] at hM
      exact IH F (by omega) hF hF'

theorem ParEta.diamond {M N₁ N₂ : Expr S} (h₁ : ParEta M N₁) (h₂ : ParEta M N₂) :
    ∃ P, ParEta N₁ P ∧ ParEta N₂ P :=
  ParEta.diamond_aux _ M (Nat.lt_succ_self _) h₁ h₂

/-! ## Parallel β-reduction and parallel η-reduction commute on erased terms -/

theorem erased_commute_aux : ∀ (n : Nat) (M : Expr S), M.size < n → Erased z M →
    ∀ {N₁ N₂ : Expr S}, Parallel M N₁ → ParEta M N₂ → ∃ P, ParEta N₁ P ∧ Parallel N₂ P := by
  intro n
  induction n with
  | zero => intro M hM; omega
  | succ n IH =>
  intro M hM hE N₁ N₂ h₁ h₂
  cases M with
  | var k => rw [Parallel.var_inv h₁, ParEta.var_inv h₂]; exact ⟨_, .var k, .var k⟩
  | sort s => rw [Parallel.sort_inv h₁, ParEta.sort_inv h₂]; exact ⟨_, .sort s, .sort s⟩
  | pi A B =>
    simp only [Expr.size] at hM
    obtain ⟨eA, eB⟩ := hE.pi
    cases h₁ with
    | pi pA pB =>
      cases h₂ with
      | pi hA hB =>
        obtain ⟨QA, e₁, e₂⟩ := IH A (by omega) eA pA hA
        obtain ⟨QB, e₃, e₄⟩ := IH B (by omega) eB pB hB
        exact ⟨_, .pi e₁ e₃, .pi e₂ e₄⟩
  | lam A b =>
    simp only [Expr.size] at hM
    obtain ⟨rfl, eb⟩ := hE.lam
    cases h₁ with
    | lam pA pb =>
      rw [Parallel.sort_inv pA]
      rcases ParEta.lam_inv h₂ with ⟨A₂, b₂, rfl, hA₂, hb₂⟩ | ⟨F, rfl, hF⟩
      · rw [ParEta.sort_inv hA₂]
        obtain ⟨Q, e₁, e₂⟩ := IH b (by omega) eb pb hb₂
        exact ⟨_, .lam (.sort z) e₁, .lam (.sort z) e₂⟩
      · have eF : Erased z F := by
          have h := eb.app.1
          unfold Erased at h ⊢
          rw [Expr.erase_rename] at h
          exact Expr.rename_injective_succ h
        simp only [Expr.size, Expr.size_rename] at hM
        rcases Parallel.shift_app_var pb with ⟨F₁, rfl, pF⟩ | ⟨C, c, c₁, rfl, rfl, pc⟩
        · obtain ⟨Q, e₁, e₂⟩ := IH F (by omega) eF pF hF
          exact ⟨Q, .head _ e₁, e₂⟩
        · obtain ⟨rfl, _⟩ := eF.lam
          have hp := Parallel.lam (Parallel.sort z) pc
          obtain ⟨Q, e₁, e₂⟩ := IH _ (by omega) eF hp hF
          exact ⟨Q, e₁, e₂⟩
  | app f a =>
    simp only [Expr.size] at hM
    obtain ⟨ef, ea⟩ := hE.app
    obtain ⟨f₂, a₂, rfl, hf₂, ha₂⟩ := ParEta.app_inv h₂
    rcases Parallel.app_inv h₁ with ⟨f₁, a₁, rfl, pf, pa⟩ | ⟨A, b, b₁, a₁, rfl, rfl, pb, pa⟩
    · obtain ⟨Qf, e₁, e₂⟩ := IH f (by omega) ef pf hf₂
      obtain ⟨Qa, e₃, e₄⟩ := IH a (by omega) ea pa ha₂
      exact ⟨_, .app e₁ e₃, .app e₂ e₄⟩
    · obtain ⟨rfl, eb⟩ := ef.lam
      simp only [Expr.size] at hM
      obtain ⟨Qa, e₃, e₄⟩ := IH a (by omega) ea pa ha₂
      rcases ParEta.lam_inv hf₂ with ⟨A₂, b₂, rfl, hA₂, hb₂⟩ | ⟨G, rfl, hG⟩
      · obtain ⟨Qb, e₁, e₂⟩ := IH b (by omega) eb pb hb₂
        exact ⟨_, e₁.instantiate e₃, .head A₂ e₂ e₄⟩
      · have eG : Erased z G := by
          have h := eb.app.1
          unfold Erased at h ⊢
          rw [Expr.erase_rename] at h
          exact Expr.rename_injective_succ h
        simp only [Expr.size, Expr.size_rename] at hM
        rcases Parallel.shift_app_var pb with ⟨G₁, rfl, pG⟩ | ⟨C, c, c₁, rfl, rfl, pc⟩
        · obtain ⟨QG, e₁, e₂⟩ := IH G (by omega) eG pG hG
          rw [Expr.instantiate_app_shift]
          exact ⟨_, .app e₁ e₃, .app e₂ e₄⟩
        · obtain ⟨rfl, ec⟩ := eG.lam
          have hp := Parallel.head (.sort z) pc pa
          have he : ParEta (.app (.lam (.sort z) c) a) (.app f₂ a₂) := .app hG ha₂
          have hsize : (Expr.app (.lam (.sort z) c) a).size < n := by
            simp only [Expr.size] at hM ⊢; omega
          exact IH _ hsize (Erased.mk_app eG ea) hp he

theorem erased_commute {M N₁ N₂ : Expr S} (hE : Erased z M) (h₁ : Parallel M N₁)
    (h₂ : ParEta M N₂) : ∃ P, ParEta N₁ P ∧ Parallel N₂ P :=
  erased_commute_aux z _ M (Nat.lt_succ_self _) hE h₁ h₂

/-! ## Confluence on erased terms -/

/-- One parallel β-step or one parallel η-step from an erased term. -/
def StepE (M N : Expr S) : Prop := Erased z M ∧ (Parallel M N ∨ ParEta M N)

theorem StepE.erased {M N : Expr S} (h : StepE z M N) : Erased z N := by
  rcases h with ⟨hM, h | h⟩
  · exact h.erased z hM
  · exact h.erased z hM

theorem StepE.diamond {a b c : Expr S} (h₁ : StepE z a b) (h₂ : StepE z a c) :
    ∃ d, StepE z b d ∧ StepE z c d := by
  obtain ⟨ha, hb⟩ := h₁
  obtain ⟨_, hc⟩ := h₂
  have eb : Erased z b := StepE.erased z ⟨ha, hb⟩
  have ec : Erased z c := StepE.erased z ⟨ha, hc⟩
  rcases hb with pb | pb <;> rcases hc with pc | pc
  · obtain ⟨d, e₁, e₂⟩ := Parallel.diamond pb pc
    exact ⟨d, ⟨eb, .inl e₁⟩, ⟨ec, .inl e₂⟩⟩
  · obtain ⟨d, e₁, e₂⟩ := erased_commute z ha pb pc
    exact ⟨d, ⟨eb, .inr e₁⟩, ⟨ec, .inl e₂⟩⟩
  · obtain ⟨d, e₁, e₂⟩ := erased_commute z ha pc pb
    exact ⟨d, ⟨eb, .inl e₂⟩, ⟨ec, .inr e₁⟩⟩
  · obtain ⟨d, e₁, e₂⟩ := ParEta.diamond pb pc
    exact ⟨d, ⟨eb, .inr e₁⟩, ⟨ec, .inr e₂⟩⟩

theorem StepE.confluent {a b c : Expr S} (hb : ReflTransGen (StepE z) a b)
    (hc : ReflTransGen (StepE z) a c) : Join (ReflTransGen (StepE z)) b c := by
  refine Relation.church_rosser (fun a b c h₁ h₂ => ?_) hb hc
  obtain ⟨d, e₁, e₂⟩ := StepE.diamond z h₁ h₂
  exact ⟨d, .single e₁, .single e₂⟩

theorem StepE.join_of_eqvGen {a b : Expr S} (h : EqvGen (StepE z) a b) :
    Join (ReflTransGen (StepE z)) a b := by
  induction h with
  | rel a b h => exact ⟨b, .single h, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
    obtain ⟨c, ha, hb⟩ := ih
    exact ⟨c, hb, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
    obtain ⟨d, ha, hb⟩ := ih₁
    obtain ⟨e, hb', hc⟩ := ih₂
    obtain ⟨f, hd, he⟩ := StepE.confluent z hb hb'
    exact ⟨f, ha.trans hd, hc.trans he⟩

/-! ## Geuvers's Domain Lemma -/

theorem eqv_lift {c : Expr S → Expr S} (hc : ∀ {x y}, BetaEta x y → BetaEta (c x) (c y))
    {M N : Expr S} (h : EqvGen BetaEta M N) : EqvGen BetaEta (c M) (c N) := by
  induction h with
  | rel a b h => exact .rel _ _ (hc h)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Two abstractions with the same body are βη-convertible, whatever their domains are.
This is Lemma 4.4.16 of Geuvers's thesis. -/
theorem domain_core (A A' c : Expr S) : EqvGen BetaEta (.lam A c) (.lam A' c) := by
  have hη : Eta (.lam A' (.app ((Expr.lam A c).rename Nat.succ) (.var 0))) (.lam A c) :=
    Eta.head A' (.lam A c)
  have hβ : Beta (.lam A' (.app ((Expr.lam A c).rename Nat.succ) (.var 0))) (.lam A' c) := by
    have := Beta.lam_body (A := A')
      (Beta.head (A.rename Nat.succ) (c.rename (Expr.liftRen Nat.succ)) (.var 0))
    rwa [Expr.instantiate_liftRen_succ_var] at this
  exact .trans _ _ _ (.symm _ _ (.rel _ _ (.inr hη))) (.rel _ _ (.inl hβ))

/-- **Domain Lemma.** Every term is βη-convertible to its erasure. -/
theorem convertsBE_erase (M : Expr S) : EqvGen BetaEta M (M.erase z) := by
  induction M with
  | var n => exact .refl _
  | sort s => exact .refl _
  | app f a ihf iha =>
    exact .trans _ _ _
      (eqv_lift (c := fun x => .app x a) (fun h => h.elim (fun h => .inl (.app_left h))
        (fun h => .inr (.app_left h))) ihf)
      (eqv_lift (c := fun x => .app (f.erase z) x) (fun h => h.elim
        (fun h => .inl (.app_right h)) (fun h => .inr (.app_right h))) iha)
  | pi A B ihA ihB =>
    exact .trans _ _ _
      (eqv_lift (c := fun x => .pi x B) (fun h => h.elim (fun h => .inl (.pi_domain h))
        (fun h => .inr (.pi_domain h))) ihA)
      (eqv_lift (c := fun x => .pi (A.erase z) x) (fun h => h.elim
        (fun h => .inl (.pi_body h)) (fun h => .inr (.pi_body h))) ihB)
  | lam A b ihA ihb =>
    exact .trans _ _ _
      (eqv_lift (c := fun x => .lam A x) (fun h => h.elim (fun h => .inl (.lam_body h))
        (fun h => .inr (.lam_body h))) ihb)
      (domain_core A (.sort z) (b.erase z))

/-! ## βη-conversion through confluence on erased terms -/

theorem BetaEta.stepE_erase {M N : Expr S} (h : BetaEta M N) :
    StepE z (M.erase z) (N.erase z) ∨ M.erase z = N.erase z := by
  rcases h with hb | he
  · rcases hb.erase z with h | h
    · exact .inl ⟨Erased.erase_erased M, .inl (Parallel.of_beta h)⟩
    · exact .inr h
  · rcases he.erase z with h | h
    · exact .inl ⟨Erased.erase_erased M, .inr (ParEta.of_eta h)⟩
    · exact .inr h

theorem eqvGen_stepE_erase {M N : Expr S} (h : EqvGen BetaEta M N) :
    EqvGen (StepE z) (M.erase z) (N.erase z) := by
  induction h with
  | rel a b h =>
    rcases BetaEta.stepE_erase z h with h | h
    · exact .rel _ _ h
    · rw [h]; exact .refl _
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem reduces_convertsBE {M N : Expr S} (h : Reduces M N) : EqvGen BetaEta M N := by
  induction h with
  | refl => exact .refl _
  | tail _ hb ih => exact .trans _ _ _ ih (.rel _ _ (.inl hb))

theorem etaStar_convertsBE {M N : Expr S} (h : ReflTransGen Eta M N) : EqvGen BetaEta M N := by
  induction h with
  | refl => exact .refl _
  | tail _ he ih => exact .trans _ _ _ ih (.rel _ _ (.inr he))

theorem StepE.convertsBE {M N : Expr S} (h : StepE z M N) : EqvGen BetaEta M N := by
  rcases h with ⟨_, h | h⟩
  · exact reduces_convertsBE (Parallel.reduces h)
  · exact etaStar_convertsBE (ParEta.eta_star h)

theorem stepE_star_convertsBE {M N : Expr S} (h : ReflTransGen (StepE z) M N) :
    EqvGen BetaEta M N := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .trans _ _ _ ih (StepE.convertsBE z hs)

/-- If two terms are βη-convertible, then their erasures have a common reduct among erased terms. -/
theorem convertsBE_join {M N : Expr S} (h : EqvGen BetaEta M N) :
    Join (ReflTransGen (StepE z)) (M.erase z) (N.erase z) :=
  StepE.join_of_eqvGen z (eqvGen_stepE_erase z h)

theorem stepE_star_pi_inv {X Y W : Expr S} (h : ReflTransGen (StepE z) (.pi X Y) W) :
    ∃ X' Y', W = .pi X' Y' ∧ ReflTransGen (StepE z) X X' ∧ ReflTransGen (StepE z) Y Y' := by
  induction h with
  | refl => exact ⟨X, Y, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨X', Y', rfl, hX, hY⟩ := ih
    obtain ⟨hE, hs⟩ := hs
    obtain ⟨eX, eY⟩ := hE.pi
    rcases hs with hs | hs
    · cases hs with
      | pi pA pB => exact ⟨_, _, rfl, hX.tail ⟨eX, .inl pA⟩, hY.tail ⟨eY, .inl pB⟩⟩
    · cases hs with
      | pi pA pB => exact ⟨_, _, rfl, hX.tail ⟨eX, .inr pA⟩, hY.tail ⟨eY, .inr pB⟩⟩

theorem stepE_star_sort_inv {s : S} {W : Expr S} (h : ReflTransGen (StepE z) (.sort s) W) :
    W = .sort s := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    rcases hs with ⟨_, hs | hs⟩
    · exact Parallel.sort_inv hs
    · exact ParEta.sort_inv hs

/-- **Injectivity of products** for βη-conversion on annotated terms. -/
theorem convertsBE_pi_inj (z : S) {A B A' B' : Expr S}
    (h : EqvGen BetaEta (.pi A B) (.pi A' B')) :
    EqvGen BetaEta A A' ∧ EqvGen BetaEta B B' := by
  obtain ⟨P, h₁, h₂⟩ := convertsBE_join z h
  obtain ⟨X, Y, rfl, hX, hY⟩ := stepE_star_pi_inv z h₁
  obtain ⟨X', Y', he, hX', hY'⟩ := stepE_star_pi_inv z h₂
  simp only [Expr.pi.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨?_, ?_⟩
  · exact .trans _ _ _ (convertsBE_erase z A) (.trans _ _ _ (stepE_star_convertsBE z hX)
      (.trans _ _ _ (.symm _ _ (stepE_star_convertsBE z hX')) (.symm _ _ (convertsBE_erase z A'))))
  · exact .trans _ _ _ (convertsBE_erase z B) (.trans _ _ _ (stepE_star_convertsBE z hY)
      (.trans _ _ _ (.symm _ _ (stepE_star_convertsBE z hY')) (.symm _ _ (convertsBE_erase z B'))))

theorem convertsBE_sort_inj {s t : S} (h : EqvGen BetaEta (Expr.sort s) (.sort t)) : s = t := by
  obtain ⟨P, h₁, h₂⟩ := convertsBE_join s h
  have e₁ := stepE_star_sort_inv s h₁
  have e₂ := stepE_star_sort_inv s h₂
  rw [e₁] at e₂
  simpa using e₂

theorem convertsBE_pi_not_sort {A B : Expr S} {s : S}
    (h : EqvGen BetaEta (.pi A B) (.sort s)) : False := by
  let z := s
  obtain ⟨P, h₁, h₂⟩ := convertsBE_join z h
  obtain ⟨X, Y, rfl, _, _⟩ := stepE_star_pi_inv z h₁
  have := stepE_star_sort_inv z h₂
  cases this

end PureTypeSystem
