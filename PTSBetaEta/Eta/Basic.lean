module

public import PTSBetaEta.Eta.Konig

@[expose] public section

/-!
# Strong normalization transfers from β to βη

This file defines η-reduction `λx:A. F x → F`, where `x` is not free in `F`, on annotated PTS pseudo-terms.
The main result is that a strongly β-normalizing term is also strongly βη-normalizing.
No typing is involved.

The proof first shows that η-steps can be moved after β-steps (η-postponement).
The induction measure combines the bound on the length of β-reductions from `PTSBetaEta.Eta.Konig` with the size of the term, which every η-step decreases.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

/-- One-step η-reduction, closed under all term constructors.
The rule `head` takes `λx:A. F x` to `F` when `x` is not free in `F`.
In de Bruijn form, this condition says that the function part of the body is `F` with its free indices shifted up by one. -/
inductive Eta : Expr S → Expr S → Prop
  | head (A F : Expr S) : Eta (.lam A (.app (F.rename Nat.succ) (.var 0))) F
  | app_left {f f' a} : Eta f f' → Eta (.app f a) (.app f' a)
  | app_right {f a a'} : Eta a a' → Eta (.app f a) (.app f a')
  | lam_domain {A A' b} : Eta A A' → Eta (.lam A b) (.lam A' b)
  | lam_body {A b b'} : Eta b b' → Eta (.lam A b) (.lam A b')
  | pi_domain {A A' B} : Eta A A' → Eta (.pi A B) (.pi A' B)
  | pi_body {A B B'} : Eta B B' → Eta (.pi A B) (.pi A B')

def BetaEta (M N : Expr S) : Prop := Beta M N ∨ Eta M N

def StronglyNormalizingBetaEta (M : Expr S) : Prop :=
  Acc (fun N M : Expr S => BetaEta M N) M

namespace Expr

def size : Expr S → Nat
  | .var _ => 1
  | .sort _ => 1
  | .app f a => f.size + a.size + 1
  | .lam A b => A.size + b.size + 1
  | .pi A B => A.size + B.size + 1

theorem size_rename (M : Expr S) (ρ : Nat → Nat) : (M.rename ρ).size = M.size := by
  induction M generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename, size, ihf, iha]
  | lam A b ihA ihb => simp [rename, size, ihA, ihb]
  | pi A B ihA ihB => simp [rename, size, ihA, ihB]

theorem rename_succ_instantiate (F a : Expr S) : (F.rename Nat.succ).instantiate a = F := by
  unfold instantiate
  rw [subst_rename]
  exact subst_var F

theorem rename_succ_liftRen (F : Expr S) (ρ : Nat → Nat) :
    (F.rename Nat.succ).rename (liftRen ρ) = (F.rename ρ).rename Nat.succ := by
  rw [rename_comp, rename_comp]
  rfl

theorem rename_succ_liftSub (F : Expr S) (σ : Nat → Expr S) :
    (F.rename Nat.succ).subst (liftSub σ) = (F.subst σ).rename Nat.succ := by
  rw [subst_rename, rename_subst]
  rfl

end Expr

namespace Eta

variable {M N : Expr S}

theorem size_lt (h : Eta M N) : N.size < M.size := by
  induction h with
  | head A F => simp only [Expr.size, Expr.size_rename]; omega
  | app_left _ ih => simp only [Expr.size]; omega
  | app_right _ ih => simp only [Expr.size]; omega
  | lam_domain _ ih => simp only [Expr.size]; omega
  | lam_body _ ih => simp only [Expr.size]; omega
  | pi_domain _ ih => simp only [Expr.size]; omega
  | pi_body _ ih => simp only [Expr.size]; omega

theorem rename (h : Eta M N) (ρ : Nat → Nat) : Eta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head A F =>
    simp only [Expr.rename, Expr.liftRen, Expr.rename_succ_liftRen]
    exact .head _ _
  | app_left _ ih => exact .app_left (ih ρ)
  | app_right _ ih => exact .app_right (ih ρ)
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftRen ρ))
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftRen ρ))

theorem subst (h : Eta M N) (σ : Nat → Expr S) : Eta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head A F =>
    simp only [Expr.subst, Expr.liftSub_zero, Expr.rename_succ_liftSub]
    exact .head _ _
  | app_left _ ih => exact .app_left (ih σ)
  | app_right _ ih => exact .app_right (ih σ)
  | lam_domain _ ih => exact .lam_domain (ih σ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftSub σ))
  | pi_domain _ ih => exact .pi_domain (ih σ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftSub σ))

end Eta

/-- If each `σ n` reduces to `τ n` by η-steps, then `M.subst σ` reduces to `M.subst τ` by η-steps.
The number of steps may grow, because a variable can occur several times in `M`. -/
theorem eta_star_subst_pointwise (M : Expr S) {σ τ : Nat → Expr S}
    (h : ∀ n, ReflTransGen Eta (σ n) (τ n)) :
    ReflTransGen Eta (M.subst σ) (M.subst τ) := by
  induction M generalizing σ τ with
  | var n => exact h n
  | sort s => exact .refl
  | app f a ihf iha =>
    exact ((ihf h).lift (fun x => Expr.app x (a.subst σ)) fun _ _ e => Eta.app_left e).trans
      ((iha h).lift (fun x => Expr.app (f.subst τ) x) fun _ _ e => Eta.app_right e)
  | lam A b ihA ihb =>
    have h' : ∀ n, ReflTransGen Eta (Expr.liftSub σ n) (Expr.liftSub τ n) := by
      intro n
      cases n with
      | zero => exact .refl
      | succ n => exact (h n).lift (Expr.rename Nat.succ) fun _ _ e => e.rename _
    exact ((ihA h).lift (fun x => Expr.lam x (b.subst (Expr.liftSub σ))) fun _ _ e => Eta.lam_domain e).trans
      ((ihb h').lift (fun x => Expr.lam (A.subst τ) x) fun _ _ e => Eta.lam_body e)
  | pi A B ihA ihB =>
    have h' : ∀ n, ReflTransGen Eta (Expr.liftSub σ n) (Expr.liftSub τ n) := by
      intro n
      cases n with
      | zero => exact .refl
      | succ n => exact (h n).lift (Expr.rename Nat.succ) fun _ _ e => e.rename _
    exact ((ihA h).lift (fun x => Expr.pi x (B.subst (Expr.liftSub σ))) fun _ _ e => Eta.pi_domain e).trans
      ((ihB h').lift (fun x => Expr.pi (A.subst τ) x) fun _ _ e => Eta.pi_body e)

theorem eta_instantiate_arg (b : Expr S) {a a' : Expr S} (h : Eta a a') :
    ReflTransGen Eta (b.instantiate a) (b.instantiate a') := by
  apply eta_star_subst_pointwise
  intro n
  cases n with
  | zero => exact .single h
  | succ n => exact .refl

namespace Steps

theorem single {M N : Expr S} (h : Beta M N) : Steps 1 M N := .step h (.refl N)

theorem map {c : Expr S → Expr S} (hc : ∀ {x y}, Beta x y → Beta (c x) (c y)) :
    ∀ {k : Nat} {x y : Expr S}, Steps k x y → Steps k (c x) (c y)
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step h s => .step (hc h) (map hc s)

theorem trans : ∀ {a b : Nat} {M N P : Expr S}, Steps a M N → Steps b N P → Steps (a + b) M P
  | _, _, _, _, _, .refl _, t => by simpa using t
  | _, b, _, _, _, @Steps.step _ k _ _ _ h s, t => by
    have e : k + 1 + b = k + b + 1 := by omega
    rw [e]
    exact .step h (trans s t)

end Steps

/-- **η-postponement for one pair of steps.**
An η-step followed by a β-step can be replaced by at least one β-step followed by η-steps. -/
theorem postpone {M N L : Expr S} (he : Eta M N) (hb : Beta N L) :
    ∃ j, 0 < j ∧ ∃ L', Steps j M L' ∧ ReflTransGen Eta L' L := by
  induction he generalizing L with
  | head A F =>
    exact ⟨1, by omega, _, .single (.lam_body (.app_left (hb.rename Nat.succ))), .single (.head A L)⟩
  | @app_left f f' a hf ih =>
    cases hb with
    | head B b _ =>
      cases hf with
      | head A F =>
        refine ⟨2, by omega, b.instantiate a, .step (.head _ _ _) ?_, .refl⟩
        have e : (Expr.app ((Expr.lam B b).rename Nat.succ) (.var 0)).instantiate a =
            .app (.lam B b) a := by
          change Expr.app (((Expr.lam B b).rename Nat.succ).instantiate a) a = _
          rw [Expr.rename_succ_instantiate]
        rw [e]
        exact .single (.head _ _ _)
      | lam_domain _ => exact ⟨1, by omega, _, .single (.head _ _ _), .refl⟩
      | lam_body hbody => exact ⟨1, by omega, _, .single (.head _ _ _), .single (hbody.subst _)⟩
    | app_left hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .app x a) (fun h => .app_left h),
        hη.lift (fun x => Expr.app x a) fun _ _ e => Eta.app_left e⟩
    | app_right hb' => exact ⟨1, by omega, _, .single (.app_right hb'), .single (.app_left hf)⟩
  | @app_right f a a' ha ih =>
    cases hb with
    | head B b _ => exact ⟨1, by omega, _, .single (.head _ _ _), eta_instantiate_arg b ha⟩
    | app_left hb' => exact ⟨1, by omega, _, .single (.app_left hb'), .single (.app_right ha)⟩
    | app_right hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .app f x) (fun h => .app_right h),
        hη.lift (fun x => Expr.app f x) fun _ _ e => Eta.app_right e⟩
  | @lam_domain A A' b hA ih =>
    cases hb with
    | lam_domain hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .lam x b) (fun h => .lam_domain h),
        hη.lift (fun x => Expr.lam x b) fun _ _ e => Eta.lam_domain e⟩
    | lam_body hb' => exact ⟨1, by omega, _, .single (.lam_body hb'), .single (.lam_domain hA)⟩
  | @lam_body A b b' hbody ih =>
    cases hb with
    | lam_domain hb' => exact ⟨1, by omega, _, .single (.lam_domain hb'), .single (.lam_body hbody)⟩
    | lam_body hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .lam A x) (fun h => .lam_body h),
        hη.lift (fun x => Expr.lam A x) fun _ _ e => Eta.lam_body e⟩
  | @pi_domain A A' B hA ih =>
    cases hb with
    | pi_domain hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .pi x B) (fun h => .pi_domain h),
        hη.lift (fun x => Expr.pi x B) fun _ _ e => Eta.pi_domain e⟩
    | pi_body hb' => exact ⟨1, by omega, _, .single (.pi_body hb'), .single (.pi_domain hA)⟩
  | @pi_body A B B' hB ih =>
    cases hb with
    | pi_domain hb' => exact ⟨1, by omega, _, .single (.pi_domain hb'), .single (.pi_body hB)⟩
    | pi_body hb' =>
      obtain ⟨j, hj, L', hs, hη⟩ := ih hb'
      exact ⟨j, hj, _, hs.map (c := fun x => .pi A x) (fun h => .pi_body h),
        hη.lift (fun x => Expr.pi A x) fun _ _ e => Eta.pi_body e⟩

theorem BoundedBy.of_steps {M Y : Expr S} {n j : Nat} (h : BoundedBy M n) (s : Steps j M Y) :
    j ≤ n ∧ BoundedBy Y (n - j) := by
  refine ⟨h j Y s, fun k P t => ?_⟩
  have := h (j + k) P (s.trans t)
  omega

/-- Postponement for whole sequences, proved by strong induction on the bound on β-reductions.
Part (1) says that η-steps followed by one β-step can be replaced by at least one β-step followed by η-steps.
Part (2) says that η-steps followed by `k` β-steps can be replaced by at least `k` β-steps followed by η-steps. -/
theorem lift_aux (n : Nat) : ∀ M : Expr S, BoundedBy M n →
    (∀ N N₁, ReflTransGen Eta M N → Beta N N₁ →
      ∃ j, 0 < j ∧ ∃ M₁, Steps j M M₁ ∧ ReflTransGen Eta M₁ N₁) ∧
    (∀ N k P, ReflTransGen Eta M N → Steps k N P →
      ∃ j, k ≤ j ∧ ∃ M', Steps j M M' ∧ ReflTransGen Eta M' P) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro M hM
  have D : ∀ N N₁, ReflTransGen Eta M N → Beta N N₁ →
      ∃ j, 0 < j ∧ ∃ M₁, Steps j M M₁ ∧ ReflTransGen Eta M₁ N₁ := by
    intro N N₁ hN hb
    induction hN generalizing N₁ with
    | refl => exact ⟨1, by omega, N₁, .single hb, .refl⟩
    | @tail N' N _ he ih =>
      obtain ⟨j, hj, X, hX, hXN⟩ := postpone he hb
      cases hX with
      | refl => omega
      | @step k _ X₁ _ hb₁ hrest =>
        obtain ⟨j₁, hj₁, Y₁, hY₁, hY₁X₁⟩ := ih X₁ hb₁
        obtain ⟨hle, hbd⟩ := hM.of_steps hY₁
        obtain ⟨_, E⟩ := IH (n - j₁) (by omega) Y₁ hbd
        obtain ⟨j₂, hj₂, M', hM', hM'X⟩ := E X₁ k X hY₁X₁ hrest
        exact ⟨j₁ + j₂, by omega, M', hY₁.trans hM', hM'X.trans hXN⟩
  refine ⟨D, fun N k P hN hs => ?_⟩
  cases hs with
  | refl => exact ⟨0, le_rfl, M, .refl _, hN⟩
  | @step k _ N₁ _ hb hrest =>
    obtain ⟨j₁, hj₁, M₁, hM₁, hM₁N₁⟩ := D N N₁ hN hb
    obtain ⟨hle, hbd⟩ := hM.of_steps hM₁
    obtain ⟨_, E⟩ := IH (n - j₁) (by omega) M₁ hbd
    obtain ⟨j₂, hj₂, M', hM', hM'P⟩ := E N₁ k P hM₁N₁ hrest
    exact ⟨j₁ + j₂, by omega, M', hM₁.trans hM', hM'P⟩

/-- An η-step never makes the longest β-reduction from a term longer. -/
theorem BoundedBy.of_eta {M N : Expr S} {n : Nat} (hM : BoundedBy M n) (he : Eta M N) :
    BoundedBy N n := by
  intro k P hs
  obtain ⟨_, E⟩ := lift_aux n M hM
  obtain ⟨j, hkj, M', hM', _⟩ := E N k P (.single he) hs
  exact hkj.trans (hM j M' hM')

theorem stronglyNormalizingBetaEta_of_bounded (n : Nat) :
    ∀ M : Expr S, BoundedBy M n → StronglyNormalizingBetaEta M := by
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  suffices h : ∀ s (M : Expr S), M.size = s → BoundedBy M n → StronglyNormalizingBetaEta M from
    fun M => h _ M rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IHs =>
  intro M hs hM
  refine Acc.intro M fun N hN => ?_
  rcases hN with hb | he
  · obtain ⟨hle, hbd⟩ := hM.of_steps (Steps.single hb)
    exact IHn (n - 1) (by omega) N hbd
  · exact IHs N.size (hs ▸ he.size_lt) N rfl (hM.of_eta he)

/-- **Strong β-normalization implies strong βη-normalization** for annotated pseudo-terms. -/
theorem StronglyNormalizing.betaEta {M : Expr S} (h : StronglyNormalizing M) :
    StronglyNormalizingBetaEta M := by
  obtain ⟨n, hn⟩ := h.bounded
  exact stronglyNormalizingBetaEta_of_bounded n M hn

theorem StronglyNormalizingBetaEta.beta {M : Expr S} (h : StronglyNormalizingBetaEta M) :
    StronglyNormalizing M := by
  induction h with
  | intro M _ ih => exact Acc.intro M fun N hb => ih N (Or.inl hb)

theorem stronglyNormalizing_iff_betaEta {M : Expr S} :
    StronglyNormalizing M ↔ StronglyNormalizingBetaEta M :=
  ⟨StronglyNormalizing.betaEta, StronglyNormalizingBetaEta.beta⟩

end PureTypeSystem
