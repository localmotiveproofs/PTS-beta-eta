module

public import PTSBetaEta.Normalization.Base

@[expose] public section

/-!
# Keys for typing with βη-conversion

The key `M.knf` is the βη-normal form of the domain erasure of `M`, in which every λ-domain is replaced by a fixed sort `dz`.
βη-reduction is confluent on erased terms, so keys are well defined.
Every term is βη-convertible to its erasure.
Hence two terms whose erasures are weakly βη-normalizing have the same key exactly when they are βη-convertible.
This needs neither typing nor a faithfulness argument.

`KConverts` is βη-conversion of erasures, and `KNormal` means erased and βη-normal.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

/-! ### Facts about βη-reduction on annotated and erased terms -/

theorem Eta.erased' (z : S) {M N : Expr S} (h : Eta M N) (hM : Erased z M) : Erased z N :=
  (ParEta.of_eta h).erased z hM

theorem BetaEta.erased (z : S) {M N : Expr S} (h : BetaEta M N) (hM : Erased z M) :
    Erased z N := by
  rcases h with h | h
  · exact Beta.erased z h hM
  · exact h.erased' z hM

theorem betaEta_star_erased (z : S) {M N : Expr S} (h : ReflTransGen BetaEta M N)
    (hM : Erased z M) : Erased z N := by
  induction h with
  | refl => exact hM
  | tail _ hs ih => exact hs.erased z ih

theorem betaEta_star_convertsBE {M N : Expr S} (h : ReflTransGen BetaEta M N) :
    ConvertsBE M N := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .trans _ _ _ ih (.rel _ _ hs)

theorem reduces_betaEta {M N : Expr S} (h : Reduces M N) : ReflTransGen BetaEta M N := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.inl hs)

theorem etaStar_betaEta {M N : Expr S} (h : ReflTransGen Eta M N) : ReflTransGen BetaEta M N := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.inr hs)

theorem stepE_star_betaEta (z : S) {M N : Expr S} (h : ReflTransGen (StepE z) M N) :
    ReflTransGen BetaEta M N := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with ⟨_, hs | hs⟩
    · exact ih.trans (reduces_betaEta hs.reduces)
    · exact ih.trans (etaStar_betaEta hs.eta_star)

theorem NormalBE.star_eq {M N : Expr S} (h : NormalBE M) (hr : ReflTransGen BetaEta M N) :
    N = M := by
  rcases hr.cases_head with e | ⟨c, hc, _⟩
  · exact e.symm
  · exact (h c hc).elim

/-- η-reduction preserves β-normality. -/
theorem Normal.of_eta {X Y : Expr S} (hX : Normal X) (h : Eta X Y) : Normal Y := by
  intro Z hZ
  obtain ⟨j, hj, L, hs, _⟩ := postpone h hZ
  cases hs with
  | refl => omega
  | step hb _ => exact hX _ hb

theorem Normal.of_eta_star {X Y : Expr S} (hX : Normal X) (h : ReflTransGen Eta X Y) :
    Normal Y := by
  induction h with
  | refl => exact hX
  | tail _ hs ih => exact ih.of_eta hs

theorem eta_normal_exists_aux : ∀ (n : Nat) (X : Expr S), X.size < n →
    ∃ Y, ReflTransGen Eta X Y ∧ ∀ Z, ¬ Eta Y Z := by
  intro n
  induction n with
  | zero => intro X hX; omega
  | succ n ih =>
    intro X hX
    by_cases h : ∃ Z, Eta X Z
    · obtain ⟨Z, hZ⟩ := h
      obtain ⟨Y, hY, hn⟩ := ih Z (by have := hZ.size_lt; omega)
      exact ⟨Y, .head hZ hY, hn⟩
    · exact ⟨X, .refl, fun Z hZ => h ⟨Z, hZ⟩⟩

theorem eta_normal_exists (X : Expr S) : ∃ Y, ReflTransGen Eta X Y ∧ ∀ Z, ¬ Eta Y Z :=
  eta_normal_exists_aux _ X (Nat.lt_succ_self _)

/-- For any renaming, an η-step of a renamed term comes from an η-step of the original term. -/
theorem Eta.rename_inv : ∀ (M : Expr S) {ρ : Nat → Nat} {N : Expr S}, Eta (M.rename ρ) N →
    ∃ M', Eta M M' ∧ N = M'.rename ρ := by
  intro M
  induction M with
  | var n => intro ρ N h; cases h
  | sort s => intro ρ N h; cases h
  | app f a ihf iha =>
    intro ρ N h
    generalize hX : (Expr.app f a).rename ρ = X at h
    cases h with
    | head A F => simp [Expr.rename] at hX
    | @app_left f₁ f₁' a₁ h' =>
      simp only [Expr.rename, Expr.app.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨f', hf', rfl⟩ := ihf h'
      exact ⟨.app f' a, .app_left hf', rfl⟩
    | @app_right f₁ a₁ a₁' h' =>
      simp only [Expr.rename, Expr.app.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨a', ha', rfl⟩ := iha h'
      exact ⟨.app f a', .app_right ha', rfl⟩
    | lam_domain _ => simp [Expr.rename] at hX
    | lam_body _ => simp [Expr.rename] at hX
    | pi_domain _ => simp [Expr.rename] at hX
    | pi_body _ => simp [Expr.rename] at hX
  | lam A b ihA ihb =>
    intro ρ N h
    generalize hX : (Expr.lam A b).rename ρ = X at h
    cases h with
    | head A' F =>
      simp only [Expr.rename, Expr.lam.injEq] at hX
      obtain ⟨_, hb⟩ := hX
      cases b with
      | app b₁ b₂ =>
        simp only [Expr.rename, Expr.app.injEq] at hb
        obtain ⟨e₁, e₂⟩ := hb
        cases b₂ with
        | var m =>
          cases m with
          | zero =>
            obtain ⟨G₀, rfl, rfl⟩ := Expr.shift_of_rename_liftRen e₁
            exact ⟨G₀, .head A G₀, rfl⟩
          | succ m => simp [Expr.rename, Expr.liftRen] at e₂
        | sort _ => simp [Expr.rename] at e₂
        | app _ _ => simp [Expr.rename] at e₂
        | lam _ _ => simp [Expr.rename] at e₂
        | pi _ _ => simp [Expr.rename] at e₂
      | var _ => simp [Expr.rename] at hb
      | sort _ => simp [Expr.rename] at hb
      | lam _ _ => simp [Expr.rename] at hb
      | pi _ _ => simp [Expr.rename] at hb
    | @lam_domain A₁ A₁' b₁ h' =>
      simp only [Expr.rename, Expr.lam.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨A', hA', rfl⟩ := ihA h'
      exact ⟨.lam A' b, .lam_domain hA', rfl⟩
    | @lam_body A₁ b₁ b₁' h' =>
      simp only [Expr.rename, Expr.lam.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨b', hb', rfl⟩ := ihb h'
      exact ⟨.lam A b', .lam_body hb', rfl⟩
    | app_left _ => simp [Expr.rename] at hX
    | app_right _ => simp [Expr.rename] at hX
    | pi_domain _ => simp [Expr.rename] at hX
    | pi_body _ => simp [Expr.rename] at hX
  | pi A B ihA ihB =>
    intro ρ N h
    generalize hX : (Expr.pi A B).rename ρ = X at h
    cases h with
    | head A' F => simp [Expr.rename] at hX
    | @pi_domain A₁ A₁' B₁ h' =>
      simp only [Expr.rename, Expr.pi.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨A', hA', rfl⟩ := ihA h'
      exact ⟨.pi A' B, .pi_domain hA', rfl⟩
    | @pi_body A₁ B₁ B₁' h' =>
      simp only [Expr.rename, Expr.pi.injEq] at hX
      obtain ⟨rfl, rfl⟩ := hX
      obtain ⟨B', hB', rfl⟩ := ihB h'
      exact ⟨.pi A B', .pi_body hB', rfl⟩
    | app_left _ => simp [Expr.rename] at hX
    | app_right _ => simp [Expr.rename] at hX
    | lam_domain _ => simp [Expr.rename] at hX
    | lam_body _ => simp [Expr.rename] at hX

namespace NormalBE

theorem sort (s : S) : NormalBE (.sort s : Expr S) := by
  intro N h
  rcases h with h | h <;> cases h

theorem var (n : Nat) : NormalBE (.var n : Expr S) := by
  intro N h
  rcases h with h | h <;> cases h

theorem pi {A B : Expr S} (hA : NormalBE A) (hB : NormalBE B) : NormalBE (.pi A B) := by
  intro N h
  rcases h with h | h
  · cases h with
    | pi_domain h => exact hA _ (.inl h)
    | pi_body h => exact hB _ (.inl h)
  · cases h with
    | pi_domain h => exact hA _ (.inr h)
    | pi_body h => exact hB _ (.inr h)

theorem pi_domain {A B : Expr S} (h : NormalBE (.pi A B)) : NormalBE A := by
  intro N hN
  rcases hN with hN | hN
  · exact h _ (.inl (.pi_domain hN))
  · exact h _ (.inr (.pi_domain hN))

theorem pi_body {A B : Expr S} (h : NormalBE (.pi A B)) : NormalBE B := by
  intro N hN
  rcases hN with hN | hN
  · exact h _ (.inl (.pi_body hN))
  · exact h _ (.inr (.pi_body hN))

theorem app_left {f a : Expr S} (h : NormalBE (.app f a)) : NormalBE f := by
  intro N hN
  rcases hN with hN | hN
  · exact h _ (.inl (.app_left hN))
  · exact h _ (.inr (.app_left hN))

theorem app_right {f a : Expr S} (h : NormalBE (.app f a)) : NormalBE a := by
  intro N hN
  rcases hN with hN | hN
  · exact h _ (.inl (.app_right hN))
  · exact h _ (.inr (.app_right hN))

theorem rename {M : Expr S} (h : NormalBE M) (ρ : Nat → Nat) : NormalBE (M.rename ρ) := by
  intro N hN
  rcases hN with hN | hN
  · exact h.normal.rename ρ N hN
  · obtain ⟨M', hM', _⟩ := Eta.rename_inv M hN
    exact h M' (.inr hM')

end NormalBE

theorem betaEta_star_pi_inv {A B W : Expr S} (h : ReflTransGen BetaEta (.pi A B) W) :
    ∃ A' B', W = .pi A' B' ∧ ReflTransGen BetaEta A A' ∧ ReflTransGen BetaEta B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨A', B', rfl, hA, hB⟩ := ih
    rcases hs with hs | hs
    · cases hs with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail (.inl h), hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail (.inl h)⟩
    · cases hs with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail (.inr h), hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail (.inr h)⟩

theorem betaEta_star_pi {A A' B B' : Expr S} (hA : ReflTransGen BetaEta A A')
    (hB : ReflTransGen BetaEta B B') : ReflTransGen BetaEta (.pi A B) (.pi A' B') :=
  (hA.lift (fun x => Expr.pi x B) fun _ _ h => h.elim (fun h => .inl (.pi_domain h))
      (fun h => .inr (.pi_domain h))).trans
    (hB.lift (fun x => Expr.pi A' x) fun _ _ h => h.elim (fun h => .inl (.pi_body h))
      (fun h => .inr (.pi_body h)))

theorem BetaEta.rename {M N : Expr S} (h : BetaEta M N) (ρ : Nat → Nat) :
    BetaEta (M.rename ρ) (N.rename ρ) := by
  rcases h with h | h
  · exact .inl (h.rename ρ)
  · exact .inr (h.rename ρ)

theorem betaEta_star_rename {M N : Expr S} (h : ReflTransGen BetaEta M N) (ρ : Nat → Nat) :
    ReflTransGen BetaEta (M.rename ρ) (N.rename ρ) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.rename ρ)

/-! ### Keys -/

section
variable [Nonempty S]

/-- The fixed sort that replaces λ-domains in the erasure. -/
noncomputable def dz : S := Classical.ofNonempty

/-- The erasure of `M` is weakly βη-normalizing. -/
def KWN (M : Expr S) : Prop := ∃ N, ReflTransGen BetaEta (M.erase dz) N ∧ NormalBE N

/-- The key of a term is the βη-normal form of its domain erasure. -/
noncomputable def Expr.knf (M : Expr S) : Expr S := by
  classical
  exact if h : KWN M then h.choose else M.erase dz

abbrev KConverts (M N : Expr S) : Prop := ConvertsBE (M.erase dz) (N.erase dz)
abbrev KReduces (M N : Expr S) : Prop := ReflTransGen BetaEta (M.erase dz) (N.erase dz)

/-- A term is erased and βη-normal. These terms are exactly the keys. -/
def KNormal (M : Expr S) : Prop := NormalBE M ∧ M.erase dz = M

def SystemENormalizing' (P : Specification S) : Prop := SystemENormalizing dz P

theorem ConvertsBE.k {M N : Expr S} (h : ConvertsBE M N) : KConverts M N :=
  .trans _ _ _ (.symm _ _ (convertsBE_erase dz M)) (.trans _ _ _ h (convertsBE_erase dz N))

theorem KConverts.convertsBE {M N : Expr S} (h : KConverts M N) : ConvertsBE M N :=
  .trans _ _ _ (convertsBE_erase dz M) (.trans _ _ _ h (.symm _ _ (convertsBE_erase dz N)))

theorem Reduces.k {M N : Expr S} (h : Reduces M N) : KReduces M N :=
  reduces_betaEta (Reduces.erase dz h)

theorem KReduces.converts {M N : Expr S} (h : KReduces M N) : KConverts M N :=
  betaEta_star_convertsBE h

theorem Expr.knf_def {M : Expr S} (h : KWN M) : M.knf = h.choose := by
  unfold Expr.knf; rw [dif_pos h]

theorem Expr.knf_def_neg {M : Expr S} (h : ¬ KWN M) : M.knf = M.erase dz := by
  unfold Expr.knf; rw [dif_neg h]

theorem Expr.knf_erased (M : Expr S) : M.knf.erase dz = M.knf := by
  classical
  by_cases h : KWN M
  · rw [Expr.knf_def h]
    exact betaEta_star_erased dz h.choose_spec.1 (Erased.erase_erased M)
  · rw [Expr.knf_def_neg h]
    exact Expr.erase_idem dz M

theorem KWN.of_normal_knf {M : Expr S} (h : NormalBE M.knf) : KWN M := by
  classical
  by_cases hw : KWN M
  · exact hw
  · rw [Expr.knf_def_neg hw] at h
    exact ⟨_, .refl, h⟩

theorem Expr.knf_spec {M : Expr S} (h : KWN M) : KReduces M M.knf ∧ KNormal M.knf := by
  have hs := h.choose_spec
  refine ⟨?_, ?_, Expr.knf_erased M⟩
  · show ReflTransGen BetaEta (M.erase dz) (M.knf.erase dz)
    rw [Expr.knf_erased, Expr.knf_def h]; exact hs.1
  · rw [Expr.knf_def h]; exact hs.2

theorem KWN.knf_normal {M : Expr S} (h : KWN M) : NormalBE M.knf := (Expr.knf_spec h).2.1

theorem KWN.iff_normal_knf {M : Expr S} : KWN M ↔ NormalBE M.knf :=
  ⟨KWN.knf_normal, KWN.of_normal_knf⟩

theorem KNormal.eq_of_kconverts {X Y : Expr S} (hX : KNormal X) (hY : KNormal Y)
    (h : KConverts X Y) : X = Y := by
  have h' : ConvertsBE (X.erase dz) (Y.erase dz) := h
  rw [hX.2, hY.2] at h'
  exact eq_of_convertsBE_normalBE dz hX.2 hY.2 hX.1 hY.1 h'

theorem Expr.knf_reduces {M : Expr S} (h : KWN M) : ReflTransGen BetaEta (M.erase dz) M.knf := by
  have hs : ReflTransGen BetaEta (M.erase dz) (M.knf.erase dz) := (Expr.knf_spec h).1
  rwa [Expr.knf_erased] at hs

theorem KNormal.knf {M : Expr S} (h : KNormal M) : M.knf = M := by
  have hw : KWN M := ⟨M, by rw [h.2], h.1⟩
  have hs := Expr.knf_reduces hw
  rw [h.2] at hs
  exact h.1.star_eq hs

theorem Expr.knf_converts {M N : Expr S} (hM : KWN M) (hN : KWN N) (h : KConverts M N) :
    M.knf = N.knf := by
  have c1 := (Expr.knf_spec hM).1.converts
  have c2 := (Expr.knf_spec hN).1.converts
  exact KNormal.eq_of_kconverts (Expr.knf_spec hM).2 (Expr.knf_spec hN).2
    (.trans _ _ _ (.symm _ _ c1) (.trans _ _ _ h c2))

/-- Any βη-normal erased reduct of the erasure of `M` is the key of `M`. -/
theorem Expr.knf_eq {M X : Expr S} (h : ReflTransGen BetaEta (M.erase dz) X)
    (hX : NormalBE X) (eX : X.erase dz = X) : M.knf = X := by
  have hw : KWN M := ⟨X, h, hX⟩
  have c : KConverts M X := by
    show ConvertsBE (M.erase dz) (X.erase dz)
    rw [eX]; exact betaEta_star_convertsBE h
  have hX' : KNormal X := ⟨hX, eX⟩
  have := Expr.knf_converts hw ⟨X, by rw [eX], hX⟩ c
  rw [this]
  exact hX'.knf

theorem KWN.of_kconverts {M N : Expr S} (h : KConverts M N) (hN : KWN N) : KWN M := by
  obtain ⟨Z, hNZ, hZ⟩ := hN
  have eZ : Z.erase dz = Z := betaEta_star_erased dz hNZ (Erased.erase_erased N)
  have hc : ConvertsBE (M.erase dz) Z := .trans _ _ _ h (betaEta_star_convertsBE hNZ)
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join dz hc
  rw [Expr.erase_idem] at h₁
  rw [eZ] at h₂
  have hW : W = Z := stepE_star_eq_of_normalBE hZ h₂
  subst hW
  exact ⟨W, stepE_star_betaEta dz h₁, hZ⟩

theorem KWN.of_knf_eq {M N : Expr S} (he : M.knf = N.knf) (hN : KWN N) : KWN M :=
  KWN.of_normal_knf (he ▸ hN.knf_normal)

theorem Expr.knf_of_normal {M : Expr S} (h : KNormal M) : M.knf = M := h.knf

theorem Expr.knf_idem (M : Expr S) : M.knf.knf = M.knf := by
  classical
  by_cases h : KWN M
  · exact (Expr.knf_spec h).2.knf
  · rw [Expr.knf_def_neg h]
    have h' : ¬ KWN (M.erase dz) := by
      intro hh; apply h
      obtain ⟨N, hN, hn⟩ := hh
      rw [Expr.erase_idem] at hN
      exact ⟨N, hN, hn⟩
    rw [Expr.knf_def_neg h', Expr.erase_idem]

namespace KNormal

theorem sort (s : S) : KNormal (.sort s : Expr S) := ⟨NormalBE.sort s, rfl⟩

theorem var (n : Nat) : KNormal (.var n : Expr S) := ⟨NormalBE.var n, rfl⟩

theorem normal {M : Expr S} (h : KNormal M) : Normal M := h.1.normal

theorem stronglyNormalizing {M : Expr S} (h : KNormal M) : StronglyNormalizing M :=
  h.normal.stronglyNormalizing

theorem pi {A B : Expr S} (hA : KNormal A) (hB : KNormal B) : KNormal (.pi A B) :=
  ⟨hA.1.pi hB.1, by simp only [Expr.erase, hA.2, hB.2]⟩

theorem pi_domain {A B : Expr S} (h : KNormal (.pi A B)) : KNormal A := by
  refine ⟨h.1.pi_domain, ?_⟩
  have := h.2; simp only [Expr.erase, Expr.pi.injEq] at this; exact this.1

theorem pi_body {A B : Expr S} (h : KNormal (.pi A B)) : KNormal B := by
  refine ⟨h.1.pi_body, ?_⟩
  have := h.2; simp only [Expr.erase, Expr.pi.injEq] at this; exact this.2

theorem app_left {f a : Expr S} (h : KNormal (.app f a)) : KNormal f := by
  refine ⟨h.1.app_left, ?_⟩
  have := h.2; simp only [Expr.erase, Expr.app.injEq] at this; exact this.1

theorem app_right {f a : Expr S} (h : KNormal (.app f a)) : KNormal a := by
  refine ⟨h.1.app_right, ?_⟩
  have := h.2; simp only [Expr.erase, Expr.app.injEq] at this; exact this.2

theorem rename {M : Expr S} (h : KNormal M) (ρ : Nat → Nat) : KNormal (M.rename ρ) :=
  ⟨h.1.rename ρ, by rw [Expr.erase_rename, h.2]⟩

theorem enormal {M : Expr S} (h : KNormal M) : ENormal dz M := by
  unfold ENormal; rw [h.2]; exact h.normal

end KNormal

theorem KWN.pi_domain {A B : Expr S} (h : KWN (.pi A B)) : KWN A := by
  obtain ⟨N, hN, hn⟩ := h
  obtain ⟨A', B', rfl, hA, _⟩ := betaEta_star_pi_inv hN
  exact ⟨A', hA, hn.pi_domain⟩

theorem KWN.pi_body {A B : Expr S} (h : KWN (.pi A B)) : KWN B := by
  obtain ⟨N, hN, hn⟩ := h
  obtain ⟨A', B', rfl, _, hB⟩ := betaEta_star_pi_inv hN
  exact ⟨B', hB, hn.pi_body⟩

theorem Expr.knf_pi {A B : Expr S} (hA : KWN A) (hB : KWN B) :
    (Expr.pi A B).knf = .pi A.knf B.knf := by
  apply Expr.knf_eq
  · exact betaEta_star_pi (Expr.knf_reduces hA) (Expr.knf_reduces hB)
  · exact (Expr.knf_spec hA).2.1.pi (Expr.knf_spec hB).2.1
  · simp only [Expr.erase, Expr.knf_erased]

theorem KWN.rename {M : Expr S} (h : KWN M) (ρ : Nat → Nat) : KWN (M.rename ρ) := by
  obtain ⟨N, hN, hn⟩ := h
  refine ⟨N.rename ρ, ?_, hn.rename ρ⟩
  rw [Expr.erase_rename]
  exact betaEta_star_rename hN ρ

theorem Expr.knf_rename {M : Expr S} (h : KWN M) (ρ : Nat → Nat) :
    (M.rename ρ).knf = M.knf.rename ρ := by
  apply Expr.knf_eq
  · rw [Expr.erase_rename]
    exact betaEta_star_rename (Expr.knf_reduces h) ρ
  · exact (Expr.knf_spec h).2.1.rename ρ
  · rw [Expr.erase_rename, Expr.knf_erased]

theorem Expr.knf_sort (s : S) : (Expr.sort s).knf = .sort s := (KNormal.sort s).knf

theorem Expr.knf_var (n : Nat) : (Expr.var n : Expr S).knf = .var n := (KNormal.var n).knf

theorem KConverts.subst {M N : Expr S} (h : KConverts M N) (σ : Nat → Expr S) :
    KConverts (M.subst σ) (N.subst σ) := by
  unfold KConverts
  rw [Expr.erase_subst, Expr.erase_subst]
  exact ConvertsBE.subst h _

theorem KConverts.of_knf_eq {M N : Expr S} (hM : KWN M) (hN : KWN N) (h : M.knf = N.knf) :
    KConverts M N := by
  have h1 := (Expr.knf_spec hM).1.converts
  have h2 := (Expr.knf_spec hN).1.converts
  rw [h] at h1
  exact .trans _ _ _ h1 (.symm _ _ h2)

theorem KConverts.knf_left {M : Expr S} (h : KWN M) : KConverts M.knf M :=
  .symm _ _ (Expr.knf_spec h).1.converts

/-- The key of a term depends only on its erasure. -/
theorem Expr.knf_eq_of_erase_eq {M M' : Expr S} (h : M.erase dz = M'.erase dz) :
    M.knf = M'.knf := by
  have hk : KWN M ↔ KWN M' := by unfold KWN; rw [h]
  by_cases hw : KWN M
  · exact Expr.knf_converts hw (hk.1 hw)
      (by show ConvertsBE (M.erase dz) (M'.erase dz); rw [h]; exact .refl _)
  · rw [Expr.knf_def_neg hw, Expr.knf_def_neg (fun h' => hw (hk.2 h')), h]

/-- Terms with equal erasures are βη-convertible. No typing is needed. -/
theorem convertsBE_of_erase_eq {M M' : Expr S} (h : M.erase dz = M'.erase dz) :
    ConvertsBE M M' :=
  .trans _ _ _ (convertsBE_erase dz M) (h ▸ .symm _ _ (convertsBE_erase dz M'))

/-- Let `M` and `N` have weakly βη-normalizing erasures.
Then `M` and `N` have the same key exactly when they are βη-convertible. -/
theorem convertsBE_iff_knf_eq {M N : Expr S} (hM : KWN M) (hN : KWN N) :
    ConvertsBE M N ↔ M.knf = N.knf :=
  ⟨fun h => Expr.knf_converts hM hN h.k, fun h => (KConverts.of_knf_eq hM hN h).convertsBE⟩

/-- If `M` has an erasure-normal β-reduct, then the erasure of `M` is weakly βη-normalizing.
The proof η-normalizes the β-normal erasure of that reduct. -/
theorem KWN.of_enormal_reduct {M M' : Expr S} (hr : Reduces M M') (hn : ENormal dz M') :
    KWN M := by
  obtain ⟨Y, hY, hYn⟩ := eta_normal_exists (M'.erase dz)
  refine ⟨Y, (Reduces.k hr).trans (etaStar_betaEta hY), ?_⟩
  intro Z hZ
  rcases hZ with hb | he
  · exact (Normal.of_eta_star hn hY) Z hb
  · exact hYn Z he

end

/-! ### Typing gives weak normalization of erasures -/

section
variable [Nonempty S] {P : Specification S}

theorem HasTypeBE.kwn {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A)
    (hw : SystemENormalizing' P) : KWN M := by
  obtain ⟨M', hr, hn⟩ := hw Γ h.valid M ⟨A, .inl h⟩
  exact KWN.of_enormal_reduct hr hn

theorem HasTypeBE.type_kwn {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A)
    (hw : SystemENormalizing' P) : KWN A := by
  obtain ⟨A', hr, hn⟩ := hw Γ h.valid A ⟨M, .inr h⟩
  exact KWN.of_enormal_reduct hr hn

/-- Two legal types with the same key are βη-convertible.
Beyond the normalization hypothesis, no typing argument is needed. -/
theorem converts_of_knf_eq (hw : SystemENormalizing' P) {Γ : List (Expr S)} {A B : Expr S}
    {s t : S} (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Γ B (.sort t))
    (he : A.knf = B.knf) : ConvertsBE A B :=
  (convertsBE_iff_knf_eq (hA.kwn hw) (hB.kwn hw)).2 he

/-- A term whose erasure is weakly βη-normalizing and whose key is a sort is βη-convertible to that sort. -/
theorem converts_sort_of_knf {A : Expr S} {s : S} (hA : KWN A) (he : A.knf = .sort s) :
    ConvertsBE A (.sort s) :=
  (convertsBE_iff_knf_eq hA (KWN.of_normal_knf (by rw [Expr.knf_sort]; exact NormalBE.sort s))).2
    (he.trans (Expr.knf_sort s).symm)

end

end PureTypeSystem
