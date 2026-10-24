module

public import PTSBetaEta.Normalization.Contexts

@[expose] public section

/-!
# Typing in the context tower up to keys

`Ω.KHasTypeBE M A` says that some judgment `M₀ : A₀` of the tower has the same keys as `M : A`.
Every closure property that OpenAI's candidate layer uses holds for this relation, because keys are faithful on legal types.
-/

set_option linter.unusedSectionVars false

namespace PureTypeSystem

universe u

variable {S : Type u} [Nonempty S]

open Relation

namespace Expr.Scoped

theorem erase {n : Nat} {M : Expr S} (h : M.Scoped n) : (M.erase dz).Scoped n := by
  induction M generalizing n with
  | var i => exact h
  | sort _ => trivial
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam A b _ ihb => exact ⟨trivial, ihb h.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩

end Expr.Scoped

theorem ConvertsBE.app_congr {f f' a a' : Expr S} (hf : ConvertsBE f f') (ha : ConvertsBE a a') :
    ConvertsBE (.app f a) (.app f' a') :=
  .trans _ _ _
    (eqv_lift (c := fun x => .app x a) (fun h => h.elim (fun h => .inl (.app_left h))
      (fun h => .inr (.app_left h))) hf)
    (eqv_lift (c := fun x => .app f' x) (fun h => h.elim (fun h => .inl (.app_right h))
      (fun h => .inr (.app_right h))) ha)

theorem ConvertsBE.lam_congr {A A' b b' : Expr S} (hA : ConvertsBE A A') (hb : ConvertsBE b b') :
    ConvertsBE (.lam A b) (.lam A' b') :=
  .trans _ _ _
    (eqv_lift (c := fun x => .lam x b) (fun h => h.elim (fun h => .inl (.lam_domain h))
      (fun h => .inr (.lam_domain h))) hA)
    (eqv_lift (c := fun x => .lam A' x) (fun h => h.elim (fun h => .inl (.lam_body h))
      (fun h => .inr (.lam_body h))) hb)

theorem Expr.Scoped.subst_convertsBE {n : Nat} {M : Expr S} (hM : M.Scoped n)
    {σ τ : Nat → Expr S} (hc : ∀ i, i < n → ConvertsBE (σ i) (τ i)) :
    ConvertsBE (M.subst σ) (M.subst τ) := by
  induction M generalizing n σ τ with
  | var i => exact hc i hM
  | sort s => exact .refl _
  | app f a ihf iha => exact ConvertsBE.app_congr (ihf hM.1 hc) (iha hM.2 hc)
  | lam A b ihA ihb | pi A b ihA ihb =>
    have he : ∀ i, i < n+1 → ConvertsBE (Expr.liftSub σ i) (Expr.liftSub τ i) := by
      intro i hi
      cases i with
      | zero => exact .refl _
      | succ i => exact (hc i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
    first
    | exact ConvertsBE.lam_congr (ihA hM.1 hc) (ihb hM.2 he)
    | exact ConvertsBE.pi (ihA hM.1 hc) (ihb hM.2 he)

namespace ContextTowerBE

variable {P : Specification S} (Ω : ContextTowerBE P)

/-- Typing in the tower up to keys. -/
def KHasTypeBE (M A : Expr S) : Prop :=
  ∃ M₀ A₀, Ω.HasTypeBE M₀ A₀ ∧ M₀.knf = M.knf ∧ A₀.knf = A.knf

/-- A substitution that is typed in the tower up to keys. -/
def KTypedSubstitutionBE (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.KHasTypeBE (σ n) (A.subst σ)

/-- The profile of `T` in the tower, up to keys. -/
def kprofile (T : Expr S) : Set S := {s | Ω.KHasTypeBE T (.sort s)}

/-- `M` is typed in the tower, and its type is given up to its key. -/
def THasTypeBE (M A : Expr S) : Prop :=
  ∃ A₀, Ω.HasTypeBE M A₀ ∧ A₀.knf = A.knf

/-- A substitution whose images are typed in the tower, with their types given up to keys. -/
def TTypedSubstitutionBE (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.THasTypeBE (σ n) (A.subst σ)

theorem domain_sorted {A B : Expr S} {s : S}
    (hT : Ω.HasTypeBE (.pi A B) (.sort s)) : ∃ a, Ω.HasTypeBE A (.sort a) := by
  obtain ⟨n, hT⟩ := hT
  obtain ⟨a, b, c, hA, _, _, _⟩ := hT.generation_pi
  exact ⟨a, n, hA⟩

variable {Ω}

theorem reverseIndex_injective (n : Nat) : Function.Injective (Expr.reverseIndex n) :=
  (Expr.reverseIndex_involutive n).injective

namespace HasTypeBE

variable {M A : Expr S}

theorem kwn_both (h : Ω.HasTypeBE M A) (hw : SystemENormalizing' P) : KWN M ∧ KWN A := by
  obtain ⟨n, hn⟩ := h
  have h1 := (hn.kwn hw).rename (Expr.reverseIndex n)
  have h2 := (hn.type_kwn hw).rename (Expr.reverseIndex n)
  rw [Expr.reverseIndex_twice] at h1 h2
  exact ⟨h1, h2⟩

theorem enormal_reduct (h : Ω.HasTypeBE M A) (hw : SystemENormalizing' P) :
    ∃ M', Reduces M M' ∧ ENormal dz M' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨M'', hr, he⟩ := hw _ hn.valid _ ⟨_, .inl hn⟩
  obtain ⟨M₁, rfl, hM₁⟩ := Reduces.rename_inv (reverseIndex_injective n) hr
  refine ⟨M₁, hM₁, ?_⟩
  unfold ENormal at he ⊢
  rw [Expr.erase_rename] at he
  exact Normal.of_rename _ he

theorem type_reduce (h : Ω.HasTypeBE M A) {A' : Expr S} (hr : Reduces A A') :
    Ω.HasTypeBE M A' := by
  rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hA⟩
  · rw [Reduces.sort_inv hr]; exact h
  · exact h.conversion (hA.subject_reduces hr) (reduces_convertsBE hr)

/-- A type of the tower that is βη-convertible to a sort reduces to that sort. -/
theorem reduces_sort (hw : SystemENormalizing' P) {X : Expr S} {u s : S}
    (h : Ω.HasTypeBE X (.sort u)) (c : ConvertsBE X (.sort s)) : Reduces X (.sort s) := by
  obtain ⟨n, hn⟩ := h
  have c' : ConvertsBE (X.rename (Expr.reverseIndex n)) (.sort s) := c.rename (Expr.reverseIndex n)
  have hr := hn.reduces_sort_of_convertsBE hw c'
  obtain ⟨X₁, he, hX₁⟩ := Reduces.rename_inv (reverseIndex_injective n) hr
  cases X₁ <;> simp [Expr.rename] at he
  subst he
  exact hX₁

/-- An erasure-normal type of the tower that is βη-convertible to a product is itself a product. -/
theorem pi_shape (hw : SystemENormalizing' P) {X C D : Expr S} {u : S}
    (h : Ω.HasTypeBE X (.sort u)) (eX : ENormal dz X)
    (c : ConvertsBE X (.pi C D)) : ∃ X₁ X₂, X = .pi X₁ X₂ := by
  obtain ⟨n, hn⟩ := h
  have eX' : ENormal dz (X.rename (Expr.reverseIndex n)) := by
    unfold ENormal at eX ⊢; rw [Expr.erase_rename]; exact eX.rename _
  obtain ⟨X₁, X₂, he⟩ := ENormal.pi_of_convertsBE dz hn eX' (c.rename (Expr.reverseIndex n))
  cases X with
  | pi X₁' X₂' => exact ⟨_, _, rfl⟩
  | var _ => simp [Expr.rename] at he
  | sort _ => simp [Expr.rename] at he
  | app _ _ => simp [Expr.rename] at he
  | lam _ _ => simp [Expr.rename] at he

end HasTypeBE

/-- Two types of the tower with the same key are βη-convertible. -/
theorem converts_of_knf_eq (hw : SystemENormalizing' P) {A B : Expr S} {s t : S}
    (hA : Ω.HasTypeBE A (.sort s)) (hB : Ω.HasTypeBE B (.sort t)) (he : A.knf = B.knf) :
    ConvertsBE A B := by
  obtain ⟨n, hA', hB'⟩ := hA.common hB
  have wA := (hA.kwn_both hw).1
  have wB := (hB.kwn_both hw).1
  have he' : (A.rename (Expr.reverseIndex n)).knf = (B.rename (Expr.reverseIndex n)).knf := by
    rw [Expr.knf_rename wA, Expr.knf_rename wB, he]
  have c := PureTypeSystem.converts_of_knf_eq hw hA' hB' he'
  have c' := c.rename (Expr.reverseIndex n)
  rwa [Expr.reverseIndex_twice, Expr.reverseIndex_twice] at c'

/-- If `M` has type `U` in the tower and `T` is a type of the tower with the same key as `U`, then `M` also has type `T`. -/
theorem HasTypeBE.retype (hw : SystemENormalizing' P) {M U T : Expr S} {t : S}
    (hM : Ω.HasTypeBE M U) (hT : Ω.HasTypeBE T (.sort t)) (he : U.knf = T.knf) :
    Ω.HasTypeBE M T := by
  rcases hM.regularity with ⟨u, rfl⟩ | ⟨u, hU⟩
  · have wT := (hT.kwn_both hw).1
    have c := converts_sort_of_knf wT (by rw [← he, Expr.knf_sort])
    exact hM.conversion hT (.symm _ _ c)
  · exact hM.conversion hT (converts_of_knf_eq hw hU hT he)

section
variable [hE : Fact (SystemENormalizing' P)]

namespace KHasTypeBE

variable {M N A B : Expr S}

theorem of (h : Ω.HasTypeBE M A) : Ω.KHasTypeBE M A := ⟨M, A, h, rfl, rfl⟩

theorem kwn (h : Ω.KHasTypeBE M A) (_hw : SystemENormalizing' P) : KWN M := by
  obtain ⟨M₀, A₀, h₀, hM, _⟩ := h
  exact KWN.of_knf_eq hM.symm (h₀.kwn_both hE.out).1

theorem type_kwn (h : Ω.KHasTypeBE M A) (_hw : SystemENormalizing' P) : KWN A := by
  obtain ⟨M₀, A₀, h₀, _, hA⟩ := h
  exact KWN.of_knf_eq hA.symm (h₀.kwn_both hE.out).2

theorem knf (h : Ω.KHasTypeBE M A) (_hw : SystemENormalizing' P) : Ω.KHasTypeBE M.knf A := by
  obtain ⟨M₀, A₀, h₀, hM, hA⟩ := h
  exact ⟨M₀, A₀, h₀, by rw [Expr.knf_idem]; exact hM, hA⟩

theorem normalize_type (h : Ω.KHasTypeBE M A) (_hw : SystemENormalizing' P) :
    Ω.KHasTypeBE M A.knf := by
  obtain ⟨M₀, A₀, h₀, hM, hA⟩ := h
  exact ⟨M₀, A₀, h₀, hM, by rw [Expr.knf_idem]; exact hA⟩

theorem denormalize_type {s : S} (h : Ω.KHasTypeBE M A.knf) (_hA : Ω.KHasTypeBE A (.sort s))
    (_hw : SystemENormalizing' P) : Ω.KHasTypeBE M A := by
  obtain ⟨M₀, A₀, h₀, hM, hA'⟩ := h
  exact ⟨M₀, A₀, h₀, hM, by rw [hA', Expr.knf_idem]⟩

theorem of_knf_eq (h : Ω.KHasTypeBE M A) {M' A' : Expr S} (hM : M.knf = M'.knf)
    (hA : A.knf = A'.knf) : Ω.KHasTypeBE M' A' := by
  obtain ⟨M₀, A₀, h₀, h1, h2⟩ := h
  exact ⟨M₀, A₀, h₀, h1.trans hM, h2.trans hA⟩

theorem subject_reduces (h : Ω.KHasTypeBE M A) (hr : Reduces M N) : Ω.KHasTypeBE N A := by
  have wM := h.kwn hE.out
  have wN : KWN N := KWN.of_kconverts (.symm _ _ hr.k.converts) wM
  exact h.of_knf_eq (Expr.knf_converts wM wN hr.k.converts) rfl

theorem conversion {s : S} (hM : Ω.KHasTypeBE M A) (hB : Ω.KHasTypeBE B (.sort s))
    (hc : KConverts A B) : Ω.KHasTypeBE M B :=
  hM.of_knf_eq rfl (Expr.knf_converts (hM.type_kwn hE.out) (hB.kwn hE.out) hc)

/-- A typing up to keys at a product type has a witness in the tower.
The type of the witness is a product whose domain and codomain are erasure-normal and have the given keys. -/
theorem pi_witness (hf : Ω.KHasTypeBE M (.pi A B)) :
    ∃ M₀ A₁ B₁, Ω.HasTypeBE M₀ (.pi A₁ B₁) ∧ M₀.knf = M.knf ∧ A₁.knf = A.knf ∧
      B₁.knf = B.knf ∧ ENormal dz A₁ ∧ ENormal dz B₁ := by
  obtain ⟨M₀, T₀, h₀, hM, hT⟩ := hf
  have wT := (h₀.kwn_both hE.out).2
  have wP : KWN (.pi A B) := KWN.of_knf_eq hT.symm wT
  rcases h₀.regularity with ⟨r, rfl⟩ | ⟨r, hT₀⟩
  · rw [Expr.knf_sort, Expr.knf_pi wP.pi_domain wP.pi_body] at hT; cases hT
  obtain ⟨T₁, hr, hn⟩ := hT₀.enormal_reduct hE.out
  have hT₁ := hT₀.subject_reduces hr
  have c : ConvertsBE T₁ (.pi A B) :=
    .trans _ _ _ (.symm _ _ (reduces_convertsBE hr)) ((convertsBE_iff_knf_eq wT wP).2 hT)
  obtain ⟨A₁, B₁, rfl⟩ := hT₁.pi_shape hE.out hn c
  have w₁ := (hT₁.kwn_both hE.out).1
  obtain ⟨cA, cB⟩ := c.product_compatibility dz
  have eA : ENormal dz A₁ := (show ENormal dz (.pi A₁ B₁) from hn).pi.1
  have eB : ENormal dz B₁ := (show ENormal dz (.pi A₁ B₁) from hn).pi.2
  exact ⟨M₀, A₁, B₁, h₀.type_reduce hr, hM,
    (convertsBE_iff_knf_eq w₁.pi_domain wP.pi_domain).1 cA,
    (convertsBE_iff_knf_eq w₁.pi_body wP.pi_body).1 cB, eA, eB⟩

theorem application (hf : Ω.KHasTypeBE M (.pi A B)) (ha : Ω.KHasTypeBE N A) :
    Ω.KHasTypeBE (.app M N) (B.instantiate N) := by
  obtain ⟨M₀, A₁, B₁, hM₀, hMk, hAk, hBk, _, _⟩ := hf.pi_witness
  obtain ⟨N₀, U₀, hN₀, hNk, hUk⟩ := ha
  obtain ⟨a, hA₁⟩ := Ω.domain_sorted ((hM₀.regularity).resolve_left (by
    rintro ⟨s, hs⟩; cases hs) |>.choose_spec)
  have hN₁ : Ω.HasTypeBE N₀ A₁ := hN₀.retype hE.out hA₁ (hUk.trans hAk.symm)
  have happ := hM₀.application hN₁
  have wM₀ := (hM₀.kwn_both hE.out).1
  have wN₀ := (hN₀.kwn_both hE.out).1
  have wM : KWN M := KWN.of_knf_eq hMk.symm wM₀
  have wN : KWN N := KWN.of_knf_eq hNk.symm wN₀
  have cM : KConverts M₀ M := KConverts.of_knf_eq wM₀ wM hMk
  have cN : KConverts N₀ N := KConverts.of_knf_eq wN₀ wN hNk
  have wapp := happ.kwn_both hE.out
  have capp : KConverts (.app M₀ N₀) (.app M N) := by
    show ConvertsBE (Expr.app (M₀.erase dz) (N₀.erase dz)) (Expr.app (M.erase dz) (N.erase dz))
    exact ConvertsBE.app_congr cM cN
  have wB₁ : KWN B₁ := (KWN.pi_body ((hM₀.kwn_both hE.out).2))
  have hB : KWN B := KWN.of_knf_eq hBk.symm wB₁
  have cB : KConverts B₁ B := KConverts.of_knf_eq wB₁ hB hBk
  have ctgt : KConverts (B₁.instantiate N₀) (B.instantiate N) := by
    unfold KConverts
    rw [Expr.erase_instantiate, Expr.erase_instantiate]
    exact .trans _ _ _ (ConvertsBE.subst cB _) (cN.instantiate_right _)
  refine ⟨_, _, happ, ?_, ?_⟩
  · exact Expr.knf_converts wapp.1 (KWN.of_kconverts (.symm _ _ capp) wapp.1) capp
  · exact Expr.knf_converts wapp.2 (KWN.of_kconverts (.symm _ _ ctgt) wapp.2) ctgt

end KHasTypeBE

namespace KTypedSubstitutionBE

variable {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem of (h : Ω.TypedSubstitutionBE Γ σ) : Ω.KTypedSubstitutionBE Γ σ :=
  fun n A hn => KHasTypeBE.of (h n A hn)

theorem tail {A : Expr S} (h : Ω.KTypedSubstitutionBE (A :: Γ) σ) :
    Ω.KTypedSubstitutionBE Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

theorem cons {A a : Expr S} (h : Ω.KTypedSubstitutionBE Γ σ)
    (ha : Ω.KHasTypeBE a (A.subst σ)) : Ω.KTypedSubstitutionBE (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn

/-- A substitution that is typed up to keys can be replaced by a typed substitution with the same keys on the context. -/
theorem realize (hΓ : ValidContextBE P Γ) (hσ : Ω.KTypedSubstitutionBE Γ σ) :
    ∃ σ₀, Ω.TypedSubstitutionBE Γ σ₀ ∧ ∀ i, i < Γ.length → (σ₀ i).knf = (σ i).knf := by
  induction hΓ generalizing σ with
  | nil =>
    refine ⟨σ, ?_, ?_⟩
    · intro n A h; cases h
    · intro i h; exact absurd h (Nat.not_lt_zero _)
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨σ₀, hσ₀, hk⟩ := ih hσ.tail
    have h0 := hσ 0 (A.rename Nat.succ) (.zero A Γ)
    rw [Expr.subst_rename] at h0
    obtain ⟨N₀, U₀, hN₀, hNk, hUk⟩ := h0
    have hAt := ContextTowerBE.HasTypeBE.subst hA hσ₀
    have wA₀ := (hAt.kwn_both hE.out).1
    have hsc := hA.scope.1
    have cA : KConverts (A.subst σ₀) (A.subst (σ ∘ Nat.succ)) := by
      unfold KConverts
      rw [Expr.erase_subst, Expr.erase_subst]
      apply (Expr.Scoped.erase hsc).subst_convertsBE
      intro i hi
      have wi := ((hσ₀ i _ (Lookup.exists_of_lt hi).choose_spec).kwn_both hE.out).1
      have wi' : KWN ((σ ∘ Nat.succ) i) := KWN.of_knf_eq (hk i hi).symm wi
      exact KConverts.of_knf_eq wi wi' (hk i hi)
    have wA : KWN (A.subst (σ ∘ Nat.succ)) := KWN.of_kconverts (.symm _ _ cA) wA₀
    have hkey : U₀.knf = (A.subst σ₀).knf := by
      rw [hUk]; exact (Expr.knf_converts wA₀ wA cA).symm
    have hN₁ : Ω.HasTypeBE N₀ (A.subst σ₀) := hN₀.retype hE.out hAt hkey
    refine ⟨fun n => match n with | 0 => N₀ | n+1 => σ₀ n, hσ₀.cons hN₁, ?_⟩
    intro i hi
    cases i with
    | zero => exact hNk
    | succ i => exact hk i (Nat.lt_of_succ_lt_succ hi)

end KTypedSubstitutionBE

namespace KHasTypeBE

variable {Γ : List (Expr S)} {σ : Nat → Expr S} {M A : Expr S}

/-- Substitution in a judgment by a substitution that is typed up to keys. -/
theorem subst (h : PureTypeSystem.HasTypeBE P Γ M A) (hσ : Ω.KTypedSubstitutionBE Γ σ) :
    Ω.KHasTypeBE (M.subst σ) (A.subst σ) := by
  obtain ⟨σ₀, hσ₀, hk⟩ := KTypedSubstitutionBE.realize h.valid hσ
  have h₀ := ContextTowerBE.HasTypeBE.subst h hσ₀
  have w := h₀.kwn_both hE.out
  have pc : ∀ i, i < Γ.length → ConvertsBE ((σ₀ i).erase dz) ((σ i).erase dz) := by
    intro i hi
    have wi := ((hσ₀ i _ (Lookup.exists_of_lt hi).choose_spec).kwn_both hE.out).1
    have wi' : KWN (σ i) := KWN.of_knf_eq (hk i hi).symm wi
    exact KConverts.of_knf_eq wi wi' (hk i hi)
  have cM : KConverts (M.subst σ₀) (M.subst σ) := by
    unfold KConverts; rw [Expr.erase_subst, Expr.erase_subst]
    exact (Expr.Scoped.erase h.scope.1).subst_convertsBE pc
  have cA : KConverts (A.subst σ₀) (A.subst σ) := by
    unfold KConverts; rw [Expr.erase_subst, Expr.erase_subst]
    exact (Expr.Scoped.erase h.scope.2).subst_convertsBE pc
  exact ⟨_, _, h₀, Expr.knf_converts w.1 (KWN.of_kconverts (.symm _ _ cM) w.1) cM,
    Expr.knf_converts w.2 (KWN.of_kconverts (.symm _ _ cA) w.2) cA⟩

end KHasTypeBE

theorem kfresh_variable_k {A : Expr S} {s : S} (h : Ω.KHasTypeBE A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.THasTypeBE (.var i) A := by
  obtain ⟨A₀, S₀, h₀, hA, hS⟩ := h
  rw [Expr.knf_sort] at hS
  have hA₀ : Ω.HasTypeBE A₀ (.sort s) := by
    rcases h₀.regularity with ⟨u, rfl⟩ | ⟨u, hU⟩
    · rw [Expr.knf_sort] at hS; cases hS; exact h₀
    · have c := converts_sort_of_knf (hU.kwn_both hE.out).1 hS
      have hs : Ω.HasTypeBE (.sort s) (.sort u) := hU.subject_reduces (hU.reduces_sort hE.out c)
      exact h₀.conversion hs c
  obtain ⟨i, hi, hv⟩ := Ω.fresh_variable hA₀ lower
  exact ⟨i, hi, ⟨_, hv, hA⟩⟩

namespace THasTypeBE

variable {M N A B : Expr S}

theorem of (h : Ω.HasTypeBE M A) : Ω.THasTypeBE M A := ⟨A, h, rfl⟩

theorem toK (h : Ω.THasTypeBE M A) : Ω.KHasTypeBE M A := by
  obtain ⟨A₀, h₀, hA⟩ := h
  exact ⟨M, A₀, h₀, rfl, hA⟩

theorem kwn (h : Ω.THasTypeBE M A) (_hw : SystemENormalizing' P) : KWN M := h.toK.kwn hE.out

theorem type_kwn (h : Ω.THasTypeBE M A) (_hw : SystemENormalizing' P) : KWN A :=
  h.toK.type_kwn hE.out

theorem of_type_knf_eq (h : Ω.THasTypeBE M A) {A' : Expr S} (hA : A.knf = A'.knf) :
    Ω.THasTypeBE M A' := by
  obtain ⟨A₀, h₀, h1⟩ := h
  exact ⟨A₀, h₀, h1.trans hA⟩

theorem normalize_type (h : Ω.THasTypeBE M A) (_hw : SystemENormalizing' P) :
    Ω.THasTypeBE M A.knf := h.of_type_knf_eq (Expr.knf_idem A).symm

theorem denormalize_type {s : S} (h : Ω.THasTypeBE M A.knf) (_hA : Ω.KHasTypeBE A (.sort s))
    (_hw : SystemENormalizing' P) : Ω.THasTypeBE M A := h.of_type_knf_eq (Expr.knf_idem A)

theorem subject_reduces (h : Ω.THasTypeBE M A) (hr : Reduces M N) : Ω.THasTypeBE N A := by
  obtain ⟨A₀, h₀, hA⟩ := h
  exact ⟨A₀, h₀.subject_reduces hr, hA⟩

theorem conversion {s : S} (hM : Ω.THasTypeBE M A) (hB : Ω.THasTypeBE B (.sort s))
    (hc : KConverts A B) : Ω.THasTypeBE M B :=
  hM.of_type_knf_eq (Expr.knf_converts (hM.type_kwn hE.out) (hB.kwn hE.out) hc)

theorem conversionK {s : S} (hM : Ω.THasTypeBE M A) (hB : Ω.KHasTypeBE B (.sort s))
    (hc : KConverts A B) : Ω.THasTypeBE M B :=
  hM.of_type_knf_eq (Expr.knf_converts (hM.type_kwn hE.out) (hB.kwn hE.out) hc)

/-- If `M` is typed at a type with the same key as a legal type `T` of the tower, then `M` has type `T`. -/
theorem retype (h : Ω.THasTypeBE M A) {T : Expr S} {t : S} (hT : Ω.HasTypeBE T (.sort t))
    (he : A.knf = T.knf) : Ω.HasTypeBE M T := by
  obtain ⟨A₀, h₀, hA⟩ := h
  exact h₀.retype hE.out hT (hA.trans he)

theorem application (hf : Ω.THasTypeBE M (.pi A B)) (ha : Ω.THasTypeBE N A) :
    Ω.THasTypeBE (.app M N) (B.instantiate N) := by
  obtain ⟨M₀, A₁, B₁, hM₀, hMk, hAk, hBk, _, _⟩ := (THasTypeBE.toK hf).pi_witness
  obtain ⟨T₀, hT₀, _⟩ := hf
  obtain ⟨a, hA₁⟩ := Ω.domain_sorted ((hM₀.regularity).resolve_left (by
    rintro ⟨s, hs⟩; cases hs) |>.choose_spec)
  -- `M` itself has the product reduct as its type.
  have hM : Ω.HasTypeBE M (.pi A₁ B₁) := by
    have hP : Ω.HasTypeBE (.pi A₁ B₁) (.sort _) := ((hM₀.regularity).resolve_left (by
      rintro ⟨s, hs⟩; cases hs)).choose_spec
    have wP := (hP.kwn_both hE.out).1
    have wT := (hT₀.kwn_both hE.out).2
    obtain ⟨T₀', hT₀', hT₀k⟩ := (⟨T₀, hT₀, rfl⟩ : Ω.THasTypeBE M T₀)
    refine (THasTypeBE.of hT₀).retype hP ?_
    rw [‹T₀.knf = _›, Expr.knf_pi (KWN.of_knf_eq hAk.symm wP.pi_domain)
      (KWN.of_knf_eq hBk.symm wP.pi_body), ← hAk, ← hBk, ← Expr.knf_pi wP.pi_domain wP.pi_body]
  have hN : Ω.HasTypeBE N A₁ := ha.retype hA₁ hAk.symm
  refine ⟨_, hM.application hN, ?_⟩
  have wB₁ : KWN B₁ := KWN.pi_body (((show Ω.HasTypeBE M (.pi A₁ B₁) from hM).kwn_both hE.out).2)
  have hB : KWN B := KWN.of_knf_eq hBk.symm wB₁
  have wapp := (hM.application hN).kwn_both hE.out
  have ctgt : KConverts (B₁.instantiate N) (B.instantiate N) := by
    unfold KConverts
    rw [Expr.erase_instantiate, Expr.erase_instantiate]
    exact ConvertsBE.subst (KConverts.of_knf_eq wB₁ hB hBk) _
  exact Expr.knf_converts wapp.2 (KWN.of_kconverts (.symm _ _ ctgt) wapp.2) ctgt

end THasTypeBE

namespace TTypedSubstitutionBE

variable {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem of (h : Ω.TypedSubstitutionBE Γ σ) : Ω.TTypedSubstitutionBE Γ σ :=
  fun n A hn => THasTypeBE.of (h n A hn)

theorem toK (h : Ω.TTypedSubstitutionBE Γ σ) : Ω.KTypedSubstitutionBE Γ σ :=
  fun n A hn => (h n A hn).toK

theorem tail {A : Expr S} (h : Ω.TTypedSubstitutionBE (A :: Γ) σ) :
    Ω.TTypedSubstitutionBE Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

theorem cons {A a : Expr S} (h : Ω.TTypedSubstitutionBE Γ σ)
    (ha : Ω.THasTypeBE a (A.subst σ)) : Ω.TTypedSubstitutionBE (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn

/-- A substitution whose images are typed in the tower is a typed substitution. -/
theorem typed (hΓ : ValidContextBE P Γ) (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    Ω.TypedSubstitutionBE Γ σ := by
  induction hΓ generalizing σ with
  | nil => intro n A h; cases h
  | @cons Γ A s hΓ hA ih =>
    have hσ' := ih hσ.tail
    have hAt := ContextTowerBE.HasTypeBE.subst hA hσ'
    have h0 := hσ 0 (A.rename Nat.succ) (.zero A Γ)
    rw [Expr.subst_rename] at h0
    have h0' : Ω.HasTypeBE (σ 0) (A.subst (σ ∘ Nat.succ)) := h0.retype hAt rfl
    intro n B hn
    cases hn with
    | zero =>
      rw [Expr.subst_rename]; exact h0'
    | succ C hn =>
      have := hσ' _ _ hn
      simpa only [Expr.subst_rename, Function.comp_def] using this

end TTypedSubstitutionBE

namespace THasTypeBE

theorem subst {Γ : List (Expr S)} {σ : Nat → Expr S} {M A : Expr S}
    (h : PureTypeSystem.HasTypeBE P Γ M A) (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    Ω.THasTypeBE (M.subst σ) (A.subst σ) :=
  THasTypeBE.of (ContextTowerBE.HasTypeBE.subst h (TTypedSubstitutionBE.typed h.valid hσ))

end THasTypeBE

theorem kfresh_variable {A : Expr S} {s : S} (h : Ω.THasTypeBE A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.THasTypeBE (.var i) A := Ω.kfresh_variable_k h.toK lower

end

end ContextTowerBE

end PureTypeSystem
