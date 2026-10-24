module

public import PTSBetaEta.Eta.Strengthening
public import PTSBetaEta.Eta.Typing

@[expose] public section

/-!
# Erasure-normal forms from weak βη-normalization, and faithfulness of erasure

Fix a sort `z`.
The erasure `M.erase z` replaces every λ-domain of `M` by `z`.
A term is erasure-normal when its erasure is β-normal, which means that it has no β-redex outside its λ-domains.

* **Curry's lemma on erased terms.** An erased term that η-reduces to a β-normal term is weakly β-normalizing (`weaklyNormalizing_of_parEta_star`). Nederpelt's critical pair does not occur on erased terms, so an η-expanded head can always be contracted by β.
* Hence **a weakly βη-normalizing term has an erasure-normal β-reduct** (`erasure_normalizes_of_betaEta`). The λ-domains of this reduct need not be normal. This is exactly the gap between weak βη-normalization and weak β-normalization.
* **Faithfulness.** Two legal terms that are erasure-normal and have the same erasure are β-convertible, provided that the first is not an abstraction or that their types are β-convertible (`faithful`). No functionality is assumed. Neutral spines are handled by `HasType.neutral_unique`.
* **Keys.** The key `M.key z` is the β-normal form of `M.erase z`. On legal types with erasure-normal reducts, two types have the same key exactly when they are β-convertible (`key_eq_iff`).
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

open Relation

theorem Normal.app_of {f a : Expr S} (hf : Normal f) (ha : Normal a)
    (hnl : ∀ A b, f ≠ .lam A b) : Normal (.app f a) := by
  intro N h
  cases h with
  | head A b _ => exact hnl A b rfl
  | app_left h => exact hf _ h
  | app_right h => exact ha _ h

theorem Normal.of_rename {M : Expr S} (ρ : Nat → Nat) (h : Normal (M.rename ρ)) : Normal M :=
  Normal.of_map (f := Expr.rename ρ) (fun h => h.rename ρ) h

theorem Converts.map {f : Expr S → Expr S} (hf : ∀ {a b}, Beta a b → Beta (f a) (f b))
    {M N : Expr S} (h : Converts M N) : Converts (f M) (f N) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem Converts.lam_congr {A A' b b' : Expr S} (hA : Converts A A') (hb : Converts b b') :
    Converts (.lam A b) (.lam A' b') :=
  .trans _ _ _ (Converts.map (f := fun x => Expr.lam x b) Beta.lam_domain hA)
    (Converts.map (f := fun x => Expr.lam A' x) Beta.lam_body hb)

theorem Converts.app_congr {f f' a a' : Expr S} (hf : Converts f f') (ha : Converts a a') :
    Converts (.app f a) (.app f' a') :=
  .trans _ _ _ (Converts.map (f := fun x => Expr.app x a) Beta.app_left hf)
    (Converts.map (f := fun x => Expr.app f' x) Beta.app_right ha)

variable (z : S)

/-! ## Curry's lemma on erased terms -/

theorem Erased.of_rename_succ {M : Expr S} (h : Erased z (M.rename Nat.succ)) : Erased z M :=
  Expr.rename_injective_succ ((Expr.erase_rename z M Nat.succ).symm.trans h)

theorem Beta.erased {M N : Expr S} (h : Beta M N) (hM : Erased z M) : Erased z N :=
  (Parallel.of_beta h).erased z hM

theorem Reduces.erased {M N : Expr S} (h : Reduces M N) (hM : Erased z M) : Erased z N := by
  induction h with
  | refl => exact hM
  | tail _ hb ih => exact hb.erased z ih

theorem ParEta.commute_reduces {M N L : Expr S} (he : ParEta M N) (hr : Reduces N L) :
    ∃ P, Reduces M P ∧ ParEta P L := by
  induction hr with
  | refl => exact ⟨M, .refl, he⟩
  | tail _ hb ih =>
    obtain ⟨P₁, hP₁, e₁⟩ := ih
    obtain ⟨P, hP, e⟩ := e₁.commute (Parallel.of_beta hb)
    exact ⟨P, hP₁.trans hP.reduces, e⟩

/-- Let `f` and `a` be β-normal and erased, and suppose their parallel η-reducts `f'` and `a'` form a β-normal application `f' a'`.
Then `f a` β-reduces to a β-normal term that parallel η-reduces to `f' a'`.
The β-steps contract the heads that were η-expanded. -/
theorem app_normalizes : ∀ (n : Nat) (f a f' a' : Expr S), f.size < n → Erased z f →
    Normal f → Normal a → ParEta f f' → ParEta a a' → Normal (.app f' a') →
    ∃ X, Reduces (.app f a) X ∧ Normal X ∧ ParEta X (.app f' a') := by
  intro n
  induction n with
  | zero => intro f _ _ _ h; omega
  | succ n IH =>
    intro f a f' a' hs hz hf ha ef ea hn
    cases f with
    | lam A b =>
      cases ef with
      | lam _ _ => exact (hn _ (.head _ _ _)).elim
      | @head _ F _ hF =>
        have hzF : Erased z F := Erased.of_rename_succ z hz.lam.2.app.1
        have hnF : Normal F := Normal.of_rename Nat.succ hf.lam_body.app_left
        simp only [Expr.size, Expr.size_rename] at hs
        obtain ⟨X, hX, hXn, eX⟩ := IH F a f' a' (by omega) hzF hnF ha hF ea hn
        have h1 : Beta (.app (.lam A (.app (F.rename Nat.succ) (.var 0))) a) (.app F a) := by
          have := Beta.head A (.app (F.rename Nat.succ) (.var 0)) a
          rwa [Expr.instantiate_app_shift] at this
        exact ⟨X, (ReflTransGen.single h1).trans hX, hXn, eX⟩
    | var k =>
      exact ⟨_, .refl, Normal.app_of hf ha (by intro _ _ h; cases h), .app ef ea⟩
    | sort s =>
      exact ⟨_, .refl, Normal.app_of hf ha (by intro _ _ h; cases h), .app ef ea⟩
    | app g c =>
      exact ⟨_, .refl, Normal.app_of hf ha (by intro _ _ h; cases h), .app ef ea⟩
    | pi C D =>
      exact ⟨_, .refl, Normal.app_of hf ha (by intro _ _ h; cases h), .app ef ea⟩

/-- Suppose an erased term `M` parallel η-reduces to a β-normal term `N`.
Then `M` β-reduces to a β-normal term that parallel η-reduces to `N`. -/
theorem ParEta.normalizes {M N : Expr S} (h : ParEta M N) (hM : Erased z M) (hN : Normal N) :
    ∃ X, Reduces M X ∧ Normal X ∧ ParEta X N := by
  induction h with
  | var k => exact ⟨_, .refl, Normal.var k, .var k⟩
  | sort s => exact ⟨_, .refl, Normal.sort s, .sort s⟩
  | @app f f' a a' _ _ ihf iha =>
    obtain ⟨X₁, r₁, n₁, e₁⟩ := ihf hM.app.1 hN.app_left
    obtain ⟨X₂, r₂, n₂, e₂⟩ := iha hM.app.2 hN.app_right
    obtain ⟨X, r, nX, eX⟩ := app_normalizes z _ X₁ X₂ f' a' (Nat.lt_succ_self _)
      (r₁.erased z hM.app.1) n₁ n₂ e₁ e₂ hN
    exact ⟨X, (Reduces.app r₁ r₂).trans r, nX, eX⟩
  | @lam A A' b b' hA _ _ ihb =>
    obtain ⟨rfl, hzb⟩ := hM.lam
    cases hA
    obtain ⟨X, r, nX, eX⟩ := ihb hzb hN.lam_body
    exact ⟨_, Reduces.lam .refl r, Normal.lam (Normal.sort z) nX, .lam (.sort z) eX⟩
  | @pi A A' B B' _ _ ihA ihB =>
    obtain ⟨X₁, r₁, n₁, e₁⟩ := ihA hM.pi.1 hN.pi_domain
    obtain ⟨X₂, r₂, n₂, e₂⟩ := ihB hM.pi.2 hN.pi_body
    exact ⟨_, Reduces.pi r₁ r₂, Normal.pi n₁ n₂, .pi e₁ e₂⟩
  | @head A F F' _ ih =>
    obtain ⟨rfl, hzb⟩ := hM.lam
    have hzF : Erased z F := Erased.of_rename_succ z hzb.app.1
    obtain ⟨X, r, nX, eX⟩ := ih hzF hN
    have h1 : Reduces (.lam (.sort z) (.app (F.rename Nat.succ) (.var 0)))
        (.lam (.sort z) (.app (X.rename Nat.succ) (.var 0))) :=
      Reduces.lam .refl (Reduces.app (r.rename Nat.succ) .refl)
    by_cases hX : ∃ C G, X = .lam C G
    · obtain ⟨C, G, rfl⟩ := hX
      obtain ⟨rfl, _⟩ := (r.erased z hzF).lam
      refine ⟨.lam (.sort z) G, h1.tail ?_, nX, eX⟩
      have := Beta.lam_body (A := .sort z)
        (Beta.head (Expr.sort z) (G.rename (Expr.liftRen Nat.succ)) (.var 0))
      rwa [Expr.instantiate_liftRen_succ_var] at this
    · have hnl : ∀ C G, X.rename Nat.succ ≠ .lam C G := by
        intro C G h
        cases X <;> simp [Expr.rename] at h
        exact hX ⟨_, _, rfl⟩
      exact ⟨_, h1, Normal.lam (Normal.sort z)
        (Normal.app_of (nX.rename Nat.succ) (Normal.var 0) hnl), .head (.sort z) eX⟩

/-- **Curry's lemma on erased terms.**
If an erased term reduces to a β-normal term by parallel η-steps, then it is weakly β-normalizing. -/
theorem weaklyNormalizing_of_parEta_star {M N : Expr S} (h : ReflTransGen ParEta M N)
    (hM : Erased z M) (hN : Normal N) : WeaklyNormalizing M := by
  revert hM
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact ⟨_, .refl, hN⟩
  | head he _ ih =>
    intro hM
    obtain ⟨X, hX, hXn⟩ := ih (he.erased z hM)
    obtain ⟨Y, hY, eY⟩ := he.commute_reduces hX
    obtain ⟨W, hW, hWn, _⟩ := eY.normalizes z (hY.erased z hM) hXn
    exact ⟨W, hY.trans hW, hWn⟩

/-! ## Erasure-normal reducts from weak βη-normalization -/

/-- A term is erasure-normal when its erasure is β-normal, that is, when it has no β-redex outside its λ-domains. -/
def ENormal (M : Expr S) : Prop := Normal (M.erase z)

/-- A weakly βη-normalizing term has a β-reduct with no β-redex outside its λ-domains. -/
theorem erasure_normalizes_of_betaEta {M : Expr S} (h : WeaklyNormalizingBE M) :
    ∃ M', Reduces M M' ∧ ENormal z M' := by
  obtain ⟨N, hMN, hN⟩ := h
  obtain ⟨L, hML, hLN⟩ := eta_postponement hMN
  have h1 : ReflTransGen ParEta (L.erase z) (N.erase z) := by
    clear hML hN hMN
    induction hLN with
    | refl => exact .refl
    | tail _ he ih =>
      rcases he.erase z with h | h
      · exact ih.tail (.of_eta h)
      · exact h ▸ ih
  obtain ⟨G, hG, hGn⟩ := weaklyNormalizing_of_parEta_star z h1 (Erased.erase_erased L)
    (normal_erase_of_normalBE z hN)
  obtain ⟨L', hL', rfl⟩ := reduces_of_erase z hG
  exact ⟨L', hML.trans hL', hGn⟩

theorem SystemWeaklyNormalizingBetaEta.erasure {P : Specification S}
    (h : SystemWeaklyNormalizingBetaEta P) {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {M : Expr S} (hM : Legal P Γ M) : ∃ M', Reduces M M' ∧ ENormal z M' :=
  erasure_normalizes_of_betaEta z (h Γ hΓ M hM)

/-! ## Faithfulness of erasure on erasure-normal legal terms -/

namespace ENormal

variable {z}

theorem app {f a : Expr S} (h : ENormal z (.app f a)) :
    ENormal z f ∧ ENormal z a ∧ ∀ A b, f ≠ .lam A b := by
  have h' : Normal (.app (f.erase z) (a.erase z)) := h
  refine ⟨h'.app_left, h'.app_right, ?_⟩
  rintro A b rfl
  exact h' _ (.head _ _ _)

theorem lam {A b : Expr S} (h : ENormal z (.lam A b)) : ENormal z b := by
  have h' : Normal (.lam (.sort z) (b.erase z)) := h
  exact h'.lam_body

theorem pi {A B : Expr S} (h : ENormal z (.pi A B)) : ENormal z A ∧ ENormal z B := by
  have h' : Normal (.pi (A.erase z) (B.erase z)) := h
  exact ⟨h'.pi_domain, h'.pi_body⟩

end ENormal

/-- An erasure-normal term with a product type that is not an abstraction is a neutral spine. -/
theorem neutral_of_enormal {P : Specification S} : ∀ (f : Expr S) {Γ : List (Expr S)}
    {D E : Expr S}, HasType P Γ f (.pi D E) → ENormal z f → (∀ A b, f ≠ .lam A b) →
      Neutral f := by
  intro f
  induction f with
  | var n => intro _ _ _ _ _ _; exact .var n
  | sort s => intro _ _ _ h _ _; exact h.sort_cannot_have_product_type.elim
  | pi A B _ _ => intro _ _ _ h _ _; exact h.product_cannot_have_product_type.elim
  | lam A b _ _ => intro _ _ _ _ _ hnl; exact (hnl A b rfl).elim
  | app g c ihg _ =>
    intro Γ D E h he _
    obtain ⟨D', E', hg, _, _⟩ := h.generation_app
    obtain ⟨eg, _, gnl⟩ := he.app
    exact .app (ihg hg eg gnl)

/-- **Faithfulness.**
Let `M` and `N` be legal terms that are erasure-normal and have the same erasure.
If `M` is not an abstraction, or if the types of `M` and `N` are β-convertible, then `M` and `N` are β-convertible. -/
theorem faithful {P : Specification S} : ∀ (M : Expr S) {Γ : List (Expr S)} {N T U : Expr S},
    HasType P Γ M T → HasType P Γ N U → ENormal z M → ENormal z N →
    M.erase z = N.erase z → ((∀ A b, M ≠ .lam A b) ∨ Converts T U) → Converts M N := by
  intro M
  induction M with
  | var n =>
    intro Γ N T U _ _ _ _ he _
    cases N <;> simp [Expr.erase] at he
    subst he
    exact .refl _
  | sort s =>
    intro Γ N T U _ _ _ _ he _
    cases N <;> simp [Expr.erase] at he
    subst he
    exact .refl _
  | pi A B ihA ihB =>
    intro Γ N T U hM hN eM eN he _
    cases N <;> simp [Expr.erase] at he
    rename_i A' B'
    obtain ⟨heA, heB⟩ := he
    obtain ⟨s₁, s₂, s₃, hA, hB, _, _⟩ := hM.generation_pi
    obtain ⟨t₁, t₂, t₃, hA', hB', _, _⟩ := hN.generation_pi
    have cA : Converts A A' := ihA hA hA' eM.pi.1 eN.pi.1 heA
      (.inl (fun C c h => by subst h; exact hA.lambda_cannot_have_sort_type))
    have hB'' := hB'.context_head_conversion hA' hA (.symm _ _ cA)
    have cB : Converts B B' := ihB hB hB'' eM.pi.2 eN.pi.2 heB
      (.inl (fun C c h => by subst h; exact hB.lambda_cannot_have_sort_type))
    exact Converts.pi cA cB
  | lam A b _ ihb =>
    intro Γ N T U hM hN eM eN he hc
    cases N <;> simp [Expr.erase] at he
    rename_i A' b'
    rcases hc with hc | hc
    · exact (hc A b rfl).elim
    obtain ⟨B, s, hb, hPi, cT⟩ := hM.generation_lam
    obtain ⟨B', s', hb', hPi', cU⟩ := hN.generation_lam
    have hpp : Converts (.pi A B) (.pi A' B') :=
      .trans _ _ _ (.symm _ _ cT) (.trans _ _ _ hc cU)
    obtain ⟨cA, cB⟩ := hpp.product_compatibility
    obtain ⟨s₁, _, _, hA, _, _, _⟩ := hPi.generation_pi
    obtain ⟨t₁, _, _, hA', _, _, _⟩ := hPi'.generation_pi
    have hb'' := hb'.context_head_conversion hA' hA (.symm _ _ cA)
    have cb : Converts b b' := ihb hb hb'' eM.lam eN.lam he (.inr cB)
    exact Converts.lam_congr cA cb
  | app f a ihf iha =>
    intro Γ N T U hM hN eM eN he _
    cases N <;> simp [Expr.erase] at he
    rename_i f' a'
    obtain ⟨hef, hea⟩ := he
    obtain ⟨D, E, hf, ha, _⟩ := hM.generation_app
    obtain ⟨D', E', hf', ha', _⟩ := hN.generation_app
    obtain ⟨ef, ea, fnl⟩ := eM.app
    obtain ⟨ef', ea', _⟩ := eN.app
    have cf : Converts f f' := ihf hf hf' ef ef' hef (.inl fnl)
    have hneu : Neutral f := neutral_of_enormal z f hf ef fnl
    have cty : Converts (.pi D E) (.pi D' E') := by
      obtain ⟨g, hg, hg'⟩ := cf.join
      exact HasType.neutral_unique (hneu.reduces hg) (hf.subject_reduces hg)
        (hf'.subject_reduces hg')
    have ca : Converts a a' := iha ha ha' ea ea' hea (.inr cty.product_compatibility.1)
    exact Converts.app_congr cf ca

/-! ## Keys -/

/-- The key of a term is the β-normal form of its erasure. -/
noncomputable def Expr.key (M : Expr S) : Expr S := (M.erase z).normalForm

theorem Reduces.erase {M N : Expr S} (h : Reduces M N) : Reduces (M.erase z) (N.erase z) := by
  induction h with
  | refl => exact .refl
  | tail _ hb ih =>
    rcases hb.erase z with h | h
    · exact ih.tail h
    · exact h ▸ ih

theorem Converts.erase {M N : Expr S} (h : Converts M N) : Converts (M.erase z) (N.erase z) := by
  induction h with
  | rel a b h =>
    rcases h.erase z with h | h
    · exact .rel _ _ h
    · rw [h]; exact .refl _
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem key_spec {M M' : Expr S} (hr : Reduces M M') (hn : ENormal z M') :
    M.key z = M'.erase z :=
  Expr.normalForm_eq (hr.erase z) hn

/-- Let `A` and `B` be legal types that have erasure-normal β-reducts.
Then `A` and `B` have the same key exactly when they are β-convertible. -/
theorem key_eq_iff {P : Specification S} {Γ : List (Expr S)} {A B : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (wA : ∃ A', Reduces A A' ∧ ENormal z A') (wB : ∃ B', Reduces B B' ∧ ENormal z B') :
    A.key z = B.key z ↔ Converts A B := by
  obtain ⟨A', rA, nA⟩ := wA
  obtain ⟨B', rB, nB⟩ := wB
  rw [key_spec z rA nA, key_spec z rB nB]
  constructor
  · intro he
    have hA' := hA.subject_reduces rA
    have hB' := hB.subject_reduces rB
    have c := faithful z A' hA' hB' nA nB he
      (.inl (fun C c h => by subst h; exact hA'.lambda_cannot_have_sort_type))
    exact .trans _ _ _ rA.converts (.trans _ _ _ c (.symm _ _ rB.converts))
  · intro hc
    have c : Converts (A'.erase z) (B'.erase z) :=
      Converts.erase z (.trans _ _ _ (.symm _ _ rA.converts) (.trans _ _ _ hc rB.converts))
    exact Normal.eq_of_converts nA nB c

end PureTypeSystem
