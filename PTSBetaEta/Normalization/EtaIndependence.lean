module

public import PTSBetaEta.Normalization.Substitution

@[expose] public section

/-!
# Independence of the evaluation from η

Consider the typing trees of two erasure-normal terms that are βη-convertible, in equivalent contexts and in environments with the same data.
They have the same values, and the same `read` at sorts.
This generalizes `enormal_tree_independence`, where the two erasures had to be equal.
The new case is an abstraction `λx. m` against a neutral term `F` with `m` convertible to `F x`.
There the value of the abstraction is the λ-value of the η-expansion of the canonical value of `F`, and `lambdaValue_eta` shows that this is the canonical value of `F` again.
The induction is on a size in which an abstraction weighs more than an application to a variable.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem
universe u
open Relation

namespace Expr
variable {S : Type u}

/-- A size in which an abstraction weighs more than an application to a variable.
λ-domains are not counted. -/
def etaSize : Expr S → Nat
  | .var _ => 1
  | .sort _ => 1
  | .app f a => etaSize f + etaSize a + 1
  | .lam _ b => etaSize b + 3
  | .pi A B => etaSize A + etaSize B + 1

theorem etaSize_pos (M : Expr S) : 1 ≤ M.etaSize := by
  cases M <;> simp only [etaSize] <;> omega

theorem etaSize_rename (M : Expr S) : ∀ ρ : Nat → Nat, (M.rename ρ).etaSize = M.etaSize := by
  induction M with
  | var n => intro ρ; rfl
  | sort s => intro ρ; rfl
  | app f a ihf iha => intro ρ; simp only [rename, etaSize, ihf, iha]
  | lam A b ihA ihb => intro ρ; simp only [rename, etaSize, ihb]
  | pi A B ihA ihB => intro ρ; simp only [rename, etaSize, ihA, ihB]

theorem rename_lift_instantiate_zero (M : Expr S) :
    (M.rename (liftRen Nat.succ)).instantiate (.var 0) = M := by
  have h : (single (.var 0 : Expr S)) ∘ liftRen Nat.succ = Expr.var := by
    funext i
    cases i <;> rfl
  rw [instantiate, subst_rename, h, subst_var]
end Expr

variable {S : Type u} [Nonempty S]

theorem neutral_rename {M : Expr S} (h : Neutral M) (ρ : Nat → Nat) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app _ ih => exact .app ih

/-- If `λx:A. m` is βη-convertible to `X`, then `m` is βη-convertible to the application of the shifted `X` to the bound variable. -/
theorem convertsBE_lam_body {A m X : Expr S} (h : ConvertsBE (.lam A m) X) :
    ConvertsBE m (.app (X.rename Nat.succ) (.var 0)) := by
  have h1 : ConvertsBE (.app ((Expr.lam A m).rename Nat.succ) (.var 0)) m := by
    have hb := Beta.head (A.rename Nat.succ) (m.rename (Expr.liftRen Nat.succ)) (.var 0)
    rw [Expr.rename_lift_instantiate_zero] at hb
    exact EqvGen.rel _ _ (Or.inl hb)
  exact .trans _ _ _ (.symm _ _ h1) (ConvertsBE.app_congr (h.rename Nat.succ) (.refl _))

theorem convertsBE_lam_lam {A B m m' : Expr S} (h : ConvertsBE (.lam A m) (.lam B m')) :
    ConvertsBE m m' := by
  have h2 : ConvertsBE (.app ((Expr.lam B m').rename Nat.succ) (.var 0)) m' := by
    have hb := Beta.head (B.rename Nat.succ) (m'.rename (Expr.liftRen Nat.succ)) (.var 0)
    rw [Expr.rename_lift_instantiate_zero] at hb
    exact EqvGen.rel _ _ (Or.inl hb)
  exact .trans _ _ _ (convertsBE_lam_body h) h2

theorem neutral_not_sort (z : S) {M : Expr S} (hM : Neutral M) {s : S}
    (h : ConvertsBE M (.sort s)) : False := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  have hW := stepE_star_neutral_erase hM h₁
  have hs : W = .sort s := stepE_star_sort_inv z h₂
  subst hs
  cases hW

theorem neutral_not_pi (z : S) {M : Expr S} (hM : Neutral M) {A B : Expr S}
    (h : ConvertsBE M (.pi A B)) : False := by
  obtain ⟨W, h₁, h₂⟩ := convertsBE_join z h
  have hW := stepE_star_neutral_erase hM h₁
  obtain ⟨Y₁, Y₂, rfl, _, _⟩ := stepE_star_pi_inv z h₂
  cases hW

end PureTypeSystem

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment.SameData
variable {Ω C hno} {Γ Δ : List (Expr S)}
theorem symm' {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
    (hef : e.SameData f) (hctx : ContextEquivalentBE P Γ Δ) : f.SameData e := by
  refine ⟨hef.1.symm, fun i A hi => ?_⟩
  obtain ⟨A', hl', hc'⟩ := ((hctx.typing _ _).mpr (HasTypeBE.lookup hctx.valid_right hi)).generation
  obtain ⟨s, hs⟩ := HasTypeBE.lookup_sorted hctx.valid_right hi
  obtain ⟨s', hs'⟩ := HasTypeBE.lookup_sorted hctx.valid_left hl'
  have hk : (A.subst f.images).knf = (A'.subst e.images).knf := by
    rw [← hef.1]
    exact Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst ((hctx.typing _ _).mpr hs) e.typed).kwn hw)
      ((ContextTowerBE.THasTypeBE.subst hs' e.typed).kwn hw) (hc'.subst e.images).k
  rw [hk]
  exact (hef.2 i A' hl').symm
end Environment.SameData

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
theorem application_frame' {f n A B : Expr S} (h : HasTypeBE P Γ (.app f n) T)
    (hf : HasTypeBE P Γ f (.pi A B)) (hn : HasTypeBE P Γ n A) (hc : ConvertsBE T (B.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi A B))
    (en : Evaluator (hw := hw) Ω C hno Γ n A)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images).knf))
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) :
    ∃ (k : FrameKey Ω C (e.activeType hf hF))
      (hp : PayloadFits Ω C hno k.domain (en e).parameter),
      k.argument = (n.subst e.images).knf ∧
      ((application h hf hn hc ef en e).val ha).val =
        (applyValue Ω C hno _ ((ef e).val hF) k (en e).parameter hp).val := by
  unfold application baseResult applicationValue
  simp only [dite_eq_left hF]
  exact ⟨_,(en e).parameter_fits,rfl,rfl⟩
end PreResult

/-- η-independence for all terms up to a given size. -/
def EtaIndep (N : Nat) : Prop :=
  ∀ {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) {Δ : List (Expr S)}
    {M' U : Expr S} (t' : TypingTreeBE P Δ M' U), M.etaSize + M'.etaSize ≤ N →
    ENormal dz M → ENormal dz M' → ConvertsBE M M' → ContextEquivalentBE P Γ Δ →
    ∀ (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ), e.SameData f →
    (ConvertsBE T U → (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' f).parameter) ∧
    (∀ s s', T = .sort s → U = .sort s' →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' f).read.val)

/-- **The η case**, in which an abstraction is compared with a neutral term. -/
theorem eta_case (hC : IsComponent (PrimaryEdge P) C) {N : Nat} (ih : EtaIndep (hw := hw) Ω C hno N)
    {Γ : List (Expr S)} {D m E T : Expr S} {a s : S}
    (ht : HasTypeBE P Γ (.lam D m) T) (d : TypingTreeBE P Γ D (.sort a))
    (b : TypingTreeBE P (D :: Γ) m E)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    {Δ : List (Expr S)} {M' U : Expr S} (t' : TypingTreeBE P Δ M' U) (hne : Neutral M')
    (hsz : (Expr.lam D m).etaSize + M'.etaSize ≤ N + 1)
    (hn : ENormal dz (.lam D m)) (hn' : ENormal dz M') (hmm : ConvertsBE (.lam D m) M')
    (hctx : ContextEquivalentBE P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.SameData f) (hTU : ConvertsBE T U) :
    (preEvaluate Ω C hno (.abstraction ht d b hp hc) e).parameter =
      (preEvaluate Ω C hno t' f).parameter := by
  have hU : ConvertsBE U (.pi D E) := .trans _ _ _ (.symm _ _ hTU) hc
  have hpΔ := (hctx.typing _ _).mp hp
  have hdΔ := (hctx.typing _ _).mp d.typing
  have hN'pi : HasTypeBE P Δ M' (.pi D E) := .conversion t'.typing hpΔ hU
  have hΔ' : ValidContextBE P (D :: Δ) := .cons hdΔ.valid hdΔ
  let ft : TypingTreeBE P (D :: Δ) (M'.rename Nat.succ)
      (.pi (D.rename Nat.succ) (E.rename (Expr.liftRen Nat.succ))) :=
    (t'.retarget hN'pi (.symm _ _ hU)).rename hΔ' Nat.succ (TypingTreeBE.DeclRenaming.weaken D)
  let at' : TypingTreeBE P (D :: Δ) (.var 0) (D.rename Nat.succ) := .var (.var hdΔ) (.zero D Δ) (.refl _)
  have hEE : (E.rename (Expr.liftRen Nat.succ)).instantiate (.var 0) = E := Expr.rename_lift_instantiate_zero E
  have happ : HasTypeBE P (D :: Δ) (.app (M'.rename Nat.succ) (.var 0)) E := by
    have h0 := HasTypeBE.application ft.typing at'.typing
    rw [hEE] at h0
    exact h0
  have hcv : ConvertsBE E ((E.rename (Expr.liftRen Nat.succ)).instantiate (.var 0)) := by
    rw [hEE]; exact .refl _
  let t'' : TypingTreeBE P (D :: Δ) (.app (M'.rename Nat.succ) (.var 0)) E :=
    .application happ ft at' hcv
  have hTk : (T.subst e.images).knf = (U.subst f.images).knf :=
    hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
      ((ContextTowerBE.THasTypeBE.subst t'.typing f.typed).type_kwn hw) hTU
  apply PreResult.parameter_congr _ _ hTk
  intro ha hb
  let Tb := f.activeType t'.typing hb
  let W := (preEvaluate Ω C hno t' f).val hb
  have hW : canonValue hno Tb W = W := preEvaluate_canonical Ω C hno hC t' f hb
  have hpi := PreResult.abstraction_type ht hp hc e
  have hns : ¬ IsSortType Tb := by
    rintro ⟨s', hs'⟩
    have h1 : (U.subst f.images).knf = .sort s' := hs'
    rw [← hTk, hpi] at h1
    cases h1
  show _ = W.val
  rw [← hW, ← lambdaValue_eta Tb hns W]
  refine lambdaValue_congr Ω C hno hTk (PreResult.abstractionAction ht hp hc (preEvaluate Ω C hno b) e ha)
    (etaAction Ω C hno Tb W) ?_
  intro k k' hkk p hp1 hp2
  obtain ⟨e1, ha1, he1, hv1, -⟩ :=
    PreResult.abstractionAction_val ht hp hc (preEvaluate Ω C hno b) e ha k p hp1
  rw [hv1]
  let t0 := ProductInstance.ofFormation hp e
  have hfa := t0.frameArgument_spec hpi k
  have hn0e : Ω.THasTypeBE (t0.frameArgument hpi k) (D.subst e.images) := t0.rawArgument hfa.1
  have hn0f : Ω.THasTypeBE (t0.frameArgument hpi k) (D.subst f.images) := hef.1 ▸ hn0e
  have hkdom : k.domain = (D.subst e.images).knf := ProductInstance.frame_domain t0 hpi k
  have hpe : PayloadFits Ω C hno (D.subst e.images).knf p := hkdom ▸ hp1
  have hpf : PayloadFits Ω C hno (D.subst f.images).knf p := hef.1 ▸ hpe
  let f1 := f.cons hn0f p hpf
  have hsd : e1.SameData f1 := by
    subst he1
    exact hef.cons hn0e hn0f rfl p hpe hpf
  have hsz' : m.etaSize + (Expr.app (M'.rename Nat.succ) (.var 0)).etaSize ≤ N := by
    simp only [Expr.etaSize, Expr.etaSize_rename] at hsz ⊢
    omega
  have hn'' : ENormal dz (.app (M'.rename Nat.succ) (.var 0)) := by
    show Normal ((Expr.app (M'.rename Nat.succ) (.var 0)).erase dz)
    simp only [Expr.erase, Expr.erase_rename]
    refine Normal.app_of (Normal.rename hn' _) (fun _ h => by cases h) ?_
    intro A b' hab
    have hne' := neutral_rename (hne.erase dz) Nat.succ
    rw [hab] at hne'
    cases hne'
  have key := (ih b t'' hsz' hn.lam hn'' (convertsBE_lam_body hmm) (hctx.cons d.typing) e1 f1 hsd).1 (.refl _)
  have hb1 : ActiveLayer P C (Ω.kprofile (E.subst f1.images).knf) := by
    rw [← hsd.1]
    exact ha1
  rw [PreResult.val_congr _ _ key ha1 hb1]
  have hFk : ((Expr.pi (D.rename Nat.succ) (E.rename (Expr.liftRen Nat.succ))).subst f1.images).knf =
      (U.subst f.images).knf := by
    have h1 : (Expr.pi (D.rename Nat.succ) (E.rename (Expr.liftRen Nat.succ))).subst f1.images =
        (Expr.pi D E).subst f.images := Expr.raise_subst_cons (.pi D E) _ f.images
    rw [h1]
    exact Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hN'pi f.typed).type_kwn hw)
      ((ContextTowerBE.THasTypeBE.subst t'.typing f.typed).type_kwn hw)
      (ConvertsBE.subst (.symm _ _ hU) f.images).k
  have hF : ActiveLayer P C (Ω.kprofile ((Expr.pi (D.rename Nat.succ)
      (E.rename (Expr.liftRen Nat.succ))).subst f1.images).knf) := by
    rw [hFk]
    exact hb
  obtain ⟨k'', hpp, hka, hval⟩ := PreResult.application_frame' happ ft.typing at'.typing hcv
    (preEvaluate Ω C hno ft) (preEvaluate Ω C hno at') f1 hF hb1
  change ((PreResult.application happ ft.typing at'.typing hcv (preEvaluate Ω C hno ft)
    (preEvaluate Ω C hno at') f1).val hb1).val = _
  rw [hval]
  have hdom : k'.domain = k.domain := (Expr.pi.inj (k'.product.symm.trans (hTk.symm.trans k.product))).1
  have hq : (preEvaluate Ω C hno at' f1).parameter = canonOpt hno k'.domain p := by
    refine (PreResult.lookup_parameter (HasTypeBE.var hdΔ) (.zero D Δ) (.refl _) f1).trans ?_
    have h2 : ((D.rename Nat.succ).subst f1.images).knf = k'.domain := by
      rw [hdom, hkdom, hef.1]
      exact congrArg Expr.knf (Expr.raise_subst_cons D _ f.images)
    rw [h2]
    rfl
  have hVft : ((preEvaluate Ω C hno ft f1).val hF).val = W.val := by
    have h1 := preEvaluate_retarget_parameter Ω C hno t' hN'pi (.symm _ _ hU) f
    have h2 := (preEvaluate_rename Ω C hno (t'.retarget hN'pi (.symm _ _ hU)) hΔ' Nat.succ
      (TypingTreeBE.DeclRenaming.weaken D) f f1 (fun i _ => ⟨rfl, rfl⟩)).1
    exact PreResult.val_congr _ _ (h1.trans h2).symm hF hb
  have hka' : k''.argument = k'.argument := by
    rw [hka, ← hkk]
    exact hfa.2
  rw [applyValue_congr Ω C hno hFk ((preEvaluate Ω C hno ft f1).val hF) W hVft k'' k' hka' _ _ hq hpp
    (canonOpt_fits hp2)]
  have h4 := applyValue_canon Tb W k' (canonOpt hno k'.domain p) (canonOpt_fits hp2)
  rw [hW] at h4
  simp only [canonOpt_idem] at h4
  exact congrArg Subtype.val h4

/-- **η-independence**, by induction on the bound on the size. -/
theorem eta_independence (hC : IsComponent (PrimaryEdge P) C) :
    ∀ N, EtaIndep (hw := hw) Ω C hno N := by
  intro N
  induction N with
  | zero =>
    intro Γ M T t Δ M' U t' hsz
    have := M.etaSize_pos
    have := M'.etaSize_pos
    omega
  | succ N ih =>
    intro Γ M T t Δ M' U t' hsz hn hn' hmm hctx e f hef
    cases t with
    | @var Γ n A T ht hd hc =>
      cases t' with
      | @var _ n' A' _ ht' hd' hc' =>
        have h1 : Expr.var n' = Expr.var n := convertsBE_var_neutral dz (.var n') hmm
        cases h1
        exact enormal_tree_independence Ω C hno (.var ht hd hc) hn (.var ht' hd' hc') hn' rfl hctx e f hef
      | sort ht' _ _ => exact (neutral_not_sort dz (.var n) hmm).elim
      | product ht' _ _ _ _ => exact (neutral_not_pi dz (.var n) hmm).elim
      | abstraction ht' d' b' hp' hc' =>
        refine ⟨fun hTU => (eta_case Ω C hno hC ih ht' d' b' hp' hc' (.var ht hd hc) (.var n)
          (by omega) hn' hn (.symm _ _ hmm) hctx.symm f e (hef.symm' hctx) (.symm _ _ hTU)).symm, ?_⟩
        intro s₁ s₂ _ hs₂
        subst hs₂
        exact ht'.lambda_cannot_have_sort_type.elim
      | application ht' gt' nt' hc' =>
        obtain ⟨eg', -, gnl'⟩ := hn'.app
        have hneu' := neutral_of_enormalBE dz _ gt'.typing eg' gnl'
        have h1 := convertsBE_var_neutral dz (Neutral.app hneu') hmm
        cases h1
    | @sort Γ s₀ t₀ T ht hax hc =>
      cases t' with
      | var ht' _ _ => exact (neutral_not_sort dz (.var _) (.symm _ _ hmm)).elim
      | @sort _ s₁ t₁ _ ht' hax' hc' =>
        have h1 : s₀ = s₁ := convertsBE_sort_inj hmm
        subst h1
        exact enormal_tree_independence Ω C hno (.sort ht hax hc) hn (.sort ht' hax' hc') hn' rfl hctx e f hef
      | product ht' _ _ _ _ => exact (convertsBE_pi_not_sort (.symm _ _ hmm)).elim
      | abstraction ht' d' b' hp' hc' =>
        refine ⟨fun hTU => (convertsBE_pi_not_sort
          (.trans _ _ _ (.symm _ _ hc') (.trans _ _ _ (.symm _ _ hTU) hc))).elim, ?_⟩
        intro s₁ s₂ _ hs₂
        subst hs₂
        exact ht'.lambda_cannot_have_sort_type.elim
      | application ht' gt' nt' hc' =>
        obtain ⟨eg', -, gnl'⟩ := hn'.app
        exact (neutral_not_sort dz (Neutral.app (neutral_of_enormalBE dz _ gt'.typing eg' gnl'))
          (.symm _ _ hmm)).elim
    | @product Γ D E a b c T ht d bt hr hc =>
      cases t' with
      | var ht' _ _ => exact (neutral_not_pi dz (.var _) (.symm _ _ hmm)).elim
      | sort ht' _ _ => exact (convertsBE_pi_not_sort hmm).elim
      | @product _ D' E' a' b' c' _ ht' d' bt' hr' hc' =>
        obtain ⟨eD, eE⟩ := hn.pi
        obtain ⟨eD', eE'⟩ := hn'.pi
        obtain ⟨cD, cE⟩ := convertsBE_pi_inj dz hmm
        have hd'Γ : HasTypeBE P Γ D' (.sort a') := (hctx.typing _ _).mpr d'.typing
        have hctx' : ContextEquivalentBE P (D :: Γ) (D' :: Δ) :=
          (ContextEquivalentBE.head_conversion d.typing hd'Γ cD).trans (hctx.cons hd'Γ)
        simp only [Expr.etaSize] at hsz
        have hM : ((Expr.pi D E).subst e.images).knf = ((Expr.pi D' E').subst f.images).knf :=
          hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).kwn hw)
            ((ContextTowerBE.THasTypeBE.subst ht' f.typed).kwn hw) hmm
        have hDk : (D.subst e.images).knf = (D'.subst f.images).knf :=
          hef.conv_eq ((ContextTowerBE.THasTypeBE.subst d.typing e.typed).kwn hw)
            ((ContextTowerBE.THasTypeBE.subst d'.typing f.typed).kwn hw) cD
        have hEk : (E.subst (Expr.liftSub e.images)).knf = (E'.subst (Expr.liftSub f.images)).knf := by
          have hK1 := KWN.pi_body ((ContextTowerBE.THasTypeBE.subst ht e.typed).kwn hw)
          have hK2 := KWN.pi_body ((ContextTowerBE.THasTypeBE.subst ht' f.typed).kwn hw)
          rw [hef.1] at hK1 ⊢
          exact Expr.knf_converts hK1 hK2 (ConvertsBE.subst cE _).k
        have hpc : (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno bt) e).val =
            (PreResult.productCandidate d'.typing bt'.typing hr' (preEvaluate Ω C hno d')
              (preEvaluate Ω C hno bt') f).val := by
          apply PreResult.productCandidate_congr d.typing bt.typing hr d'.typing bt'.typing hr'
            _ _ _ _ e f hDk hEk
          · exact fun _ => (ih d d' (by omega) eD eD' cD hctx e f hef).2 a a' rfl rfl
          · intro n hn₁ hn₂ p hp hp' _
            exact (ih bt bt' (by omega) eE eE' cE hctx' (e.cons hn₁ p hp) (f.cons hn₂ p hp')
              (hef.cons hn₁ hn₂ rfl p hp hp')).2 b b' rfl rfl
        constructor
        · intro hh
          have hsorts : ConvertsBE (.sort c) (.sort c') :=
            .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
          have he : c = c' := hsorts.sort_inj
          have hT := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
            ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hh
          apply PreResult.parameter_congr _ _ hT
          apply PreResult.product_val_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
            hc hc' _ _ _ _ e f hT hM
          · exact he ▸ Iff.rfl
          · exact fun _ => hpc
        · intro _ _ _ _
          exact PreResult.product_read_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
            hc hc' _ _ _ _ e f hM (fun _ => hpc)
      | abstraction ht' d' b' hp' hc' =>
        refine ⟨fun hTU => (convertsBE_pi_not_sort
          (.trans _ _ _ (.symm _ _ hc') (.trans _ _ _ (.symm _ _ hTU) hc))).elim, ?_⟩
        intro s₁ s₂ _ hs₂
        subst hs₂
        exact ht'.lambda_cannot_have_sort_type.elim
      | application ht' gt' nt' hc' =>
        obtain ⟨eg', -, gnl'⟩ := hn'.app
        exact (neutral_not_pi dz (Neutral.app (neutral_of_enormalBE dz _ gt'.typing eg' gnl'))
          (.symm _ _ hmm)).elim
    | @abstraction Γ D m E a s T ht d b hp hc =>
      cases t' with
      | var ht' hd' hc' =>
        refine ⟨fun hTU => eta_case Ω C hno hC ih ht d b hp hc (.var ht' hd' hc') (.var _) hsz hn hn'
          hmm hctx e f hef hTU, ?_⟩
        intro s₁ _ hs₁ _
        subst hs₁
        exact ht.lambda_cannot_have_sort_type.elim
      | sort ht' _ hc' =>
        refine ⟨fun hTU => (convertsBE_pi_not_sort
          (.trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hTU hc'))).elim, ?_⟩
        intro s₁ _ hs₁ _
        subst hs₁
        exact ht.lambda_cannot_have_sort_type.elim
      | product ht' _ _ _ hc' =>
        refine ⟨fun hTU => (convertsBE_pi_not_sort
          (.trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hTU hc'))).elim, ?_⟩
        intro s₁ _ hs₁ _
        subst hs₁
        exact ht.lambda_cannot_have_sort_type.elim
      | @abstraction _ D' m' E' a' s' _ ht' d' b' hp' hc' =>
        have cm : ConvertsBE m m' := convertsBE_lam_lam hmm
        simp only [Expr.etaSize] at hsz
        constructor
        · intro hh
          have hproducts : ConvertsBE (.pi D E) (.pi D' E') :=
            .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
          obtain ⟨cD, cE⟩ := hproducts.product_compatibility dz
          have hT := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
            ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hh
          have hd'Γ : HasTypeBE P Γ D' (.sort a') := (hctx.typing _ _).mpr d'.typing
          have hctx' : ContextEquivalentBE P (D :: Γ) (D' :: Δ) :=
            (ContextEquivalentBE.head_conversion d.typing hd'Γ cD).trans (hctx.cons hd'Γ)
          apply PreResult.parameter_congr _ _ hT
          apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e f hT
          intro n n' hnt hn'' hnn p hpa hpb hact hact'
          subst hnn
          exact PreResult.val_congr _ _ ((ih b b' (by omega) hn.lam hn'.lam cm hctx'
            (e.cons hnt p hpa) (f.cons hn'' p hpb) (hef.cons hnt hn'' rfl p hpa hpb)).1 cE) hact hact'
        · intro r r' hs _
          exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
      | application ht' gt' nt' hc' =>
        obtain ⟨eg', -, gnl'⟩ := hn'.app
        have hneu' := neutral_of_enormalBE dz _ gt'.typing eg' gnl'
        refine ⟨fun hTU => eta_case Ω C hno hC ih ht d b hp hc (.application ht' gt' nt' hc')
          (.app hneu') hsz hn hn' hmm hctx e f hef hTU, ?_⟩
        intro s₁ _ hs₁ _
        subst hs₁
        exact ht.lambda_cannot_have_sort_type.elim
    | @application Γ g n D E T ht gt nt hc =>
      obtain ⟨eg, en, gnl⟩ := hn.app
      have hneu : Neutral g := neutral_of_enormalBE dz g gt.typing eg gnl
      cases t' with
      | var ht' hd' hc' =>
        have h1 := convertsBE_var_neutral dz (Neutral.app hneu) (.symm _ _ hmm)
        cases h1
      | sort ht' _ _ => exact (neutral_not_sort dz (Neutral.app hneu) hmm).elim
      | product ht' _ _ _ _ => exact (neutral_not_pi dz (Neutral.app hneu) hmm).elim
      | abstraction ht' d' b' hp' hc' =>
        refine ⟨fun hTU => (eta_case Ω C hno hC ih ht' d' b' hp' hc' (.application ht gt nt hc)
          (.app hneu) (by omega) hn' hn (.symm _ _ hmm) hctx.symm f e (hef.symm' hctx)
          (.symm _ _ hTU)).symm, ?_⟩
        intro s₁ s₂ _ hs₂
        subst hs₂
        exact ht'.lambda_cannot_have_sort_type.elim
      | @application _ g' n' D' E' _ ht' gt' nt' hc' =>
        obtain ⟨eg', en', gnl'⟩ := hn'.app
        have hneu' : Neutral g' := neutral_of_enormalBE dz g' gt'.typing eg' gnl'
        obtain ⟨g'', b'', heq, -, cg, cn⟩ := convertsBE_app_neutral dz hneu (Neutral.app hneu') hmm
        obtain ⟨rfl, rfl⟩ := Expr.app.inj heq
        simp only [Expr.etaSize] at hsz
        have hgΓ := (hctx.typing _ _).mpr gt'.typing
        have hF : ConvertsBE (.pi D E) (.pi D' E') :=
          HasTypeBE.neutral_unique_conv dz hneu hneu' cg gt.typing hgΓ
        have hD := (hF.product_compatibility dz).1
        have hv : ConvertsBE T U → (preEvaluate Ω C hno (.application ht gt nt hc) e).parameter =
            (preEvaluate Ω C hno (.application ht' gt' nt' hc') f).parameter := by
          intro hh
          have hT := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
            ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hh
          apply PreResult.parameter_congr _ _ hT
          apply PreResult.application_val_congr ht ht' gt.typing gt'.typing nt.typing nt'.typing
            hc hc' _ _ _ _ e f hT
            (hef.conv_eq ((ContextTowerBE.THasTypeBE.subst gt.typing e.typed).type_kwn hw)
              ((ContextTowerBE.THasTypeBE.subst gt'.typing f.typed).type_kwn hw) hF)
            (hef.conv_eq ((ContextTowerBE.THasTypeBE.subst nt.typing e.typed).kwn hw)
              ((ContextTowerBE.THasTypeBE.subst nt'.typing f.typed).kwn hw) cn)
          · exact fun ha hb => PreResult.val_congr _ _
              ((ih gt gt' (by omega) eg eg' cg hctx e f hef).1 hF) ha hb
          · exact (ih nt nt' (by omega) en en' cn hctx e f hef).1 hD
        refine ⟨hv, ?_⟩
        intro s s' hs hs'
        subst hs hs'
        have ht'' := (hctx.typing _ _).mpr ht'
        have hss : ConvertsBE (Expr.sort s) (.sort s') :=
          HasTypeBE.neutral_unique_conv dz (Neutral.app hneu) (Neutral.app hneu') hmm ht ht''
        have he : s = s' := hss.sort_inj
        subst he
        apply PreResult.baseRead_congr ht ht'
          (hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).kwn hw)
            ((ContextTowerBE.THasTypeBE.subst ht' f.typed).kwn hw) hmm) rfl Iff.rfl
        exact fun ha hb => PreResult.val_congr _ _ (hv (.refl _)) ha hb

/-- **Independence of conversion.**
The typing trees of two erasure-normal terms that are βη-convertible have the same values and the same `read` at sorts. -/
theorem enormal_conv_independence (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) (hM : ENormal dz M)
    {Δ : List (Expr S)} {M' U : Expr S} (t' : TypingTreeBE P Δ M' U) (hM' : ENormal dz M')
    (hmm : ConvertsBE M M') (hctx : ContextEquivalentBE P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ) (hef : e.SameData f) :
    (ConvertsBE T U → (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' f).parameter) ∧
    (∀ s s', T = .sort s → U = .sort s' →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' f).read.val) :=
  eta_independence Ω C hno hC _ t t' le_rfl hM hM' hmm hctx e f hef

end PureTypeSystem.KP.ObservationValues

