/- Adapted to typing with βη-conversion from OpenAI's `ObservationReduction.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.EtaIndependence

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
theorem application_frame {f n A B : Expr S} (h : HasTypeBE P Γ (.app f n) T)
    (hf : HasTypeBE P Γ f (.pi A B)) (hn : HasTypeBE P Γ n A) (hc : ConvertsBE T (B.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi A B))
    (en : Evaluator (hw := hw) Ω C hno Γ n A)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images).knf))
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) :
    ∃ (k : FrameKey Ω C (e.activeType hf hF))
      (hp : PayloadFits Ω C hno k.domain (en e).parameter),
      k.argument = (n.subst e.images).knf ∧ k.domain = (A.subst e.images).knf ∧
      ((application h hf hn hc ef en e).val ha).val =
        (applyValue Ω C hno _ ((ef e).val hF) k (en e).parameter hp).val := by
  unfold application baseResult applicationValue
  simp only [dite_eq_left hF]
  exact ⟨_,(en e).parameter_fits,rfl,rfl,rfl⟩

theorem abstractionAction_raw {D m E : Expr S} {s : S}
    (h : HasTypeBE P Γ (.lam D m) T) (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hc : ConvertsBE T (.pi D E)) (b : TypingTreeBE P (D :: Γ) m E)
    (hC : IsComponent (PrimaryEdge P) C)
    (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (k : FrameKey Ω C (e.activeType h ha))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hpp : PayloadFits Ω C hno k.domain p)
    (n : Expr S) (hn : Ω.THasTypeBE n (D.subst e.images))
    (hp' : PayloadFits Ω C hno (D.subst e.images).knf p)
    (hkn : k.argument = n.knf)
    (ha' : ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n e.images)).knf)) :
    (abstractionAction h hp hc (preEvaluate Ω C hno b) e ha k p hpp).val =
      ((preEvaluate Ω C hno b (e.cons hn p hp')).val ha').val := by
  unfold abstractionAction
  apply val_congr
  apply (preEvaluate_compatible Ω C hno hC b _ _ ?_).1
  constructor
  · intro i hi
    cases i with
    | zero =>
        have hs := ProductInstance.frameArgument_spec (ProductInstance.ofFormation hp e)
          (PreResult.abstraction_type h hp hc e) k
        exact KConverts.of_knf_eq (hs.1.kwn hw) (hn.kwn hw) (hs.2.trans hkn)
    | succ i => exact .refl _
  · intro i hi
    cases i <;> rfl
end PreResult

 theorem application_abstraction_beta {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasTypeBE P Γ (.app (.lam D m) n) T)
    (hf : HasTypeBE P Γ (.lam D m) (.pi A B))
    (d : TypingTreeBE P Γ D (.sort a)) (b : TypingTreeBE P (D :: Γ) m E)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hcF : ConvertsBE (.pi A B) (.pi D E))
    (nt : TypingTreeBE P Γ n A) (hc : ConvertsBE T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images).knf))
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) :
    ∃ (hnD : Ω.THasTypeBE (n.subst e.images) (D.subst e.images))
      (hpp : PayloadFits Ω C hno (D.subst e.images).knf (preEvaluate Ω C hno nt e).parameter)
      (hb : ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub (n.subst e.images) e.images)).knf)),
      (Ω.kprofile (D.subst e.images) ∈ ObservationLayers P C → ActiveLayer P C (Ω.kprofile (D.subst e.images))) ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno b (e.cons hnD (preEvaluate Ω C hno nt e).parameter hpp)).val hb).val := by
  obtain ⟨k,hpk,hkn,hkD,hval⟩ := PreResult.application_frame ht hf nt.typing hc
    (preEvaluate Ω C hno (.abstraction hf d b hp hcF)) (preEvaluate Ω C hno nt) e hF ha
  have hnD : HasTypeBE P Γ n D := .conversion nt.typing d.typing (hcF.product_compatibility dz).1
  have hAD := e.type_convert_eq nt.typing hnD (hcF.product_compatibility dz).1
  have hpp : PayloadFits Ω C hno (D.subst e.images).knf (preEvaluate Ω C hno nt e).parameter :=
    hAD ▸ (preEvaluate Ω C hno nt e).parameter_fits
  have hbT : ConvertsBE T (E.instantiate n) := .trans _ _ _ hc ((hcF.product_compatibility dz).2.subst (Expr.single n))
  have heT := e.type_convert_eq ht (b.typing.instantiate hnD) hbT
  have heT' : (T.subst e.images).knf =
      (E.subst (Expr.consSub (n.subst e.images) e.images)).knf := by
    simpa only [Expr.instantiate,Expr.subst_compSub,Expr.comp_single] using heT
  have hb : ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub (n.subst e.images) e.images)).knf) := heT' ▸ ha
  refine ⟨ContextTowerBE.THasTypeBE.subst hnD e.typed,hpp,hb,?_,?_⟩
  · intro hH
    have heD : Ω.kprofile k.domain = Ω.kprofile (D.subst e.images) := by rw [hkD,hAD,Ω.kprofile_knf]
    rw [← heD]
    exact k.domain_active hw (heD.symm ▸ hH)
  · obtain ⟨F,hB⟩ := preEvaluate_uniform Ω C hno hC b
    refine hval.trans ?_
    rw [show ((preEvaluate Ω C hno (.abstraction hf d b hp hcF) e).val hF) =
      (PreResult.abstraction hf hp hcF (preEvaluate Ω C hno b) e).val hF from rfl,
      PreResult.abstraction_beta hf hp hcF _ hB e hF k _ hpk]
    apply PreResult.abstractionAction_raw hf hp hcF b hC e hF k _ hpk
      (n.subst e.images) (ContextTowerBE.THasTypeBE.subst hnD e.typed) hpp _ hb
    exact hkn

/-- Transport between two typing trees with the same root type.
Only the observations of good trees are required to be equal, and environments and values are otherwise unrestricted. -/
structure GoodTransport {Γ : List (Expr S)} {M N T : Expr S}
    (t : TypingTreeBE P Γ M T) (t' : TypingTreeBE P Γ N T) : Prop where
  val : ∀ (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)),
    ValGood Ω C t e.images → ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno t e).val ha).val = ((preEvaluate Ω C hno t' e).val ha).val
  read : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C t e.images →
    ReadGood Ω C t' e.images ∧ (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val

 theorem baseRead_transport {Γ : List (Expr S)} {M N T : Expr S}
    (ht : HasTypeBE P Γ M T) (t' : TypingTreeBE P Γ N T)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hMN : (M.subst e.images).knf = (N.subst e.images).knf)
    (hne : Neutral M → Neutral N)
    (v : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
      Value (hw := hw) Ω C hno (T.subst e.images).knf) (G : Prop)
    (hr : baseGood Ω C M T e.images G)
    (hv : ∀ ha, G → ValGood Ω C t' e.images ∧ (v ha).val = ((preEvaluate Ω C hno t' e).val ha).val) :
    ReadGood Ω C t' e.images ∧ (PreResult.baseRead ht v).val = (preEvaluate Ω C hno t' e).read.val := by
  by_cases hm : Ω.kprofile (M.subst e.images).knf ∈ C
  · have hm' : Ω.kprofile (N.subst e.images).knf ∈ C := hMN ▸ hm
    obtain ⟨s,hs,hsC,hval,hn⟩ := hr (by simpa only [Ω.kprofile_knf] using hm)
    subst T
    by_cases ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)
    · have hvg := hv ha (hval (by simpa only [Ω.kprofile_knf] using ha))
      refine ⟨(readGood_active_iff Ω C t' (by simpa only [Ω.kprofile_knf] using hm') hsC
        (by simpa only [Ω.kprofile_knf] using ha)).mpr hvg.1,?_⟩
      refine Eq.trans (PreResult.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEvaluate_read_base Ω C hno t' e hm' hsC ha).symm)
      rw [hvg.2]
      exact congrArg (fun X : ActualType Ω =>
        ((RawValue.base Ω C hno ((preEvaluate Ω C hno t' e).val ha).val) X).val) (Subtype.ext hMN)
    · have hn' := hne (hn (by simpa only [Ω.kprofile_knf] using ha))
      refine ⟨neutral_readGood Ω C t' hn' e.images hsC (by simpa only [Expr.subst,Ω.kprofile_sort,Ω.kprofile_knf] using ha),?_⟩
      have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hsC⟩
      rw [preEvaluate_neutral_read_inactive Ω C hno t' e hn' ha]
      simp only [PreResult.baseRead,dite_eq_left hm,dite_eq_left hex,dite_eq_right ha]
      exact congrArg (Candidates.Top Ω) hMN
  · have hm' : Ω.kprofile (N.subst e.images).knf ∉ C := hMN ▸ hm
    refine ⟨readGood_outside Ω C t' e.images (by simpa only [Ω.kprofile_knf] using hm'),?_⟩
    rw [preEvaluate_read_outside Ω C hno t' e hm']
    simp only [PreResult.baseRead,dite_eq_right hm]
    exact congrArg (Candidates.Top Ω) hMN

 theorem root_transport {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasTypeBE P Γ (.app (.lam D m) n) T)
    (hf : HasTypeBE P Γ (.lam D m) (.pi A B))
    (d : TypingTreeBE P Γ D (.sort a)) (b : TypingTreeBE P (D :: Γ) m E)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hcF : ConvertsBE (.pi A B) (.pi D E))
    (nt : TypingTreeBE P Γ n A) (hc : ConvertsBE T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) :
    ∃ t' : TypingTreeBE P Γ (m.instantiate n) T,
      GoodTransport (hw := hw) Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) t' := by
  have hnD : HasTypeBE P Γ n D := .conversion nt.typing d.typing (hcF.product_compatibility dz).1
  let ntD := nt.retarget hnD (.symm _ _ (hcF.product_compatibility dz).1)
  let ts := TypingTreeBE.StoredSubstitution.single ntD
  let bt := b.subst ht.valid (Expr.single n) ts
  have ht' := ht.subject_reduction (.head D m n)
  have hc' : ConvertsBE T (E.instantiate n) := .trans _ _ _ hc ((hcF.product_compatibility dz).2.subst (Expr.single n))
  let t' := bt.retarget ht' hc'
  refine ⟨t',?_⟩
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)),
      ValGood Ω C (.application ht (.abstraction hf d b hp hcF) nt hc) e.images →
      ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno t' e).val ha).val := by
    intro e ha hg
    have hF : ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images)) := by
      by_contra hh
      change (if ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images)) then _ else _) at hg
      rw [ite_eq_right hh] at hg
      cases hg with | app hf => cases hf
    change (if ActiveLayer P C (Ω.kprofile ((Expr.pi A B).subst e.images)) then _ else _) at hg
    rw [ite_eq_left hF] at hg
    obtain ⟨hraw,hpp,hbody,hguard,hbeta⟩ := application_abstraction_beta Ω C hno ht hf d b hp hcF nt hc hC e
      (by simpa only [Ω.kprofile_knf] using hF) ha
    let er := e.cons (ContextTowerBE.THasTypeBE.subst hnD e.typed) (preEvaluate Ω C hno ntD e).parameter
      (preEvaluate Ω C hno ntD e).parameter_fits
    have herimages : er.images = Expr.consSub (n.subst e.images) e.images := by
      funext i; cases i <;> rfl
    have hpEq : (preEvaluate Ω C hno nt e).parameter = (preEvaluate Ω C hno ntD e).parameter :=
      preEvaluate_retarget_parameter Ω C hno nt hnD (.symm _ _ (hcF.product_compatibility dz).1) e
    have heren : (e.cons hraw (preEvaluate Ω C hno nt e).parameter hpp).Compatible er := by
      constructor
      · intro i hi; exact .refl _
      · intro i hi; cases i with
        | zero => exact hpEq
        | succ i => rfl
    have hgoodB : ValGood Ω C b er.images := hg.1 (n.subst e.images) hraw
      (by simpa only [Ω.kprofile_knf] using hbody)
    have heT := e.type_convert_eq ht bt.typing hc'
    have haBt : ActiveLayer P C (Ω.kprofile ((E.instantiate n).subst e.images).knf) := heT ▸ ha
    have hsGuard : SubstitutionGuard Ω C (D :: Γ) (Expr.single n) er.images := single_guard Ω C e.images hguard
    have hgoodN : GoodReplacement Ω C ts e.images := single_goodReplacement Ω C ntD e.images (by
      intro hD
      apply (valGood_retarget Ω C nt hnD (.symm _ _ (hcF.product_compatibility dz).1) e.images).mpr
      apply hg.2
      have heD := e.type_convert_eq nt.typing hnD (hcF.product_compatibility dz).1
      rw [← Ω.kprofile_knf,heD,Ω.kprofile_knf]
      exact hD)
    have hgoodBt : ValGood Ω C bt e.images := (goodness_subst Ω C hw b ht.valid (Expr.single n) ts e.images e.typed
      (by simpa only [Expr.comp_single,←herimages] using hsGuard) hgoodN).1
      (by simpa only [Expr.comp_single,Ω.kprofile_knf] using hbody)
      (by simpa only [Expr.comp_single,←herimages] using hgoodB)
    refine ⟨(valGood_retarget Ω C bt ht' hc' e.images).mpr hgoodBt,?_⟩
    refine hbeta.trans (Eq.trans ?_ (preEvaluate_retarget_val Ω C hno bt ht' hc' e haBt ha))
    refine Eq.trans (PreResult.val_congr _ _ (preEvaluate_compatible Ω C hno hC b _ _ heren).1 hbody hbody) ?_
    exact (preEvaluate_subst Ω C hno b ht.valid (Expr.single n) ts er e (single_assigned Ω C hno hC ntD e) hsGuard).1
      hbody haBt hgoodB
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht t' e
    (e.expression_convert_eq ht ht' (.rel _ _ (.inl (.head D m n))))
    (fun h => by cases h with | app hf => cases hf) _ _ hr
  exact hval e

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
@[simp] theorem cons_images (e : Environment (hw := hw) Ω C hno Γ) {D n : Expr S}
    (hn : Ω.THasTypeBE n (D.subst e.images)) p hp :
    (e.cons hn p hp).images = Expr.consSub n e.images := by
  funext i; cases i <;> rfl
end Environment

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N T : Expr S}
 theorem refl (t : TypingTreeBE P Γ M T) : GoodTransport (hw := hw) Ω C hno t t :=
  ⟨fun _ _ h => ⟨h,rfl⟩,fun _ h => ⟨h,rfl⟩⟩
 theorem parameter_eq {t : TypingTreeBE P Γ M T} {t' : TypingTreeBE P Γ N T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (e : Environment (hw := hw) Ω C hno Γ)
    (hg : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) → ValGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' e).parameter := by
  apply PreResult.parameter_congr _ _ rfl
  intro ha ha'
  exact (h.val e ha (hg ha)).2
end GoodTransport

 theorem application_transport {Γ : List (Expr S)} {f n f' n' D E T : Expr S}
    (ht : HasTypeBE P Γ (.app f n) T) (ht' : HasTypeBE P Γ (.app f' n') T)
    (ft : TypingTreeBE P Γ f (.pi D E)) (ft' : TypingTreeBE P Γ f' (.pi D E))
    (nt : TypingTreeBE P Γ n D) (nt' : TypingTreeBE P Γ n' D)
    (hc : ConvertsBE T (E.instantiate n)) (hc' : ConvertsBE T (E.instantiate n'))
    (hf : GoodTransport (hw := hw) Ω C hno ft ft') (hn : GoodTransport (hw := hw) Ω C hno nt nt')
    (hff : ConvertsBE f f') (hnn : ConvertsBE n n') (hne : Neutral f → Neutral f') :
    GoodTransport (hw := hw) Ω C hno (.application ht ft nt hc) (.application ht' ft' nt' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)),
      ValGood Ω C (.application ht ft nt hc) e.images →
      ValGood Ω C (.application ht' ft' nt' hc') e.images ∧
      ((preEvaluate Ω C hno (.application ht ft nt hc) e).val ha).val =
      ((preEvaluate Ω C hno (.application ht' ft' nt' hc') e).val ha).val := by
    intro e ha hg
    change (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst e.images)) then _ else _) at hg
    change (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst e.images)) then _ else _) ∧ _
    by_cases hF : ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst e.images))
    · rw [ite_eq_left hF] at hg ⊢
      have hFa : ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst e.images).knf) := by
        simpa only [Ω.kprofile_knf] using hF
      refine ⟨⟨(hf.val e hFa hg.1).1,fun haD => (hn.val e
        (by simpa only [Ω.kprofile_knf] using haD) (hg.2 haD)).1⟩,?_⟩
      apply PreResult.application_val_congr ht ht' ft.typing ft'.typing nt.typing nt'.typing hc hc'
        _ _ _ _ e e rfl rfl (e.expression_convert_eq nt.typing nt'.typing hnn)
      · exact fun _ _ => (hf.val e hFa hg.1).2
      · exact hn.parameter_eq e (fun haD => hg.2 (by simpa only [Ω.kprofile_knf] using haD))
    · rw [ite_eq_right hF] at hg ⊢
      refine ⟨?_,?_⟩
      · cases hg with | app hg => exact .app (hne hg)
      · have hFa : ¬ ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst e.images).knf) := by
          simpa only [Ω.kprofile_knf] using hF
        simp only [preEvaluate,PreResult.application,PreResult.baseResult,PreResult.applicationValue,dite_eq_right hFa]
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.application ht' ft' nt' hc') e
    (e.expression_convert_eq ht ht' (ConvertsBE.app_congr hff hnn))
    (fun hh => by cases hh with | app hh => exact .app (hne hh)) _ _ hr
  exact hval e

 theorem abstraction_transport {Γ : List (Expr S)} {D m E D' m' E' T : Expr S} {a a' s s' : S}
    (ht : HasTypeBE P Γ (.lam D m) T) (ht' : HasTypeBE P Γ (.lam D' m') T)
    (d : TypingTreeBE P Γ D (.sort a)) (d' : TypingTreeBE P Γ D' (.sort a'))
    (b : TypingTreeBE P (D :: Γ) m E) (b' : TypingTreeBE P (D' :: Γ) m' E')
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hp' : HasTypeBE P Γ (.pi D' E') (.sort s'))
    (hc : ConvertsBE T (.pi D E)) (hc' : ConvertsBE T (.pi D' E'))
    (hD : ConvertsBE D D') (hm : ConvertsBE m m') (hE : ConvertsBE E E')
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n (D'.subst e.images))
      p hpp hpp' ha ha', ValGood Ω C b (e.cons hn p hpp).images →
        ValGood Ω C b' (e.cons hn' p hpp').images ∧
        ((preEvaluate Ω C hno b (e.cons hn p hpp)).val ha).val =
        ((preEvaluate Ω C hno b' (e.cons hn' p hpp')).val ha').val) :
    GoodTransport (hw := hw) Ω C hno (.abstraction ht d b hp hc) (.abstraction ht' d' b' hp' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)),
      ValGood Ω C (.abstraction ht d b hp hc) e.images →
      ValGood Ω C (.abstraction ht' d' b' hp' hc') e.images ∧
      ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
      ((preEvaluate Ω C hno (.abstraction ht' d' b' hp' hc') e).val ha).val := by
    intro e ha hg
    have hnold {n : Expr S} (hn : Ω.THasTypeBE n (D'.subst e.images)) : Ω.THasTypeBE n (D.subst e.images) :=
      .conversion hn (ContextTowerBE.THasTypeBE.subst d.typing e.typed) (.symm _ _ (hD.subst e.images).k)
    have hEeq (n : Expr S) (hn : Ω.THasTypeBE n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).knf = (E'.subst (Expr.consSub n e.images)).knf :=
      Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst b.typing (e.typed.cons (hnold hn))).type_kwn hw)
        ((ContextTowerBE.THasTypeBE.subst b'.typing (e.typed.cons hn)).type_kwn hw)
        (hE.subst (Expr.consSub n e.images)).k
    refine ⟨?_,?_⟩
    · intro n hn ha'
      have haold : ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n e.images)).knf) := by
        rw [hEeq n hn,Ω.kprofile_knf]; exact ha'
      obtain ⟨pa,hpD⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hDD := e.expression_convert_eq d.typing d'.typing hD
      have hpD' : PayloadFits Ω C hno (D'.subst e.images).knf pa := hDD ▸ hpD
      exact (hb e n (hnold hn) hn pa hpD hpD' haold
        (by simpa only [Ω.kprofile_knf,Environment.cons_images] using ha') (hg n (hnold hn)
          (by simpa only [Ω.kprofile_knf] using haold))).1
    · apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e rfl
      intro n n' hn hn' he p hpp hpp' haB haB'
      subst n'
      exact (hb e n hn hn' p hpp hpp' haB haB' (hg n hn
        (by simpa only [Ω.kprofile_knf,Environment.cons_images] using haB))).2
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.abstraction ht' d' b' hp' hc') e
    (e.expression_convert_eq ht ht' (ConvertsBE.lam_congr hD hm)) (fun hn => by cases hn) _ _ hr
  exact hval e

 theorem product_transport {Γ : List (Expr S)} {D E D' E' T : Expr S} {a q c : S}
    (ht : HasTypeBE P Γ (.pi D E) T) (ht' : HasTypeBE P Γ (.pi D' E') T)
    (d : TypingTreeBE P Γ D (.sort a)) (d' : TypingTreeBE P Γ D' (.sort a))
    (b : TypingTreeBE P (D :: Γ) E (.sort q)) (b' : TypingTreeBE P (D' :: Γ) E' (.sort q))
    (hr : P.rule a q c) (hc : ConvertsBE T (.sort c))
    (hD : ConvertsBE D D') (hE : ConvertsBE E E')
    (hd : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C d e.images →
      ReadGood Ω C d' e.images ∧ (preEvaluate Ω C hno d e).read.val = (preEvaluate Ω C hno d' e).read.val)
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n (D'.subst e.images))
      p hpp hpp', ReadGood Ω C b (e.cons hn p hpp).images →
        ReadGood Ω C b' (e.cons hn' p hpp').images ∧
        (preEvaluate Ω C hno b (e.cons hn p hpp)).read.val =
        (preEvaluate Ω C hno b' (e.cons hn' p hpp')).read.val) :
    GoodTransport (hw := hw) Ω C hno (.product ht d b hr hc) (.product ht' d' b' hr hc) := by
  have hdata (e : Environment (hw := hw) Ω C hno Γ) :
      (D.subst e.images).knf = (D'.subst e.images).knf ∧
      (E.subst (Expr.liftSub e.images)).knf = (E'.subst (Expr.liftSub e.images)).knf := by
    have hpi := e.expression_convert_eq ht ht' (.pi hD hE)
    have hwp := (ContextTowerBE.THasTypeBE.subst ht e.typed).kwn hw
    have hwp' := (ContextTowerBE.THasTypeBE.subst ht' e.typed).kwn hw
    rw [Expr.subst,Expr.subst,Expr.knf_pi hwp.pi_domain hwp.pi_body,
      Expr.knf_pi hwp'.pi_domain hwp'.pi_body] at hpi
    exact Expr.pi.inj hpi
  have hchildren (e : Environment (hw := hw) Ω C hno Γ)
      (hg : ProductGood Ω C d b e.images) :
      ProductGood Ω C d' b' e.images ∧
      (PreResult.productCandidate d.typing b.typing hr (preEvaluate Ω C hno d) (preEvaluate Ω C hno b) e).val =
      (PreResult.productCandidate d'.typing b'.typing hr (preEvaluate Ω C hno d') (preEvaluate Ω C hno b') e).val := by
    have hnold {n : Expr S} (hn : Ω.THasTypeBE n (D'.subst e.images)) : Ω.THasTypeBE n (D.subst e.images) :=
      .conversion hn (ContextTowerBE.THasTypeBE.subst d.typing e.typed) (.symm _ _ (hD.subst e.images).k)
    have hEeq (n : Expr S) (hn : Ω.THasTypeBE n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).knf = (E'.subst (Expr.consSub n e.images)).knf :=
      Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst b.typing (e.typed.cons (hnold hn))).kwn hw)
        ((ContextTowerBE.THasTypeBE.subst b'.typing (e.typed.cons hn)).kwn hw)
        (hE.subst (Expr.consSub n e.images)).k
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro hD'
      apply (hd e (hg.1 ?_)).1
      rw [← Ω.kprofile_knf,(hdata e).1,Ω.kprofile_knf]
      exact hD'
    · intro n hn hE'
      have hEold : Ω.kprofile (E.subst (Expr.consSub n e.images)) ∈ C := by
        rw [← Ω.kprofile_knf,hEeq n hn,Ω.kprofile_knf]; exact hE'
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hp' : PayloadFits Ω C hno (D'.subst e.images).knf p := (hdata e).1 ▸ hp
      have hh := (hb e n (hnold hn) hn p hp hp' (by
        simpa only [Environment.cons_images] using hg.2 n (hnold hn) hEold)).1
      simpa only [Environment.cons_images] using hh
    · apply PreResult.productCandidate_congr d.typing b.typing hr d'.typing b'.typing hr _ _ _ _ e e
        (hdata e).1 (hdata e).2
      · intro hD
        exact (hd e (hg.1 (by simpa only [Ω.kprofile_knf] using hD))).2
      · intro n hn hn' p hp hp' hE
        exact (hb e n hn hn' p hp hp' (hg.2 n hn
          (by simpa only [Ω.kprofile_knf,Environment.cons_images] using hE))).2
  constructor
  · intro e ha hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hgate
      exact (hchildren e (hg ⟨hgate.1,by
        rw [← Ω.kprofile_knf,hM,Ω.kprofile_knf]; exact hgate.2⟩)).1
    · by_cases hs : ({c} : Set S) ∈ C
      · apply PreResult.product_val_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
          _ _ _ _ e e rfl hM Iff.rfl
        intro hm
        exact (hchildren e (hg ⟨hs,by simpa only [Ω.kprofile_knf] using hm⟩)).2
      · have hgate : ¬ (({c} : Set S) ∈ C ∧ Ω.kprofile ((Expr.pi D E).subst e.images).knf ∈ C) :=
          fun h => hs h.1
        have hgate' : ¬ (({c} : Set S) ∈ C ∧ Ω.kprofile ((Expr.pi D' E').subst e.images).knf ∈ C) :=
          fun h => hs h.1
        simp only [preEvaluate,PreResult.product,dite_eq_right hgate,dite_eq_right hgate']
  · intro e hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hm
      exact (hchildren e (hg (by rw [← Ω.kprofile_knf,hM,Ω.kprofile_knf]; exact hm))).1
    · apply PreResult.product_read_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
        _ _ _ _ e e hM
      intro hm
      exact (hchildren e (hg (by simpa only [Ω.kprofile_knf] using hm))).2

 theorem reduction_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTreeBE P Γ M T) (hr : Beta M N) :
    ∃ t' : TypingTreeBE P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr generalizing Γ T with
  | head D m n =>
      cases t with
      | application ht ft nt hc =>
          cases ft with
          | abstraction hf d b hp hcF =>
              exact root_transport Ω C hno ht hf d b hp hcF nt hc hC
  | app_left hr ih =>
      cases t with
      | application ht ft nt hc =>
          obtain ⟨ft',hft⟩ := ih ft
          have ht' := ht.subject_reduction (.app_left hr)
          exact ⟨.application ht' ft' nt hc,application_transport Ω C hno ht ht' ft ft' nt nt hc hc
            hft (.refl nt) (.rel _ _ (.inl hr)) (.refl _) (fun hn => hn.beta hr)⟩
  | app_right hr ih =>
      cases t with
      | @application Γ f n D E T ht ft nt hc =>
          obtain ⟨nt',hnt⟩ := ih nt
          have ht' := ht.subject_reduction (.app_right hr)
          have hc' : ConvertsBE T (E.instantiate _) := .trans _ _ _ hc ((show ConvertsBE _ _ from .rel _ _ (.inl hr)).instantiate_right E)
          exact ⟨.application ht' ft nt' hc',application_transport Ω C hno ht ht' ft ft nt nt' hc hc'
            (.refl ft) hnt (.refl _) (.rel _ _ (.inl hr)) (fun hn => hn)⟩
  | @lam_domain D D' m hr ih =>
      cases t with
      | @abstraction Γ _ _ E a s T ht d b hp hc =>
          obtain ⟨d',_⟩ := ih d
          let hctx := ContextEquivalentBE.head_conversion d.typing d'.typing (.rel _ _ (.inl hr))
          let b' := b.recontext hctx
          have ht' := ht.subject_reduction (.lam_domain hr)
          have hp' := hp.subject_reduction (.pi_domain hr)
          have hc' : ConvertsBE T (.pi D' E) := .trans _ _ _ hc (.rel _ _ (.inl (.pi_domain hr)))
          refine ⟨.abstraction ht' d' b' hp' hc',abstraction_transport Ω C hno ht ht' d d' b b' hp hp'
            hc hc' (.rel _ _ (.inl hr)) (.refl _) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (b.recontext hctx) (e.cons hn' p hpp').images).1
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · apply PreResult.val_congr
            exact (preEvaluate_recontext Ω C hno b hctx (e.cons hn p hpp) (e.cons hn' p hpp') (Environment.SameData.of_eq rfl rfl)).1
  | lam_body hr ih =>
      cases t with
      | abstraction ht d b hp hc =>
          obtain ⟨b',hb⟩ := ih b
          have ht' := ht.subject_reduction (.lam_body hr)
          refine ⟨.abstraction ht' d b' hp hc,abstraction_transport Ω C hno ht ht' d d b b' hp hp
            hc hc (.refl _) (.rel _ _ (.inl hr)) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          exact hb.val (e.cons hn p hpp) ha hg
  | @pi_domain D D' E hr ih =>
      cases t with
      | @product Γ _ _ a b c T ht d bt hrule hc =>
          obtain ⟨d',hd⟩ := ih d
          let hctx := ContextEquivalentBE.head_conversion d.typing d'.typing (.rel _ _ (.inl hr))
          let b' := bt.recontext hctx
          have ht' := ht.subject_reduction (.pi_domain hr)
          refine ⟨.product ht' d' b' hrule hc,product_transport Ω C hno ht ht' d d' bt b' hrule hc
            (.rel _ _ (.inl hr)) (.refl _) hd.read ?_⟩
          intro e n hn hn' p hpp hpp' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (bt.recontext hctx) (e.cons hn' p hpp').images).2
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · exact (preEvaluate_recontext Ω C hno bt hctx (e.cons hn p hpp) (e.cons hn' p hpp') (Environment.SameData.of_eq rfl rfl)).2
  | pi_body hr ih =>
      cases t with
      | product ht d bt hrule hc =>
          obtain ⟨b',hb⟩ := ih bt
          have ht' := ht.subject_reduction (.pi_body hr)
          refine ⟨.product ht' d b' hrule hc,product_transport Ω C hno ht ht' d d bt b' hrule hc
            (.refl _) (.rel _ _ (.inl hr)) (fun e hg => ⟨hg,rfl⟩) ?_⟩
          intro e n hn hn' p hpp hpp' hg
          exact hb.read (e.cons hn p hpp) hg

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N L T : Expr S}
 theorem trans {t : TypingTreeBE P Γ M T} {t' : TypingTreeBE P Γ N T} {t'' : TypingTreeBE P Γ L T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (h' : GoodTransport (hw := hw) Ω C hno t' t'') :
    GoodTransport (hw := hw) Ω C hno t t'' := by
  constructor
  · intro e ha hg
    have hh := h.val e ha hg
    have hh' := h'.val e ha hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
  · intro e hg
    have hh := h.read e hg
    have hh' := h'.read e hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
end GoodTransport

 theorem reduces_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTreeBE P Γ M T) (hr : Reduces M N) :
    ∃ t' : TypingTreeBE P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr with
  | refl => exact ⟨t,.refl t⟩
  | tail _ h ih =>
      obtain ⟨t',ht⟩ := ih
      obtain ⟨t'',ht'⟩ := reduction_transport Ω C hno hC t' h
      exact ⟨t'',ht.trans ht'⟩

/-- The good part of any stored typing tree can be transported to an erasure-normal stored tree. -/
theorem normalize_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) :
    ∃ t' : TypingTreeBE P Γ M.rnf T, GoodTransport (hw := hw) Ω C hno t t' :=
  reduces_transport Ω C hno hC t (HasTypeBE.rnf_spec hw t.typing).1

/-- A good active value equals the value of every erasure-normal convertible tree at a convertible expected type. -/
theorem good_normal_value (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M M' T U : Expr S} (t : TypingTreeBE P Γ M T)
    (t' : TypingTreeBE P Γ M' U) (hM' : ENormal dz M') (hMM : ConvertsBE M M') (hc : ConvertsBE T U)
    (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (ha' : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf))
    (hg : ValGood Ω C t e.images) :
    ((preEvaluate Ω C hno t e).val ha).val = ((preEvaluate Ω C hno t' e).val ha').val := by
  obtain ⟨tn,htn⟩ := normalize_transport Ω C hno hC t
  have he := (htn.val e ha hg).2
  have hr := HasTypeBE.rnf_spec hw t.typing
  have hconv : ConvertsBE M.rnf M' := .trans _ _ _ (.symm _ _ (reduces_convertsBE hr.1)) hMM
  have hctx : ContextEquivalentBE P Γ Γ := ⟨t.typing.valid, t.typing.valid, fun _ _ => Iff.rfl⟩
  exact he.trans (PreResult.val_congr _ _
    ((enormal_conv_independence Ω C hno hC tn hr.2 t' hM' hconv hctx e e
      (Environment.SameData.of_eq rfl rfl)).1 hc) ha ha')

/-- A good `read` at a sort equals the `read` of every erasure-normal convertible tree, even when the expected sort is a different sort. -/
theorem good_normal_read (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M M' : Expr S} {s r : S} (t : TypingTreeBE P Γ M (.sort s))
    (t' : TypingTreeBE P Γ M' (.sort r)) (hM' : ENormal dz M') (hMM : ConvertsBE M M')
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val := by
  obtain ⟨tn,htn⟩ := normalize_transport Ω C hno hC t
  have hr := HasTypeBE.rnf_spec hw t.typing
  have hconv : ConvertsBE M.rnf M' := .trans _ _ _ (.symm _ _ (reduces_convertsBE hr.1)) hMM
  have hctx : ContextEquivalentBE P Γ Γ := ⟨t.typing.valid, t.typing.valid, fun _ _ => Iff.rfl⟩
  exact (htn.read e hg).2.trans
    ((enormal_conv_independence Ω C hno hC tn hr.2 t' hM' hconv hctx e e
      (Environment.SameData.of_eq rfl rfl)).2 s r rfl rfl)
end PureTypeSystem.KP.ObservationValues

