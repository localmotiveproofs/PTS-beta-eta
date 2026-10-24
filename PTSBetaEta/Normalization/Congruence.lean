/- Adapted to typing with βη-conversion from OpenAI's `Congruence.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Bounds

@[expose] public section

/-!
# Congruence for typing with βη-conversion

This file adapts OpenAI's `Congruence.lean` (`PTSBetaEta.Beta.Congruence`) to keys.
Most of the adaptation is mechanical.
One lemma is new and replaces OpenAI's `normal_tree_independence`.
The new lemma `enormal_tree_independence` compares the typing trees of two erasure-normal terms with the same erasure, in equivalent contexts.
The two terms may differ in their λ-domains.
The evaluator ignores the subtrees of λ-domains, so the values and the `read`s agree.
The relevant types are convertible by faithfulness of erasure (`faithful`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


/-! ### Syntactic helpers in the root namespace -/

namespace PureTypeSystem
universe u

theorem erase_eq_lam {S : Type u} (z : S) {X A b : Expr S} (h : X.erase z = .lam A b) :
    ∃ A' b', X = .lam A' b' ∧ b'.erase z = b := by
  cases X <;> simp [Expr.erase] at h
  exact ⟨_, _, rfl, h.2⟩

theorem Expr.knf_subst_of_erase_eq {S : Type u} [Nonempty S] {M M' : Expr S}
    (h : M.erase dz = M'.erase dz) (σ : Nat → Expr S) :
    (M.subst σ).knf = (M'.subst σ).knf := by
  apply Expr.knf_eq_of_erase_eq
  rw [Expr.erase_subst, Expr.erase_subst, h]

namespace ContextEquivalentBE
variable {S : Type u} {P : Specification S} {Γ Δ Θ : List (Expr S)}
theorem trans (h : ContextEquivalentBE P Γ Δ) (k : ContextEquivalentBE P Δ Θ) :
    ContextEquivalentBE P Γ Θ :=
  ⟨h.valid_left, k.valid_right, fun M A => (h.typing M A).trans (k.typing M A)⟩
end ContextEquivalentBE

namespace ContextTowerBE
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)

theorem kprofile_sort (s : S) : Ω.kprofile (.sort s) = AxProfile P s := by
  ext t
  constructor
  · intro h
    obtain ⟨T₀, hT₀, hk⟩ := KHasTypeBE.sorted_witness Ω h
    rw [Expr.knf_sort] at hk
    have w := (hT₀.kwn_both hE.out).1
    have c := converts_sort_of_knf w hk
    have hs : Ω.HasTypeBE (.sort s) (.sort t) := hT₀.subject_reduces (hT₀.reduces_sort hE.out c)
    obtain ⟨n, hn⟩ := hs
    have hn' : PureTypeSystem.HasTypeBE P (Ω.context n) (.sort s) (.sort t) := hn
    obtain ⟨u, ha, hc⟩ := hn'.generation
    exact hc.sort_inj ▸ ha
  · intro h
    exact KHasTypeBE.of ⟨0, PureTypeSystem.HasTypeBE.sort_of_valid (Ω.valid 0) h⟩

theorem kprofile_converts {A B : Expr S} (hA : KWN A) (hB : KWN B) (hc : KConverts A B) :
    Ω.kprofile A = Ω.kprofile B :=
  Ω.kprofile_of_knf_eq (Expr.knf_converts hA hB hc)

end ContextTowerBE

namespace ContextTowerBE.TTypedSubstitutionBE
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P} {Γ Δ : List (Expr S)} {σ ξ : Nat → Expr S}

/-- Composition with a plain typed substitution. -/
theorem comp (hξ : Ω.TTypedSubstitutionBE Δ ξ) (hσ : PureTypeSystem.TypedSubstitutionBE P Γ Δ σ) :
    Ω.TTypedSubstitutionBE Γ (fun n => (σ n).subst ξ) := by
  intro n A hn
  have h := THasTypeBE.subst (hσ n A hn) hξ
  simpa only [Expr.subst_subst] using h

end ContextTowerBE.TTypedSubstitutionBE

end PureTypeSystem

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

theorem lambdaValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (act : LambdaAction (hw := hw) Ω C hno T) (act' : LambdaAction (hw := hw) Ω C hno U)
    (hr : ∀ (a : FrameKey Ω C T) (a' : FrameKey Ω C U), a.argument = a'.argument →
      ∀ p hp hp', (act a p hp).val = (act' a' p hp').val) :
    (lambdaValue Ω C hno T act).val = (lambdaValue Ω C hno U act').val := by
  have hu := ActiveType.ext hTU
  subst U
  have he : act = act' := by
    funext a p hp
    exact Subtype.ext (hr a a rfl p hp hp)
  rw [he]

theorem applyValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (v : Value (hw := hw) Ω C hno T.type) (v' : Value (hw := hw) Ω C hno U.type)
    (hvv : v.val = v'.val) (a : FrameKey Ω C T) (a' : FrameKey Ω C U)
    (hq : a.argument = a'.argument) (p p' : Option (RawValue (hw := hw) Ω C hno)) (hpp : p = p')
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a'.domain p') :
    (applyValue Ω C hno T v a p hp).val = (applyValue Ω C hno U v' a' p' hp').val := by
  have hu := ActiveType.ext hTU
  subst U
  have hv : v = v' := Subtype.ext hvv
  have ha : a = a' := FrameKey.ext hq
  subst v'
  subst a'
  subst p'
  rfl

theorem withBase_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (b b' : Base Ω) (hbb : b = b') :
    (withBase (hw := hw) Ω C hno T b).val = (withBase Ω C hno U b').val := by
  have hu := ActiveType.ext hTU
  subst U
  subst b'
  rfl

theorem distinguished_congr {T U : ActiveType Ω C} (hTU : T.type = U.type) :
    (distinguished (hw := hw) Ω C hno T).val = (distinguished Ω C hno U).val := by
  have hu := ActiveType.ext hTU
  subst U
  rfl

theorem canonValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (v : Value (hw := hw) Ω C hno T.type) (w : Value (hw := hw) Ω C hno U.type)
    (hvw : v.val = w.val) : (canonValue hno T v).val = (canonValue hno U w).val := by
  have hu := ActiveType.ext hTU
  subst U
  have h : v = w := Subtype.ext hvw
  subst h
  rfl

theorem canonDistinguished_congr {T U : ActiveType Ω C} (hTU : T.type = U.type) :
    (canonValue hno T (distinguished (hw := hw) Ω C hno T)).val =
      (canonValue hno U (distinguished Ω C hno U)).val :=
  canonValue_congr Ω C hno hTU _ _ (distinguished_congr Ω C hno hTU)

namespace PreResult

section
variable {Ω C hno} {Γ Δ : List (Expr S)} {M M' T T' : Expr S}
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}

theorem parameter_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hT : (T.subst e.images).knf = (T'.subst f.images).knf)
    (hv : ∀ ha hb, (r.val ha).val = (q.val hb).val) : r.parameter = q.parameter := by
  by_cases ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)
  · have hb : ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf) := hT ▸ ha
    rw [r.parameter_eq ha,q.parameter_eq hb,hv ha hb]
  · have hb : ¬ ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf) := hT ▸ ha
    simp only [parameter,ha,hb,dite_false]

theorem val_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hr : r.parameter = q.parameter)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf)) :
    (r.val ha).val = (q.val hb).val := by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact Option.some.inj hr

/-- A form of congruence for the base projection that allows two different contexts. -/
theorem baseRead_congr (h : HasTypeBE P Γ M T) (h' : HasTypeBE P Δ M' T')
    (hM : (M.subst e.images).knf = (M'.subst f.images).knf)
    (hT : (T.subst e.images).knf = (T'.subst f.images).knf)
    (hS : (∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C) ↔
      (∃ s : S, T' = .sort s ∧ ({s} : Set S) ∈ C))
    (v : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
      Value (hw := hw) Ω C hno (T.subst e.images).knf)
    (w : ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf) →
      Value (hw := hw) Ω C hno (T'.subst f.images).knf)
    (hv : ∀ ha hb, (v ha).val = (w hb).val) :
    (baseRead h v).val = (baseRead h' w).val := by
  by_cases hm : Ω.kprofile (M.subst e.images).knf ∈ C
  · have hm' : Ω.kprofile (M'.subst f.images).knf ∈ C := hM ▸ hm
    by_cases hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C
    · have hs' := hS.mp hs
      by_cases ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)
      · have hb : ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true]
        have hX : e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs'.choose_spec.1 ▸ h') := Subtype.ext hM
        rw [hv ha hb]
        exact congrArg (fun X : ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb : ¬ ActiveLayer P C (Ω.kprofile (T'.subst f.images).knf) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true,dite_false]
        exact congrArg (Candidates.Top Ω) hM
    · have hs' := mt hS.mpr hs
      simp only [baseRead,hm,hm',hs,hs',dite_true,dite_false]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.kprofile (M'.subst f.images).knf ∉ C := hM ▸ hm
    simp only [baseRead,hm,hm',dite_false]
    exact congrArg (Candidates.Top Ω) hM
end

variable {Ω C hno} {Γ Δ : List (Expr S)} {T T' : Expr S}

theorem abstraction_type {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (e : Environment (hw := hw) Ω C hno Γ) :
    (T.subst e.images).knf =
      .pi (ProductInstance.ofFormation hp e).domainNF (ProductInstance.ofFormation hp e).bodyNF :=
  (Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst h e.typed).type_kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hp e.typed).kwn hw) (hc.subst e.images).k).trans
    (ProductInstance.ofFormation hp e).product_nf

theorem abstractionAction_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasTypeBE P Γ (.lam D m) T) (h' : HasTypeBE P Δ (.lam D' m') T')
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hp' : HasTypeBE P Δ (.pi D' E') (.sort s'))
    (hc : ConvertsBE T (.pi D E)) (hc' : ConvertsBE T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).knf = (T'.subst e'.images).knf)
    (hb : ∀ n n' (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (ha' : ActiveLayer P C (Ω.kprofile (T'.subst e'.images).knf))
    (a : FrameKey Ω C (e.activeType h ha)) (a' : FrameKey Ω C (e'.activeType h' ha'))
    (haa : a.argument = a'.argument) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpa : PayloadFits Ω C hno a.domain p) (hpa' : PayloadFits Ω C hno a'.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp' hc' eb' e' ha' a' p hpa').val := by
  have hdom : (ProductInstance.ofFormation hp e).domainNF =
      (ProductInstance.ofFormation hp' e').domainNF :=
    (Expr.pi.inj ((abstraction_type h hp hc e).symm.trans
      (hT.trans (abstraction_type h' hp' hc' e')))).1
  dsimp only [abstractionAction, ProductInstance.frameEnvironment, ProductInstance.extend]
  refine hb _ _ _ _ ?_ p _ _ _ _
  simp only [ProductInstance.frameArgument, hdom, haa]

theorem abstraction_val_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasTypeBE P Γ (.lam D m) T) (h' : HasTypeBE P Δ (.lam D' m') T')
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hp' : HasTypeBE P Δ (.pi D' E') (.sort s'))
    (hc : ConvertsBE T (.pi D E)) (hc' : ConvertsBE T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).knf = (T'.subst e'.images).knf)
    (hb : ∀ n n' (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (ha' : ActiveLayer P C (Ω.kprofile (T'.subst e'.images).knf)) :
    ((abstraction h hp hc eb e).val ha).val =
      ((abstraction h' hp' hc' eb' e').val ha').val := by
  apply lambdaValue_congr Ω C hno hT
  exact abstractionAction_congr h h' hp hp' hc hc' eb eb' e e' hT hb ha ha'

theorem application_val_congr {f n D E f' n' D' E' : Expr S}
    (h : HasTypeBE P Γ (.app f n) T) (h' : HasTypeBE P Δ (.app f' n') T')
    (hf : HasTypeBE P Γ f (.pi D E)) (hf' : HasTypeBE P Δ f' (.pi D' E'))
    (hn : HasTypeBE P Γ n D) (hn' : HasTypeBE P Δ n' D')
    (hc : ConvertsBE T (E.instantiate n)) (hc' : ConvertsBE T' (E'.instantiate n'))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (ef' : Evaluator (hw := hw) Ω C hno Δ f' (.pi D' E'))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (en' : Evaluator (hw := hw) Ω C hno Δ n' D')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).knf = (T'.subst e'.images).knf)
    (hF : (Expr.pi D E |>.subst e.images).knf = (Expr.pi D' E' |>.subst e'.images).knf)
    (hN : (n.subst e.images).knf = (n'.subst e'.images).knf)
    (hvf : ∀ ha ha', ((ef e).val ha).val = ((ef' e').val ha').val)
    (hvn : (en e).parameter = (en' e').parameter)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (ha' : ActiveLayer P C (Ω.kprofile (T'.subst e'.images).knf)) :
    ((application h hf hn hc ef en e).val ha).val =
      ((application h' hf' hn' hc' ef' en' e').val ha').val := by
  by_cases hA : ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images).knf)
  · have hA' : ActiveLayer P C (Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_left hA,dite_eq_left hA']
    apply applyValue_congr Ω C hno hF _ _ (hvf _ _) _ _ hN _ _ hvn
  · have hA' : ¬ ActiveLayer P C (Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_right hA,dite_eq_right hA']
    exact canonDistinguished_congr Ω C hno hT

theorem productCandidate_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasTypeBE P Δ D' (.sort a')) (hb' : HasTypeBE P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hD : (D.subst e.images).knf = (D'.subst e'.images).knf)
    (hE : (E.subst (Expr.liftSub e.images)).knf = (E'.subst (Expr.liftSub e'.images)).knf)
    (hvd : Ω.kprofile (D.subst e.images).knf ∈ C → (ed e).read.val = (ed' e').read.val)
    (hvb : ∀ n (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n (D'.subst e'.images))
        p hp hp', Ω.kprofile (E.subst (e.cons hn p hp).images).knf ∈ C →
        (eb (e.cons hn p hp)).read.val = (eb' (e'.cons hn' p hp')).read.val) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val := by
  dsimp only [productCandidate]
  apply ProductInstance.candidate_eq (t := productData hd hb hr e) (t' := productData hd' hb' hr' e') hD hE
  · exact hvd
  · intro n hn p hp hh
    exact hvb n _ _ p _ _ hh

theorem product_val_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasTypeBE P Γ (.pi D E) T) (h' : HasTypeBE P Δ (.pi D' E') T')
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasTypeBE P Δ D' (.sort a')) (hb' : HasTypeBE P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : ConvertsBE T (.sort c)) (hc' : ConvertsBE T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).knf = (T'.subst e'.images).knf)
    (hM : (Expr.pi D E |>.subst e.images).knf = (Expr.pi D' E' |>.subst e'.images).knf)
    (hcc : ({c} : Set S) ∈ C ↔ ({c'} : Set S) ∈ C)
    (hpc : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (ha' : ActiveLayer P C (Ω.kprofile (T'.subst e'.images).knf)) :
    ((product h hd hb hr hc ed eb e).val ha).val =
      ((product h' hd' hb' hr' hc' ed' eb' e').val ha').val := by
  by_cases hh : ({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C
  · have hh' : ({c'} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf ∈ C :=
      ⟨hcc.mp hh.1,hM ▸ hh.2⟩
    simp only [product,dite_eq_left hh,dite_eq_left hh']
    apply withBase_congr Ω C hno hT
    apply Base.update_congr Ω _ (Subtype.ext hM)
    exact hpc hh.2
  · have hh' : ¬ (({c'} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf ∈ C) :=
      fun hcc' => hh ⟨hcc.mpr hcc'.1,hM.symm ▸ hcc'.2⟩
    simp only [product,dite_eq_right hh,dite_eq_right hh']
    exact distinguished_congr Ω C hno hT

theorem product_read_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasTypeBE P Γ (.pi D E) T) (h' : HasTypeBE P Δ (.pi D' E') T')
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasTypeBE P Δ D' (.sort a')) (hb' : HasTypeBE P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : ConvertsBE T (.sort c)) (hc' : ConvertsBE T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hM : (Expr.pi D E |>.subst e.images).knf = (Expr.pi D' E' |>.subst e'.images).knf)
    (hpc : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val) :
    (product h hd hb hr hc ed eb e).read.val = (product h' hd' hb' hr' hc' ed' eb' e').read.val := by
  by_cases hh : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C
  · have hh' : Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf ∈ C := hM ▸ hh
    simp only [product,ite_eq_left hh,ite_eq_left hh']
    exact hpc hh
  · have hh' : Ω.kprofile (Expr.pi D' E' |>.subst e'.images).knf ∉ C := hM ▸ hh
    simp only [product,ite_eq_right hh,ite_eq_right hh']
    exact congrArg (Candidates.Top Ω) hM
end PreResult

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
/-- Two environments match under reindexing of declarations when their old images and parameters agree. -/
def Reindexed (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) (ρ : Nat → Nat) : Prop :=
  ∀ i, i < Γ.length → e.images i = f.images (ρ i) ∧ e.parameters i = f.parameters (ρ i)

namespace Reindexed
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable {ρ : Nat → Nat} (he : e.Reindexed f ρ)
include he
theorem raw_eq {M : Expr S} (hm : M.Scoped Γ.length) :
    M.subst e.images = (M.rename ρ).subst f.images := by
  rw [Expr.subst_rename]
  apply hm.subst_congr
  exact fun n hn => (he n hn).1
theorem expr_eq {M T : Expr S} (h : HasTypeBE P Γ M T) :
    (M.subst e.images).knf = (M.rename ρ |>.subst f.images).knf :=
  congrArg Expr.knf (he.raw_eq h.scope.1)
theorem type_eq {M T : Expr S} (h : HasTypeBE P Γ M T) :
    (T.subst e.images).knf = (T.rename ρ |>.subst f.images).knf :=
  congrArg Expr.knf (he.raw_eq h.scope.2)
theorem cons {A : Expr S} {n m : Expr S}
    (hn : Ω.THasTypeBE n (A.subst e.images)) (hm : Ω.THasTypeBE m (A.rename ρ |>.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).knf p)
    (hp' : PayloadFits Ω C hno (A.rename ρ |>.subst f.images).knf p) :
    (e.cons hn p hp).Reindexed (f.cons hm p hp') (Expr.liftRen ρ) := by
  intro i hi
  cases i with
  | zero => exact ⟨hnm,rfl⟩
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
end Reindexed
end Environment

theorem preEvaluate_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat) (hρ : TypingTreeBE.DeclRenaming Γ Δ ρ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.Reindexed f ρ) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).read.val := by
  induction t generalizing Δ ρ with
  | var ht hd hc =>
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).parameter := by
        refine (PreResult.lookup_parameter ht hd hc e).trans (Eq.trans ?_ (PreResult.lookup_parameter
          (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).symm)
        rw [← hef.type_eq ht, (hef _ ht.scope.1).2]
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ))
        (hef.expr_eq ht) (hef.type_eq ht)
      · simp only [Expr.rename_eq_sort]
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.type_eq ht)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.type_eq ht)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq ht)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasTypeBE P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTreeBE.abstraction ht d b hp hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) hp
          (hp.rename hΔ ρ (hρ.typed hΔ)) hc (hc.rename ρ) _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
          (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg hΔ ρ hρ e f hef
      have hn := ihn hΔ ρ hρ e f hef
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTreeBE.application ht gtr ntr hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.application_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) gtr.typing
          (gtr.typing.rename hΔ ρ (hρ.typed hΔ)) ntr.typing (ntr.typing.rename hΔ ρ (hρ.typed hΔ))
          hc _ _ _ _ _ e f he (hef.type_eq gtr.typing) (hef.expr_eq ntr.typing)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh : HasTypeBE P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb := btr.typing.rename (.cons hΔ hh) (Expr.liftRen ρ) ((hρ.lift D).typed (.cons hΔ hh))
      have hm := hef.expr_eq ht
      have he := hef.type_eq ht
      have hDE := Expr.pi.inj (hef.raw_eq ht.scope.1)
      have hpc : ∀ (_ : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.rename hΔ ρ hρ))
            (preEvaluate Ω C hno (btr.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.knf hDE.1) (congrArg Expr.knf hDE.2)
        · intro _
          exact (ihd hΔ ρ hρ e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
            (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f hm hpc

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
/-- Two environments have the same data when their images are equal and their parameters are equal after canonicalization at the declared types.
Variables only observe canonical parameters. -/
def SameData (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) : Prop :=
  e.images = f.images ∧ ∀ i A, Lookup Γ i A →
    canonOpt hno (A.subst e.images).knf (e.parameters i) = canonOpt hno (A.subst e.images).knf (f.parameters i)
namespace SameData
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}

theorem of_eq (hi : e.images = f.images) (hp : e.parameters = f.parameters) : e.SameData f :=
  ⟨hi, fun i _ _ => by rw [hp]⟩

variable (he : e.SameData f)
include he
theorem raw_eq (M : Expr S) : M.subst e.images = M.subst f.images := congrArg (M.subst) he.1
theorem expr_eq (M : Expr S) : (M.subst e.images).knf = (M.subst f.images).knf :=
  congrArg Expr.knf (he.raw_eq M)
theorem cons_canon {A B : Expr S} {n m : Expr S}
    (hn : Ω.THasTypeBE n (A.subst e.images)) (hm : Ω.THasTypeBE m (B.subst f.images))
    (hnm : n = m) (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hpp : canonOpt hno (A.subst e.images).knf p = canonOpt hno (A.subst e.images).knf p')
    (hp : PayloadFits Ω C hno (A.subst e.images).knf p)
    (hp' : PayloadFits Ω C hno (B.subst f.images).knf p') :
    (e.cons hn p hp).SameData (f.cons hm p' hp') := by
  constructor
  · funext i; cases i with
    | zero => exact hnm
    | succ i => exact congrFun he.1 i
  · intro i A' hi
    cases hi with
    | zero =>
      simp only [Environment.cons, Expr.subst_rename, Function.comp_def]
      exact hpp
    | succ _ hi =>
      simp only [Environment.cons, Expr.subst_rename, Function.comp_def]
      exact he.2 _ _ hi
theorem cons {A B : Expr S} {n m : Expr S}
    (hn : Ω.THasTypeBE n (A.subst e.images)) (hm : Ω.THasTypeBE m (B.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).knf p)
    (hp' : PayloadFits Ω C hno (B.subst f.images).knf p) :
    (e.cons hn p hp).SameData (f.cons hm p hp') :=
  he.cons_canon hn hm hnm p p rfl hp hp'
/-- The canonical observations of a variable agree. -/
theorem lookup_eq {i : Nat} {A T : Expr S} (hd : Lookup Γ i A)
    (hT : (T.subst e.images).knf = (A.subst e.images).knf) :
    canonOpt hno (T.subst e.images).knf (e.parameters i) =
      canonOpt hno (T.subst f.images).knf (f.parameters i) := by
  rw [← he.1, hT]
  exact he.2 i A hd
/-- Terms with equal erasures have equal keys after substitution. -/
theorem erase_eq {M M' : Expr S} (h : M.erase dz = M'.erase dz) :
    (M.subst e.images).knf = (M'.subst f.images).knf := by
  rw [he.1]
  exact Expr.knf_subst_of_erase_eq h _
/-- Convertible terms have equal keys after substitution. -/
theorem conv_eq {X Y : Expr S} (hX : KWN (X.subst e.images)) (hY : KWN (Y.subst f.images))
    (hc : ConvertsBE X Y) : (X.subst e.images).knf = (Y.subst f.images).knf := by
  rw [he.1] at hX ⊢
  exact Expr.knf_converts hX hY (hc.subst f.images).k
end SameData
end Environment

theorem preEvaluate_recontext {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (h : ContextEquivalentBE P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.SameData f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.recontext h) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.recontext h) f).read.val := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup ht' g.choose_spec.1 g.choose_spec.2 f).parameter := by
        rw [PreResult.lookup_parameter, PreResult.lookup_parameter]
        exact hef.lookup_eq hd (e.type_convert_eq ht (HasTypeBE.lookup ht.valid hd) hc)
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht ht' (hef.expr_eq _) (hef.expr_eq _)
      · exact Iff.rfl
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.expr_eq _)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.expr_eq _)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq _)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTreeBE.abstraction ht d b hp hc).recontext h) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht ((h.typing _ _).mp ht) hp ((h.typing _ _).mp hp)
          hc hc _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (h.cons d.typing) (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg h e f hef
      have hn := ihn h e f hef
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTreeBE.application ht gtr ntr hc).recontext h) f).val ha').val := by
        apply PreResult.application_val_congr ht ((h.typing _ _).mp ht) gtr.typing
          ((h.typing _ _).mp gtr.typing) ntr.typing ((h.typing _ _).mp ntr.typing)
          hc hc _ _ _ _ e f he (hef.expr_eq _) (hef.expr_eq _)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh := (h.typing _ _).mp d.typing
      have hb := ((h.cons d.typing).typing _ _).mp btr.typing
      have hm := hef.expr_eq (.pi D E)
      have he := hef.expr_eq T
      have hDE := Expr.pi.inj (hef.raw_eq (.pi D E))
      have hpc : ∀ (_ : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.recontext h))
            (preEvaluate Ω C hno (btr.recontext (h.cons d.typing))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.knf hDE.1) (congrArg Expr.knf hDE.2)
        · intro _
          exact (ihd h e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (h.cons d.typing) (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f hm hpc

/-- **Independence from λ-domains.**
Consider the typing trees of two erasure-normal terms with equal erasures, in equivalent contexts and in environments with the same data.
They have the same values at convertible expected types, and the same `read` at sorts.
This replaces OpenAI's independence of normal trees.
Erasure-normal representatives are unique only up to their λ-domains, and the evaluator ignores λ-domains. -/
theorem enormal_tree_independence {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTreeBE P Γ M T) : ENormal dz M →
    ∀ {Δ : List (Expr S)} {M' U : Expr S} (t' : TypingTreeBE P Δ M' U), ENormal dz M' →
    M.erase dz = M'.erase dz → ContextEquivalentBE P Γ Δ →
    ∀ (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ), e.SameData f →
    (ConvertsBE T U → (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' f).parameter) ∧
    (∀ s s', T = .sort s → U = .sort s' →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' f).read.val) := by
  induction t with
  | @var Γ n A T ht hd hc =>
      intro _ Δ M' U t' _ hme hctx e f hef
      have hM' : M' = .var n := erase_eq_var dz hme.symm
      subst hM'
      cases t' with
      | var ht' hd' hc' =>
          have hv : (PreResult.lookup ht hd hc e).parameter =
              (PreResult.lookup ht' hd' hc' f).parameter := by
            have ht'' := (hctx.typing _ _).mpr ht'
            have hTU : ConvertsBE T U :=
              HasTypeBE.neutral_unique_conv dz (.var n) (.var n) (.refl _) ht ht''
            have hk := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
              ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hTU
            have hl := hef.lookup_eq hd (e.type_convert_eq ht (HasTypeBE.lookup ht.valid hd) hc)
            rw [PreResult.lookup_parameter, PreResult.lookup_parameter, ← hk]
            rw [← hef.1] at hl
            exact hl
          refine ⟨fun _ => hv, ?_⟩
          intro s s' hs hs'
          subst hs hs'
          have ht'' := (hctx.typing _ _).mpr ht'
          have he : s = s' := (HasTypeBE.neutral_unique (.var n) ht ht'').sort_inj
          subst he
          apply PreResult.baseRead_congr ht ht' (hef.expr_eq _) rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ hv ha hb
  | @sort Γ s₀ t₀ T ht ha hc =>
      intro _ Δ M' U t' _ hme hctx e f hef
      have hM' : M' = .sort s₀ := erase_eq_sort dz hme.symm
      subst hM'
      cases t' with
      | sort ht' ha' hc' =>
          constructor
          · intro hh
            have hT := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
              ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hh
            apply PreResult.parameter_congr _ _ hT
            intro _ _
            exact distinguished_congr Ω C hno hT
          · exact fun _ _ _ _ => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      intro hn Δ M' U t' hn' hme hctx e f hef
      obtain ⟨D', m', rfl, hm⟩ := erase_eq_lam dz hme.symm
      cases t' with
      | @abstraction _ _ _ E' a' s' _ ht' d' b' hp' hc' =>
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
            exact PreResult.val_congr _ _ ((ihb hn.lam b' hn'.lam hm.symm hctx'
              (e.cons hnt p hpa) (f.cons hn'' p hpb) (hef.cons hnt hn'' rfl p hpa hpb)).1 cE)
              hact hact'
          · intro r r' hs _
            exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht ft nt hc ihf ihn =>
      intro hn Δ M' U t' hn' hme hctx e f hef
      obtain ⟨g', n', rfl, hg, hnn⟩ := erase_eq_app dz hme.symm
      cases t' with
      | @application _ _ _ D' E' _ ht' ft' nt' hc' =>
          obtain ⟨eg, en, gnl⟩ := hn.app
          obtain ⟨eg', en', _⟩ := hn'.app
          have hgΓ := (hctx.typing _ _).mpr ft'.typing
          have cg : ConvertsBE g g' := convertsBE_of_erase_eq hg.symm
          have hneu : Neutral g := neutral_of_enormalBE dz g ft.typing eg gnl
          have hneu' : Neutral g' := by
            apply neutral_of_enormalBE dz g' ft'.typing eg'
            intro A b h
            subst h
            obtain ⟨A', b', hgl, _⟩ := erase_eq_lam dz (show g.erase dz = (Expr.lam A b).erase dz from hg.symm)
            exact gnl A' b' hgl
          have hF : ConvertsBE (.pi D E) (.pi D' E') :=
            HasTypeBE.neutral_unique_conv dz hneu hneu' cg ft.typing hgΓ
          have hD := (hF.product_compatibility dz).1
          have hme' : (Expr.app g n).erase dz = (Expr.app g' n').erase dz := by
            simp only [Expr.erase, hg, hnn]
          have hv : ConvertsBE T U →
              (preEvaluate Ω C hno (.application ht ft nt hc) e).parameter =
              (preEvaluate Ω C hno (.application ht' ft' nt' hc') f).parameter := by
            intro hh
            have hT := hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
              ((ContextTowerBE.THasTypeBE.subst ht' f.typed).type_kwn hw) hh
            apply PreResult.parameter_congr _ _ hT
            apply PreResult.application_val_congr ht ht' ft.typing ft'.typing nt.typing nt'.typing
              hc hc' _ _ _ _ e f hT
              (hef.conv_eq ((ContextTowerBE.THasTypeBE.subst ft.typing e.typed).type_kwn hw)
                ((ContextTowerBE.THasTypeBE.subst ft'.typing f.typed).type_kwn hw) hF)
              (hef.erase_eq hnn.symm)
            · exact fun ha hb => PreResult.val_congr _ _
                ((ihf eg ft' eg' hg.symm hctx e f hef).1 hF) ha hb
            · exact (ihn en nt' en' hnn.symm hctx e f hef).1 hD
          refine ⟨hv, ?_⟩
          intro s s' hs hs'
          subst hs hs'
          have ht'' := (hctx.typing _ _).mpr ht'
          have hc0 : ConvertsBE (Expr.app g n) (.app g' n') := convertsBE_of_erase_eq hme'
          have hss : ConvertsBE (Expr.sort s) (.sort s') :=
            HasTypeBE.neutral_unique_conv dz (Neutral.app hneu) (Neutral.app hneu') hc0 ht ht''
          have he : s = s' := hss.sort_inj
          subst he
          apply PreResult.baseRead_congr ht ht' (hef.erase_eq hme') rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ (hv (.refl _)) ha hb
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      intro hn Δ M' U t' hn' hme hctx e f hef
      obtain ⟨D', E', rfl, hDe, hEe⟩ := erase_eq_pi dz hme.symm
      cases t' with
      | @product _ _ _ a' b' c' _ ht' d' bt' hr' hc' =>
          obtain ⟨eD, eE⟩ := hn.pi
          obtain ⟨eD', eE'⟩ := hn'.pi
          have hd'Γ : HasTypeBE P Γ D' (.sort a') := (hctx.typing _ _).mpr d'.typing
          have cD : ConvertsBE D D' := convertsBE_of_erase_eq hDe.symm
          have hctx' : ContextEquivalentBE P (D :: Γ) (D' :: Δ) :=
            (ContextEquivalentBE.head_conversion d.typing hd'Γ cD).trans (hctx.cons hd'Γ)
          have hme' : (Expr.pi D E).erase dz = (Expr.pi D' E').erase dz := by
            simp only [Expr.erase, hDe, hEe]
          have hM : ((Expr.pi D E).subst e.images).knf = ((Expr.pi D' E').subst f.images).knf :=
            hef.erase_eq hme'
          have hEk : (E.subst (Expr.liftSub e.images)).knf =
              (E'.subst (Expr.liftSub f.images)).knf := by
            rw [hef.1]
            exact Expr.knf_subst_of_erase_eq hEe.symm _
          have hpc : (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
              (preEvaluate Ω C hno bt) e).val =
              (PreResult.productCandidate d'.typing bt'.typing hr' (preEvaluate Ω C hno d')
                (preEvaluate Ω C hno bt') f).val := by
            apply PreResult.productCandidate_congr d.typing bt.typing hr d'.typing bt'.typing hr'
              _ _ _ _ e f (hef.erase_eq hDe.symm) hEk
            · exact fun _ => (ihd eD d' eD' hDe.symm hctx e f hef).2 a a' rfl rfl
            · intro n hn₁ hn₂ p hp hp' _
              exact (ihb eE bt' eE' hEe.symm hctx' (e.cons hn₁ p hp) (f.cons hn₂ p hp')
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

end PureTypeSystem.KP.ObservationValues

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))

/-- Goodness at the base. It deliberately does not depend on observation parameters. -/
def baseGood (M T : Expr S) (σ : Nat → Expr S) (v : Prop) : Prop :=
  Ω.kprofile (M.subst σ) ∈ C →
    ∃ s, T = .sort s ∧ ({s} : Set S) ∈ C ∧
      (ActiveLayer P C (Ω.kprofile (T.subst σ)) → v) ∧
      (¬ ActiveLayer P C (Ω.kprofile (T.subst σ)) → Neutral M)

noncomputable def goodness {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTreeBE P Γ M T) (σ : Nat → Expr S) : Prop × Prop :=
  match t with
  | .var _ _ _ => (True,baseGood Ω C M T σ True)
  | .sort _ _ _ => (True,True)
  | @TypingTreeBE.product _ _ _ D E _ _ c _ _ d e _ _ =>
    let g := (Ω.kprofile (D.subst σ) ∈ C → (goodness d σ).2) ∧
      ∀ n, Ω.THasTypeBE n (D.subst σ) → Ω.kprofile (E.subst (Expr.consSub n σ)) ∈ C →
        (goodness e (Expr.consSub n σ)).2
    ((({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst σ) ∈ C) → g,
      Ω.kprofile (Expr.pi D E |>.subst σ) ∈ C → g)
  | @TypingTreeBE.abstraction _ _ _ D m E _ _ _ _ _ b _ _ =>
    let g := ∀ n, Ω.THasTypeBE n (D.subst σ) → ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n σ))) →
      (goodness b (Expr.consSub n σ)).1
    (g,baseGood Ω C M T σ g)
  | @TypingTreeBE.application _ _ _ g n D E _ _ f a _ =>
    let v := if ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst σ)) then
      (goodness f σ).1 ∧ (ActiveLayer P C (Ω.kprofile (D.subst σ)) → (goodness a σ).1)
      else Neutral (.app g n)
    (v,baseGood Ω C M T σ v)

abbrev ValGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).1
abbrev ReadGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).2

def Relevant (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P Γ M) K
namespace Relevant
variable {Ω C}
theorem pred {Γ Δ : List (Expr S)} {M N : Expr S} (h : Relevant (P := P) C Γ M)
    (hp : Reach (PrimaryEdge P) (ProfileR P Δ N) (ProfileR P Γ M)) : Relevant (P := P) C Δ N := by
  obtain ⟨K,hK,hp'⟩ := h
  exact ⟨K,hK,hp.trans hp'⟩
end Relevant

variable (hw : SystemENormalizing' P) (hC : IsComponent (PrimaryEdge P) C)
include hw hC
theorem relevant_actual_mem {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : HasTypeBE P Γ M (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hr : Relevant (P := P) C Γ M) (hm : Ω.kprofile (M.subst σ) ∈ C) : ProfileR P Γ M ∈ C := by
  obtain ⟨K,hK,hp⟩ := hr
  have hg := Ω.kprofile_subst_growth hw ht hσ.toK
  have hga := ContextTowerBE.THasTypeBE.subst ht hσ
  have hpath := Profile.inclusion_path (Ω.kprofile_feasible hw hga.toK)
    (ProfileR.feasible' hw ht) hg
  exact hC.between hm hK hpath.reach hp

theorem normal_baseGood {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (h : HasTypeBE P Γ M (.sort s)) (hn : ENormal dz M) (hne : Neutral M)
    (hσ : Ω.TTypedSubstitutionBE Γ σ) (hr : Relevant (P := P) C Γ M) {v : Prop}
    (hv : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst σ)) → v) :
    baseGood Ω C M (.sort s) σ v := by
  intro hm
  have hp := relevant_actual_mem Ω C hw hC h hσ hr hm
  rw [ProfileR.neutral_enormal hw hn hne h] at hp
  exact ⟨s,rfl,hp,hv,fun _ => hne⟩

theorem normal_good {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    (hn : ENormal dz M) (σ : Nat → Expr S) (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    (ActiveLayer P C (Ω.kprofile (T.subst σ)) → ValGood Ω C t σ) ∧
    (∀ s, T = .sort s → Relevant (P := P) C Γ M → ReadGood Ω C t σ) := by
  induction t generalizing σ with
  | var ht hd hc =>
      refine ⟨fun _ => trivial,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn (.var _) hσ hr (fun _ => trivial)
  | sort ht ha hc => exact ⟨fun _ => trivial,fun _ _ _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv : ValGood Ω C (.abstraction ht d b hp hc) σ := by
        intro n hn' ha
        exact (ihb hn.lam (Expr.consSub n σ) (hσ.cons hn')).1 ha
      refine ⟨fun _ => hv,?_⟩
      intro s hs _
      exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      obtain ⟨eg, ea, gnl⟩ := hn.app
      have hne : Neutral (.app g n) := .app (neutral_of_enormalBE dz g f.typing eg gnl)
      have hv : ValGood Ω C (.application ht f a hc) σ := by
        dsimp only [ValGood,goodness]
        split
        · rename_i hf
          exact ⟨(ihf eg σ hσ).1 hf,fun ha => (iha ea σ hσ).1 ha⟩
        · exact hne
      refine ⟨fun _ => hv,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn hne hσ hr (fun _ => hv)
  | @product Γ D E a b c T ht d e hr hc ihd ihe =>
      have hpi : HasTypeBE P Γ (.pi D E) (.sort c) := .product d.typing e.typing hr
      have hp := ProfileR.triple' hw hpi
      have hg : Relevant (P := P) C Γ (.pi D E) →
          (Ω.kprofile (D.subst σ) ∈ C → ReadGood Ω C d σ) ∧
          (∀ n, Ω.THasTypeBE n (D.subst σ) → Ω.kprofile (E.subst (Expr.consSub n σ)) ∈ C →
            ReadGood Ω C e (Expr.consSub n σ)) := by
        intro hrel
        constructor
        · intro _
          exact (ihd hn.pi.1 σ hσ).2 a rfl (hrel.pred (.single (.domain hp)))
        · intro n hn' _
          exact (ihe hn.pi.2 (Expr.consSub n σ) (hσ.cons hn')).2 b rfl
            (hrel.pred (.single (.codomain hp)))
      constructor
      · intro hat hcc
        have hconv : (T.subst σ).knf = .sort c :=
          (Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst ht hσ).type_kwn hw)
            ((ContextTowerBE.THasTypeBE.subst hpi hσ).type_kwn hw) (hc.subst σ).k).trans
              (Expr.knf_sort c)
        have hax : (AxProfile P c).Nonempty := by
          have hh := hat.nonempty
          rwa [← Ω.kprofile_knf (T.subst σ),hconv,Ω.kprofile_sort] at hh
        have hs : ({c} : Set S) ⊆ ProfileR P Γ (.pi D E) := by
          intro r hr'
          have he : r = c := hr'
          subst r
          exact ProfileR.of_type hpi
        exact hg ⟨{c},hcc.1,(Profile.inclusion_path hp.product (FeasibleProfile.singleton hax) hs).reach⟩
      · intro _ _ hrel
        exact fun _ => hg hrel

end PureTypeSystem.KP.ObservationValues

namespace PureTypeSystem
universe u
namespace ContextTowerBE.TTypedSubstitutionBE
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
    {Ω : ContextTowerBE P} {Γ : List (Expr S)} {σ τ : Nat → Expr S}
/-- Two substitutions are compatible on a context when their images have equal keys. -/
def Compatible (Γ : List (Expr S)) (σ τ : Nat → Expr S) : Prop :=
  ∀ n, n < Γ.length → KConverts (σ n) (τ n)
namespace Compatible
variable (hw : SystemENormalizing' P)
include hw
theorem expr_eq (he : Compatible Γ σ τ) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hτ : Ω.TTypedSubstitutionBE Γ τ) {M A : Expr S} (h : PureTypeSystem.HasTypeBE P Γ M A) :
    (M.subst σ).knf = (M.subst τ).knf :=
  Expr.knf_converts ((THasTypeBE.subst h hσ).kwn hw)
    ((THasTypeBE.subst h hτ).kwn hw) (h.scope.1.subst_kconverts he)
theorem type_eq (he : Compatible Γ σ τ) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hτ : Ω.TTypedSubstitutionBE Γ τ) {M A : Expr S} (h : PureTypeSystem.HasTypeBE P Γ M A) :
    (A.subst σ).knf = (A.subst τ).knf :=
  Expr.knf_converts ((THasTypeBE.subst h hσ).type_kwn hw)
    ((THasTypeBE.subst h hτ).type_kwn hw) (h.scope.2.subst_kconverts he)
theorem expr_profile (he : Compatible Γ σ τ) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hτ : Ω.TTypedSubstitutionBE Γ τ) {M A : Expr S} (h : PureTypeSystem.HasTypeBE P Γ M A) :
    Ω.kprofile (M.subst σ) = Ω.kprofile (M.subst τ) :=
  Ω.kprofile_of_knf_eq (he.expr_eq hw hσ hτ h)
theorem type_profile (he : Compatible Γ σ τ) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hτ : Ω.TTypedSubstitutionBE Γ τ) {M A : Expr S} (h : PureTypeSystem.HasTypeBE P Γ M A) :
    Ω.kprofile (A.subst σ) = Ω.kprofile (A.subst τ) :=
  Ω.kprofile_of_knf_eq (he.type_eq hw hσ hτ h)
omit hw in
theorem cons (he : Compatible Γ σ τ) {D n m : Expr S} (hh : KConverts n m) :
    Compatible (D :: Γ) (Expr.consSub n σ) (Expr.consSub m τ) := by
  intro i hi
  cases i with
  | zero => exact hh
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
omit hw in
theorem cons_same (he : Compatible Γ σ τ) (D n : Expr S) :
    Compatible (D :: Γ) (Expr.consSub n σ) (Expr.consSub n τ) := he.cons (.refl _)
end Compatible
end ContextTowerBE.TTypedSubstitutionBE

namespace KP.ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))
variable (hw : SystemENormalizing' P)
include hw

theorem baseGood_congr {Γ : List (Expr S)} {M T : Expr S} {σ τ : Nat → Expr S}
    (h : HasTypeBE P Γ M T) (hσ : Ω.TTypedSubstitutionBE Γ σ) (hτ : Ω.TTypedSubstitutionBE Γ τ)
    (he : ContextTowerBE.TTypedSubstitutionBE.Compatible Γ σ τ) {v w : Prop} (hv : v ↔ w) :
    baseGood Ω C M T σ v ↔ baseGood Ω C M T τ w := by
  simp only [baseGood,he.expr_profile hw hσ hτ h,he.type_profile hw hσ hτ h,hv]

theorem goodness_compatible {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {σ τ : Nat → Expr S} (hσ : Ω.TTypedSubstitutionBE Γ σ) (hτ : Ω.TTypedSubstitutionBE Γ τ)
    (he : ContextTowerBE.TTypedSubstitutionBE.Compatible Γ σ τ) :
    (ValGood Ω C t σ ↔ ValGood Ω C t τ) ∧ (ReadGood Ω C t σ ↔ ReadGood Ω C t τ) := by
  induction t generalizing σ τ with
  | var ht hd hc => exact ⟨Iff.rfl,baseGood_congr Ω C hw ht hσ hτ he Iff.rfl⟩
  | sort ht ha hc => exact ⟨Iff.rfl,Iff.rfl⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hind (n : Expr S) : Ω.THasTypeBE n (D.subst σ) ↔ Ω.THasTypeBE n (D.subst τ) := by
        have hk := he.expr_eq hw hσ hτ d.typing
        exact ⟨fun hn => hn.of_type_knf_eq hk, fun hn => hn.of_type_knf_eq hk.symm⟩
      have hv : ValGood Ω C (.abstraction ht d b hp hc) σ ↔ ValGood Ω C (.abstraction ht d b hp hc) τ := by
        dsimp only [ValGood,goodness]
        apply forall_congr'; intro n
        constructor
        · intro h hn
          have hn' := (hind n).mpr hn
          have he' := he.cons_same D n
          rw [← he'.type_profile hw (hσ.cons hn') (hτ.cons hn) b.typing]
          exact fun ha => (ihb (hσ.cons hn') (hτ.cons hn) he').1.mp (h hn' ha)
        · intro h hn
          have hn' := (hind n).mp hn
          have he' := he.cons_same D n
          rw [he'.type_profile hw (hσ.cons hn) (hτ.cons hn') b.typing]
          exact fun ha => (ihb (hσ.cons hn) (hτ.cons hn') he').1.mpr (h hn' ha)
      exact ⟨hv,baseGood_congr Ω C hw ht hσ hτ he hv⟩
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hv : ValGood Ω C (.application ht f a hc) σ ↔ ValGood Ω C (.application ht f a hc) τ := by
        dsimp only [ValGood,goodness]
        have hF := he.type_profile hw hσ hτ f.typing
        have hD := he.type_profile hw hσ hτ a.typing
        rw [hF,hD]
        split
        · exact and_congr (ihf hσ hτ he).1 (imp_congr_right fun _ => (iha hσ hτ he).1)
        · exact Iff.rfl
      exact ⟨hv,baseGood_congr Ω C hw ht hσ hτ he hv⟩
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hind (n : Expr S) : Ω.THasTypeBE n (D.subst σ) ↔ Ω.THasTypeBE n (D.subst τ) := by
        have hk := he.expr_eq hw hσ hτ d.typing
        exact ⟨fun hn => hn.of_type_knf_eq hk, fun hn => hn.of_type_knf_eq hk.symm⟩
      have hbody : (∀ n, Ω.THasTypeBE n (D.subst σ) → Ω.kprofile (E.subst (Expr.consSub n σ)) ∈ C → ReadGood Ω C bt (Expr.consSub n σ)) ↔
          (∀ n, Ω.THasTypeBE n (D.subst τ) → Ω.kprofile (E.subst (Expr.consSub n τ)) ∈ C → ReadGood Ω C bt (Expr.consSub n τ)) := by
        apply forall_congr'; intro n
        constructor
        · intro h hn
          have hn' := (hind n).mpr hn
          have he' := he.cons_same D n
          rw [← he'.expr_profile hw (hσ.cons hn') (hτ.cons hn) bt.typing]
          exact fun hh => (ihb (hσ.cons hn') (hτ.cons hn) he').2.mp (h hn' hh)
        · intro h hn
          have hn' := (hind n).mp hn
          have he' := he.cons_same D n
          rw [he'.expr_profile hw (hσ.cons hn) (hτ.cons hn') bt.typing]
          exact fun hh => (ihb (hσ.cons hn) (hτ.cons hn') he').2.mpr (h hn' hh)
      dsimp only [ValGood,ReadGood,goodness]
      have hD := he.expr_profile hw hσ hτ d.typing
      have hM := he.expr_profile hw hσ hτ ht
      rw [hD,hM]
      have hg := and_congr (imp_congr_right fun (_ : Ω.kprofile (D.subst τ) ∈ C) => (ihd hσ hτ he).2) hbody
      exact ⟨imp_congr_right fun _ => hg,imp_congr_right fun _ => hg⟩

end KP.ObservationValues

namespace KP.ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S))

theorem baseGood_rename {M T : Expr S} (ρ : Nat → Nat) (σ : Nat → Expr S) (v : Prop) :
    baseGood Ω C (M.rename ρ) (T.rename ρ) σ v ↔ baseGood Ω C M T (σ ∘ ρ) v := by
  simp only [baseGood,Expr.subst_rename,Expr.rename_eq_sort,Neutral.rename_iff]

theorem goodness_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) (ρ : Nat → Nat) (hρ : TypingTreeBE.DeclRenaming Γ Δ ρ)
    (σ : Nat → Expr S) :
    goodness Ω C (t.rename hΔ ρ hρ) σ = goodness Ω C t (σ ∘ ρ) := by
  induction t generalizing Δ ρ σ with
  | var ht hd hc =>
      apply Prod.ext
      · rfl
      · exact propext (baseGood_rename Ω C ρ σ True)
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasTypeBE P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      have hv : (∀ n, Ω.THasTypeBE n ((D.rename ρ).subst σ) →
          ActiveLayer P C (Ω.kprofile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ))) →
          (goodness Ω C (b.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).1) ↔
          (∀ n, Ω.THasTypeBE n (D.subst (σ ∘ ρ)) →
          ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n (σ ∘ ρ)))) →
          (goodness Ω C b (Expr.consSub n (σ ∘ ρ))).1) := by
        simp only [Expr.subst_rename,Expr.consSub_liftRen,hb]
      apply Prod.ext
      · exact propext hv
      · change baseGood Ω C (Expr.lam D m |>.rename ρ) (T.rename ρ) σ _ = _
        exact (propext (baseGood_rename Ω C ρ σ _)).trans
          (congrArg (baseGood Ω C (.lam D m) T (σ ∘ ρ)) (propext hv))
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hg := ihf hΔ ρ hρ σ
      have hn := iha hΔ ρ hρ σ
      have hv : (goodness Ω C ((TypingTreeBE.application ht f a hc).rename hΔ ρ hρ) σ).1 =
          (goodness Ω C (.application ht f a hc) (σ ∘ ρ)).1 := by
        change (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E |>.rename ρ).subst σ)) then
          (goodness Ω C (f.rename hΔ ρ hρ) σ).1 ∧
            (ActiveLayer P C (Ω.kprofile ((D.rename ρ).subst σ)) → (goodness Ω C (a.rename hΔ ρ hρ) σ).1)
          else Neutral ((Expr.app g n).rename ρ)) =
          (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst (σ ∘ ρ))) then
            (goodness Ω C f (σ ∘ ρ)).1 ∧
              (ActiveLayer P C (Ω.kprofile (D.subst (σ ∘ ρ))) → (goodness Ω C a (σ ∘ ρ)).1)
            else Neutral (.app g n))
        rw [hg,hn]
        rw [Expr.subst_rename,Expr.subst_rename]
        split
        · rfl
        · exact propext Neutral.rename_iff
      apply Prod.ext hv
      change baseGood Ω C (Expr.app g n |>.rename ρ) (T.rename ρ) σ _ = _
      exact (propext (baseGood_rename Ω C ρ σ _)).trans
        (congrArg (baseGood Ω C (.app g n) T (σ ∘ ρ)) hv)
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hh : HasTypeBE P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hd := ihd hΔ ρ hρ σ
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      let g : Prop := (Ω.kprofile ((D.rename ρ).subst σ) ∈ C →
          (goodness Ω C (d.rename hΔ ρ hρ) σ).2) ∧
          ∀ n, Ω.THasTypeBE n ((D.rename ρ).subst σ) →
            Ω.kprofile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ)) ∈ C →
              (goodness Ω C (bt.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).2
      let g' : Prop := (Ω.kprofile (D.subst (σ ∘ ρ)) ∈ C → (goodness Ω C d (σ ∘ ρ)).2) ∧
          ∀ n, Ω.THasTypeBE n (D.subst (σ ∘ ρ)) → Ω.kprofile (E.subst (Expr.consSub n (σ ∘ ρ))) ∈ C →
            (goodness Ω C bt (Expr.consSub n (σ ∘ ρ))).2
      have he : g = g' := by
        dsimp only [g,g']
        simp only [hd,hb,Expr.subst_rename,Expr.consSub_liftRen]
      change ((({c} : Set S) ∈ C ∧ Ω.kprofile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C) → g,
        Ω.kprofile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C → g) =
        ((({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C) → g',
        Ω.kprofile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C → g')
      simp only [Expr.subst_rename,he]

theorem valGood_retarget {Γ : List (Expr S)} {M T T' : Expr S} (t : TypingTreeBE P Γ M T)
    (ht : HasTypeBE P Γ M T') (hc : ConvertsBE T' T) (σ : Nat → Expr S) :
    ValGood Ω C (t.retarget ht hc) σ ↔ ValGood Ω C t σ := by
  cases t <;> exact Iff.rfl
end KP.ObservationValues

namespace ContextTowerBE
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)
variable (hw : SystemENormalizing' P)
include hw

theorem kinstantiate_profile_ascent {Γ : List (Expr S)} {D E n : Expr S} {s : S}
    (hp : PureTypeSystem.HasTypeBE P Γ (.pi D E) (.sort s))
    (hn : PureTypeSystem.HasTypeBE P Γ n D) {σ : Nat → Expr S} (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.kprofile ((E.instantiate n).subst σ))
      (Ω.kprofile (Expr.pi D E |>.subst σ)) := by
  have hp' := THasTypeBE.subst hp hσ
  have hn' := THasTypeBE.subst hn hσ
  obtain ⟨J,htr,hpath⟩ := Ω.kframe_profiles hw hp'.toK hn'.toK
  rw [← Expr.instantiate_subst]
  exact hpath.trans (.single (.codomain htr))

theorem kneutral_profile_ascent {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : PureTypeSystem.HasTypeBE P Γ M T)
    {σ : Nat → Expr S} (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Ω.kprofile (T.subst σ)) (Ω.kprofile (D.subst σ)) := by
  induction hne generalizing T with
  | var n =>
      obtain ⟨D,hd,hc⟩ := ht.generation
      refine ⟨n,D,rfl,hd,?_⟩
      rw [Ω.kprofile_converts ((THasTypeBE.subst ht hσ).type_kwn hw)
        ((THasTypeBE.subst (PureTypeSystem.HasTypeBE.lookup ht.valid hd) hσ).type_kwn hw)
        (hc.subst σ).k]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D,E,hf,ha,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hf.product_type_sorted
      obtain ⟨n,A,hh,hl,hr⟩ := ih hf
      refine ⟨n,A,hh,hl,?_⟩
      rw [Ω.kprofile_converts ((THasTypeBE.subst ht hσ).type_kwn hw)
        ((THasTypeBE.subst (PureTypeSystem.HasTypeBE.application hf ha) hσ).type_kwn hw)
        (hc.subst σ).k]
      exact (Ω.kinstantiate_profile_ascent hw hp ha hσ).trans hr
end ContextTowerBE

namespace KP.ObservationValues
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) (C : Set (Set S)) (hw : SystemENormalizing' P)
/-- Only replacements that are not neutral need the guard on activity. -/
def SubstitutionGuard (Γ : List (Expr S)) (σ ξ : Nat → Expr S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Ω.kprofile (D.subst ξ) ∈ ObservationLayers P C →
    ActiveLayer P C (Ω.kprofile (D.subst ξ))

include hw
theorem neutral_subst_of_inactive {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : HasTypeBE P Γ M T) {σ ξ : Nat → Expr S}
    (hξ : Ω.TTypedSubstitutionBE Γ ξ) (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hH : Ω.kprofile (T.subst ξ) ∈ ObservationLayers P C)
    (hina : ¬ ActiveLayer P C (Ω.kprofile (T.subst ξ))) : Neutral (M.subst σ) := by
  apply hne.subst_of_head
  intro n hhead
  by_contra hn
  obtain ⟨i,D,hhead',hd,hpath⟩ := Ω.kneutral_profile_ascent hw hne ht hξ
  have he : i = n := Expr.var.inj (hhead'.symm.trans hhead)
  subst i
  have hI := ObservationLayers.positive hH hpath
  exact hina ((hguard n D hd hn hI).predecessor (ObservationLayers.secondary hH hpath).reach)

theorem skipped_application_subst {Γ : List (Expr S)} {f a D E T : Expr S}
    (h : HasTypeBE P Γ (.app f a) T) (hf : HasTypeBE P Γ f (.pi D E)) (ha : HasTypeBE P Γ a D)
    (hc : ConvertsBE T (E.instantiate a)) (hne : Neutral (.app f a))
    {σ ξ : Nat → Expr S} (hξ : Ω.TTypedSubstitutionBE Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hactive : ActiveLayer P C (Ω.kprofile (T.subst ξ)))
    (hina : ¬ ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst ξ))) :
    Neutral (Expr.app f a |>.subst σ) := by
  have hF : Ω.kprofile (Expr.pi D E |>.subst ξ) ∈ ObservationLayers P C := by
    obtain ⟨s,hp⟩ := hf.product_type_sorted
    have he := Ω.kprofile_converts ((ContextTowerBE.THasTypeBE.subst h hξ).type_kwn hw)
      ((ContextTowerBE.THasTypeBE.subst (HasTypeBE.application hf ha) hξ).type_kwn hw) (hc.subst ξ).k
    exact ObservationLayers.positive (he ▸ hactive.layer) (Ω.kinstantiate_profile_ascent hw hp ha hξ)
  have hnf : Neutral f := by cases hne; assumption
  exact .app (neutral_subst_of_inactive Ω C hw hnf hf hξ hguard hF hina)

theorem skipped_read_subst {Γ : List (Expr S)} {M : Expr S} {s : S}
    (h : HasTypeBE P Γ M (.sort s)) (hne : Neutral M)
    {σ ξ : Nat → Expr S} (hξ : Ω.TTypedSubstitutionBE Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ) (hs : ({s} : Set S) ∈ C)
    (hina : ¬ ActiveLayer P C (AxProfile P s)) : Neutral (M.subst σ) := by
  have hH : AxProfile P s ∈ ObservationLayers P C :=
    ⟨s,hs,h.neutral_axiom hw hne,.refl⟩
  apply neutral_subst_of_inactive Ω C hw hne h hξ hguard
  · simpa only [Expr.subst,Ω.kprofile_sort] using hH
  · simpa only [Expr.subst,Ω.kprofile_sort] using hina
end KP.ObservationValues
end PureTypeSystem

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

theorem distinguished_base (T : ActiveType Ω C) :
    RawValue.base (hw := hw) Ω C hno (distinguished (hw := hw) Ω C hno T).val = topBase Ω := by
  unfold distinguished
  split
  · exact (ActualPlain.schema hw).distinguished_base _ _ _
  · split
    · rfl
    · rfl

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M : Expr S} {s : S}
    {e : Environment (hw := hw) Ω C hno Γ}
theorem baseRead_eq (h : HasTypeBE P Γ M (.sort s))
    (v : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf) →
      Value (hw := hw) Ω C hno (Expr.sort s |>.subst e.images).knf)
    (hM : Ω.kprofile (M.subst e.images).knf ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)) :
    (baseRead h v).val = ((RawValue.base Ω C hno (v ha).val) (e.actualExpression h)).val := by
  have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hs⟩
  simp only [baseRead,dite_eq_left hM,dite_eq_left hex,dite_eq_left ha]

theorem product_read_base {D E : Expr S} {a b c : S}
    (h : HasTypeBE P Γ (.pi D E) (.sort s))
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (hc : ConvertsBE (.sort s) (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (e : Environment (hw := hw) Ω C hno Γ)
    (hm : Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)) :
    (product h hd hb hr hc ed eb e).read.val =
      ((RawValue.base Ω C hno ((product h hd hb hr hc ed eb e).val ha).val) (e.actualExpression h)).val := by
  have hh : ({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C := ⟨hc.sort_inj ▸ hs,hm⟩
  dsimp only [product]
  rw [ite_eq_left hm,dite_eq_left hh,withBase_base]
  simp only [Base.update_same]
end PreResult

theorem preEvaluate_read_base {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTreeBE P Γ M (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hM : Ω.kprofile (M.subst e.images).knf ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)) :
    (preEvaluate Ω C hno t e).read.val =
      ((RawValue.base Ω C hno ((preEvaluate Ω C hno t e).val ha).val) (e.actualExpression t.typing)).val := by
  cases t with
  | var ht hd hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | sort ht hax hc =>
      change (Candidates.Top Ω (Expr.sort _ |>.subst e.images).knf) = _
      rw [show ((preEvaluate Ω C hno (.sort ht hax hc) e).val ha).val =
        (distinguished Ω C hno (e.activeType ht ha)).val from rfl,distinguished_base]
      rfl
  | product ht d b hr hc => exact PreResult.product_read_base ht d.typing b.typing hr hc _ _ e hM hs ha
  | abstraction ht d b hp hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | application ht f a hc => exact PreResult.baseRead_eq ht _ hM hs ha

omit hno [Fintype S] in
theorem baseGood_active_iff {M : Expr S} {s : S} {σ : Nat → Expr S} {v : Prop}
    (hm : Ω.kprofile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst σ))) :
    baseGood Ω C M (.sort s) σ v ↔ v := by
  constructor
  · intro h
    obtain ⟨s',_,_,hv,_⟩ := h hm
    exact hv ha
  · intro hv _
    exact ⟨s,rfl,hs,fun _ => hv,fun hn => False.elim (hn ha)⟩

omit hno [Fintype S] in
theorem readGood_active_iff {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTreeBE P Γ M (.sort s)) {σ : Nat → Expr S}
    (hm : Ω.kprofile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst σ))) :
    ReadGood Ω C t σ ↔ ValGood Ω C t σ := by
  cases t with
  | var ht hd hc => exact baseGood_active_iff Ω C hm hs ha
  | sort ht hax hc => exact Iff.rfl
  | product ht d b hr hc =>
      dsimp only [ReadGood,ValGood,goodness]
      have hc' := hc.sort_inj
      simp only [← hc',hm,hs,true_and,true_implies]
  | abstraction ht d b hp hc => exact baseGood_active_iff Ω C hm hs ha
  | application ht f a hc => exact baseGood_active_iff Ω C hm hs ha
end PureTypeSystem.KP.ObservationValues

