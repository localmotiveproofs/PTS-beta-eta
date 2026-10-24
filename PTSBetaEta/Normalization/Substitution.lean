/- Adapted to typing with βη-conversion from OpenAI's `Substitution.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.CanonLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem
universe u

namespace TypingTreeBE.StoredSubstitution
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {n D : Expr S}
noncomputable def single (t : TypingTreeBE P Γ n D) :
    StoredSubstitution P (D :: Γ) Γ (Expr.single n) :=
  fun i => match i with
  | 0 => fun A hi => by
      have he : A = D.rename Nat.succ := by cases hi; rfl
      have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
      exact t.retarget (he'.symm ▸ t.typing) (by rw [he']; exact .refl _)
  | i+1 => fun A hi => by
      let hex : ∃ B, Lookup Γ i B ∧ A = B.rename Nat.succ := by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he : A.subst (Expr.single n) = hex.choose := by
        exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
          (Expr.subst_lift_single hex.choose n)
      exact .var (he.symm ▸ HasTypeBE.lookup t.typing.valid hex.choose_spec.1)
        hex.choose_spec.1 (by rw [he]; exact .refl _)
end TypingTreeBE.StoredSubstitution

namespace KP.ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) (C : Set (Set S))

namespace SubstitutionGuard
variable {Ω C} {Γ Δ : List (Expr S)} {σ ξ : Nat → Expr S}
theorem lift (hg : SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (D n : Expr S) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ)
      (Expr.compSub (Expr.liftSub σ) (Expr.consSub n ξ)) := by
  rw [Expr.lift_comp_cons]
  intro i A hi hne hH
  cases hi with
  | zero => exact False.elim (hne (.var 0))
  | succ D hi =>
      have hne' : ¬ Neutral (σ _) := fun h => hne (h.rename Nat.succ)
      simpa only [Expr.raise_subst_cons] using hg _ _ hi hne' (by
        simpa only [Expr.raise_subst_cons] using hH)
end SubstitutionGuard

/-- The goodness assumptions on the values that a stored substitution grafts at the declarations. -/
def GoodReplacement {Γ Δ : List (Expr S)} {σ : Nat → Expr S}
    (ts : TypingTreeBE.StoredSubstitution P Γ Δ σ) (ξ : Nat → Expr S) : Prop :=
  ∀ i A (hi : Lookup Γ i A), ActiveLayer P C (Ω.kprofile (A.subst (Expr.compSub σ ξ))) →
    ValGood Ω C (ts i A hi) ξ

 theorem goodReplacement_lift {Γ Δ : List (Expr S)} {σ ξ : Nat → Expr S}
    (ts : TypingTreeBE.StoredSubstitution P Γ Δ σ) (hg : GoodReplacement Ω C ts ξ)
    {D : Expr S} {s : S} (hD : HasTypeBE P Δ (D.subst σ) (.sort s)) (n : Expr S) :
    GoodReplacement Ω C (ts.lift hD) (Expr.consSub n ξ) := by
  intro i A hi ha
  cases i with
  | zero =>
      have he : A = D.rename Nat.succ := by cases hi; rfl
      subst A
      exact True.intro
  | succ i =>
      let hex : ∃ A', Lookup Γ i A' ∧ A = A'.rename Nat.succ := by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he := hex.choose_spec.2
      have hgood := hg i hex.choose hex.choose_spec.1
      have hh : ActiveLayer P C (Ω.kprofile (hex.choose.subst (Expr.compSub σ ξ))) := by
        rw [Expr.lift_comp_cons,he,Expr.raise_subst_cons] at ha
        exact ha
      have hr := congrArg Prod.fst (goodness_rename Ω C (ts i hex.choose hex.choose_spec.1)
        (.cons hD.valid hD) Nat.succ (TypingTreeBE.DeclRenaming.weaken _) (Expr.consSub n ξ))
      have hgr : ValGood Ω C ((ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TypingTreeBE.DeclRenaming.weaken _)) (Expr.consSub n ξ) := by
        rw [show ValGood Ω C _ _ = _ from hr]
        exact hgood hh
      let tt := (ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
        Nat.succ (TypingTreeBE.DeclRenaming.weaken _)
      have he' : A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) he
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]; rfl
      exact (valGood_retarget Ω C tt (he'.symm ▸ tt.typing)
        (by rw [he']; exact .refl _) (Expr.consSub n ξ)).mpr hgr

 theorem neutral_readGood {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTreeBE P Γ M (.sort s)) (hne : Neutral M) (ξ : Nat → Expr S)
    (hs : ({s} : Set S) ∈ C) (ha : ¬ ActiveLayer P C (AxProfile P s)) : ReadGood Ω C t ξ := by
  have hbase (v : Prop) : baseGood Ω C M (.sort s) ξ v := by
    intro _
    refine ⟨s,rfl,hs,?_,fun _ => hne⟩
    intro hh
    exact False.elim (ha (by simpa only [Expr.subst,Ω.kprofile_sort] using hh))
  cases t with
  | var ht hd hc => exact hbase True
  | sort ht hax hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hbase _
end KP.ObservationValues
end PureTypeSystem

namespace PureTypeSystem.KP.ObservationValues

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T U : Expr S}

 theorem sort_val_retarget {s t : S} (h : HasTypeBE P Γ (.sort s) T)
    (h' : HasTypeBE P Γ (.sort s) U) (ht : P.axioms s t) (hc : ConvertsBE T (.sort t))
    (hc' : ConvertsBE U (.sort t)) (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).knf = (U.subst e.images).knf)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((sort h ht hc e).val ha).val = ((sort h' ht hc' e).val hb).val :=
  distinguished_congr Ω C hno he

 theorem lookup_val_retarget {n : Nat} {A : Expr S} (h : HasTypeBE P Γ (.var n) T)
    (h' : HasTypeBE P Γ (.var n) U) (hd : Lookup Γ n A) (hc : ConvertsBE T A)
    (hc' : ConvertsBE U A) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((lookup h hd hc e).val ha).val = ((lookup h' hd hc' e).val hb).val := by
  apply Option.some.inj
  rw [← parameter_eq _ ha,← parameter_eq _ hb,lookup_parameter,lookup_parameter,
    e.type_convert_eq h h' (.trans _ _ _ hc (.symm _ _ hc'))]

 theorem abstractionAction_retarget {D m E : Expr S} {s : S}
    (h : HasTypeBE P Γ (.lam D m) T) (h' : HasTypeBE P Γ (.lam D m) U)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (hc' : ConvertsBE U (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).knf = (U.subst e.images).knf)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf))
    (a : FrameKey Ω C (e.activeType h ha)) (b : FrameKey Ω C (e.activeType h' hb))
    (hab : a.argument = b.argument) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpa : PayloadFits Ω C hno a.domain p) (hpb : PayloadFits Ω C hno b.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp hc' eb e hb b p hpb).val := by
  have hA : (e.activeType h ha).type = (ProductInstance.ofFormation hp e).domainNF.pi
      (ProductInstance.ofFormation hp e).bodyNF :=
    PreResult.abstraction_type h hp hc e
  have hB : (e.activeType h' hb).type = (ProductInstance.ofFormation hp e).domainNF.pi
      (ProductInstance.ofFormation hp e).bodyNF :=
    he.symm.trans hA
  have hee : (ProductInstance.ofFormation hp e).frameEnvironment hA a p hpa =
      (ProductInstance.ofFormation hp e).frameEnvironment hB b p hpb := by
    dsimp only [ProductInstance.frameEnvironment,ProductInstance.extend,Environment.cons,
      ProductInstance.frameArgument]
    congr 1
    funext n
    cases n <;> simp only [hab]
  dsimp only [abstractionAction]
  apply val_congr
  exact congrArg (fun ee : Environment (hw := hw) Ω C hno (D :: Γ) => (eb ee).parameter) hee

 theorem abstraction_val_retarget {D m E : Expr S} {s : S}
    (h : HasTypeBE P Γ (.lam D m) T) (h' : HasTypeBE P Γ (.lam D m) U)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (hc' : ConvertsBE U (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).knf = (U.subst e.images).knf)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((abstraction h hp hc eb e).val ha).val = ((abstraction h' hp hc' eb e).val hb).val := by
  apply lambdaValue_congr Ω C hno he
  exact abstractionAction_retarget h h' hp hc hc' eb e he ha hb

 theorem product_val_retarget {D E : Expr S} {a b c : S}
    (h : HasTypeBE P Γ (.pi D E) T) (h' : HasTypeBE P Γ (.pi D E) U)
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (hc : ConvertsBE T (.sort c)) (hc' : ConvertsBE U (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).knf = (U.subst e.images).knf)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hu : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((product h hd hb hr hc ed eb e).val ha).val = ((product h' hd hb hr hc' ed eb e).val hu).val := by
  dsimp only [product]
  split
  · exact withBase_congr Ω C hno he _ _ rfl
  · exact distinguished_congr Ω C hno he

 theorem application_val_retarget {f n D E : Expr S}
    (h : HasTypeBE P Γ (.app f n) T) (h' : HasTypeBE P Γ (.app f n) U)
    (hf : HasTypeBE P Γ f (.pi D E)) (hn : HasTypeBE P Γ n D)
    (hc : ConvertsBE T (E.instantiate n)) (hc' : ConvertsBE U (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).knf = (U.subst e.images).knf)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hu : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((application h hf hn hc ef en e).val ha).val = ((application h' hf hn hc' ef en e).val hu).val := by
  dsimp only [application,baseResult,applicationValue]
  split
  · rfl
  · exact canonDistinguished_congr Ω C hno he
end PreResult

 theorem preEvaluate_retarget_val {Γ : List (Expr S)} {M T U : Expr S} (t : TypingTreeBE P Γ M T)
    (h : HasTypeBE P Γ M U) (hc : ConvertsBE U T) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hb : ActiveLayer P C (Ω.kprofile (U.subst e.images).knf)) :
    ((preEvaluate Ω C hno t e).val ha).val =
      ((preEvaluate Ω C hno (t.retarget h hc) e).val hb).val := by
  have he := e.type_convert_eq t.typing h (.symm _ _ hc)
  cases t with
  | var ht hd ht' => exact PreResult.lookup_val_retarget ht h hd ht' (.trans _ _ _ hc ht') e ha hb
  | sort ht ht' htc => exact PreResult.sort_val_retarget ht h ht' htc (.trans _ _ _ hc htc) e he ha hb
  | product ht d b hr htc => exact PreResult.product_val_retarget ht h d.typing b.typing hr htc (.trans _ _ _ hc htc) _ _ e he ha hb
  | abstraction ht d b hp htc => exact PreResult.abstraction_val_retarget ht h hp htc (.trans _ _ _ hc htc) _ e he ha hb
  | application ht f n htc => exact PreResult.application_val_retarget ht h f.typing n.typing htc (.trans _ _ _ hc htc) _ _ e he ha hb

 theorem preEvaluate_retarget_parameter {Γ : List (Expr S)} {M T U : Expr S}
    (t : TypingTreeBE P Γ M T) (h : HasTypeBE P Γ M U) (hc : ConvertsBE U T)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.retarget h hc) e).parameter := by
  apply PreResult.parameter_congr _ _ (e.type_convert_eq t.typing h (.symm _ _ hc))
  exact preEvaluate_retarget_val Ω C hno t h hc e

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)} {σ : Nat → Expr S}
structure Assigned (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) (ts : TypingTreeBE.StoredSubstitution P Γ Δ σ) : Prop where
  images : e.images = Expr.compSub σ f.images
  parameters : ∀ i A (hi : Lookup Γ i A),
    canonOpt hno (A.subst e.images).knf (e.parameters i) = (preEvaluate Ω C hno (ts i A hi) f).parameter

namespace Assigned
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable {ts : TypingTreeBE.StoredSubstitution P Γ Δ σ} (he : e.Assigned f ts)
include he
 theorem raw_eq (M : Expr S) : M.subst e.images = (M.subst σ).subst f.images := by
  rw [he.images,Expr.subst_compSub]
 theorem normal_eq (M : Expr S) :
    (M.subst e.images).knf = ((M.subst σ).subst f.images).knf :=
  congrArg Expr.knf (he.raw_eq M)

 theorem cons {D : Expr S} {s : S} (hD : HasTypeBE P Δ (D.subst σ) (.sort s))
    (n : Expr S) (hn : Ω.THasTypeBE n (D.subst e.images)) (hn' : Ω.THasTypeBE n ((D.subst σ).subst f.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (D.subst e.images).knf p)
    (hp' : PayloadFits Ω C hno ((D.subst σ).subst f.images).knf p) :
    (e.cons hn p hp).Assigned (f.cons hn' p hp') (ts.lift hD) := by
  have himg : (e.cons hn p hp).images = Expr.compSub (Expr.liftSub σ) (f.cons hn' p hp').images := by
    change Expr.consSub n e.images = Expr.compSub (Expr.liftSub σ) (Expr.consSub n f.images)
    rw [Expr.lift_comp_cons,he.images]
  constructor
  · exact himg
  · intro i A hi
    cases i with
    | zero =>
        have heA : A = D.rename Nat.succ := by cases hi; rfl
        have he' : A.subst (Expr.liftSub σ) = (D.subst σ).rename Nat.succ := by
          rw [heA,Expr.subst_rename,Expr.rename_subst]; rfl
        refine Eq.trans ?_ (PreResult.lookup_parameter (he'.symm ▸ HasTypeBE.var hD) (.zero _ _)
          (by rw [he']; exact .refl _) (f.cons hn' p hp')).symm
        rw [himg, ← Expr.subst_compSub]
        rfl
    | succ i =>
        let hex : ∃ A', Lookup Γ i A' ∧ A = A'.rename Nat.succ := by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        let tt := (ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TypingTreeBE.DeclRenaming.weaken _)
        have he' : A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
          calc
            A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
              congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
            _ = (hex.choose.subst σ).rename Nat.succ := by
              rw [Expr.subst_rename,Expr.rename_subst]; rfl
        have hr := (preEvaluate_rename Ω C hno (ts i hex.choose hex.choose_spec.1)
          (.cons hD.valid hD) Nat.succ (TypingTreeBE.DeclRenaming.weaken _) f (f.cons hn' p hp')
          (fun _ _ => ⟨rfl,rfl⟩)).1
        refine Eq.trans ?_ ((he.parameters i hex.choose hex.choose_spec.1).trans
          (hr.trans (preEvaluate_retarget_parameter Ω C hno tt (he'.symm ▸ tt.typing)
            (by rw [he']; exact .refl _) (f.cons hn' p hp'))))
        have hA : A.subst (e.cons hn p hp).images = hex.choose.subst e.images := by
          have h2 := hex.choose_spec.2
          calc A.subst (e.cons hn p hp).images
              = (hex.choose.rename Nat.succ).subst (Expr.consSub n e.images) := by rw [← h2]; rfl
            _ = hex.choose.subst e.images := Expr.raise_subst_cons _ _ _
        rw [hA]
        rfl
end Assigned
end Environment

 theorem preEvaluate_read_outside {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTreeBE P Γ M T) (e : Environment (hw := hw) Ω C hno Γ)
    (hm : Ω.kprofile (M.subst e.images).knf ∉ C) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).knf := by
  cases t with
  | var ht hd hc => exact by simp only [preEvaluate,PreResult.lookup,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]
  | sort ht ha hc => rfl
  | product ht d b hr hc => exact by simp only [preEvaluate,PreResult.product,ite_eq_right hm]
  | abstraction ht d b hp hc => exact by simp only [preEvaluate,PreResult.abstraction,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]
  | application ht f a hc => exact by simp only [preEvaluate,PreResult.application,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]

 theorem preEvaluate_neutral_read_inactive {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTreeBE P Γ M (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hne : Neutral M) (ha : ¬ ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).knf := by
  have hb (v : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf) →
      Value (hw := hw) Ω C hno (Expr.sort s |>.subst e.images).knf) :
      (PreResult.baseRead t.typing v).val = Candidates.Top Ω (M.subst e.images).knf := by
    simp only [PreResult.baseRead,dite_eq_right ha]
    split <;> try rfl
    split <;> rfl
  cases t with
  | var ht hd hc => exact hb _
  | sort ht ha hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hb _
end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) (C : Set (Set S))

 theorem readGood_outside {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    (ξ : Nat → Expr S) (hm : Ω.kprofile (M.subst ξ) ∉ C) : ReadGood Ω C t ξ := by
  cases t with
  | var ht hd hc => exact fun h => False.elim (hm h)
  | sort ht ha hc => trivial
  | product ht d b hr hc => exact fun h => False.elim (hm h)
  | abstraction ht d b hp hc => exact fun h => False.elim (hm h)
  | application ht f a hc => exact fun h => False.elim (hm h)

abbrev ProductGood {Γ : List (Expr S)} {D E : Expr S} {a b : S}
    (d : TypingTreeBE P Γ D (.sort a)) (e : TypingTreeBE P (D :: Γ) E (.sort b)) (ξ : Nat → Expr S) : Prop :=
  (Ω.kprofile (D.subst ξ) ∈ C → ReadGood Ω C d ξ) ∧
    ∀ n, Ω.THasTypeBE n (D.subst ξ) → Ω.kprofile (E.subst (Expr.consSub n ξ)) ∈ C →
      ReadGood Ω C e (Expr.consSub n ξ)

 theorem goodness_subst (hw : SystemENormalizing' P)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S)
    (ts : TypingTreeBE.StoredSubstitution P Γ Δ σ) (ξ : Nat → Expr S)
    (hξ : Ω.TTypedSubstitutionBE Δ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (hg : GoodReplacement Ω C ts ξ) :
    (ActiveLayer P C (Ω.kprofile (T.subst (Expr.compSub σ ξ))) →
      ValGood Ω C t (Expr.compSub σ ξ) → ValGood Ω C (t.subst hΔ σ ts) ξ) ∧
    (ReadGood Ω C t (Expr.compSub σ ξ) → ReadGood Ω C (t.subst hΔ σ ts) ξ) := by
  induction t generalizing Δ σ ξ with
  | @var Γ i A T ht hd hc =>
      have hcomp := hξ.comp ts.typed
      have hprof := Ω.kprofile_converts ((ContextTowerBE.THasTypeBE.subst ht hcomp).type_kwn hw)
        ((ContextTowerBE.THasTypeBE.subst (HasTypeBE.lookup ht.valid hd) hcomp).type_kwn hw)
        (hc.subst (Expr.compSub σ ξ)).k
      have hv : ActiveLayer P C (Ω.kprofile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C ((TypingTreeBE.var ht hd hc).subst hΔ σ ts) ξ := by
        intro ha
        change ValGood Ω C ((ts i A hd).retarget (ht.subst hΔ σ ts.typed) (hc.subst σ)) ξ
        exact (valGood_retarget Ω C _ _ _ _).mpr (hg i A hd (hprof ▸ ha))
      refine ⟨fun ha _ => hv ha,?_⟩
      intro hr
      by_cases hm : Ω.kprofile ((Expr.var i).subst (Expr.compSub σ ξ)) ∈ C
      · obtain ⟨s,he,hs,_,_⟩ := hr hm
        subst T
        by_cases ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst (Expr.compSub σ ξ)))
        · exact (readGood_active_iff Ω C ((TypingTreeBE.var ht hd hc).subst hΔ σ ts)
            (by exact hm) hs (by exact ha)).mpr (hv ha)
        · apply neutral_readGood Ω C _ _ ξ hs (by simpa only [Expr.subst,Ω.kprofile_sort] using ha)
          exact skipped_read_subst Ω C hw ht (.var i) hcomp hguard hs
            (by simpa only [Expr.subst,Ω.kprofile_sort] using ha)
      · exact readGood_outside Ω C _ ξ hm
  | sort ht ha hc => exact ⟨fun _ _ => trivial,fun _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      let bs := b.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
      have hbody : ValGood Ω C (.abstraction ht d b hp hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TypingTreeBE.abstraction ht d b hp hc).subst hΔ σ ts) ξ := by
        intro hb n hn ha
        have hn' : Ω.THasTypeBE n (D.subst (Expr.compSub σ ξ)) := by simpa only [Expr.subst_compSub] using hn
        have hi := (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
          (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).1
        apply hi
        · simpa only [Expr.subst_compSub] using ha
        · rw [Expr.lift_comp_cons]
          exact hb n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using ha)
      refine ⟨fun _ => hbody,?_⟩
      intro hr hm
      have hm' : Ω.kprofile (Expr.lam D m |>.subst (Expr.compSub σ ξ)) ∈ C := by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s',he,hs,hv,hn⟩ := hr hm'
      subst T
      exact False.elim ht.lambda_cannot_have_sort_type
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hcomp := hξ.comp ts.typed
      have hv : ActiveLayer P C (Ω.kprofile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C (.application ht ft nt hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TypingTreeBE.application ht ft nt hc).subst hΔ σ ts) ξ := by
        intro ha hg'
        change (if ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst (Expr.compSub σ ξ))) then
          ValGood Ω C ft (Expr.compSub σ ξ) ∧
            (ActiveLayer P C (Ω.kprofile (D.subst (Expr.compSub σ ξ))) → ValGood Ω C nt (Expr.compSub σ ξ))
          else Neutral (.app f n)) at hg'
        change (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E |>.subst σ).subst ξ)) then
          ValGood Ω C (ft.subst hΔ σ ts) ξ ∧
            (ActiveLayer P C (Ω.kprofile ((D.subst σ).subst ξ)) → ValGood Ω C (nt.subst hΔ σ ts) ξ)
          else Neutral ((Expr.app f n).subst σ))
        simp only [Expr.subst_compSub]
        split <;> rename_i hF
        · rw [ite_eq_left hF] at hg'
          exact ⟨(ihf hΔ σ ts ξ hξ hguard hg).1 hF hg'.1,
            fun hA => (ihn hΔ σ ts ξ hξ hguard hg).1 hA (hg'.2 hA)⟩
        · rw [ite_eq_right hF] at hg'
          exact skipped_application_subst Ω C hw ht ft.typing nt.typing hc hg' hcomp hguard ha hF
      refine ⟨hv,?_⟩
      intro hr hm
      have hm' : Ω.kprofile (Expr.app f n |>.subst (Expr.compSub σ ξ)) ∈ C := by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s,he,hs,hval,hne⟩ := hr hm'
      subst T
      refine ⟨s,rfl,hs,?_,?_⟩
      · intro ha
        apply hv (by exact ha)
        exact hval (by exact ha)
      · intro ha
        have hax : ¬ ActiveLayer P C (AxProfile P s) := by simpa only [Expr.subst,Ω.kprofile_sort] using ha
        exact skipped_read_subst Ω C hw ht (hne (by exact ha)) hcomp hguard hs hax
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hpg : ProductGood Ω C d bt (Expr.compSub σ ξ) →
          ProductGood Ω C (d.subst hΔ σ ts) (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)) ξ := by
        intro hh
        constructor
        · intro hm
          exact (ihd hΔ σ ts ξ hξ hguard hg).2 (hh.1 (by simpa only [Expr.subst_compSub] using hm))
        · intro n hn hm
          have hn' : Ω.THasTypeBE n (D.subst (Expr.compSub σ ξ)) := by simpa only [Expr.subst_compSub] using hn
          apply (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
            (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).2
          rw [Expr.lift_comp_cons]
          exact hh.2 n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using hm)
      constructor
      · intro _ hv hgate
        apply hpg
        apply hv
        change ({c} : Set S) ∈ C ∧ Ω.kprofile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hgate
        simpa only [Expr.subst_compSub] using hgate
      · intro hr' hm
        apply hpg
        apply hr'
        change Ω.kprofile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hm
        simpa only [Expr.subst_compSub] using hm

end

universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

 theorem baseRead_substitution {Γ Δ : List (Expr S)} {M T : Expr S} {σ : Nat → Expr S}
    (ht : HasTypeBE P Γ M T) (t' : TypingTreeBE P Δ (M.subst σ) (T.subst σ))
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.images = Expr.compSub σ f.images)
    (hg : SubstitutionGuard Ω C Γ σ e.images)
    (v : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
      Value (hw := hw) Ω C hno (T.subst e.images).knf) (G : Prop)
    (hr : baseGood Ω C M T e.images G)
    (hv : ∀ ha hb, G → (v ha).val = ((preEvaluate Ω C hno t' f).val hb).val) :
    (PreResult.baseRead ht v).val = (preEvaluate Ω C hno t' f).read.val := by
  have hM : (M.subst e.images).knf = ((M.subst σ).subst f.images).knf := by
    rw [he,Expr.subst_compSub]
  by_cases hm : Ω.kprofile (M.subst e.images).knf ∈ C
  · have hm' : Ω.kprofile ((M.subst σ).subst f.images).knf ∈ C := hM ▸ hm
    obtain ⟨s,hs,hsC,hval,hne⟩ := hr (by simpa only [Ω.kprofile_knf] using hm)
    subst T
    by_cases ha : ActiveLayer P C (Ω.kprofile (Expr.sort s |>.subst e.images).knf)
    · refine Eq.trans (PreResult.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEvaluate_read_base Ω C hno t' f hm' hsC ha).symm)
      have hX : e.actualExpression ht = f.actualExpression t'.typing := Subtype.ext hM
      rw [hv ha ha (hval (by simpa only [Ω.kprofile_knf] using ha))]
      exact congrArg (fun X : ActualType Ω =>
        ((RawValue.base Ω C hno ((preEvaluate Ω C hno t' f).val ha).val) X).val) hX
    · have hnew := skipped_read_subst Ω C hw ht
        (hne (by simpa only [Ω.kprofile_knf] using ha)) e.typed hg hsC
        (by simpa only [Expr.subst,Ω.kprofile_knf,Ω.kprofile_sort] using ha)
      refine Eq.trans ?_ (preEvaluate_neutral_read_inactive Ω C hno t' f hnew ha).symm
      have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hsC⟩
      simp only [PreResult.baseRead,dite_eq_left hm,dite_eq_left hex,dite_eq_right ha]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.kprofile ((M.subst σ).subst f.images).knf ∉ C := hM ▸ hm
    rw [preEvaluate_read_outside Ω C hno t' f hm']
    simp only [PreResult.baseRead,dite_eq_right hm]
    exact congrArg (Candidates.Top Ω) hM

 theorem preEvaluate_subst {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S)
    (ts : TypingTreeBE.StoredSubstitution P Γ Δ σ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.Assigned f ts) (hg : SubstitutionGuard Ω C Γ σ e.images) :
    (∀ ha hb, ValGood Ω C t e.images →
      ((preEvaluate Ω C hno t e).val ha).val =
        ((preEvaluate Ω C hno (t.subst hΔ σ ts) f).val hb).val) ∧
    (ReadGood Ω C t e.images →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.subst hΔ σ ts) f).read.val) := by
  induction t generalizing Δ σ with
  | @var Γ i A T ht hd hc =>
      have hp : (preEvaluate Ω C hno (.var ht hd hc) e).parameter =
          (preEvaluate Ω C hno ((TypingTreeBE.var ht hd hc).subst hΔ σ ts) f).parameter := by
        exact (PreResult.lookup_parameter ht hd hc e).trans
          ((congrArg (fun X => canonOpt hno X (e.parameters i))
            (e.type_convert_eq ht (HasTypeBE.lookup ht.valid hd) hc)).trans
          ((he.parameters i A hd).trans (preEvaluate_retarget_parameter Ω C hno
            (ts i A hd) (ht.subst hΔ σ ts.typed) (hc.subst σ) f)))
      have hv : ∀ ha hb, ValGood Ω C (.var ht hd hc) e.images →
          ((preEvaluate Ω C hno (.var ht hd hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTreeBE.var ht hd hc).subst hΔ σ ts) f).val hb).val :=
        fun ha hb _ => PreResult.val_congr _ _ hp ha hb
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | sort ht ha hc =>
      exact ⟨fun _ _ _ => distinguished_congr Ω C hno (he.normal_eq _),
        fun _ => congrArg (Candidates.Top Ω) (he.normal_eq _)⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hv : ∀ ha hb, ValGood Ω C (.abstraction ht d b hp hc) e.images →
          ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTreeBE.abstraction ht d b hp hc).subst hΔ σ ts) f).val hb).val := by
        intro ha hb hgood
        apply PreResult.abstraction_val_congr ht (ht.subst hΔ σ ts.typed) hp
          (hp.subst hΔ σ ts.typed) hc (hc.subst σ) _ _ e f (he.normal_eq _)
        intro n n' hn hn' hnn p hp hp' ha' hb'
        subst n'
        have hae := he.cons hD n hn hn' p hp hp'
        have hgu : SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images := by
          rw [hae.images]
          apply SubstitutionGuard.lift
          rwa [← he.images]
        exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
          (e.cons hn p hp) (f.cons hn' p hp') hae hgu).1 ha' hb'
          (hgood n hn (by
            change ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n e.images)).knf) at ha'
            simpa only [Ω.kprofile_knf] using ha'))
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @application Γ g n D E T ht gt nt hc ihg ihn =>
      have hv : ∀ ha hb, ValGood Ω C (.application ht gt nt hc) e.images →
          ((preEvaluate Ω C hno (.application ht gt nt hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTreeBE.application ht gt nt hc).subst hΔ σ ts) f).val hb).val := by
        intro ha hb hgood
        by_cases hF : ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images))
        · change (if ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images)) then
            ValGood Ω C gt e.images ∧ (ActiveLayer P C (Ω.kprofile (D.subst e.images)) → ValGood Ω C nt e.images)
            else Neutral (.app g n)) at hgood
          rw [ite_eq_left hF] at hgood
          apply PreResult.application_val_congr ht (ht.subst hΔ σ ts.typed) gt.typing
            (gt.typing.subst hΔ σ ts.typed) nt.typing (nt.typing.subst hΔ σ ts.typed)
            hc _ _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) (he.normal_eq _)
          · exact fun hA hB => (ihg hΔ σ ts e f he hg).1 hA hB hgood.1
          · apply PreResult.parameter_congr _ _ (he.normal_eq _)
            intro hA hB
            exact (ihn hΔ σ ts e f he hg).1 hA hB (hgood.2 (by simpa only [Ω.kprofile_knf] using hA))
        · have hF' : ¬ ActiveLayer P C (Ω.kprofile (((Expr.pi D E).subst σ).subst f.images).knf) := by
            rw [← he.normal_eq _ ,Ω.kprofile_knf]
            exact hF
          have hF0 : ¬ ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images).knf) := by
            simpa only [Ω.kprofile_knf] using hF
          change ((PreResult.application ht gt.typing nt.typing hc _ _ e).val ha).val =
            ((PreResult.application (ht.subst hΔ σ ts.typed) (gt.typing.subst hΔ σ ts.typed)
              (nt.typing.subst hΔ σ ts.typed) _ _ _ f).val hb).val
          change ¬ ActiveLayer P C (Ω.kprofile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).knf) at hF'
          simp only [PreResult.application,PreResult.baseResult,PreResult.applicationValue,dite_eq_right hF0,dite_eq_right hF']
          exact canonDistinguished_congr Ω C hno (he.normal_eq T)
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hB := bt.typing.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD).typed
      have hpc : ProductGood Ω C d bt e.images →
          (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno bt) e).val =
          (PreResult.productCandidate hD hB hr (preEvaluate Ω C hno (d.subst hΔ σ ts))
            (preEvaluate Ω C hno (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD))) f).val := by
        intro hgood
        have hDE := Expr.pi.inj (he.raw_eq (.pi D E))
        apply PreResult.productCandidate_congr d.typing bt.typing hr hD hB hr _ _ _ _ e f
          (congrArg Expr.knf hDE.1) (congrArg Expr.knf hDE.2)
        · intro hm
          exact (ihd hΔ σ ts e f he hg).2 (hgood.1 (by simpa only [Ω.kprofile_knf] using hm))
        · intro n hn hn' p hp hp' hm
          have hae := he.cons hD n hn hn' p hp hp'
          have hgu : SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images := by
            rw [hae.images]
            apply SubstitutionGuard.lift
            rwa [← he.images]
          exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
            (e.cons hn p hp) (f.cons hn' p hp') hae hgu).2
            (hgood.2 n hn (by
              change Ω.kprofile (E.subst (Expr.consSub n e.images)).knf ∈ C at hm
              simpa only [Ω.kprofile_knf] using hm))
      constructor
      · intro ha hb hv
        by_cases hs : ({c} : Set S) ∈ C
        · apply PreResult.product_val_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
            hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) Iff.rfl
          intro hm
          exact hpc (hv ⟨hs,by simpa only [Ω.kprofile_knf] using hm⟩)
        · have hgate : ¬ (({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C) := fun h => hs h.1
          have hgate' : ¬ (({c} : Set S) ∈ C ∧ Ω.kprofile (((Expr.pi D E).subst σ).subst f.images).knf ∈ C) := fun h => hs h.1
          change ((PreResult.product ht d.typing bt.typing hr hc _ _ e).val ha).val =
            ((PreResult.product (ht.subst hΔ σ ts.typed) hD hB hr (hc.subst σ) _ _ f).val hb).val
          change ¬ (({c} : Set S) ∈ C ∧ Ω.kprofile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).knf ∈ C) at hgate'
          simp only [PreResult.product,dite_eq_right hgate,dite_eq_right hgate']
          exact distinguished_congr Ω C hno (he.normal_eq T)
      · intro hgood
        apply PreResult.product_read_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
          hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _)
        intro hm
        exact hpc (hgood (by simpa only [Ω.kprofile_knf] using hm))
end PureTypeSystem.KP.ObservationValues

namespace PureTypeSystem
universe u
namespace KP.ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

omit [Fintype S] in
 theorem goodness_recontext {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    {Δ : List (Expr S)} (h : ContextEquivalentBE P Γ Δ) (ξ : Nat → Expr S) :
    goodness Ω C (t.recontext h) ξ = goodness Ω C t ξ := by
  induction t generalizing Δ ξ with
  | var ht hd hc => rfl
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv : (∀ n, Ω.THasTypeBE n (D.subst ξ) → ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).1) =
        (∀ n, Ω.THasTypeBE n (D.subst ξ) → ActiveLayer P C (Ω.kprofile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C b (Expr.consSub n ξ)).1) := by simp only [ihb]
      exact congrArg (fun G => (G,baseGood Ω C (.lam D m) T ξ G)) hv
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hv : (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C (ft.recontext h) ξ).1 ∧
            (ActiveLayer P C (Ω.kprofile (D.subst ξ)) → (goodness Ω C (nt.recontext h) ξ).1)
          else Neutral (.app f n)) =
        (if ActiveLayer P C (Ω.kprofile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C ft ξ).1 ∧
            (ActiveLayer P C (Ω.kprofile (D.subst ξ)) → (goodness Ω C nt ξ).1)
          else Neutral (.app f n)) := by simp only [ihf,ihn]
      exact congrArg (fun G => (G,baseGood Ω C (.app f n) T ξ G)) hv
  | @product Γ D E a b c T ht d b hr hc ihd ihb =>
      have hg : ((Ω.kprofile (D.subst ξ) ∈ C → (goodness Ω C (d.recontext h) ξ).2) ∧
          ∀ n, Ω.THasTypeBE n (D.subst ξ) → Ω.kprofile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).2) =
        ((Ω.kprofile (D.subst ξ) ∈ C → (goodness Ω C d ξ).2) ∧
          ∀ n, Ω.THasTypeBE n (D.subst ξ) → Ω.kprofile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C b (Expr.consSub n ξ)).2) := by simp only [ihd,ihb]
      exact congrArg (fun G => ((({c} : Set S) ∈ C ∧ Ω.kprofile ((Expr.pi D E).subst ξ) ∈ C → G),
        (Ω.kprofile ((Expr.pi D E).subst ξ) ∈ C → G))) hg

omit [Fintype S] in
 theorem single_guard {Γ : List (Expr S)} {n D : Expr S} (ξ : Nat → Expr S)
    (ha : Ω.kprofile (D.subst ξ) ∈ ObservationLayers P C → ActiveLayer P C (Ω.kprofile (D.subst ξ))) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.single n) (Expr.consSub (n.subst ξ) ξ) := by
  intro i A hi hne hH
  cases hi with
  | zero => simpa only [Expr.raise_subst_cons] using ha (by simpa only [Expr.raise_subst_cons] using hH)
  | succ D hi => exact False.elim (hne (.var _))

omit [Fintype S] in
 theorem single_goodReplacement {Γ : List (Expr S)} {n D : Expr S}
    (t : TypingTreeBE P Γ n D) (ξ : Nat → Expr S)
    (hg : ActiveLayer P C (Ω.kprofile (D.subst ξ)) → ValGood Ω C t ξ) :
    GoodReplacement Ω C (TypingTreeBE.StoredSubstitution.single t) ξ := by
  intro i A hi ha
  cases i with
  | zero =>
      have he : A = D.rename Nat.succ := by cases hi; rfl
      have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
      exact (valGood_retarget Ω C t (he'.symm ▸ t.typing) (by rw [he']; exact .refl _) ξ).mpr (hg (by
        simpa only [Expr.comp_single,he,Expr.raise_subst_cons] using ha))
  | succ i => exact True.intro

 theorem single_assigned (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {n D : Expr S} (t : TypingTreeBE P Γ n D)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (e.cons (ContextTowerBE.THasTypeBE.subst t.typing e.typed) (preEvaluate Ω C hno t e).parameter
      (preEvaluate Ω C hno t e).parameter_fits).Assigned e (TypingTreeBE.StoredSubstitution.single t) := by
  have himg : (e.cons (ContextTowerBE.THasTypeBE.subst t.typing e.typed) (preEvaluate Ω C hno t e).parameter
      (preEvaluate Ω C hno t e).parameter_fits).images = Expr.compSub (Expr.single n) e.images :=
    (Expr.comp_single n e.images).symm
  constructor
  · exact himg
  · intro i A hi
    rw [himg, ← Expr.subst_compSub]
    cases i with
    | zero =>
        have he : A = D.rename Nat.succ := by cases hi; rfl
        have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
        refine Eq.trans ?_ (preEvaluate_retarget_parameter Ω C hno t (he'.symm ▸ t.typing)
          (by rw [he']; exact .refl _) e)
        rw [he']
        exact preEvaluate_parameter_canonical Ω C hno hC t e
    | succ i =>
        let hex : ∃ B, Lookup Γ i B ∧ A = B.rename Nat.succ := by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        have he : A.subst (Expr.single n) = hex.choose := by
          exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
            (Expr.subst_lift_single hex.choose n)
        exact (PreResult.lookup_parameter (he.symm ▸ HasTypeBE.lookup t.typing.valid hex.choose_spec.1)
          hex.choose_spec.1 (by rw [he]; exact .refl _) e).symm
end KP.ObservationValues
end PureTypeSystem

