/- Adapted to typing with βη-conversion from OpenAI's `ObservationCandidates.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.ObservationReduction

@[expose] public section

/-!
# The interface for case 3 with typing with βη-conversion

This file adapts OpenAI's `ObservationCandidates.lean` (`PTSBetaEta.Beta.ObservationCandidates`) to typing with βη-conversion.
A plain type is read through the typing tree of its chosen erasure-normal reduct `rnf`.
The lemma `normalRead_eq` shows that the `read` is the same for every convertible erasure-normal tree, using `enormal_tree_independence`.
OpenAI obtained this fact from uniqueness of normal forms.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem.KP.ObservationValues

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

/-- Replacing a type by its chosen erasure-normal reduct before a typed substitution does not change the key of the result. -/
theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    (A.rnf.subst e.images).knf = (A.subst e.images).knf := by
  have hr := (HasTypeBE.rnf_spec hw hA).1
  have hA' := hA.subject_reduces hr
  exact Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hA' e.typed).kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hA e.typed).kwn hw) (.symm _ _ (ConvertsBE.subst (reduces_convertsBE hr) e.images).k)

omit [Fintype S] in
/-- The stored typing tree of the chosen erasure-normal reduct. -/
noncomputable def rnfTree {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) : TypingTreeBE P Γ A.rnf (.sort s) :=
  TypingTreeBE.ofTyping (hA.subject_reduces (HasTypeBE.rnf_spec hE.out hA).1)

noncomputable def normalRead {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidate Ω (A.subst e.images).knf :=
  ⟨(preEvaluate Ω C hno (rnfTree hA) e).read.val,
    normal_subst_eq Ω C hno hA e ▸ (preEvaluate Ω C hno (rnfTree hA) e).read.property⟩

/-- The `read` agrees with that of any erasure-normal tree with the same erasure. -/
theorem normalRead_eq_erase {Γ : List (Expr S)} {A A' : Expr S} {s r : S}
    (hA : HasTypeBE P Γ A (.sort s)) (t : TypingTreeBE P Γ A' (.sort r)) (hA' : ENormal dz A')
    (herase : A.rnf.erase dz = A'.erase dz) (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val := by
  have hr := HasTypeBE.rnf_spec hE.out hA
  have hctx : ContextEquivalentBE P Γ Γ := ⟨hA.valid, hA.valid, fun _ _ => Iff.rfl⟩
  exact (enormal_tree_independence Ω C hno (rnfTree hA) hr.2 t hA' herase hctx e e
    (Environment.SameData.of_eq rfl rfl)).2 s r rfl rfl

/-- The `read` agrees with that of any convertible erasure-normal tree. -/
theorem normalRead_eq (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A A' : Expr S} {s r : S}
    (hA : HasTypeBE P Γ A (.sort s)) (t : TypingTreeBE P Γ A' (.sort r)) (hA' : ENormal dz A')
    (hc : ConvertsBE A A') (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val := by
  have hr := HasTypeBE.rnf_spec hE.out hA
  have hconv : ConvertsBE A.rnf A' := .trans _ _ _ (.symm _ _ (reduces_convertsBE hr.1)) hc
  have hctx : ContextEquivalentBE P Γ Γ := ⟨hA.valid, hA.valid, fun _ _ => Iff.rfl⟩
  exact (enormal_conv_independence Ω C hno hC (rnfTree hA) hr.2 t hA' hconv hctx e e
    (Environment.SameData.of_eq rfl rfl)).2 s r rfl rfl

theorem normalRead_congr (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Γ B (.sort r)) (hc : ConvertsBE A B)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hB e).val :=
  normalRead_eq Ω C hno hC hA (rnfTree hB) (HasTypeBE.rnf_spec hE.out hB).2
    (.trans _ _ _ hc (reduces_convertsBE (HasTypeBE.rnf_spec hE.out hB).1)) e

theorem read_outside {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    (e : Environment (hw := hw) Ω C hno Γ) (ho : Ω.kprofile (M.subst e.images).knf ∉ C) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).knf := by
  cases t <;> simp only [preEvaluate,PreResult.lookup,PreResult.sort,PreResult.product,
    PreResult.abstraction,PreResult.application,PreResult.baseResult,PreResult.baseRead,ho,ite_false,dite_false]

theorem normalRead_outside {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : Ω.kprofile (A.subst e.images) ∉ C) :
    (normalRead Ω C hno hA e).val = Candidates.Top Ω (A.subst e.images).knf := by
  have hh := read_outside Ω C hno (rnfTree hA) e (by
    rw [normal_subst_eq Ω C hno hA e,Ω.kprofile_knf]; exact ho)
  exact hh.trans (congrArg (Candidates.Top Ω) (normal_subst_eq Ω C hno hA e))

theorem normalRead_sort {Γ : List (Expr S)} {s r : S}
    (hs : HasTypeBE P Γ (.sort s) (.sort r)) (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hs e).val = Candidates.Top Ω (.sort s) := by
  obtain ⟨t,ha,hc⟩ := hs.generation
  let tree : TypingTreeBE P Γ (.sort s) (.sort r) := .sort hs ha hc
  have hn : ENormal dz (Expr.sort s : Expr S) := show Normal (Expr.sort s) from Normal.sort s
  exact (normalRead_eq_erase Ω C hno hs tree hn (by rw [Expr.rnf_sort]) e).trans (by
    simp only [tree,preEvaluate,PreResult.sort,Expr.subst,Expr.knf_sort])

/-- The interpretation `R A e` of a type `A` in the environment `e`.
For a type whose reduct profile lies in the component, it is the `read` of the normal tree.
For other profiles, and for a type that is a sort without a type, it is the typed top set. -/
noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) : Set (Expr S) :=
  if ProfileR P Γ A ∈ C then
    if hs : ∃ s, HasTypeBE P Γ A (.sort s) then (normalRead Ω C hno hs.choose_spec e).val
    else Candidates.Top Ω (A.subst e.images).knf
  else Candidates.Top Ω (A.subst e.images).knf

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidates.IsCandidate Ω (A.subst e.images).knf (R Ω C hno A e) := by
  unfold R
  split
  · split
    · exact (normalRead Ω C hno _ e).property
    · exact Candidates.top_candidate
  · exact Candidates.top_candidate

theorem R_of_sorted {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hg : ProfileR P Γ A ∈ C) :
    R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  simp only [R,hg,dite_true,show ∃ s, HasTypeBE P Γ A (.sort s) from ⟨s,hA⟩]
  exact normalRead_eq_erase Ω C hno _ (rnfTree hA) (HasTypeBE.rnf_spec hE.out hA).2 rfl e

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : ProfileR P Γ A ∉ C ∨ Ω.kprofile (A.subst e.images) ∉ C) :
    R Ω C hno A e = Candidates.Top Ω (A.subst e.images).knf := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_outside Ω C hno hs.choose_spec e (ho.resolve_left (not_not.mpr hg))
  · rfl
  · rfl

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment (hw := hw) Ω C hno Γ) :
    R Ω C hno (.sort s) e = Candidates.Top Ω (.sort s) := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_sort Ω C hno hs.choose_spec e
  · simp only [Expr.subst,Expr.knf_sort]
  · simp only [Expr.subst,Expr.knf_sort]

namespace Environment
variable {Ω C hno}
noncomputable def ofImages {Γ : List (Expr S)} (σ : Nat → Expr S)
    (hσ : Ω.TTypedSubstitutionBE Γ σ) : Environment (hw := hw) Ω C hno Γ where
  images := σ
  typed := hσ
  parameters := fun i => if hi : ∃ A, Lookup Γ i A then
    (PayloadFits.exists_of_actual (hno := hno) ⟨_,(hσ _ _ hi.choose_spec).actual_type hw⟩).choose else none
  lawful := by
    intro i A hi
    simp only [dite_eq_left (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)]
    have he := Lookup.unique (show Lookup Γ i (Exists.choose (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)) from
      (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec) hi
    simpa only [he] using (PayloadFits.exists_of_actual (hno := hno)
      ⟨_,(hσ _ _ (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec).actual_type hw⟩).choose_spec

def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.parameters (i+1) = e.parameters i

theorem Ext.reindexed {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : e.Reindexed f Nat.succ := by
  intro i _
  exact ⟨(congrFun he.1 (i+1)).symm,(he.2 i).symm⟩

theorem cons_ext {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.THasTypeBE n (D.subst e.images)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (D.subst e.images).knf p) : e.Ext (e.cons hn p hp) n :=
  ⟨rfl,fun _ => rfl⟩

theorem extend_exists {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.THasTypeBE n (D.subst e.images)) : ∃ f : Environment (hw := hw) Ω C hno (D :: Γ), e.Ext f n := by
  obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,hn.actual_type hw⟩
  exact ⟨e.cons hn p hp,e.cons_ext hn p hp⟩
theorem ext_data {Γ : List (Expr S)} {e f : Environment (hw := hw) Ω C hno Γ}
    (hi : e.images = f.images) (hp : e.parameters = f.parameters) : e = f := by
  cases e; cases f
  cases hi; cases hp
  rfl

theorem Ext.payload {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : PayloadFits Ω C hno (D.subst e.images).knf (f.parameters 0) := by
  have hp := f.lawful 0 _ (.zero D Γ)
  simpa only [he.1,Expr.subst_raise_extend] using hp

theorem Ext.eq_cons {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) (hn : Ω.THasTypeBE n (D.subst e.images)) :
    f = e.cons hn (f.parameters 0) he.payload := by
  apply ext_data he.1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i

end Environment

theorem R_sorted_conversion (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Γ B (.sort r)) (hc : ConvertsBE A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  have hp := ProfileR.converts hw hA hB hc
  by_cases ha : ProfileR P Γ A ∈ C
  · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno hB e (hp ▸ ha)]
    exact normalRead_congr Ω C hno hC hA hB hc e
  · rw [R_outside Ω C hno A e (.inl ha),R_outside Ω C hno B e (.inl (hp ▸ ha))]
    exact congrArg (Candidates.Top Ω) (Expr.knf_converts
      ((ContextTowerBE.THasTypeBE.subst hA e.typed).kwn hw)
      ((ContextTowerBE.THasTypeBE.subst hB e.typed).kwn hw) (hc.subst e.images).k)

theorem R_rnf (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A : Expr S} (hA : ExpectedBE P Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno A.rnf e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.rnf_sort]
  · exact R_sorted_conversion Ω C hno hC hA (hA.subject_reduces (HasTypeBE.rnf_spec hw hA).1)
      (reduces_convertsBE (HasTypeBE.rnf_spec hw hA).1) e

theorem R_conversion (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A B : Expr S}
    (hA : ExpectedBE P Γ A) (hB : ExpectedBE P Γ B) (hc : ConvertsBE A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩ <;> rcases hB with ⟨t,rfl⟩ | ⟨t,hB⟩
  · rw [hc.sort_inj]
  · exact R_sorted_conversion Ω C hno hC
      (hB.subject_reduces (hB.reduces_sort_of_convertsBE hw (.symm _ _ hc))) hB hc e
  · exact R_sorted_conversion Ω C hno hC hA (hA.subject_reduces (hA.reduces_sort_of_convertsBE hw hc)) hc e
  · exact R_sorted_conversion Ω C hno hC hA hB hc e

theorem normalRead_weaken (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A D : Expr S} {s r : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hD : HasTypeBE P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) :
    (normalRead Ω C hno (HasTypeBE.weaken hA hD) f).val = (normalRead Ω C hno hA e).val := by
  let t := rnfTree hA
  have hr := HasTypeBE.rnf_spec hE.out hA
  have hen : ENormal dz (A.rnf.rename Nat.succ) := by
    unfold ENormal; rw [Expr.erase_rename]; exact hr.2.rename _
  have hh := normalRead_eq Ω C hno hC (HasTypeBE.weaken hA hD)
    (t.rename (.cons hD.valid hD) Nat.succ (TypingTreeBE.DeclRenaming.weaken D))
    hen (ConvertsBE.rename (reduces_convertsBE hr.1) Nat.succ) f
  exact hh.trans (preEvaluate_rename Ω C hno t (.cons hD.valid hD) Nat.succ
    (TypingTreeBE.DeclRenaming.weaken D) e f he.reindexed).2.symm

theorem R_weakening (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {A D : Expr S} {r : S}
    (hA : ExpectedBE P Γ A) (hD : HasTypeBE P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) : R Ω C hno (A.rename Nat.succ) f = R Ω C hno A e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s f).trans (R_sort Ω C hno s e).symm
  · have hp := ProfileR.weaken' hw hA hD
    by_cases ha : ProfileR P Γ A ∈ C
    · rw [R_of_sorted Ω C hno (HasTypeBE.weaken hA hD) f (hp ▸ ha),R_of_sorted Ω C hno hA e ha]
      exact normalRead_weaken Ω C hno hC hA hD he
    · rw [R_outside Ω C hno _ f (.inl (hp ▸ ha)),R_outside Ω C hno _ e (.inl ha),
        he.1,Expr.subst_raise_extend]

theorem normalRead_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (h : ContextEquivalentBE P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno ((h.typing _ _).mp hA) f).val := by
  let t := rnfTree hA
  have hr := HasTypeBE.rnf_spec hE.out hA
  exact (preEvaluate_recontext Ω C hno t h e f he).2.trans
    (normalRead_eq_erase Ω C hno ((h.typing _ _).mp hA) (t.recontext h) hr.2 rfl f).symm

theorem R_recontext {Γ Δ : List (Expr S)} {A : Expr S} (hA : ExpectedBE P Γ A)
    (h : ContextEquivalentBE P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) : R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · have hp : ProfileR P Γ A = ProfileR P Δ A := ProfileR.context_equiv h
    by_cases ha : ProfileR P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno ((h.typing _ _).mp hA) f (hp ▸ ha)]
      exact normalRead_recontext Ω C hno hA h e f he
    · rw [R_outside Ω C hno _ e (.inl ha),R_outside Ω C hno _ f (.inl (hp ▸ ha)),he.1]

end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem R_eq_normalRead_relevant {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  by_cases hg : ProfileR P Γ A ∈ C
  · exact R_of_sorted Ω C hno hA e hg
  · have ha : Ω.kprofile (A.subst e.images) ∉ C := fun ha =>
      hg (relevant_actual_mem Ω C hw hC hA e.typed hr ha)
    exact (R_outside Ω C hno A e (.inl hg)).trans (normalRead_outside Ω C hno hA e ha).symm

theorem R_eq_read_normal {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTreeBE P Γ A (.sort s)) (hn : ENormal dz A) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (normalRead_eq Ω C hno hC t.typing t hn (.refl _) e)

theorem R_eq_read_good {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTreeBE P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (good_normal_read Ω C hno hC t (rnfTree t.typing) (HasTypeBE.rnf_spec hE.out t.typing).2
      (reduces_convertsBE (HasTypeBE.rnf_spec hE.out t.typing).1) e hg).symm

theorem normal_product_candidate {Γ : List (Expr S)} {D E : Expr S} {a b c : S}
    (d : TypingTreeBE P Γ D (.sort a)) (q : TypingTreeBE P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hn : ENormal dz (.pi D E)) (hg : ProfileR P Γ (.pi D E) ∈ C)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) :
    R Ω C hno (.pi D E) e = (PreResult.productCandidate d.typing q.typing hr
      (preEvaluate Ω C hno d) (preEvaluate Ω C hno q) e).val := by
  let t : TypingTreeBE P Γ (.pi D E) (.sort c) :=
    .product (.product d.typing q.typing hr) d q hr (.refl _)
  have he := R_eq_read_normal Ω C hno hC t hn ⟨_,hg,.refl _⟩ e
  exact he.trans (by
    simp only [t,preEvaluate,PreResult.product,Ω.kprofile_knf,ha,ite_true])

theorem normal_product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hn : ENormal dz (.pi D E))
    (hg : ProfileR P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).knf ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let d := TypingTreeBE.ofTyping hD
  let q := TypingTreeBE.ofTyping hE
  let t := PreResult.productData hD hE hr e
  let bd : t.BodyReads := fun n hn p hp => (preEvaluate Ω C hno q (t.extend hn p hp)).read
  have hf := ProfileR.triple' hw hp
  have hdrel : Relevant (P := P) C Γ D := ⟨_,hg,.single (.domain hf)⟩
  have herel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain hf)⟩
  have hrd := R_eq_read_normal Ω C hno hC d hn.pi.1 hdrel e
  have htest : t.testers (preEvaluate Ω C hno d e).read = R Ω C hno D e := by
    unfold ProductInstance.testers
    split_ifs with hc
    · exact hrd.symm
    · exact (R_outside Ω C hno D e (.inr (by simpa only [t,PreResult.productData,
        ProductInstance.domainNF,ProductInstance.rawDomain,Ω.kprofile_knf] using hc))).symm
  have hre : ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      R Ω C hno E f = (preEvaluate Ω C hno q f).read.val :=
    fun f => R_eq_read_normal Ω C hno hC q hn.pi.2 herel f
  rw [normal_product_candidate Ω C hno hC d q hr hn hg e ha]
  change h ∈ (t.candidate (preEvaluate Ω C hno d e).read bd).val ↔ _
  constructor
  · intro hh
    refine ⟨?_,?_⟩
    · exact t.product_nf.symm ▸ hh.1
    · intro n hnr f he
      have hnt : n ∈ t.testers (preEvaluate Ω C hno d e).read := htest.symm ▸ hnr
      have hnty := (t.testers_top _ hnt).1
      have hfcons := he.eq_cons (t.rawArgument hnty)
      rw [hfcons,hre]
      by_cases hc : Ω.kprofile (t.targetNF n) ∈ C
      · exact t.candidate_body _ bd hh hnt hc (f.parameters 0) he.payload
      · have hout := t.candidate_outside _ bd hh hnt hc
        have heo := read_outside Ω C hno q (t.extend hnty (f.parameters 0) he.payload) hc
        exact heo.symm ▸ hout
  · rintro ⟨hht,hbody⟩
    refine ⟨t.product_nf ▸ hht,?_⟩
    intro n hn U hU
    have hnty := (t.testers_top _ hn).1
    have hnr : n ∈ R Ω C hno D e := htest ▸ hn
    simp only [ProductInstance.fibers,hnty,dite_true] at hU
    split_ifs at hU with hc
    · obtain ⟨p,hp,rfl⟩ := hU
      rw [← hre]
      exact hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
    · have heU : U = Candidates.Top Ω (t.targetNF n) := hU
      rw [heU]
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,(t.rawArgument hnty).actual_type hw⟩
      have hmem := hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
      rw [hre,read_outside Ω C hno q (t.extend hnty p hp) hc] at hmem
      exact hmem

end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno}
theorem Ext.argument {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : Ω.THasTypeBE n (D.subst e.images) := by
  have hh := f.typed 0 _ (.zero D Γ)
  simpa only [he.1,Expr.extend_zero,Expr.subst_raise_extend] using hh

theorem Ext.convert_domain {Γ : List (Expr S)} {D D' n : Expr S} {a b : S}
    (hD : HasTypeBE P Γ D (.sort a)) (hD' : HasTypeBE P Γ D' (.sort b)) (hc : ConvertsBE D D')
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : ∃ g : Environment (hw := hw) Ω C hno (D' :: Γ), e.Ext g n ∧
      f.images = g.images ∧ f.parameters = g.parameters := by
  have ht := ContextTowerBE.THasTypeBE.subst hD' e.typed
  have hnf := Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hD e.typed).kwn hw)
    (ht.kwn hw) (hc.subst e.images).k
  have hn := he.argument.of_type_knf_eq hnf
  let g := e.cons hn (f.parameters 0) (hnf ▸ he.payload)
  refine ⟨g,e.cons_ext hn _ _,he.1,?_⟩
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i
end Environment

theorem normalRead_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} {s : S} (hA : HasTypeBE P Γ A (.sort s))
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hA f).val :=
  (preEvaluate_compatible Ω C hno hC (rnfTree hA) e f he).2

theorem R_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} (hA : ExpectedBE P Γ A)
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · by_cases hc : ProfileR P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e hc,R_of_sorted Ω C hno hA f hc]
      exact normalRead_compatible Ω C hno hC hA e f he
    · rw [R_outside Ω C hno A e (.inl hc),R_outside Ω C hno A f (.inl hc),
        e.actual_expr_eq he.1 hA]

theorem R_binder_conversion (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {D D' E E' n : Expr S} {a b s r : S}
    (hD : HasTypeBE P Γ D (.sort a)) (hD' : HasTypeBE P Γ D' (.sort b)) (hc : ConvertsBE D D')
    (hE : HasTypeBE P (D :: Γ) E (.sort s)) (hE' : HasTypeBE P (D' :: Γ) E' (.sort r))
    (hh : ConvertsBE E E') (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (g : Environment (hw := hw) Ω C hno (D' :: Γ))
    (_he : e.Ext f n) (_he' : e.Ext g n) (heq : f.SameData g) :
    R Ω C hno E f = R Ω C hno E' g := by
  let hctx := ContextEquivalentBE.head_conversion hD hD' hc
  exact (R_recontext Ω C hno (.sorted hE) hctx f g heq).trans
    (R_sorted_conversion Ω C hno hC ((hctx.typing _ _).mp hE) hE' hh g)

end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hg : ProfileR P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).knf ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have rD := HasTypeBE.rnf_spec hw hD
  have rE := HasTypeBE.rnf_spec hw hE
  have hDN := hD.subject_reduces rD.1
  have hEN := hE.subject_reduces rE.1
  have cD : ConvertsBE D D.rnf := reduces_convertsBE rD.1
  have cE : ConvertsBE E E.rnf := reduces_convertsBE rE.1
  let ctx := ContextEquivalentBE.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasTypeBE P Γ (.pi D.rnf E.rnf) (.sort c) := .product hDN hEN' hr
  have nc := ConvertsBE.pi cD cE
  have hn : ENormal dz (.pi D.rnf E.rnf) := by
    have h1 := rD.2
    have h2 := rE.2
    unfold ENormal at h1 h2 ⊢
    exact Normal.pi h1 h2
  have hprof := ProfileR.converts hw hp hpn nc
  have haprof := Ω.kprofile_converts ((ContextTowerBE.THasTypeBE.subst hp e.typed).kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hpn e.typed).kwn hw) (nc.subst e.images).k
  have hnf := Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hp e.typed).kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hpn e.typed).kwn hw) (nc.subst e.images).k
  have hR := R_sorted_conversion Ω C hno hC hp hpn nc e
  have hRD := R_rnf Ω C hno hC (.sorted hD) e
  rw [hR,normal_product_iff Ω C hno hC hpn hn (hprof ▸ hg) e (haprof ▸ ha) h,hnf]
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr f he
    obtain ⟨g,heg,hfi,hfp⟩ := he.convert_domain hD hDN cD
    have hmem := hbody n (hRD ▸ hnr) g heg
    have heq := R_binder_conversion Ω C hno hC hD hDN cD hE hEN' cE e f g he heg
      (Environment.SameData.of_eq hfi hfp)
    exact heq.symm ▸ hmem
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr g heg
    obtain ⟨f,hef,hgi,hgp⟩ := heg.convert_domain hDN hD (.symm _ _ cD)
    have hmem := hbody n (hRD.symm ▸ hnr) f hef
    have heq := R_binder_conversion Ω C hno hC hD hDN cD hE hEN' cE e f g hef heg
      (Environment.SameData.of_eq hgi.symm hgp.symm)
    exact heq ▸ hmem

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hg : ProfileR P Γ (.pi D E) ∈ C) (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C)
    (h : Expr S) (ht : h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).knf)
    (hb : ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      e.Ext f n → Expr.app h n ∈ R Ω C hno E f) : h ∈ R Ω C hno (.pi D E) e :=
  (product_iff Ω C hno hC hp hg e ha h).mpr ⟨ht,hb⟩

end

section
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_argument_active {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hN : HasTypeBE P Γ N D)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hpC : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.kprofile ((E.instantiate N).subst e.images) ∈ C)
    (hD : Ω.kprofile (D.subst e.images) ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.kprofile (D.subst e.images)) := by
  obtain ⟨J,hf,hpath⟩ := Ω.kframe_profiles hw (ContextTowerBE.THasTypeBE.subst hp e.typed).toK
    (ContextTowerBE.THasTypeBE.subst hN e.typed).toK
  have hJC : J ∈ C := hC.between (by simpa only [Expr.instantiate_subst] using hNC)
    hpC hpath.reach (.single (.codomain hf))
  exact ⟨_,⟨hD,J,hJC,_,hpC,hf⟩,.refl _⟩

theorem R_instantiate_normal {Γ : List (Expr S)} {D E N : Expr S} {a b c : S}
    (hD : HasTypeBE P Γ D (.sort a)) (hE : HasTypeBE P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (n : TypingTreeBE P Γ N D) (hnE : ENormal dz E) (hnN : ENormal dz N)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hg : ProfileR P Γ (.pi D E) ∈ C) (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.kprofile ((E.instantiate N).subst e.images) ∈ C) :
    R Ω C hno E (e.cons (ContextTowerBE.THasTypeBE.subst n.typing e.typed)
      (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits) =
    R Ω C hno (E.instantiate N) e := by
  let q := TypingTreeBE.ofTyping hE
  let f := e.cons (ContextTowerBE.THasTypeBE.subst n.typing e.typed)
    (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits
  let ts := TypingTreeBE.StoredSubstitution.single n
  let qt := q.subst hD.valid (Expr.single N) ts
  have hp := HasTypeBE.product hD hE hr
  have hrel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain (ProfileR.triple' hw hp))⟩
  have hrelN : Relevant (P := P) C Γ (E.instantiate N) :=
    ⟨_,hg,(ProfileR.instantiate_product_path hw hp n.typing).reach⟩
  have hgood : ReadGood Ω C q f.images := (normal_good Ω C hw hC q hnE f.images f.typed).2 b rfl hrel
  have hgN : ActiveLayer P C (Ω.kprofile (D.subst e.images)) → ValGood Ω C n e.images :=
    (normal_good Ω C hw hC n hnN e.images e.typed).1
  have hguard : SubstitutionGuard Ω C (D :: Γ) (Expr.single N) f.images :=
    single_guard Ω C e.images (product_argument_active Ω C hno hC hp n.typing e ha hNC)
  have hfi : f.images = Expr.consSub (N.subst e.images) e.images := by
    funext i; cases i <;> rfl
  have hgR := single_goodReplacement Ω C n e.images hgN
  have hgood' : ReadGood Ω C qt e.images := (goodness_subst Ω C hw q hD.valid (Expr.single N) ts
    e.images e.typed (by simpa only [Expr.comp_single,←hfi] using hguard) hgR).2
      (by simpa only [Expr.comp_single,←hfi] using hgood)
  have heval := (preEvaluate_subst Ω C hno q hD.valid (Expr.single N) ts f e
    (single_assigned Ω C hno hC n e) hguard).2 hgood
  exact (R_eq_read_normal Ω C hno hC q hnE hrel f).trans (heval.trans
    (R_eq_read_good Ω C hno hC qt hrelN e hgood').symm)

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hN : HasTypeBE P Γ N D) (hg : ProfileR P Γ (.pi D E) ∈ C)
    (ha : Ω.kprofile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C hno (.pi D E) e) (hn : N.subst e.images ∈ R Ω C hno D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have rE := HasTypeBE.rnf_spec hw hE
  have rN := HasTypeBE.rnf_spec hw hN
  have hNN : HasTypeBE P Γ N.rnf D := hN.subject_reduces rN.1
  have hEN : HasTypeBE P (D :: Γ) E.rnf (.sort b) := hE.subject_reduces rE.1
  let n := TypingTreeBE.ofTyping hNN
  let pn := (preEvaluate Ω C hno n e).parameter
  have pp := (preEvaluate Ω C hno n e).parameter_fits
  let f := e.cons (ContextTowerBE.THasTypeBE.subst hN e.typed) pn pp
  let g := e.cons (ContextTowerBE.THasTypeBE.subst hNN e.typed) pn pp
  have hm := ((product_iff Ω C hno hC hp hg e ha h).mp hh).2 (N.subst e.images) hn f
    (e.cons_ext _ pn pp)
  have hnE := rE.2
  have hnN := rN.2
  have cE : ConvertsBE E E.rnf := reduces_convertsBE rE.1
  have cN : ConvertsBE N N.rnf := reduces_convertsBE rN.1
  have hp' : HasTypeBE P Γ (.pi D E.rnf) (.sort c) := .product hD hEN hr
  have cP : ConvertsBE (.pi D E) (.pi D E.rnf) := .pi (.refl _) cE
  have cT : ConvertsBE (E.instantiate N) (E.rnf.instantiate N.rnf) :=
    .trans _ _ _ (cE.subst (Expr.single N)) (cN.instantiate_right E.rnf)
  have hT := hE.instantiate hN
  have hT' := hEN.instantiate hNN
  have hRT := R_sorted_conversion Ω C hno hC hT hT' cT e
  by_cases htC : Ω.kprofile ((E.rnf.instantiate N.rnf).subst e.images) ∈ C
  · have hgg := ProfileR.converts hw hp hp' cP
    have haa := Ω.kprofile_converts ((ContextTowerBE.THasTypeBE.subst hp e.typed).kwn hw)
      ((ContextTowerBE.THasTypeBE.subst hp' e.typed).kwn hw) (cP.subst e.images).k
    have hfg : f.Compatible g := by
      constructor
      · intro i hi
        cases i with
        | zero => exact (cN.subst e.images).k
        | succ i => exact .refl _
      · intro i hi; cases i <;> rfl
    have hrE := (R_rnf Ω C hno hC (.sorted hE) f).trans
      ((R_compatible Ω C hno hC (.sorted hEN) f g hfg).trans
      (R_instantiate_normal Ω C hno hC hD hEN hr n hnE hnN e (hgg ▸ hg) (haa ▸ ha) htC))
    exact hRT.symm ▸ (hrE ▸ hm)
  · have hmem := (R_candidate Ω C hno E f).upper hm
    have he : (E.subst f.images).knf = ((E.instantiate N).subst e.images).knf := by
      congr 1
      rw [← Expr.instantiate_subst,Expr.instantiate_liftSub]
      rfl
    have hnf := Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hT e.typed).kwn hw)
      ((ContextTowerBE.THasTypeBE.subst hT' e.typed).kwn hw) (cT.subst e.images).k
    rw [hRT,R_outside Ω C hno _ e (.inr htC)]
    exact (hnf ▸ he ▸ hmem)

end

universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

/-- The observation interpretation of the component, for case 3.
It allows arbitrary typed images, which need not be normal, and all matching extensions of the payload. -/
noncomputable def componentInterface (hC : IsComponent (PrimaryEdge P) C) : ComponentInterface Ω hw C where
  Env := Environment (hw := hw) Ω C hno
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨Environment.ofImages σ hσ,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ _ hn := e.extend_exists hn
  R := R Ω C hno
  candidate e _ := R_candidate Ω C hno _ e
  conversion e ha hb hc := R_conversion Ω C hno hC ha hb hc e
  outside e _ ho := R_outside Ω C hno _ e ho
  weakening hd he hx := R_weakening Ω C hno hC he hd hx
  product_intro e hp hg ha h ht hb := product_intro Ω C hno hC e hp hg ha h ht hb
  specialization e hp hN hg ha h hh hn := specialization Ω C hno hC e hp hN hg ha h hh hn

end PureTypeSystem.KP.ObservationValues

