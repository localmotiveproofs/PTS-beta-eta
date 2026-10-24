/- Adapted to typing with βη-conversion from OpenAI's `Interface.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Potential

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


/-! The exact local obligations that are used when a primary component is advanced.
This is an internal interface, and it is not a hypothesis of the main theorem. -/
namespace PureTypeSystem.KP
universe u v

/-- An expected type is a sort, or a term that has a sort as its type.
The first case covers sorts that have no type themselves, as in the correctness of types. -/
def ExpectedBE {S : Type u} (P : Specification S) (Γ : List (Expr S)) (A : Expr S) : Prop :=
  (∃ s, A = .sort s) ∨ ∃ s, HasTypeBE P Γ A (.sort s)
namespace ExpectedBE
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Γ : List (Expr S)} {A D : Expr S}
theorem of_type {M : Expr S} (h : HasTypeBE P Γ M A) : ExpectedBE P Γ A := h.regularity
theorem sorted {s : S} (h : HasTypeBE P Γ A (.sort s)) : ExpectedBE P Γ A := .inr ⟨s,h⟩
theorem wn (hw : SystemENormalizing' P) (h : ExpectedBE P Γ A) : KWN A := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,NormalBE.sort s⟩
  · exact h.kwn hw
theorem weaken {s : S} (h : ExpectedBE P Γ A) (hD : HasTypeBE P Γ D (.sort s)) :
    ExpectedBE P (D :: Γ) (A.rename Nat.succ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inl ⟨s,rfl⟩
  · exact .inr ⟨s,.weaken h hD⟩
theorem profileR_eq (hw : SystemENormalizing' P) {B : Expr S} (hA : ExpectedBE P Γ A)
    (hB : ExpectedBE P Γ B) (hc : ConvertsBE A B) : ProfileR P Γ A = ProfileR P Γ B := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩ <;> rcases hB with ⟨t,rfl⟩ | ⟨t,hB⟩
  · rw [hc.sort_inj]
  · exact ProfileR.reduces hw hB (hB.reduces_sort_of_convertsBE hw (.symm _ _ hc))
  · exact (ProfileR.reduces hw hA (hA.reduces_sort_of_convertsBE hw hc)).symm
  · exact ProfileR.converts hw hA hB hc
end ExpectedBE

/-- The set `U` of components that are already processed.
`Ground` (OpenAI's `G_T`) equals `Top` (OpenAI's `⊤_T`) on `U`, `U` is closed under predecessors, and `U` contains every strict predecessor of the component that is being processed. -/
structure Processed {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P)
    (U C : Set (Set S)) : Prop where
  disjoint : Disjoint U C
  closed : ∀ {I J}, J ∈ U → Reach (PrimaryEdge P) I J → I ∈ U
  before : ∀ {I J}, J ∈ C → Reach (PrimaryEdge P) I J → I ∈ U ∨ I ∈ C
  invariant : ∀ {T}, Candidates.ActualType Ω T → Ω.kprofile T ∈ U →
    Candidates.Ground Ω T = Candidates.Top Ω T

/-- The interface that a component must provide.
Environments carry arbitrary typed images, which need not be normal.
Each collection of extensions is nonempty and keeps the old parameters.
Product tests range over all listed extensions, and specialization can select the tested payload of the normal argument. -/
structure ComponentInterface {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P)
    (hw : SystemENormalizing' P) (C : Set (Set S)) where
  Env : List (Expr S) → Type v
  images : {Γ : List (Expr S)} → Env Γ → Nat → Expr S
  typed : ∀ {Γ} (e : Env Γ), Ω.TTypedSubstitutionBE Γ (images e)
  inhabit : ∀ {Γ} (σ : Nat → Expr S), Ω.TTypedSubstitutionBE Γ σ →
    ∃ e : Env Γ, images e = σ
  Ext : {Γ : List (Expr S)} → {D : Expr S} → Env Γ → Env (D :: Γ) → Expr S → Prop
  ext_images : ∀ {Γ D} {e : Env Γ} {e' : Env (D :: Γ)} {n}, Ext e e' n →
    images e' = Expr.extend (images e) n
  extend : ∀ {Γ D s} (e : Env Γ), HasTypeBE P Γ D (.sort s) → ∀ n,
    Ω.THasTypeBE n (D.subst (images e)) → ∃ e' : Env (D :: Γ), Ext e e' n
  R : {Γ : List (Expr S)} → Expr S → Env Γ → Set (Expr S)
  candidate : ∀ {Γ A} (e : Env Γ), ExpectedBE P Γ A →
    Candidates.IsCandidate Ω (A.subst (images e)).knf (R A e)
  conversion : ∀ {Γ A B} (e : Env Γ), ExpectedBE P Γ A → ExpectedBE P Γ B →
    ConvertsBE A B → R A e = R B e
  outside : ∀ {Γ A} (e : Env Γ), ExpectedBE P Γ A →
    (ProfileR P Γ A ∉ C ∨ Ω.kprofile (A.subst (images e)) ∉ C) →
    R A e = Candidates.Top Ω (A.subst (images e)).knf
  weakening : ∀ {Γ D A s} {e : Env Γ} {e' : Env (D :: Γ)} {n},
    HasTypeBE P Γ D (.sort s) → ExpectedBE P Γ A → Ext e e' n →
    R (A.rename Nat.succ) e' = R A e
  product_intro : ∀ {Γ D E s} (e : Env Γ), HasTypeBE P Γ (.pi D E) (.sort s) →
    ProfileR P Γ (.pi D E) ∈ C → Ω.kprofile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ Candidates.Top Ω ((Expr.pi D E).subst (images e)).knf →
    (∀ n, n ∈ R D e → ∀ e' : Env (D :: Γ), Ext e e' n → Expr.app h n ∈ R E e') →
    h ∈ R (.pi D E) e
  specialization : ∀ {Γ D E s N} (e : Env Γ), HasTypeBE P Γ (.pi D E) (.sort s) →
    HasTypeBE P Γ N D → ProfileR P Γ (.pi D E) ∈ C →
    Ω.kprofile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ R (.pi D E) e → N.subst (images e) ∈ R D e →
    Expr.app h (N.subst (images e)) ∈ R (E.instantiate N) e

namespace ComponentInterface
open Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable {hw : SystemENormalizing' P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Admissible {Γ : List (Expr S)} (e : J.Env Γ) : Prop :=
  ∀ i B, Lookup Γ i B →
    (ProfileR P Γ B ∈ C → J.images e i ∈ J.R B e) ∧
    (ProfileR P Γ B ∈ U → StronglyNormalizing (J.images e i)) ∧
    (ProfileR P Γ B ∉ U → ProfileR P Γ B ∉ C →
      J.images e i ∈ Ground Ω (B.subst (J.images e)).knf)

theorem admissible_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    {e : J.Env Γ} {e' : J.Env (D :: Γ)} {n : Expr S}
    (hD : HasTypeBE P Γ D (.sort s)) (he : J.Ext e e' n)
    (ha : J.Admissible (U := U) e)
    (hnC : ProfileR P Γ D ∈ C → n ∈ J.R D e)
    (hnU : ProfileR P Γ D ∈ U → StronglyNormalizing n)
    (hnG : ProfileR P Γ D ∉ U → ProfileR P Γ D ∉ C → n ∈ Ground Ω (D.subst (J.images e)).knf) :
    J.Admissible (U := U) e' := by
  intro i B hi
  cases hi with
  | zero =>
    have hp := ProfileR.weaken' hw hD hD
    rw [hp,J.weakening hD (.sorted hD) he]
    simpa only [J.ext_images he,Expr.extend_zero,Expr.subst_raise_extend] using ⟨hnC,hnU,hnG⟩
  | succ D hi =>
    obtain ⟨t,hB⟩ := HasTypeBE.lookup_sorted hD.valid hi
    rw [ProfileR.weaken' hw hB hD,J.weakening hD (.sorted hB) he]
    simpa only [J.ext_images he,Expr.extend_succ,Expr.subst_raise_extend] using ha _ _ hi

/-- Sending a binder to a fresh typed variable always preserves admissibility.
Strong normalization of that instance transfers back to the open substituted body by reflection under substitution.
So no global renaming and no bound on the height of reductions is needed. -/
theorem fresh_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    (e : J.Env Γ) (hD : HasTypeBE P Γ D (.sort s)) (ha : J.Admissible (U := U) e) :
    ∃ n, ∃ e' : J.Env (D :: Γ), J.Ext e e' (.var n) ∧ J.Admissible (U := U) e' := by
  have ht := ContextTowerBE.THasTypeBE.subst hD (J.typed e)
  obtain ⟨n,_,hn⟩ := Ω.kfresh_variable ht 0
  obtain ⟨e',he⟩ := J.extend e hD (.var n) hn
  have hng := var_ground n (hn.normalize_type hw)
  exact ⟨n,e',he,J.admissible_extension hD he ha
    (fun _ => (J.candidate e (.sorted hD)).lower hng)
    (fun _ => (KNormal.var n).stronglyNormalizing) (fun _ _ => hng)⟩

end ComponentInterface

namespace ExpectedBE
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S}
theorem subst_wn (h : ExpectedBE P Γ A) (hw : SystemENormalizing' P)
    (hσ : Ω.TTypedSubstitutionBE Γ σ) : KWN (A.subst σ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,NormalBE.sort s⟩
  · exact (ContextTowerBE.THasTypeBE.subst h hσ).kwn hw

theorem actual (h : ExpectedBE P Γ A) (hw : SystemENormalizing' P)
    (hσ : Ω.TTypedSubstitutionBE Γ σ) : Candidates.ActualType Ω (A.subst σ).knf := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inr ⟨s,Expr.knf_of_normal (KNormal.sort s)⟩
  · have ht := ContextTowerBE.THasTypeBE.subst h hσ
    exact .inl ⟨(Expr.knf_spec (ht.kwn hw)).2, s, ht.toK.knf hw⟩
end ExpectedBE

end PureTypeSystem.KP

namespace PureTypeSystem.ContextTowerBE
universe u
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P)
variable (hw : SystemENormalizing' P)
include hw
theorem kprofile_subst_path {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : PureTypeSystem.HasTypeBE P Γ T (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.kprofile (T.subst σ)) (ProfileR P Γ T) :=
  Profile.inclusion_path (Ω.kprofile_feasible hw (ContextTowerBE.THasTypeBE.subst ht hσ).toK)
    (ProfileR.feasible' hw ht)
    (Ω.kprofile_subst_growth hw ht hσ.toK)

theorem kprofile_instantiate_product_path_k {D E n : Expr S} {s : S}
    (hp : Ω.KHasTypeBE (.pi D E) (.sort s)) (hn : Ω.KHasTypeBE n D) :
    PositivePath (PrimaryEdge P) (Ω.kprofile (E.instantiate n)) (Ω.kprofile (.pi D E)) := by
  obtain ⟨J, htr, hpath⟩ := Ω.kframe_profiles hw hp hn
  exact hpath.trans (.single (.codomain htr))

theorem kprofile_instantiate_product_path {D E n : Expr S} {s : S}
    (hp : Ω.THasTypeBE (.pi D E) (.sort s)) (hn : Ω.THasTypeBE n D) :
    PositivePath (PrimaryEdge P) (Ω.kprofile (E.instantiate n)) (Ω.kprofile (.pi D E)) :=
  Ω.kprofile_instantiate_product_path_k hw hp.toK hn.toK

/-- The key profiles of the domain, the codomain and the whole of a product that is typed up to keys form a profile triple. -/
theorem kprofile_triple {D E : Expr S} {s : S} (hp : Ω.KHasTypeBE (.pi D E) (.sort s)) :
    ∃ J, ProfileTriple P (Ω.kprofile D) J (Ω.kprofile (.pi D E)) := by
  obtain ⟨A₁, B₁, hP, hA, hB, eA, eB⟩ := KHasTypeBE.pi_type_witness Ω hp
  obtain ⟨n, hPn⟩ := hP
  obtain ⟨a, b, c, hAn, hBn, _, _⟩ := hPn.generation_pi
  have wP := (ContextTowerBE.HasTypeBE.kwn_both (⟨n, hPn⟩ : Ω.HasTypeBE (.pi A₁ B₁) (.sort s)) hw).1
  have kP : (Expr.pi A₁ B₁).knf = (Expr.pi D E).knf := by
    rw [Expr.knf_pi wP.pi_domain wP.pi_body, hA, hB,
      ← Expr.knf_pi (KWN.of_knf_eq hA.symm wP.pi_domain) (KWN.of_knf_eq hB.symm wP.pi_body)]
  refine ⟨ProfileR P (A₁.rename (Expr.reverseIndex n) :: Ω.context n)
    (B₁.rename (Expr.liftRen (Expr.reverseIndex n))), ?_⟩
  rw [← Ω.kprofile_of_knf_eq hA, ← Ω.kprofile_of_knf_eq kP, Ω.kprofile_at hw hAn,
    Ω.kprofile_at hw (T := .pi A₁ B₁) hPn]
  exact ProfileR.triple' hw hPn
end PureTypeSystem.ContextTowerBE

namespace PureTypeSystem.KP
universe u v

namespace Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable (hw : SystemENormalizing' P)
include hw
/-- Membership in `Ground` propagates through the normal form of a dependent product whose instance need not be normal. -/
theorem ground_application_subst {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hh : h ∈ Ground Ω ((Expr.pi D E).subst σ).knf)
    (hn : n ∈ Top Ω (D.subst σ).knf) :
    Expr.app h n ∈ Ground Ω (E.subst (Expr.extend σ n)).knf := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTowerBE.THasTypeBE.subst hp hσ
  have hwraw := hraw.kwn hw
  change KWN (.pi (D.subst σ) (E.subst (Expr.liftSub σ))) at hwraw
  have hrawD := ContextTowerBE.THasTypeBE.subst hD hσ
  have hnr : Ω.THasTypeBE n (D.subst σ) := hn.1.conversion hrawD
    (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
  have hparts : KWN (D.subst σ) ∧
      KWN (E.subst (Expr.liftSub σ)) := ⟨hwraw.pi_domain, hwraw.pi_body⟩
  have htarget : Ω.THasTypeBE (E.subst (Expr.extend σ n)) (.sort b) :=
    ContextTowerBE.THasTypeBE.subst hE (hσ.cons hnr)
  have hnf : ((Expr.pi D E).subst σ).knf =
      .pi (D.subst σ).knf (E.subst (Expr.liftSub σ)).knf :=
    Expr.knf_pi hparts.1 hparts.2
  rw [hnf] at hh
  have hout := ground_application hw hh hn
  have hpN := hraw.toK.knf hw
  rw [hnf] at hpN
  obtain ⟨t,ht⟩ := Ω.kframe_target_sorted hpN hn.1.toK
  have hr : KConverts (E.subst (Expr.extend σ n))
      ((E.subst (Expr.liftSub σ)).knf.instantiate n) := by
    rw [← Expr.instantiate_extended]
    unfold KConverts
    rw [Expr.erase_instantiate, Expr.erase_instantiate]
    exact ConvertsBE.subst (Expr.knf_spec hparts.2).1.converts (Expr.single (n.erase dz))
  have he := Expr.knf_converts (htarget.kwn hw) (ht.kwn hw) hr
  rwa [he]
end Candidates

namespace Processed
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable {U C : Set (Set S)} (H : Processed Ω U C) (hw : SystemENormalizing' P)
variable {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
include H hw
theorem subst_closed (ht : HasTypeBE P Γ T (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hT : ProfileR P Γ T ∈ U) : Ω.kprofile (T.subst σ) ∈ U :=
  H.closed hT (Ω.kprofile_subst_path hw ht hσ).reach

theorem subst_before (ht : HasTypeBE P Γ T (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hT : ProfileR P Γ T ∈ C) : Ω.kprofile (T.subst σ) ∈ U ∨ Ω.kprofile (T.subst σ) ∈ C :=
  H.before hT (Ω.kprofile_subst_path hw ht hσ).reach

theorem top_ground_generic {e : Expr S}
    (ht : HasTypeBE P Γ T (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hT : ProfileR P Γ T ∈ U) (he : e ∈ Candidates.Top Ω (T.subst σ).knf) :
    e ∈ Candidates.Ground Ω (T.subst σ).knf := by
  rw [H.invariant ((ExpectedBE.sorted ht).actual hw hσ) (by
    rw [Ω.kprofile_knf]
    exact H.subst_closed hw ht hσ hT)]
  exact he
end Processed

namespace ComponentInterface
open Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable {hw : SystemENormalizing' P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

/-- The extra invariant for neutral terms.
It says that every prefix of a neutral spine stays in `Ground` (OpenAI's "G-prefix" invariant), as in the spine argument of OpenAI's preprint. -/
def Transported {Γ : List (Expr S)} (M A : Expr S) (e : J.Env Γ) : Prop :=
  M.subst (J.images e) ∈ J.R A e ∧
    (Neutral M → ProfileR P Γ A ∉ C →
      M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).knf)

namespace Transported
variable {J} {Γ : List (Expr S)} {M A B : Expr S} {e : J.Env Γ}
theorem sn (h : J.Transported M A e) (hA : ExpectedBE P Γ A) :
    StronglyNormalizing (M.subst (J.images e)) := (J.candidate e hA).upper h.1 |>.2

theorem convert (h : J.Transported M A e) (hA : ExpectedBE P Γ A)
    (hB : ExpectedBE P Γ B) (hc : ConvertsBE A B) : J.Transported M B e := by
  have hp := ExpectedBE.profileR_eq hw hA hB hc
  have he := Expr.knf_converts (hA.subst_wn hw (J.typed e))
    (hB.subst_wn hw (J.typed e)) (hc.subst (J.images e)).k
  refine ⟨?_,?_⟩
  · rw [← J.conversion e hA hB hc]; exact h.1
  · intro hn hout
    rw [← he]
    exact h.2 hn (hp ▸ hout)
end Transported

theorem transported_of_ground {Γ : List (Expr S)} {M A : Expr S} {e : J.Env Γ}
    (hA : ExpectedBE P Γ A) (hg : M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).knf) :
    J.Transported M A e := ⟨(J.candidate e hA).lower hg,fun _ _ => hg⟩

theorem transported_at_sort {Γ : List (Expr S)} {M : Expr S} {e : J.Env Γ} {s : S}
    (ht : HasTypeBE P Γ M (.sort s)) (hs : StronglyNormalizing (M.subst (J.images e))) :
    J.Transported M (.sort s) e := by
  apply J.transported_of_ground (.inl ⟨s,rfl⟩)
  have hh : M.subst (J.images e) ∈ Top Ω (.sort s) :=
    ⟨ContextTowerBE.THasTypeBE.subst ht (J.typed e),hs⟩
  simpa only [Expr.subst,Expr.knf_of_normal (KNormal.sort s),sort_ground_eq_top] using hh

variable (H : Processed Ω U C)
include H

theorem transported_var {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (ht : HasTypeBE P Γ (.var i) A) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.var i) A e := by
  obtain ⟨B,hB,hc⟩ := ht.generation
  obtain ⟨s,hBs⟩ := HasTypeBE.lookup_sorted ht.valid hB
  have hea := ExpectedBE.of_type ht
  apply Transported.convert (A := B) (hA := .sorted hBs) (hB := hea) (hc := .symm _ _ hc)
  have hdr := ha i B hB
  by_cases hBU : ProfileR P Γ B ∈ U
  · apply J.transported_of_ground (.sorted hBs)
    exact H.top_ground_generic hw hBs (J.typed e) hBU
      ⟨(J.typed e i B hB).normalize_type hw,hdr.2.1 hBU⟩
  · by_cases hBC : ProfileR P Γ B ∈ C
    · exact ⟨hdr.1 hBC,fun _ hn => False.elim (hn hBC)⟩
    · exact J.transported_of_ground (.sorted hBs) (hdr.2.2 hBU hBC)

/-- Propagation for a neutral prefix.
Unlike a candidate, `Ground` is closed under application.
The invariant for processed components handles the only transition out of the current component. -/
theorem transported_neutral_app {Γ : List (Expr S)} {f n D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hn : HasTypeBE P Γ n D)
    (hf : Neutral f) (e : J.Env Γ)
    (hfr : J.Transported f (.pi D E) e) (hnr : J.Transported n D e) :
    J.Transported (.app f n) (E.instantiate n) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hExpected := ExpectedBE.sorted (hE.instantiate hn)
  have hnt := (J.candidate e (.sorted hD)).upper hnr.1
  have hg (hfg : f.subst (J.images e) ∈ Ground Ω ((Expr.pi D E).subst (J.images e)).knf) :
      J.Transported (.app f n) (E.instantiate n) e := by
    apply J.transported_of_ground hExpected
    rw [← Expr.instantiate_subst,Expr.instantiate_extended]
    exact ground_application_subst hw hp (J.typed e) hfg hnt
  by_cases hK : ProfileR P Γ (.pi D E) ∈ C
  · by_cases hKa : Ω.kprofile ((Expr.pi D E).subst (J.images e)) ∈ C
    · have hr := J.specialization e hp hn hK hKa _ hfr.1 hnr.1
      refine ⟨hr,?_⟩
      intro _ ho
      have hL := H.before hK (ProfileR.instantiate_product_path hw hp hn).reach
      rcases hL with hLU | hLC
      · exact H.top_ground_generic hw (hE.instantiate hn) (J.typed e) hLU
          ((J.candidate e hExpected).upper hr)
      · exact False.elim (ho hLC)
    · apply hg
      have haK := (H.subst_before hw hp (J.typed e) hK).resolve_right hKa
      rw [H.invariant ((ExpectedBE.sorted hp).actual hw (J.typed e)) (by
        rwa [Ω.kprofile_knf])]
      exact (J.candidate e (.sorted hp)).upper hfr.1
  · exact hg (hfr.2 hf hK)

end ComponentInterface
end PureTypeSystem.KP

namespace PureTypeSystem.KP.Candidates
universe u
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] {Ω : ContextTowerBE P}
variable (hw : SystemENormalizing' P)
include hw

theorem application_subst_type {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hh : Ω.THasTypeBE h ((Expr.pi D E).subst σ).knf)
    (hn : Ω.THasTypeBE n (D.subst σ).knf) :
    Ω.THasTypeBE (.app h n) (E.subst (Expr.extend σ n)).knf := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTowerBE.THasTypeBE.subst hp hσ
  have hrawD := ContextTowerBE.THasTypeBE.subst hD hσ
  have hhr := hh.conversion hraw
    (.symm _ _ (Expr.knf_spec (hraw.kwn hw)).1.converts)
  have hnr := hn.conversion hrawD
    (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
  have hout := (hhr.application hnr).normalize_type hw
  simpa only [Expr.instantiate_extended] using hout

def RawProduct (Ω : ContextTowerBE P) (D E : Expr S) (σ : Nat → Expr S)
    (X : Set (Expr S)) (Y : Expr S → Bool → Set (Expr S)) : Set (Expr S) :=
  {h | h ∈ Top Ω ((Expr.pi D E).subst σ).knf ∧
    ∀ n ∈ X, ∀ b, Expr.app h n ∈ Y n b}

theorem rawProduct_candidate {Γ : List (Expr S)} {D E : Expr S} {s : S}
    {σ : Nat → Expr S} {X : Set (Expr S)} {Y : Expr S → Bool → Set (Expr S)}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hσ : Ω.TTypedSubstitutionBE Γ σ)
    (hX : IsCandidate Ω (D.subst σ).knf X)
    (hY : ∀ n ∈ X, ∀ b, IsCandidate Ω (E.subst (Expr.extend σ n)).knf (Y n b)) :
    IsCandidate Ω ((Expr.pi D E).subst σ).knf (RawProduct Ω D E σ X Y) where
  lower := by
    intro h hh
    refine ⟨ground_le_top hh,?_⟩
    intro n hn b
    exact (hY n hn b).lower (ground_application_subst hw hp hσ hh (hX.upper hn))
  upper := fun _ hh => hh.1
  expansion := by
    intro D' m a ns ht hD hm ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hm ha hns hc.1.2⟩,?_⟩
    intro n hn b
    have ht' := application_subst_type hw hp hσ ht (hX.upper hn).1
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · exact (List.mem_singleton.mp hx).symm ▸ (hX.upper hn).2
    have hc' := hc.2 n hn b
    have ht'' : Ω.THasTypeBE ((Expr.app (.lam D' m) a).apps (ns ++ [n]))
        (E.subst (Expr.extend σ n)).knf := by
      simpa only [Expr.apps_append,Expr.apps] using ht'
    have hc'' : (m.instantiate a).apps (ns ++ [n]) ∈ Y n b := by
      simpa only [Expr.apps_append,Expr.apps] using hc'
    simpa only [Expr.apps_append,Expr.apps] using
      (hY n hn b).expansion D' m a (ns ++ [n]) ht'' hD hm ha hsn hc'' 
end PureTypeSystem.KP.Candidates

