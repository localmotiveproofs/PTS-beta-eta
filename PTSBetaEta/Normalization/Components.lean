/- Adapted to typing with βη-conversion from OpenAI's `Components.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Interface

@[expose] public section

/-!
# Components for typing with βη-conversion

This file adapts OpenAI's `Components.lean` (`PTSBetaEta.Beta.Components`) to typing with βη-conversion, with keys as indices.
The stack argument (`StackAt`, `run_stack`) keeps, for each tested argument, a typing in some finite prefix of the tower together with the key of its type.
It runs the component interface on legal representatives of each key in that prefix.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem

universe u

/-- In a plain context, a term can be given any legal type with the same key as its type. -/
theorem HasTypeBE.retype_plain {S : Type u} [Nonempty S] {P : Specification S}
    (hw : SystemENormalizing' P) {Γ : List (Expr S)} {M U T : Expr S} {t : S}
    (h : HasTypeBE P Γ M U) (hT : HasTypeBE P Γ T (.sort t)) (he : U.knf = T.knf) :
    HasTypeBE P Γ M T := by
  rcases h.regularity with ⟨u, rfl⟩ | ⟨u, hU⟩
  · have c := converts_sort_of_knf (hT.kwn hw) (by rw [← he, Expr.knf_sort])
    exact .conversion h hT (.symm _ _ c)
  · exact .conversion h hT (converts_of_knf_eq hw hU hT he)

end PureTypeSystem

namespace PureTypeSystem.KP

section
universe u v

namespace ComponentInterface
open Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P}
variable {hw : SystemENormalizing' P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Transports (M : Expr S) : Prop :=
  ∀ (Γ : List (Expr S)) A, HasTypeBE P Γ M A →
    ∀ e : J.Env Γ, J.Admissible (U := U) e → J.Transported M A e

/-- The open body of an abstraction is strongly normalizing after substitution.
The proof sends the bound variable to a fresh typed variable and reflects strong normalization of that instance. -/
theorem open_sn {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasTypeBE P (D :: Γ) b B) (hD : HasTypeBE P Γ D (.sort s))
    (ih : J.Transports (U := U) b) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    StronglyNormalizing (b.subst (Expr.liftSub (J.images e))) := by
  obtain ⟨z,e',he',ha'⟩ := J.fresh_extension e hD ha
  have hsn := (ih _ _ hb e' ha').sn (.of_type hb)
  rw [J.ext_images he',← Expr.instantiate_extended] at hsn
  exact StronglyNormalizing.of_subst (Expr.single (.var z)) hsn

variable (H : Processed Ω U C)
include H

theorem transports_lam {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasTypeBE P (D :: Γ) b B) (hp : HasTypeBE P Γ (.pi D B) (.sort s))
    (ihD : J.Transports (U := U) D) (ihb : J.Transports (U := U) b)
    (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.lam D b) (.pi D B) e := by
  classical
  obtain ⟨a,c,d,hD,hB,_,_⟩ := hp.generation_pi
  have hDs := (ihD _ _ hD e ha).sn (.of_type hD)
  have hbs := J.open_sn hb hD ihb e ha
  have htop : (Expr.lam D b).subst (J.images e) ∈
      Top Ω ((Expr.pi D B).subst (J.images e)).knf :=
    ⟨(ContextTowerBE.THasTypeBE.subst (.abstraction hb hp) (J.typed e)).normalize_type hw,
      hDs.lam hbs⟩
  refine ⟨?_,fun hn => by cases hn⟩
  by_cases hK : ProfileR P Γ (.pi D B) ∈ C
  · by_cases hKa : Ω.kprofile ((Expr.pi D B).subst (J.images e)) ∈ C
    · apply J.product_intro e hp hK hKa _ htop
      intro n hn e' he
      have hnt := (J.candidate e (.sorted hD)).upper hn
      have hDomain := ContextTowerBE.THasTypeBE.subst hD (J.typed e)
      have hnr := hnt.1.conversion hDomain
        (.symm _ _ (Expr.knf_spec (hDomain.kwn hw)).1.converts)
      have hdBefore := H.before hK (Reach.single (.domain (ProfileR.triple' hw hp)))
      have hadm : J.Admissible (U := U) e' := J.admissible_extension hD he ha
        (fun _ => hn) (fun _ => hnt.2) (fun hnu hnc => by
          rcases hdBefore with hu | hc
          · exact False.elim (hnu hu)
          · exact False.elim (hnc hc))
      have hbody := (ihb _ _ hb e' hadm).1
      have htapp := ((ContextTowerBE.THasTypeBE.subst (.abstraction hb hp)
        (J.typed e)).application hnr).normalize_type hw
      change Ω.THasTypeBE (.app (.lam (D.subst (J.images e)) (b.subst (Expr.liftSub (J.images e)))) n)
        ((B.subst (Expr.liftSub (J.images e))).instantiate n).knf at htapp
      rw [Expr.instantiate_extended,← J.ext_images he] at htapp
      have hbmem : (b.subst (Expr.liftSub (J.images e))).instantiate n ∈ J.R B e' := by
        rwa [Expr.instantiate_extended,← J.ext_images he]
      exact (J.candidate e' (.of_type hb)).expansion _ _ _ [] htapp hDs hbs hnt.2 .nil hbmem
    · rw [J.outside e (.sorted hp) (.inr hKa)]; exact htop
  · rw [J.outside e (.sorted hp) (.inl hK)]; exact htop

/-- Every strongly normalizing term transports under substitution.
The induction also carries the invariant that every prefix of a neutral spine stays in `Ground` (OpenAI's `G_T`). -/
theorem sn_fundamental {M : Expr S} (hs : StronglyNormalizing M) :
    J.Transports (U := U) M := by
  apply StronglyNormalizing.induction_descendants (Q := J.Transports (U := U)) _ hs
  intro M _ ihr ihp Γ A ht e ha
  cases M with
  | var i => exact J.transported_var H ht e ha
  | sort s =>
    obtain ⟨t,hat,hc⟩ := ht.generation
    have hst := HasTypeBE.sort_of_valid ht.valid hat
    exact (J.transported_at_sort hst (Normal.sort s).stronglyNormalizing).convert
      (.inl ⟨t,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | pi D E =>
    obtain ⟨a,b,c,hD,hE,hr,hc⟩ := ht.generation_pi
    have hDs := (ihp D (Expr.ProperPart.child (.pi_domain D E)) _ _ hD e ha).sn (.of_type hD)
    have hEs := J.open_sn hE hD (ihp E (Expr.ProperPart.child (.pi_body D E))) e ha
    exact (J.transported_at_sort (.product hD hE hr) (hDs.pi hEs)).convert
      (.inl ⟨c,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | lam D b =>
    obtain ⟨B,s,hb,hp,hc⟩ := ht.generation_lam
    exact (J.transports_lam H hb hp
      (ihp D (Expr.ProperPart.child (.lam_domain D b)))
      (ihp b (Expr.ProperPart.child (.lam_body D b))) e ha).convert
      (.sorted hp) (.of_type ht) (.symm _ _ hc)
  | app f n =>
    rcases ht.app_spine with hf | ⟨D,b,n',ns,he⟩
    · obtain ⟨D,E,hft,hnt,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hft.product_type_sorted
      have hfr := ihp f (Expr.ProperPart.child (.app_left f n)) _ _ hft e ha
      have hnr := ihp n (Expr.ProperPart.child (.app_right f n)) _ _ hnt e ha
      exact (J.transported_neutral_app H hp hnt hf e hfr hnr).convert
        (.of_type (.application hft hnt)) (.of_type ht) (.symm _ _ hc)
    · have ht' : HasTypeBE P Γ ((Expr.app (.lam D b) n').apps ns) A := he ▸ ht
      have parts : ∀ N, Expr.ProperPart N ((Expr.app (.lam D b) n').apps ns) →
          J.Transports (U := U) N := by
        intro N hN; apply ihp N; change Expr.ProperPart N (.app f n); rwa [he]
      have hlampart : Expr.ProperPart (.lam D b) ((Expr.app (.lam D b) n').apps ns) :=
        (Expr.ProperPart.child (.app_left _ _)).trans_right (Expr.Subterm.apps_head ns)
      obtain ⟨T,hthead⟩ := ht'.apps_head
      obtain ⟨D',E',hlam,hn',_⟩ := hthead.generation_app
      obtain ⟨B,s,hb,hp,_⟩ := hlam.generation_lam
      obtain ⟨a,c,d,hD,_,_,_⟩ := hp.generation_pi
      have hDs := (parts D (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_domain D b)) hlampart) _ _ hD e ha).sn (.of_type hD)
      have hbs := J.open_sn hb hD (parts b (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_body D b)) hlampart)) e ha
      have hnp := (Expr.ProperPart.child (.app_right (.lam D b) n')).trans_right (Expr.Subterm.apps_head ns)
      have hns := (parts n' hnp _ _ hn' e ha).sn (.of_type hn')
      have hargs : StronglyNormalizingArgs (ns.map (Expr.subst (J.images e))) := by
        apply StronglyNormalizingArgs.of_forall
        intro z hz
        rcases List.mem_map.mp hz with ⟨L,hL,rfl⟩
        obtain ⟨Z,hZ⟩ := ht'.apps_arg hL
        exact (parts L (Expr.ProperPart.apps_arg hL) _ _ hZ e ha).sn (.of_type hZ)
      have hred : Beta (.app f n) ((b.instantiate n').apps ns) := by
        rw [he]; exact (Beta.head D b n').apps ns
      have hctr := (ihr _ hred _ _ (ht.subject_reduction hred) e ha).1
      have hctr' : ((b.subst (Expr.liftSub (J.images e))).instantiate (n'.subst (J.images e))).apps
          (ns.map (Expr.subst (J.images e))) ∈ J.R A e := by
        simpa only [Expr.subst_apps,Expr.instantiate_subst] using hctr
      have hty := (ContextTowerBE.THasTypeBE.subst ht' (J.typed e)).normalize_type hw
      rw [Expr.subst_apps] at hty
      have hexp := (J.candidate e (.of_type ht)).expansion _ _ _ _ hty hDs hbs hns hargs hctr'
      constructor
      · rw [he,Expr.subst_apps]
        exact hexp
      · intro hn
        rw [he] at hn
        have hh := hn.apps_head
        cases hh with
        | app hn => cases hn
end ComponentInterface

namespace Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)
/-- `StackAt k T ns` says that the prefix of length `k` of the tower types every tested argument in `ns`.
Each argument is typed at a type whose key is the tested domain. -/
inductive StackAt (k : Nat) : Expr S → List (Expr S) → Prop
  | nil (T) : StackAt k T []
  | cons {D E n ns} (D₀ : Expr S) :
      HasTypeBE P (Ω.context k) (n.rename (Expr.reverseIndex k)) (D₀.rename (Expr.reverseIndex k)) →
      D₀.knf = D.knf →
      StronglyNormalizing n → StackAt k (E.instantiate n).knf ns →
      StackAt k (.pi D E) (n :: ns)
namespace StackAt
variable {Ω} {k j : Nat} {T : Expr S} {ns : List (Expr S)}
theorem mono (h : StackAt Ω k T ns) (hkj : k ≤ j) : StackAt Ω j T ns := by
  induction h with
  | nil T => exact .nil T
  | cons D₀ hn hk hsn _ ih => exact .cons D₀ (Ω.at_mono hn hkj) hk hsn ih

theorem tested (h : StackAt Ω k T ns) : TestedStack Ω T ns := by
  induction h with
  | nil T => exact .nil T
  | cons D₀ hn hk hs _ ih => exact .cons ⟨⟨D₀, ⟨k, hn⟩, hk⟩, hs⟩ ih
end StackAt
namespace TestedStack
variable {Ω} {T : Expr S} {ns : List (Expr S)}
theorem common_stage (h : TestedStack Ω T ns) : ∃ k, StackAt Ω k T ns := by
  induction h with
  | nil T => exact ⟨0,.nil T⟩
  | cons hn _ ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨A₀, ⟨j, hj⟩, hA⟩ := hn.1
    exact ⟨max j k,.cons A₀ (Ω.at_mono hj (le_max_left j k)) hA hn.2 (hk.mono (le_max_right j k))⟩
end TestedStack
end Candidates

namespace ComponentInterface

section
open Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P}
variable {hw : SystemENormalizing' P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

theorem identity_admissible {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) : J.Admissible (U := U) e := by
  intro i B hi
  obtain ⟨s,hB⟩ := HasTypeBE.lookup_sorted (Ω.valid k) hi
  have ht := (J.typed e i B hi).normalize_type hw
  have hG : J.images e i ∈ Ground Ω (B.subst (J.images e)).knf := by
    rw [he] at ht ⊢
    exact var_ground _ ht
  exact ⟨fun _ => (J.candidate e (.sorted hB)).lower hG,
    fun _ => (ground_le_top hG).2,fun _ _ => hG⟩

@[simp] theorem identity_actual {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) (T : Expr S) :
    (T.rename (Expr.reverseIndex k)).subst (J.images e) = T := by
  rw [he,Expr.subst_var_rename,Expr.reverseIndex_twice]

end

open Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P}
variable {hw : SystemENormalizing' P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C) (H : Processed Ω U C)
include J H

theorem run_stack {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k)
    {T : Expr S} {ns : List (Expr S)} (hstack : StackAt Ω k T ns) :
    ∀ {T₀ : Expr S} {s}, HasTypeBE P (Ω.context k) (T₀.rename (Expr.reverseIndex k)) (.sort s) →
    T₀.knf = T → KNormal T → Ω.kprofile T ∈ U ∨ Ω.kprofile T ∈ C →
    ∀ h, h ∈ J.R (T₀.rename (Expr.reverseIndex k)) e → StronglyNormalizing (h.apps ns) := by
  induction hstack with
  | nil T =>
      intro T₀ s ht _ _ _ h hr
      exact (J.candidate e (.sorted ht)).upper hr |>.2
  | @cons D E n ns D₀ hn hD₀ hsn hstack ih =>
      intro T₀ s ht hT₀ hN hprofile h hr
      -- An erasure-normal representative in this prefix that is a product.
      obtain ⟨X, rX, eX⟩ := hE.out _ ht.valid _ ⟨_, .inl ht⟩
      obtain ⟨X₀, rfl, rX₀⟩ := Reduces.rename_inv (ContextTowerBE.reverseIndex_injective k) rX
      have eX₀ : ENormal dz X₀ := by
        unfold ENormal at eX ⊢; rw [Expr.erase_rename] at eX; exact Normal.of_rename _ eX
      have wT₀ : KWN T₀ := by
        have := (ht.kwn hw).rename (Expr.reverseIndex k)
        rwa [Expr.reverseIndex_twice] at this
      have kX : X₀.knf = Expr.pi D E := by
        rw [← hT₀]
        exact Expr.knf_converts (KWN.of_kconverts (.symm _ _ rX₀.k.converts) wT₀) wT₀
          (.symm _ _ rX₀.k.converts)
      have hT₁ := ht.subject_reduces rX
      have hX₀t : Ω.HasTypeBE X₀ (.sort s) := ⟨k, hT₁⟩
      have wX₀ := (hX₀t.kwn_both hE.out).1
      have wDE : KWN (Expr.pi D E) := KWN.of_normal_knf (by rw [hN.knf]; exact hN.1)
      have cX : ConvertsBE X₀ (.pi D E) :=
        (convertsBE_iff_knf_eq wX₀ wDE).2 (kX.trans hN.knf.symm)
      obtain ⟨D₁, E₁, rfl⟩ := hX₀t.pi_shape hE.out eX₀ cX
      have eD₁ : ENormal dz D₁ := (show ENormal dz (.pi D₁ E₁) from eX₀).pi.1
      have eE₁ : ENormal dz E₁ := (show ENormal dz (.pi D₁ E₁) from eX₀).pi.2
      obtain ⟨cD, cE⟩ := cX.product_compatibility dz
      have kD₁ : D₁.knf = D := by
        rw [(convertsBE_iff_knf_eq wX₀.pi_domain wDE.pi_domain).1 cD]; exact hN.pi_domain.knf
      have kE₁ : E₁.knf = E := by
        rw [(convertsBE_iff_knf_eq wX₀.pi_body wDE.pi_body).1 cE]; exact hN.pi_body.knf
      have hr₁ : h ∈ J.R ((Expr.pi D₁ E₁).rename (Expr.reverseIndex k)) e := by
        rw [← J.conversion e (.sorted ht) (.sorted hT₁) (reduces_convertsBE rX)]; exact hr
      have hND := hN.pi_domain
      have hNE := hN.pi_body
      have hPk : Ω.KHasTypeBE (.pi D E) (.sort s) :=
        (ContextTowerBE.KHasTypeBE.of (⟨k, hT₁⟩ : Ω.HasTypeBE (.pi D₁ E₁) (.sort s))).of_knf_eq
          (kX.trans hN.knf.symm) rfl
      have hactual : ActualType Ω (.pi D E) := .inl ⟨hN, s, hPk⟩
      rcases hprofile with hU | hC
      · have htop := (J.candidate e (.sorted hT₁)).upper hr₁
        rw [J.identity_actual he, kX] at htop
        have hg : h ∈ Ground Ω (.pi D E) := by
          rw [H.invariant hactual hU]; exact htop
        exact hg.2 (n :: ns) (.cons ⟨⟨D₀, ⟨k, hn⟩, hD₀⟩, hsn⟩ hstack.tested)
      · obtain ⟨a,b,c,hD,hEt,_,_⟩ := hT₁.generation_pi
        have hn₁ : HasTypeBE P (Ω.context k) (n.rename (Expr.reverseIndex k))
            (D₁.rename (Expr.reverseIndex k)) := by
          apply HasTypeBE.retype_plain hw hn hD
          have w0 := (hn.type_kwn hw)
          have w0' : KWN D₀ := by
            have := w0.rename (Expr.reverseIndex k); rwa [Expr.reverseIndex_twice] at this
          rw [Expr.knf_rename w0', Expr.knf_rename (KWN.of_normal_knf (by rw [kD₁]; exact hND.1)),
            hD₀, kD₁, hND.knf]
        have hnR := (J.sn_fundamental H (hsn.reverseIndex k) _ _ hn₁ e
          (J.identity_admissible he)).1
        have hKC : ProfileR P (Ω.context k) ((Expr.pi D₁ E₁).rename (Expr.reverseIndex k)) ∈ C := by
          rw [← Ω.kprofile_at hw hT₁, Ω.kprofile_of_knf_eq (kX.trans hN.knf.symm)]; exact hC
        have hr' := J.specialization e hT₁ hn₁ hKC
          (by
            change Ω.kprofile (((Expr.pi D₁ E₁).rename (Expr.reverseIndex k)).subst (J.images e)) ∈ C
            rw [J.identity_actual he, Ω.kprofile_of_knf_eq (kX.trans hN.knf.symm)]; exact hC)
          h hr₁ hnR
        change Expr.app h ((n.rename (Expr.reverseIndex k)).subst (J.images e)) ∈
          J.R ((E₁.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) e at hr'
        rw [J.identity_actual he,Expr.instantiate_rename] at hr'
        have htarget : HasTypeBE P (Ω.context k) ((E₁.instantiate n).rename (Expr.reverseIndex k)) (.sort b) := by
          have hti := hEt.instantiate hn₁
          change HasTypeBE P (Ω.context k) ((E₁.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) (.sort b) at hti
          rwa [Expr.instantiate_rename] at hti
        have htT : Ω.HasTypeBE (E₁.instantiate n) (.sort b) := ⟨k, htarget⟩
        have wt := (htT.kwn_both hE.out).1
        have hkey : (E₁.instantiate n).knf = (E.instantiate n).knf := by
          have wE₁ : KWN E₁ := KWN.of_normal_knf (by rw [kE₁]; exact hNE.1)
          have wE : KWN E := KWN.of_normal_knf (by rw [hNE.knf]; exact hNE.1)
          have c1 : KConverts (E₁.instantiate n) (E.instantiate n) := by
            unfold KConverts
            rw [Expr.erase_instantiate, Expr.erase_instantiate]
            exact ConvertsBE.subst (KConverts.of_knf_eq wE₁ wE (kE₁.trans hNE.knf.symm)) _
          exact Expr.knf_converts wt (KWN.of_kconverts (.symm _ _ c1) wt) c1
        have hnT : Ω.THasTypeBE n D := ⟨D₀, ⟨k, hn⟩, hD₀⟩
        have hprofile' : Ω.kprofile (E.instantiate n).knf ∈ U ∨
            Ω.kprofile (E.instantiate n).knf ∈ C := by
          rw [Ω.kprofile_knf]
          have hP₁ : Ω.THasTypeBE (.pi D₁ E₁) (.sort s) := ContextTowerBE.THasTypeBE.of ⟨k, hT₁⟩
          have hn₁T : Ω.THasTypeBE n D₁ := ContextTowerBE.THasTypeBE.of ⟨k, hn₁⟩
          have hpath := Ω.kprofile_instantiate_product_path hw hP₁ hn₁T
          rw [Ω.kprofile_of_knf_eq hkey, Ω.kprofile_of_knf_eq (kX.trans hN.knf.symm)] at hpath
          exact H.before hC hpath.reach
        exact ih htarget hkey
          (Expr.knf_spec (KWN.of_knf_eq hkey.symm wt)).2 hprofile' (.app h n) hr'

/-- Advancing a component uses one evaluation in the identity environment.
It does not make a new choice of substitution at each prefix of the stack. -/
theorem advance {T : Expr S} (hT : ActualType Ω T) (hC : Ω.kprofile T ∈ C) :
    Ground Ω T = Top Ω T := by
  apply Set.Subset.antisymm ground_le_top
  intro h hh
  rcases hT with ⟨hN,s,hks⟩ | ⟨s,rfl⟩
  · refine ⟨hh.1,?_⟩
    intro ns hstack
    obtain ⟨T₀, ⟨ks, ht⟩, hT₀⟩ := ContextTowerBE.KHasTypeBE.sorted_witness Ω hks
    obtain ⟨kn,hs⟩ := hstack.common_stage
    obtain ⟨A₀, ⟨kh,hhT⟩, hA₀⟩ := hh.1
    let k := max ks (max kn kh)
    have hkT : ks ≤ k := le_max_left _ _
    have hkN : kn ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkH : kh ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have ht' := Ω.at_mono ht hkT
    have hh' := Ω.at_mono hhT hkH
    obtain ⟨e,he⟩ := J.inhabit (.var ∘ Expr.reverseIndex k)
      (ContextTowerBE.TTypedSubstitutionBE.of (.identity k))
    have hr := (J.sn_fundamental H (hh.2.reverseIndex k) _ _ hh' e
      (J.identity_admissible he)).1
    rw [J.identity_actual he] at hr
    have hT₀k : HasTypeBE P (Ω.context k) (T₀.rename (Expr.reverseIndex k)) (.sort s) := ht'
    have hA₀k : HasTypeBE P (Ω.context k) (A₀.rename (Expr.reverseIndex k))
        (A₀.rename (Expr.reverseIndex k)) → True := fun _ => trivial
    have hr' : h ∈ J.R (T₀.rename (Expr.reverseIndex k)) e := by
      have hconv : ConvertsBE (A₀.rename (Expr.reverseIndex k)) (T₀.rename (Expr.reverseIndex k)) := by
        have hAt := (show Ω.HasTypeBE h A₀ from ⟨k, hh'⟩)
        rcases hAt.regularity with ⟨u, rfl⟩ | ⟨u, hAu⟩
        · have c := converts_sort_of_knf ((show Ω.HasTypeBE T₀ (.sort s) from ⟨k, ht'⟩).kwn_both hE.out).1
            (by rw [hT₀, ← hA₀, Expr.knf_sort])
          exact (ConvertsBE.rename (.symm _ _ c) _)
        · exact ConvertsBE.rename (ContextTowerBE.converts_of_knf_eq hE.out hAu ⟨k, ht'⟩
            (hA₀.trans hT₀.symm)) _
      rw [← J.conversion e (.of_type hh') (.sorted hT₀k) hconv]
      simpa only [J.identity_actual he] using hr
    exact J.run_stack H he (hs.mono hkN) hT₀k (hT₀.trans hN.knf) hN (.inr hC) h hr'
  · rwa [sort_ground_eq_top]

end ComponentInterface
end

universe u v
open Classical Candidates

theorem _root_.PureTypeSystem.ContextTowerBE.variable_substitution {S : Type u}
    {P : Specification S} (Ω : ContextTowerBE P) {Γ : List (Expr S)} (hΓ : ValidContextBE P Γ) :
    ∃ ρ : Nat → Nat, Ω.TypedSubstitutionBE Γ (Expr.var ∘ ρ) := by
  induction hΓ with
  | nil => exact ⟨id,fun _ _ h => nomatch h⟩
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨ρ,hρ⟩ := ih
    have ht := ContextTowerBE.HasTypeBE.subst hA hρ
    obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
    refine ⟨fun i => match i with | 0 => n | i+1 => ρ i,?_⟩
    convert hρ.cons hn using 1
    funext i; cases i <;> rfl

/-- Induction over the finitely many primary components shows that `Ground` equals `Top` (OpenAI's `⊤_T`) at every actual type. -/
theorem all_ground_eq_top {S : Type u} [Nonempty S] [Fintype S] {P : Specification S}
    [Fact (SystemENormalizing' P)]
    (Ω : ContextTowerBE P) (hw : SystemENormalizing' P)
    (interfaces : ∀ C, IsComponent (PrimaryEdge P) C →
      Nonempty (ComponentInterface.{u,v} Ω hw C)) :
    ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T := by
  intro T hT
  let E := PrimaryEdge P
  have h : ∀ n, ∀ T : Expr S, Reach.rank E (Ω.kprofile T) = n → ActualType Ω T →
      Ground Ω T = Top Ω T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hr hT
      let V := Ω.kprofile T
      let C := Reach.component E V
      let U := {I | Reach.rank E I < n}
      have hC : IsComponent E C := Reach.component_isComponent E V
      have rankC {I} (hi : I ∈ C) : Reach.rank E I = n := by
        exact (Nat.le_antisymm (Reach.rank_mono E hi.2) (Reach.rank_mono E hi.1)).trans hr
      have hp : Processed Ω U C := by
        refine ⟨?_,?_,?_,?_⟩
        · apply Set.disjoint_left.mpr
          intro I hI hc
          have : Reach.rank E I < n := hI
          rw [rankC hc] at this
          exact Nat.lt_irrefl _ this
        · intro I J hj hij
          exact lt_of_le_of_lt (Reach.rank_mono E hij) hj
        · intro I J hj hij
          have hle : Reach.rank E I ≤ n := (Reach.rank_mono E hij).trans (le_of_eq (rankC hj))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact .inl hlt
          · exact .inr ⟨hj.1.trans (Reach.reverse_of_rank_eq E hij (heq.trans (rankC hj).symm)),
              hij.trans hj.2⟩
        · intro A hA hAu
          exact ih _ hAu A rfl hA
      obtain ⟨J⟩ := interfaces C hC
      exact J.advance hp hT (Reach.mem_component E V)
  exact h _ T rfl hT

/-- If `Ground` equals `Top` at every actual type, then a typed application of strongly normalizing terms is strongly normalizing. -/
theorem application_sn_of_ground {S : Type u} [Nonempty S] {P : Specification S}
    [hE : Fact (SystemENormalizing' P)]
    (Ω : ContextTowerBE P) (hw : SystemENormalizing' P)
    (hground : ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T)
    {Γ : List (Expr S)} {f a D E : Expr S}
    (hf : HasTypeBE P Γ f (.pi D E)) (ha : HasTypeBE P Γ a D)
    (hsf : StronglyNormalizing f) (hsa : StronglyNormalizing a) :
    StronglyNormalizing (.app f a) := by
  obtain ⟨ρ,hρ⟩ := Ω.variable_substitution hf.valid
  have hf' := ContextTowerBE.HasTypeBE.subst hf hρ
  have ha' := ContextTowerBE.HasTypeBE.subst ha hρ
  simp only [Expr.subst_var_rename] at hf' ha'
  obtain ⟨s,hpi⟩ := hf.product_type_sorted
  have hpi' := ContextTowerBE.HasTypeBE.subst hpi hρ
  simp only [Expr.subst_var_rename,Expr.rename] at hpi'
  obtain ⟨a',b',c',hD,hE',hr,_⟩ := hpi.generation_pi
  have wP := (hpi'.kwn_both hE.out).1
  have hpNF : ((Expr.pi D E).rename ρ).knf =
      .pi (D.rename ρ).knf (E.rename (Expr.liftRen ρ)).knf :=
    Expr.knf_pi wP.pi_domain wP.pi_body
  have htype : ActualType Ω ((Expr.pi D E).rename ρ).knf :=
    .inl ⟨(Expr.knf_spec wP).2,s,(ContextTowerBE.KHasTypeBE.of hpi').knf hw⟩
  have hfg : f.rename ρ ∈ Ground Ω ((Expr.pi D E).rename ρ).knf := by
    rw [hground htype]
    exact ⟨(ContextTowerBE.THasTypeBE.of hf').normalize_type hw,hsf.rename ρ⟩
  rw [hpNF] at hfg
  have hag : a.rename ρ ∈ Top Ω (D.rename ρ).knf :=
    ⟨(ContextTowerBE.THasTypeBE.of ha').normalize_type hw,hsa.rename ρ⟩
  have hs := (ground_le_top (ground_application hw hfg hag)).2
  exact StronglyNormalizing.of_rename ρ hs

end PureTypeSystem.KP

