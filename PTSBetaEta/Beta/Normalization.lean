/- Modified from OpenAI's `Normalization.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Beta.Restriction
public import PTSBetaEta.Beta.Components
public import PTSBetaEta.Beta.Signed
public import PTSBetaEta.Beta.OneChild
public import PTSBetaEta.Beta.ObservationCandidates
public import PTSBetaEta.Beta.Diagonal

@[expose] public section


namespace PureTypeSystem

section
universe u
open Classical

/-- Relational exclusion for the finite components of the profile graph.
This internal proposition is proved from weak normalization, and the main theorem does not assume it. -/
def RelationalExclusion {S : Type u} (P : Specification S) : Prop :=
  ∀ C, IsComponent (PrimaryEdge P) C →
    (∃ I ∈ C, SignedPath (PrimaryEdge P) I I true) →
    (∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C) →
    ¬ ForbiddenConfiguration P C

/-- The three candidate models, chosen by the case split of the preprint.
The interface for exclusion is kept separate, and it is not hidden inside a law of candidates. -/
theorem interfaces_of_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P) (he : RelationalExclusion P)
    (C : Set (Set S)) (hC : IsComponent (PrimaryEdge P) C) :
    Nonempty (ComponentInterface.{u,u} Ω hw C) := by
  by_cases ho : ∃ I ∈ C, SignedPath (PrimaryEdge P) I I true
  · by_cases ht : ∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C
    · exact ⟨ObservationValues.componentInterface Ω C (he C hC ho ht) hC⟩
    · exact ⟨OneChildInterpretation.componentInterface Ω C hw hC
        (fun h hi hj hk => ht ⟨_,_,_,h,hi,hj,hk⟩)⟩
  · exact ⟨SignedInterpretation.componentInterface Ω hC hw
      (fun I hi hp => ho ⟨I,hi,hp⟩)⟩

theorem finite_normalization_of_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (hw : SystemWeaklyNormalizing P) (he : RelationalExclusion P) :
    SystemStronglyNormalizing P := by
  apply stronglyNormalizing_of_application
  intro Γ f a D E hf ha hsf hsa
  obtain ⟨s,t,hat⟩ := hf.has_axiom
  let Ω := ContextTowerConstruction.tower P hat
  exact application_sn_of_ground Ω hw
    (all_ground_eq_top Ω hw (interfaces_of_exclusion Ω hw he)) hf ha hsf hsa

/-- Restriction to finitely many sorts keeps open contexts, annotations and every rule of the given PTS.
So the main theorem follows once typed relational exclusion is proved for finite specifications.
The main theorem is not replaced by a statement about finite specifications only. -/
theorem normalization_of_finite_exclusion
    (exclude : ∀ (S : Type u) [Fintype S] (P : Specification S),
      SystemWeaklyNormalizing P → RelationalExclusion P)
    {S : Type u} {P : Specification S} (hw : SystemWeaklyNormalizing P) :
    SystemStronglyNormalizing P := by
  by_contra hn
  obtain ⟨Γ,f,a,D,E,hf,ha,hsf,hsa,hbad⟩ := exists_bad_application hn
  have htype := HasType.application hf ha
  obtain ⟨F,Γ',M',T',ht,hn',hw'⟩ := htype.finite_counterexample hbad hw
  have hsn := finite_normalization_of_exclusion hw' (exclude _ _ hw')
  exact hn' (hsn Γ' ht.valid M' ⟨T',.inl ht⟩)

end

universe u
open Labelled
/-- Relational exclusion, proved with the concrete illative encoding in a finite ambient context.
It is not supplied as an axiom. -/
theorem relational_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (hw : SystemWeaklyNormalizing P) : RelationalExclusion P := by
  intro C hC ho ht hf
  obtain ⟨Γ,γ,hΓ,⟨L⟩⟩ := LogicSetup.exists_setup C hC ho ht
  obtain ⟨K,⟨R⟩⟩ := ChannelSetup.exists_setup_return (L := L) hC ho hf
  let KY := L.quantifiers K.logicalVertex K.directLogical
  let KP := L.quantifiers K.predVertex K.directPred
  obtain ⟨b,hb,mb⟩ := R.specialized_formed.relational_bottom KY KP
  exact no_proof_at_target hw hΓ
    ⟨.terminal (L.witnesses.allData L.base L.triple.codomain),L.witnesses.normal L.base L.triple.codomain⟩ hb mb

/-- **Weak normalization implies strong normalization** for every PTS, with arbitrary types of sorts, rules that need not be functional, and annotated terms. -/
theorem weak_implies_strong {S : Type u} (P : Specification S)
    (h : SystemWeaklyNormalizing P) : SystemStronglyNormalizing P :=
  normalization_of_finite_exclusion (fun _ _ _ hw => relational_exclusion hw) h
end PureTypeSystem

