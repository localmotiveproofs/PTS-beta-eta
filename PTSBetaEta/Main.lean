module

public import PTSBetaEta.Normalization.Signed
public import PTSBetaEta.Normalization.ObservationCandidates

@[expose] public section

/-!
# Weak βη-normalization implies strong βη-normalization

This file assembles the main theorems for pure type systems whose conversion rule uses βη-conversion (`HasTypeBE`).
If every legal term is weakly βη-normalizing, then every legal term is strongly β-normalizing, and hence strongly βη-normalizing.

The proof uses weak βη-normalization only through its consequence `SystemENormalizing z P`.
This property says that every legal term has a β-reduct with no β-redex outside its λ-domains.
It is used in two places.

* The paradox is OpenAI's argument for the system with β-conversion. It applies here because every term that is legal with β-conversion is also legal with βη-conversion.
* The candidate model in `PTSBetaEta.Normalization` uses OpenAI's three component interpretations. Its candidates are indexed by keys, which are βη-normal forms of erased types, and its observation values are η-canonical.

The reduction to finitely many sorts preserves `SystemENormalizing`, because it only maps sorts to sorts.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PureTypeSystem

universe u

/-! ### Reduction and conversion under maps of sorts -/

theorem Eta.mapSort {S T : Type u} {M N : Expr S} (h : Eta M N) (f : S → T) :
    Eta (M.mapSort f) (N.mapSort f) := by
  induction h with
  | head A F =>
    simpa only [Expr.mapSort, Expr.mapSort_rename] using Eta.head (A.mapSort f) (F.mapSort f)
  | app_left _ ih => exact .app_left ih
  | app_right _ ih => exact .app_right ih
  | lam_domain _ ih => exact .lam_domain ih
  | lam_body _ ih => exact .lam_body ih
  | pi_domain _ ih => exact .pi_domain ih
  | pi_body _ ih => exact .pi_body ih

theorem BetaEta.mapSort {S T : Type u} {M N : Expr S} (h : BetaEta M N) (f : S → T) :
    BetaEta (M.mapSort f) (N.mapSort f) :=
  h.elim (fun h => .inl (h.mapSort f)) (fun h => .inr (h.mapSort f))

theorem ConvertsBE.mapSort {S T : Type u} {M N : Expr S} (h : ConvertsBE M N) (f : S → T) :
    ConvertsBE (M.mapSort f) (N.mapSort f) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.mapSort f)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-! ### Typing with βη-conversion under maps and restrictions of sorts -/

namespace HasTypeBE

variable {S T : Type u} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A)
    (ha : ∀ s t, P.axioms s t → Q.axioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasTypeBE Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha => exact .application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA hc

theorem mapSort {Q : Specification T} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasTypeBE P Γ M A) (f : S → T)
    (ha : ∀ s t, P.axioms s t → Q.axioms (f s) (f t))
    (hr : ∀ a b c, P.rule a b c → Q.rule (f a) (f b) (f c)) :
    HasTypeBE Q (Γ.map (Expr.mapSort f)) (M.mapSort f) (A.mapSort f) := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => simpa only [List.map_cons, Expr.mapSort, Expr.mapSort_rename] using HasTypeBE.var ih
  | weaken _ _ ihM ihA =>
      simpa only [List.map_cons, Expr.mapSort_rename] using HasTypeBE.weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using HasTypeBE.application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA (hc.mapSort f)

theorem has_axiom {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    ∃ s t, P.axioms s t := by
  induction h with
  | ax h => exact ⟨_, _, h⟩
  | var _ ih => exact ih
  | weaken _ _ ih _ => exact ih
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ ih _ => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

theorem restrict_mono {Γ : List (Expr S)} {M A : Expr S}
    {X X' : Finset (S × S)} {R R' : Finset (S × S × S)}
    (h : HasTypeBE (P.restrict X R) Γ M A) (hX : X ⊆ X') (hR : R ⊆ R') :
    HasTypeBE (P.restrict X' R') Γ M A :=
  h.monotone (fun _ _ h => ⟨h.1, hX h.2⟩) (fun _ _ _ h => ⟨h.1, hR h.2⟩)

theorem finite_support {Γ : List (Expr S)} {M A : Expr S} (h : HasTypeBE P Γ M A) :
    ∃ X : Finset (S × S), ∃ R : Finset (S × S × S), HasTypeBE (P.restrict X R) Γ M A := by
  classical
  induction h with
  | ax h => exact ⟨{(_,_)}, ∅, .ax ⟨h, Finset.mem_singleton_self _⟩⟩
  | var _ ih =>
      obtain ⟨X, R, ht⟩ := ih
      exact ⟨X, R, .var ht⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨X, R, hM⟩ := ihM
      obtain ⟨X', R', hA⟩ := ihA
      exact ⟨X ∪ X', R ∪ R', .weaken
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hA.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | @product Γ D E a b c _ _ hr ihD ihE =>
      obtain ⟨X, R, hD⟩ := ihD
      obtain ⟨X', R', hE⟩ := ihE
      refine ⟨X ∪ X', insert (a,b,c) (R ∪ R'), .product
        (hD.restrict_mono Finset.subset_union_left
          (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
        (hE.restrict_mono Finset.subset_union_right
          (Finset.subset_union_right.trans (Finset.subset_insert _ _))) ?_⟩
      exact ⟨hr, Finset.mem_insert_self _ _⟩
  | abstraction _ _ ihb ihPi =>
      obtain ⟨X, R, hb⟩ := ihb
      obtain ⟨X', R', hPi⟩ := ihPi
      exact ⟨X ∪ X', R ∪ R', .abstraction
        (hb.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hPi.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | application _ _ ihf iha =>
      obtain ⟨X, R, hf⟩ := ihf
      obtain ⟨X', R', ha⟩ := iha
      exact ⟨X ∪ X', R ∪ R', .application
        (hf.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (ha.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | conversion _ _ hc ihM ihT =>
      obtain ⟨X, R, hM⟩ := ihM
      obtain ⟨X', R', hT⟩ := ihT
      exact ⟨X ∪ X', R ∪ R', .conversion
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hT.restrict_mono Finset.subset_union_right Finset.subset_union_right) hc⟩

end HasTypeBE

theorem Expr.erase_mapSort {S T : Type u} (f : S → T) (z : S) (M : Expr S) :
    (M.mapSort f).erase (f z) = (M.erase z).mapSort f := by
  induction M <;> simp_all [Expr.mapSort, Expr.erase]

/-- Suppose every legal term of `P` has a β-reduct with no β-redex outside its λ-domains.
Then the same holds for the restriction `P.on D` of `P` to a set `D` of sorts. -/
theorem SystemENormalizing.on {S : Type u} {P : Specification S}
    {D : Set S} (hE₀ : ∀ z : S, SystemENormalizing z P) (z : D) :
    SystemENormalizing z (P.on D) := by
  classical
  let f : S → D := fun s => if h : s ∈ D then ⟨s,h⟩ else z
  have hf : Function.LeftInverse f Subtype.val := by
    intro s
    apply Subtype.ext
    simp only [f, dite_eq_left s.property]
  have hfe : f ∘ Subtype.val = id := funext hf
  have hE := hE₀ z.val
  have back : ∀ {M : Expr D} (X : Expr S),
      Reduces (M.mapSort Subtype.val) X → ENormal z.val X →
      ∃ M', Reduces M M' ∧ ENormal z M' := by
    intro M X hr hn
    refine ⟨X.mapSort f, ?_, ?_⟩
    · simpa only [Expr.mapSort_comp, hfe, Expr.mapSort_id] using hr.mapSort f
    · have key : (X.mapSort f).erase z = (X.erase z.val).mapSort f := by
        have := Expr.erase_mapSort f z.val X
        rwa [hf z] at this
      show Normal ((X.mapSort f).erase z)
      rw [key]
      exact hn.mapSort f
  intro Γ _ M hM
  obtain ⟨A, h | h⟩ := hM
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    obtain ⟨X, hr, hn⟩ := hE _ ht.valid _ ⟨_, Or.inl ht⟩
    exact back X hr hn
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    obtain ⟨X, hr, hn⟩ := hE _ ht.valid _ ⟨_, Or.inr ht⟩
    exact back X hr hn

namespace HasTypeBE

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- If a typed term is not strongly β-normalizing, then there is also such a term over the restriction of `P` to a finite set of sorts.
The restricted specification still gives every legal term a β-reduct with no β-redex outside its λ-domains. -/
theorem finite_counterexample (h : HasTypeBE P Γ M T) (hn : ¬ StronglyNormalizing M)
    (hE : ∀ z : S, SystemENormalizing z P) :
    ∃ D : Finset S, ∃ Γ' : List (Expr {s // s ∈ D}),
      ∃ M' T' : Expr {s // s ∈ D},
        HasTypeBE (P.on (D : Set S)) Γ' M' T' ∧ ¬ StronglyNormalizing M' ∧
          ∀ z : {s // s ∈ D}, SystemENormalizing z (P.on (D : Set S)) := by
  classical
  obtain ⟨X, R, hr⟩ := h.finite_support
  let D := X.biUnion (fun a => {a.1, a.2}) ∪
    R.biUnion (fun r => {r.1, r.2.1, r.2.2})
  have ax_mem {s t : S} (h : (s,t) ∈ X) : s ∈ D ∧ t ∈ D := by
    constructor
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
  have rule_mem {a b c : S} (h : (a,b,c) ∈ R) : a ∈ D ∧ b ∈ D ∧ c ∈ D := by
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
  obtain ⟨s₀, t₀, h₀⟩ := hr.has_axiom
  let d₀ : {s // s ∈ D} := ⟨s₀, (ax_mem h₀.2).1⟩
  let f : S → {s // s ∈ D} := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have f_val {s : S} (h : s ∈ D) : (f s).val = s := by
    simp only [f, dite_eq_left h]
  have ha : ∀ s t, (P.restrict X R).axioms s t →
      (P.on (D : Set S)).axioms (f s) (f t) := by
    intro s t hst
    change P.axioms (f s).val (f t).val
    rw [f_val (ax_mem hst.2).1, f_val (ax_mem hst.2).2]
    exact hst.1
  have hp : ∀ a b c, (P.restrict X R).rule a b c →
      (P.on (D : Set S)).rule (f a) (f b) (f c) := by
    intro a b c habc
    change P.rule (f a).val (f b).val (f c).val
    rw [f_val (rule_mem habc.2).1, f_val (rule_mem habc.2).2.1,
      f_val (rule_mem habc.2).2.2]
    exact habc.1
  exact ⟨D, _, _, _, hr.mapSort f ha hp,
    fun hs => hn (StronglyNormalizing.of_mapSort f hs),
    fun z => SystemENormalizing.on (D := (D : Set S)) hE z⟩

end HasTypeBE

/-! ### The paradox -/

namespace Labelled

/-- OpenAI's `no_proof_at_target`, proved from the hypothesis that every term that is legal with βη-conversion has a β-reduct with no β-redex outside its λ-domains. -/
theorem no_proof_at_target_be {S : Type u} (z : S) {P : Specification S}
    (hw : SystemENormalizing z P) {Γ : List (Expr S)} {γ : Nat → Mode}
    {M T : Expr S} (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) : False := by
  have he := h.erase
  obtain ⟨N, hN, hEN⟩ := hw _ (.of_validContext he.valid) _ (.of_legal ⟨_, .inl he⟩)
  obtain ⟨M', hMM', heq, ht⟩ := h.lift_erased_reduces hN
  have hEN' : ENormal z M'.erase := by rw [heq]; exact hEN
  exact no_enormal_proof z hΓ hT ht (hm.reduces hMM') hEN'

end Labelled

open Labelled in
/-- OpenAI's relational exclusion, proved from the same hypothesis on the β-reducts of terms that are legal with βη-conversion. -/
theorem relational_exclusion_be {S : Type u} [Fintype S] {P : Specification S}
    (hw : ∀ z : S, SystemENormalizing z P) : RelationalExclusion P := by
  intro C hC ho ht hf
  have hz : Nonempty S := by
    obtain ⟨I, _, _, h, _⟩ := ht
    obtain ⟨s, _⟩ := h.domain.1
    exact ⟨s⟩
  obtain ⟨z⟩ := hz
  obtain ⟨Γ,γ,hΓ,⟨L⟩⟩ := LogicSetup.exists_setup C hC ho ht
  obtain ⟨K,⟨R⟩⟩ := ChannelSetup.exists_setup_return (L := L) hC ho hf
  let KY := L.quantifiers K.logicalVertex K.directLogical
  let KQ := L.quantifiers K.predVertex K.directPred
  obtain ⟨b,hb,mb⟩ := R.specialized_formed.relational_bottom KY KQ
  exact no_proof_at_target_be z (hw z) hΓ
    ⟨.terminal (L.witnesses.allData L.base L.triple.codomain),
      L.witnesses.normal L.base L.triple.codomain⟩ hb mb

/-! ### The case split on components and the theorem for finitely many sorts -/

namespace KP

/-- Every component of the primary graph has an interpretation, chosen by OpenAI's case split.
If the component has no closed signed path of sign `true`, the signed interpretation is used.
Otherwise, if the component contains no profile triple, the one-child interpretation is used.
In the remaining case the observation values are used, and this is where relational exclusion is needed. -/
theorem interfaces_of_exclusionBE {S : Type u} [Fintype S] [Nonempty S] {P : Specification S}
    [Fact (SystemENormalizing' P)]
    (Ω : ContextTowerBE P) (hw : SystemENormalizing' P) (he : RelationalExclusion P)
    (C : Set (Set S)) (hC : IsComponent (PrimaryEdge P) C) :
    Nonempty (ComponentInterface.{u,u} Ω hw C) := by
  by_cases ho : ∃ I ∈ C, SignedPath (PrimaryEdge P) I I true
  · by_cases ht : ∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C
    · exact ⟨ObservationValues.componentInterface Ω C (he C hC ho ht) hC⟩
    · exact ⟨OneChildInterpretation.componentInterface Ω C hw hC
        (fun h hi hj hk => ht ⟨_,_,_,h,hi,hj,hk⟩)⟩
  · exact ⟨SignedInterpretation.componentInterface Ω hC hw
      (fun I hi hp => ho ⟨I,hi,hp⟩)⟩

/-- For a finite type of sorts, the hypothesis on β-reducts and relational exclusion together give strong β-normalization of every legal term. -/
theorem finite_normalizationBE {S : Type u} [Fintype S] [Nonempty S] {P : Specification S}
    [Fact (SystemENormalizing' P)] (hw : SystemENormalizing' P) (he : RelationalExclusion P) :
    SystemBetaSNBE P := by
  apply stronglyNormalizing_of_applicationBE
  intro Γ f a D E hf ha hsf hsa
  obtain ⟨s,t,hat⟩ := hf.has_axiom
  let Ω := ContextTowerBEConstruction.tower P hat
  exact application_sn_of_ground Ω hw
    (all_ground_eq_top Ω hw (interfaces_of_exclusionBE Ω hw he)) hf ha hsf hsa

end KP

/-! ### Main theorems -/

/-- **Erasure-normal reducts imply strong β-normalization.**
Suppose every legal term of `PTS_βη` has a β-reduct with no β-redex outside its λ-domains.
Then every legal term is strongly β-normalizing.
No assumption is made on the sorts, axioms or rules.
The erasure replaces each λ-domain by a sort `z`, and the hypothesis is required for every `z`.
Whether an erased term is β-normal does not depend on the choice of `z`. -/
theorem strong_beta_of_eNormalizing_BE {S : Type u} (P : Specification S)
    (hE : ∀ z : S, SystemENormalizing z P) : SystemBetaSNBE P := by
  by_contra hn
  obtain ⟨Γ,f,a,D,E,hf,ha,hsf,hsa,hbad⟩ := exists_bad_applicationBE hn
  have htype := HasTypeBE.application hf ha
  obtain ⟨F,Γ',M',T',ht,hn',hE'⟩ := htype.finite_counterexample hbad hE
  have : Nonempty {s // s ∈ F} := by
    obtain ⟨s, _, _⟩ := ht.has_axiom
    exact ⟨s⟩
  have : Fact (SystemENormalizing' (P.on (F : Set S))) := ⟨hE' dz⟩
  have hsn := KP.finite_normalizationBE (hE' dz) (relational_exclusion_be hE')
  exact hn' (hsn Γ' ht.valid M' ⟨T',.inl ht⟩)

/-- **Weak βη-normalization implies strong β-normalization** for `PTS_βη`.
If every legal term is weakly βη-normalizing, then every legal term is strongly β-normalizing. -/
theorem weak_betaEta_implies_strong_beta_BE {S : Type u} (P : Specification S)
    (hw : SystemWeaklyNormalizingBE P) : SystemBetaSNBE P :=
  strong_beta_of_eNormalizing_BE P (fun z => hw.eNormalizing z)

theorem Normal.erase' {S : Type u} (z : S) {N : Expr S} (h : Normal N) : Normal (N.erase z) := by
  intro G hG
  obtain ⟨N', hN', _⟩ := Beta.of_erase z hG
  exact h N' hN'

/-- **Weak β-normalization implies strong β-normalization** for `PTS_βη`.
If every legal term is weakly β-normalizing, then every legal term is strongly β-normalizing. -/
theorem weak_beta_implies_strong_beta_BE {S : Type u} (P : Specification S)
    (hw : ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → WeaklyNormalizing M) :
    SystemBetaSNBE P :=
  strong_beta_of_eNormalizing_BE P (fun z Γ hΓ M hM => by
    obtain ⟨N, hr, hN⟩ := hw Γ hΓ M hM
    exact ⟨N, hr, Normal.erase' z hN⟩)

/-- **Weak β-normalization implies strong βη-normalization** for `PTS_βη`.
This is the second theorem of `Challenge.lean`. -/
theorem weak_beta_implies_strong_betaEta_BE {S : Type u} (P : Specification S)
    (hw : ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → WeaklyNormalizing M) :
    SystemStronglyNormalizingBE P :=
  fun Γ hΓ M hM => (weak_beta_implies_strong_beta_BE P hw Γ hΓ M hM).betaEta

/-- **Weak βη-normalization implies strong βη-normalization** for `PTS_βη`.
If every legal term is weakly βη-normalizing, then every legal term is strongly βη-normalizing.
This is the βη version of the Barendregt–Geuvers–Klop conjecture for `PTS_βη`, and the first theorem of `Challenge.lean`. -/
theorem weak_betaEta_implies_strong_betaEta_BE {S : Type u} (P : Specification S)
    (hw : SystemWeaklyNormalizingBE P) : SystemStronglyNormalizingBE P :=
  fun Γ hΓ M hM => (weak_betaEta_implies_strong_beta_BE P hw Γ hΓ M hM).betaEta

end PureTypeSystem
