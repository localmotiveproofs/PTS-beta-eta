/- Adapted to typing with βη-conversion from OpenAI's `Signed.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Components

@[expose] public section

/-!
# Case 1 for typing with βη-conversion: components without an odd closed walk

This file adapts OpenAI's `Signed.lean` (`PTSBetaEta.Beta.Signed`) to typing with βη-conversion, with candidates indexed by keys.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem.KP.SignedInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemENormalizing' P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Vector := (T : Expr S) → SignedCandidate Ω T (hC.signing (Ω.kprofile T))

noncomputable def value (v : Vector Ω hC) (T : Expr S) : Set (Expr S) :=
  if Ω.kprofile T ∈ C then (v T).set else Top Ω T

theorem value_candidate (v : Vector Ω hC) (T : Expr S) :
    IsCandidate Ω T (value Ω hC v T) := by
  unfold value; split
  · exact (v T).candidate
  · exact top_candidate

theorem value_forward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.kprofile T ∈ C → hC.signing (Ω.kprofile T) = false) :
    value Ω hC v T ⊆ value Ω hC w T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,Bool.false_eq_true,ite_false] using hh
  · exact Set.Subset.rfl

theorem value_backward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.kprofile T ∈ C → hC.signing (Ω.kprofile T) = true) :
    value Ω hC w T ⊆ value Ω hC v T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,ite_true] using hh
  · exact Set.Subset.rfl

noncomputable def stepCandidate (v : Vector Ω hC) (T : Expr S) : Candidate Ω T :=
  match T with
  | .pi D E =>
    if KNormal (.pi D E) ∧ (∃ s, Ω.KHasTypeBE (.pi D E) (.sort s)) ∧ Ω.kprofile (.pi D E) ∈ C then
      ⟨ProductTest Ω D E (value Ω hC v D) (fun n => {value Ω hC v (E.instantiate n).knf}),
        productTest_candidate hw (value_candidate Ω hC v D).upper (by
          intro n _ X hX
          rcases Set.mem_singleton_iff.mp hX with rfl
          exact value_candidate Ω hC v _)⟩
    else ⟨Top Ω (.pi D E),top_candidate⟩
  | T => ⟨Top Ω T,top_candidate⟩

noncomputable def step (v : Vector Ω hC) : Vector Ω hC :=
  fun T => SignedCandidate.wrap (stepCandidate Ω hC hw v T)

include hno in
theorem step_monotone : Monotone (step Ω hC hw) := by
  intro v w hv T
  apply (SignedCandidate.order _ _).mpr
  simp only [step,SignedCandidate.set_wrap]
  cases T with
  | sort s => cases hC.signing (Ω.kprofile (.sort s)) <;> exact Set.Subset.rfl
  | var i => cases hC.signing (Ω.kprofile (.var i)) <;> exact Set.Subset.rfl
  | lam D E => cases hC.signing (Ω.kprofile (.lam D E)) <;> exact Set.Subset.rfl
  | app f n => cases hC.signing (Ω.kprofile (.app f n)) <;> exact Set.Subset.rfl
  | pi D E =>
    dsimp only [stepCandidate]
    by_cases H : KNormal (.pi D E) ∧ (∃ s, Ω.KHasTypeBE (.pi D E) (.sort s)) ∧
        Ω.kprofile (.pi D E) ∈ C
    · simp only [ite_eq_left H]
      obtain ⟨hn,⟨s,ht⟩,hpC⟩ := H
      have hd : ∀ hD : Ω.kprofile D ∈ C,
          hC.signing (Ω.kprofile (.pi D E)) = Bool.xor (hC.signing (Ω.kprofile D)) true := by
        intro hD
        obtain ⟨J, hglob⟩ := Ω.kprofile_triple hw ht
        exact hC.signing_cross hno hD hpC (.singleton (.domain hglob))
      have he : ∀ n, Ω.THasTypeBE n D → Ω.kprofile (E.instantiate n).knf ∈ C →
          hC.signing (Ω.kprofile (E.instantiate n).knf) = hC.signing (Ω.kprofile (.pi D E)) := by
        intro n hn hnc
        rw [Ω.kprofile_knf] at hnc ⊢
        simpa only [Bool.xor_false] using
          (hC.signing_cross hno hnc hpC
            (Ω.kprofile_instantiate_product_path_k hw ht hn.toK).parity).symm
      have flip (a b : Bool) (h : a = Bool.xor b true) : b = !a := by
        cases a <;> cases b <;> cases h <;> rfl
      cases hs : hC.signing (Ω.kprofile (.pi D E)) with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC v D := value_backward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_forward Ω hC hv (fun hc => (he n (value_candidate Ω hC w D |>.upper hn).1 hc).trans hs) hout
      | true =>
        simp only [ite_true]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC w D := value_forward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_backward Ω hC hv (fun hc => (he n (value_candidate Ω hC v D |>.upper hn).1 hc).trans hs) hout
    · simp only [ite_eq_right H]
      cases hC.signing (Ω.kprofile (.pi D E)) <;> exact Set.Subset.rfl

noncomputable def operator : Vector Ω hC →o Vector Ω hC :=
  ⟨step Ω hC hw,step_monotone Ω hC hw hno⟩

noncomputable def fixed : Vector Ω hC := (operator Ω hC hw hno).lfp

noncomputable def actual (T : Expr S) : Set (Expr S) := value Ω hC (fixed Ω hC hw hno) T

theorem actual_candidate (T : Expr S) : IsCandidate Ω T (actual Ω hC hw hno T) :=
  value_candidate Ω hC _ T

theorem actual_outside {T : Expr S} (ho : Ω.kprofile T ∉ C) : actual Ω hC hw hno T = Top Ω T := by
  simp only [actual,value,ho,ite_false]

theorem actual_product {D E : Expr S} {s : S} (hn : KNormal (.pi D E))
    (ht : Ω.KHasTypeBE (.pi D E) (.sort s)) (hc : Ω.kprofile (.pi D E) ∈ C) :
    actual Ω hC hw hno (.pi D E) =
      ProductTest Ω D E (actual Ω hC hw hno D) (fun n => {actual Ω hC hw hno (E.instantiate n).knf}) := by
  have he := congrArg (fun v : Vector Ω hC => (v (.pi D E)).set) (operator Ω hC hw hno).map_lfp
  change (step Ω hC hw (fixed Ω hC hw hno) (.pi D E)).set = _ at he
  dsimp only [step,SignedCandidate.set_wrap,stepCandidate] at he
  rw [ite_eq_left (show KNormal (.pi D E) ∧ (∃ s, Ω.KHasTypeBE (.pi D E) (.sort s)) ∧
    Ω.kprofile (.pi D E) ∈ C from ⟨hn,⟨s,ht⟩,hc⟩)] at he
  simpa only [actual,value,hc,ite_true,SignedCandidate.set_wrap,fixed] using he.symm
end

universe u
open Classical Candidates
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemENormalizing' P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Environment (Γ : List (Expr S)) := {σ : Nat → Expr S // Ω.TTypedSubstitutionBE Γ σ}

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  if ProfileR P Γ A ∈ C then actual Ω hC hw hno (A.subst e.val).knf
  else Top Ω (A.subst e.val).knf

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.val).knf (R Ω hC hw hno A e) := by
  unfold R; split
  · exact actual_candidate Ω hC hw hno _
  · exact top_candidate

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ)
    (ho : ProfileR P Γ A ∉ C ∨ Ω.kprofile (A.subst e.val) ∉ C) :
    R Ω hC hw hno A e = Top Ω (A.subst e.val).knf := by
  unfold R; split
  · exact actual_outside Ω hC hw hno (by
      rw [Ω.kprofile_knf]; exact ho.resolve_left (not_not.mpr ‹_›))
  · rfl

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (e : Environment Ω Γ) (hA : ExpectedBE P Γ A) (hB : ExpectedBE P Γ B) (hc : ConvertsBE A B) :
    R Ω hC hw hno A e = R Ω hC hw hno B e := by
  have hp := ExpectedBE.profileR_eq hw hA hB hc
  have hn := Expr.knf_converts (hA.subst_wn hw e.property) (hB.subst_wn hw e.property)
    (hc.subst e.val).k
  simp only [R,hp,hn]

theorem actual_sort (s : S) : actual Ω hC hw hno (.sort s) = Top Ω (.sort s) := by
  by_cases hc : Ω.kprofile (.sort s) ∈ C
  · have he := congrArg (fun v : Vector Ω hC => (v (.sort s)).set) (operator Ω hC hw hno).map_lfp
    change (step Ω hC hw (fixed Ω hC hw hno) (.sort s)).set = _ at he
    simpa only [step,stepCandidate,SignedCandidate.set_wrap,actual,value,hc,ite_true,fixed] using he.symm
  · exact actual_outside Ω hC hw hno hc

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω hC hw hno (.sort s) e = Top Ω (.sort s) := by
  simp only [R,Expr.subst,Expr.knf_of_normal (KNormal.sort s),actual_sort,ite_self]

theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasTypeBE P Γ D (.sort s)) (hA : ExpectedBE P Γ A)
    (he : f.val = Expr.extend e.val n) :
    R Ω hC hw hno (A.rename Nat.succ) f = R Ω hC hw hno A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω hC hw hno a f).trans (R_sort Ω hC hw hno a e).symm
  · simp only [R,ProfileR.weaken' hw hA hD,he,Expr.subst_raise_extend]

theorem R_before {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) (e : Environment Ω Γ)
    (hp : ∃ K ∈ C, Reach (PrimaryEdge P) (ProfileR P Γ A) K) :
    R Ω hC hw hno A e = actual Ω hC hw hno (A.subst e.val).knf := by
  unfold R; split
  · rfl
  · rename_i hn
    refine (actual_outside Ω hC hw hno ?_).symm
    rw [Ω.kprofile_knf]
    intro ha
    obtain ⟨K,hK,hp⟩ := hp
    exact hn (hC.between ha hK (Ω.kprofile_subst_path hw hA e.property).reach hp)

/-- The fixed point at a product type tests exactly the arguments, which need not be normal. -/
theorem actual_raw_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (e : Environment Ω Γ)
    (ha : Ω.kprofile ((Expr.pi D E).subst e.val) ∈ C) (h : Expr S) :
    h ∈ actual Ω hC hw hno ((Expr.pi D E).subst e.val).knf ↔
    h ∈ Top Ω ((Expr.pi D E).subst e.val).knf ∧
      ∀ n, n ∈ actual Ω hC hw hno (D.subst e.val).knf →
        Expr.app h n ∈ actual Ω hC hw hno (E.subst (Expr.extend e.val n)).knf := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTowerBE.THasTypeBE.subst hp e.property
  have hwraw := hraw.kwn hw
  change KWN (.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))) at hwraw
  have hparts : KWN (D.subst e.val) ∧ KWN (E.subst (Expr.liftSub e.val)) :=
    ⟨hwraw.pi_domain, hwraw.pi_body⟩
  have hnf := Expr.knf_pi hparts.1 hparts.2
  have hpN := hraw.toK.knf hw
  change Ω.KHasTypeBE (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).knf (.sort s) at hpN
  rw [hnf] at hpN
  have hNC : Ω.kprofile (.pi (D.subst e.val).knf (E.subst (Expr.liftSub e.val)).knf) ∈ C := by
    rw [← hnf,Ω.kprofile_knf]; exact ha
  have hnormal : KNormal (.pi (D.subst e.val).knf (E.subst (Expr.liftSub e.val)).knf) :=
    .pi (Expr.knf_spec hparts.1).2 (Expr.knf_spec hparts.2).2
  have hbody (n : Expr S) (hn : n ∈ actual Ω hC hw hno (D.subst e.val).knf) :
      (E.subst (Expr.extend e.val n)).knf =
        ((E.subst (Expr.liftSub e.val)).knf.instantiate n).knf := by
    have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
    have hrawD := ContextTowerBE.THasTypeBE.subst hD e.property
    have hnr := hnt.conversion hrawD
      (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
    have htarget := ContextTowerBE.THasTypeBE.subst hE (e.property.cons hnr)
    obtain ⟨t,ht⟩ := Ω.kframe_target_sorted hpN hnt.toK
    have hr : KConverts (E.subst (Expr.extend e.val n))
        ((E.subst (Expr.liftSub e.val)).knf.instantiate n) := by
      rw [← Expr.instantiate_extended]
      unfold KConverts
      rw [Expr.erase_instantiate, Expr.erase_instantiate]
      exact ConvertsBE.subst (Expr.knf_spec hparts.2).1.converts (Expr.single (n.erase dz))
    exact Expr.knf_converts (htarget.kwn hw) (ht.kwn hw) hr
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).knf ↔
    h ∈ Top Ω (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).knf ∧ _
  rw [hnf,actual_product Ω hC hw hno hnormal hpN hNC]
  constructor
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn
    rw [hbody n hn]
    exact hb n hn _ (Set.mem_singleton _)
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    rw [← hbody n hn]
    exact hb n hn

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasTypeBE P Γ (.pi D E) (.sort s))
    (hg : ProfileR P Γ (.pi D E) ∈ C) (ha : Ω.kprofile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (ht : h ∈ Top Ω ((Expr.pi D E).subst e.val).knf)
    (hb : ∀ n, n ∈ R Ω hC hw hno D e → ∀ f : Environment Ω (D :: Γ),
      f.val = Expr.extend e.val n → Expr.app h n ∈ R Ω hC hw hno E f) :
    h ∈ R Ω hC hw hno (.pi D E) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := ProfileR.triple' hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  simp only [R,hg,ite_true]
  apply (actual_raw_product Ω hC hw hno hp e ha h).mpr
  refine ⟨ht,?_⟩
  intro n hn
  have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
  have hrawD := ContextTowerBE.THasTypeBE.subst hD e.property
  have hnr := hnt.conversion hrawD
    (.symm _ _ (Expr.knf_spec (hrawD.kwn hw)).1.converts)
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.val n,e.property.cons hnr⟩
  have he := R_before Ω hC hw hno hE f ⟨_,hg,.single (.codomain hf)⟩
  have hh := hb n (hd.symm ▸ hn) f rfl
  exact he ▸ hh

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hN : HasTypeBE P Γ N D)
    (hg : ProfileR P Γ (.pi D E) ∈ C) (ha : Ω.kprofile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (hh : h ∈ R Ω hC hw hno (.pi D E) e)
    (hn : N.subst e.val ∈ R Ω hC hw hno D e) :
    Expr.app h (N.subst e.val) ∈ R Ω hC hw hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := ProfileR.triple' hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  have he := R_before Ω hC hw hno (hE.instantiate hN) e
    ⟨_,hg,(ProfileR.instantiate_product_path hw hp hN).reach⟩
  simp only [R,hg,ite_true] at hh
  have hout := (actual_raw_product Ω hC hw hno hp e ha h).mp hh |>.2 _ (hd ▸ hn)
  rw [he,← Expr.instantiate_subst,Expr.instantiate_extended]
  exact hout

noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Subtype.val
  typed := Subtype.property
  inhabit σ hσ := ⟨⟨σ,hσ⟩,rfl⟩
  Ext e f n := f.val = Expr.extend e.val n
  ext_images he := he
  extend e _ _ hn := ⟨⟨_,e.property.cons hn⟩,rfl⟩
  R := R Ω hC hw hno
  candidate e _ := R_candidate Ω hC hw hno _ e
  conversion e ha hb hc := R_conversion Ω hC hw hno e ha hb hc
  outside e _ ho := R_outside Ω hC hw hno _ e ho
  weakening hd he hx := R_weakening Ω hC hw hno hd he hx
  product_intro e hp hg ha h ht hb := product_intro Ω hC hw hno e hp hg ha h ht hb
  specialization e hp hn hg ha h hh hN := specialization Ω hC hw hno e hp hn hg ha h hh hN

end PureTypeSystem.KP.SignedInterpretation

