module

public import PTSBetaEta.Eta.Faithful

@[expose] public section

/-!
# OpenAI's paradox under weak βη-normalization

The paradox half of OpenAI's proof (`relational_exclusion`) uses weak normalization at exactly one point, the lemma `no_proof_at_target`.
There a legal proof of a positive target is normalized, and normal proofs are ruled out by an argument about their shape (`no_normal_proof`).

That shape argument only looks at application spines and λ-bodies, and never at λ-domains.
So it also works for proofs that are normal outside their λ-domains, and weak βη-normalization supplies such proofs (`erasure_normalizes_of_betaEta`).
Everything else is reused unchanged from OpenAI's library, including the illative encoding, the channel and logic setups, and the specialized relational bottom.
-/

namespace PureTypeSystem

universe u

namespace Labelled

variable {S : Type u} (z : S)

namespace WellModed

variable {γ : Nat → Mode}

theorem enormal_proof_shape {M : Expr S} (h : WellModed γ M .proof)
    (hn : ENormal z M.erase) : (∃ l A b, M = .lam l A b) ∨ M.Neutral := by
  induction M generalizing γ with
  | var n => exact .inr (.var n)
  | sort s => cases h
  | pi l A B ihA ihB => cases h
  | lam l A b ihA ihb => exact .inl ⟨_, _, _, rfl⟩
  | app l f a ihf iha =>
      obtain ⟨hl, hf, _⟩ := h.app_inv
      have hn' : ENormal z (PureTypeSystem.Expr.app f.erase a.erase) := hn
      obtain ⟨hnf, _, hnl⟩ := hn'.app
      obtain ⟨k, A, b, rfl⟩ | hf' := ihf (hl ▸ hf) hnf
      · exact False.elim (hnl _ _ rfl)
      · exact .inr (.app hf')

end WellModed

namespace Expr.Neutral

variable {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}

theorem first_target_e (hM : M.Neutral) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : ENormal z M.erase) (hΓ : ProofContext Γ γ) :
    (∃ n, M = .var n) ∨
    ∃ Q R, Q.weight < M.weight ∧ R.Target ∧ HasType P Γ Q R ∧
      WellModed γ Q .proof ∧ ENormal z Q.erase := by
  induction hM generalizing T with
  | var n => exact .inl ⟨n, rfl⟩
  | @app l f a hM ih =>
      have hn' : ENormal z (PureTypeSystem.Expr.app f.erase a.erase) := hn
      obtain ⟨hnf, hna, _⟩ := hn'.app
      obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
      obtain ⟨hl, hmf, hma⟩ := hm.app_inv
      have hmf' : WellModed γ f .proof := hl ▸ hmf
      obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ := ih hf hmf' hnf
      · obtain ⟨A, hlookup, hc⟩ := hf.generation
        obtain ⟨R, F, rfl, hR⟩ := hΓ n A hlookup hmf'.var_inv
        obtain ⟨rfl, hDR, _⟩ := hc.product_compatibility
        obtain ⟨r, hPi⟩ := (HasType.lookup h.valid hlookup).product_type_sorted
        obtain ⟨s, hs⟩ := hPi.product_domain _ _ _ rfl
        exact .inr ⟨a, R, by simp only [weight]; omega, hR,
          .conversion ha hs hDR, hma, hna⟩
      · exact .inr ⟨Q, R, by simp only [weight]; omega, hR, hQR, hmode, hnorm⟩

end Expr.Neutral

/-- There is no proof of a positive target that is normal outside its λ-domains.
The argument is the one of OpenAI's `no_normal_proof`. -/
theorem no_enormal_proof {P : Specification S}
    {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}
    (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : ENormal z M.erase) : False := by
  induction M using (measure Expr.weight).wf.induction generalizing Γ γ T with
  | h M ih =>
      obtain ⟨l, A, b, rfl⟩ | hneutral := hm.enormal_proof_shape z hn
      · obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
        obtain ⟨hl, _, hmb⟩ := hm.lam_inv
        obtain ⟨rfl, D, E, rfl, hE, hAD, hBE⟩ := hT.product hl (.symm _ _ hc)
        obtain ⟨r, hTsort⟩ := h.abstraction_type_sorted
        obtain ⟨_, _, _, hD, hEopen, _, _⟩ := hTsort.generation_pi
        obtain ⟨_, hA⟩ := hPi.product_domain _ _ _ rfl
        have hEsort := hEopen.context_head_conversion hD hA (.symm _ _ hAD)
        have hbody := HasType.conversion hb hEsort hBE
        have hn' : ENormal z (PureTypeSystem.Expr.lam A.erase b.erase) := hn
        exact ih b (by change b.weight < 1 + A.weight + b.weight; omega)
          (hΓ.data_cons A) hE hbody hmb hn'.lam
      · obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ :=
          hneutral.first_target_e z h hm hn hΓ
        · obtain ⟨A, hlookup, hc⟩ := h.generation
          obtain ⟨R, F, rfl, _⟩ := hΓ n A hlookup hm.var_inv
          have hl := (hT.product rfl (.symm _ _ hc)).1
          cases hl
        · exact ih Q hQ hΓ hR hQR hmode hnorm

/-- OpenAI's `no_proof_at_target`, proved from weak βη-normalization of the system with β-conversion. -/
theorem no_proof_at_target_betaEta (z : S) {P : Specification S}
    (hw : SystemWeaklyNormalizingBetaEta P) {Γ : List (Expr S)} {γ : Nat → Mode}
    {M T : Expr S} (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) : False := by
  have he := h.erase
  obtain ⟨N, hN, hEN⟩ := SystemWeaklyNormalizingBetaEta.erasure z hw he.valid ⟨_, .inl he⟩
  obtain ⟨M', hMM', heq, ht⟩ := h.lift_erased_reduces hN
  have hEN' : ENormal z M'.erase := by rw [heq]; exact hEN
  exact no_enormal_proof z hΓ hT ht (hm.reduces hMM') hEN'

end Labelled

open Labelled

/-- **Relational exclusion from weak βη-normalization.**
The proof is OpenAI's proof of `relational_exclusion`, with `no_proof_at_target` replaced by the lemma above. -/
theorem relational_exclusion_betaEta {S : Type u} [Fintype S] {P : Specification S}
    (hw : SystemWeaklyNormalizingBetaEta P) : RelationalExclusion P := by
  intro C hC ho ht hf
  have hz : Nonempty S := by
    obtain ⟨I, _, _, h, _⟩ := ht
    obtain ⟨s, _⟩ := h.domain.1
    exact ⟨s⟩
  obtain ⟨z⟩ := hz
  obtain ⟨Γ,γ,hΓ,⟨L⟩⟩ := LogicSetup.exists_setup C hC ho ht
  obtain ⟨K,⟨R⟩⟩ := ChannelSetup.exists_setup_return (L := L) hC ho hf
  let KY := L.quantifiers K.logicalVertex K.directLogical
  let KP := L.quantifiers K.predVertex K.directPred
  obtain ⟨b,hb,mb⟩ := R.specialized_formed.relational_bottom KY KP
  exact no_proof_at_target_betaEta z hw hΓ
    ⟨.terminal (L.witnesses.allData L.base L.triple.codomain),
      L.witnesses.normal L.base L.triple.codomain⟩ hb mb

end PureTypeSystem
