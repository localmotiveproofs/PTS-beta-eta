module

public import PTSBetaEta.Main

@[expose] public section

/-!
# Proofs of the two main theorems

This file restates the two theorems of `Challenge.lean` with the same statements and proves them from the library.
Comparator checks that the statements agree with `Challenge.lean` and that the proofs use only the axioms `propext`, `Quot.sound` and `Classical.choice`.

The proofs are in `PTSBetaEta.Main`.
Both theorems go through the intermediate result `strong_beta_of_eNormalizing_BE`.
It says that if every legal term has a β-reduct with no β-redex outside its λ-domains, then every legal term is strongly β-normalizing.
Strong β-normalization of a term then gives its strong βη-normalization.
-/

namespace PureTypeSystem

universe u

variable {S : Type u}

theorem weak_implies_strong_betaEta (P : Specification S)
    (h : SystemWeaklyNormalizingBE P) : SystemStronglyNormalizingBE P :=
  weak_betaEta_implies_strong_betaEta_BE P h

theorem weak_beta_implies_strong_betaEta (P : Specification S)
    (h : ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → WeaklyNormalizing M) :
    SystemStronglyNormalizingBE P :=
  weak_beta_implies_strong_betaEta_BE P h

end PureTypeSystem
