/- Adapted to typing with βη-conversion from OpenAI's `Typing.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Keys

@[expose] public section

/-! This file adapts OpenAI's typing trees, spine lemmas, context equivalence and expected types to typing with βη-conversion (`HasTypeBE`). -/


namespace PureTypeSystem

universe u

/-- Every term that is legal with βη-conversion is strongly β-normalizing. -/
def SystemBetaSNBE {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ, ValidContextBE P Γ → ∀ M, LegalBE P Γ M → StronglyNormalizing M

/-! Typing trees are finite and syntax-directed, and they keep all the witnesses of the generation lemma.
They impose no functionality and no unique choice of sorts. -/

inductive TypingTreeBE {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Type u
  | var {Γ n A T} (typing : HasTypeBE P Γ (.var n) T)
      (declaration : Lookup Γ n A) (convert : ConvertsBE T A) : TypingTreeBE P Γ (.var n) T
  | sort {Γ s t T} (typing : HasTypeBE P Γ (.sort s) T)
      (axioms : P.axioms s t) (convert : ConvertsBE T (.sort t)) : TypingTreeBE P Γ (.sort s) T
  | product {Γ A B a b c T} (typing : HasTypeBE P Γ (.pi A B) T)
      (domain : TypingTreeBE P Γ A (.sort a)) (body : TypingTreeBE P (A :: Γ) B (.sort b))
      (rule : P.rule a b c) (convert : ConvertsBE T (.sort c)) : TypingTreeBE P Γ (.pi A B) T
  | abstraction {Γ A b B a s T} (typing : HasTypeBE P Γ (.lam A b) T)
      (annotation : TypingTreeBE P Γ A (.sort a)) (body : TypingTreeBE P (A :: Γ) b B)
      (product : HasTypeBE P Γ (.pi A B) (.sort s)) (convert : ConvertsBE T (.pi A B)) :
      TypingTreeBE P Γ (.lam A b) T
  | application {Γ f a A B T} (typing : HasTypeBE P Γ (.app f a) T)
      (function : TypingTreeBE P Γ f (.pi A B)) (argument : TypingTreeBE P Γ a A)
      (convert : ConvertsBE T (B.instantiate a)) : TypingTreeBE P Γ (.app f a) T

namespace TypingTreeBE
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- The judgment at the root of a typing tree.
Its type may be a sort that has no type itself. -/
theorem typing (t : TypingTreeBE P Γ M T) : HasTypeBE P Γ M T := by
  cases t with
  | var h _ _ => exact h
  | sort h _ _ => exact h
  | product h _ _ _ _ => exact h
  | abstraction h _ _ _ _ => exact h
  | application h _ _ _ => exact h

/-- Changes only the type at the root of a typing tree.
The stored generation data (OpenAI's "core") and all children stay the same. -/
def retarget {T' : Expr S} (t : TypingTreeBE P Γ M T)
    (ht : HasTypeBE P Γ M T') (hc : ConvertsBE T' T) : TypingTreeBE P Γ M T' := by
  cases t with
  | var _ hd he => exact .var ht hd (.trans _ _ _ hc he)
  | sort _ ha he => exact .sort ht ha (.trans _ _ _ hc he)
  | product _ d b hr he => exact .product ht d b hr (.trans _ _ _ hc he)
  | abstraction _ d b hp he => exact .abstraction ht d b hp (.trans _ _ _ hc he)
  | application _ f a he => exact .application ht f a (.trans _ _ _ hc he)

/-- Every derivation has a finite typing tree, by the generation lemma.
The proof does not eliminate a `Prop`-valued derivation into data, and it does not assume unique formation triples. -/
theorem nonempty (h : HasTypeBE P Γ M T) : Nonempty (TypingTreeBE P Γ M T) := by
  induction M generalizing Γ T with
  | var n =>
      obtain ⟨A, hd, hc⟩ := h.generation
      exact ⟨.var h hd hc⟩
  | sort s =>
      obtain ⟨t, ha, hc⟩ := h.generation
      exact ⟨.sort h ha hc⟩
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, hr, hc⟩ := h.generation_pi
      exact ⟨.product h (ihA hA).some (ihB hB).some hr hc⟩
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hp, hc⟩ := h.generation_lam
      obtain ⟨a, a', c, hA, _, _, _⟩ := hp.generation_pi
      exact ⟨.abstraction h (ihA hA).some (ihb hb).some hp hc⟩
  | app f a ihf iha =>
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact ⟨.application h (ihf hf).some (iha ha).some hc⟩

noncomputable def ofTyping (h : HasTypeBE P Γ M T) : TypingTreeBE P Γ M T := (nonempty h).some

/-- A renaming of declarations sends each declaration of `Γ` to the renamed declaration in `Δ`.
It is not enough for the two declarations to be convertible. -/
def DeclRenaming (Γ Δ : List (Expr S)) (ρ : Nat → Nat) : Prop :=
  ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (A.rename ρ)

namespace DeclRenaming
variable {Δ : List (Expr S)} {ρ : Nat → Nat}
theorem typed (h : DeclRenaming Γ Δ ρ) (hΔ : ValidContextBE P Δ) :
    ∀ n A, Lookup Γ n A → HasTypeBE P Δ (.var (ρ n)) (A.rename ρ) :=
  fun n A hn => HasTypeBE.lookup hΔ (h n A hn)

theorem lift (h : DeclRenaming Γ Δ ρ) (A : Expr S) :
    DeclRenaming (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ) := by
  intro n B hn
  cases hn with
  | zero =>
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using Lookup.zero (A.rename ρ) Δ
  | succ _ hn =>
      have hh := Lookup.succ (A.rename ρ) (h _ _ hn)
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using hh
end DeclRenaming

/-- Renaming a typing tree transports every stored witness and keeps the shape of the tree.
Binder annotations are transported as well. -/
noncomputable def rename (t : TypingTreeBE P Γ M T) {Δ : List (Expr S)} (hΔ : ValidContextBE P Δ)
    (ρ : Nat → Nat) (hρ : DeclRenaming Γ Δ ρ) :
    TypingTreeBE P Δ (M.rename ρ) (T.rename ρ) := by
  induction t generalizing Δ ρ with
  | var h hd hc => exact .var (h.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ)
  | sort h ha hc => exact .sort (h.rename hΔ ρ (hρ.typed hΔ)) ha (hc.rename ρ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasTypeBE P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .product (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) hr (hc.rename ρ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasTypeBE P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .abstraction (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) (hp.rename hΔ ρ (hρ.typed hΔ)) (hc.rename ρ)
  | application h f a hc ihf iha =>
      apply TypingTreeBE.application (h.rename hΔ ρ (hρ.typed hΔ)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
      simpa only [Expr.instantiate_rename] using hc.rename ρ

namespace DeclRenaming
variable {Δ : List (Expr S)}
theorem weaken (A : Expr S) : DeclRenaming Γ (A :: Γ) Nat.succ :=
  fun _ _ h => .succ A h
end DeclRenaming

/-- A substitution that stores a typing tree for each declared variable. -/
abbrev StoredSubstitution (P : Specification S) (Γ Δ : List (Expr S))
    (σ : Nat → Expr S) : Type u :=
  ∀ n A, Lookup Γ n A → TypingTreeBE P Δ (σ n) (A.subst σ)

namespace StoredSubstitution
variable {Δ : List (Expr S)} {σ : Nat → Expr S}
theorem typed (ts : StoredSubstitution P Γ Δ σ) : TypedSubstitutionBE P Γ Δ σ :=
  fun n A hn => (ts n A hn).typing

noncomputable def lift (ts : StoredSubstitution P Γ Δ σ) {A : Expr S} {s : S}
    (hA : HasTypeBE P Δ (A.subst σ) (.sort s)) :
    StoredSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) :=
  fun n => match n with
  | 0 => fun B hn => by
      have he : B = A.rename Nat.succ := by cases hn; rfl
      have he' : B.subst (Expr.liftSub σ) = (A.subst σ).rename Nat.succ := by
        rw [he,Expr.subst_rename,Expr.rename_subst]
        rfl
      exact .var (he'.symm ▸ HasTypeBE.var hA) (.zero _ _) (by rw [he']; exact .refl _)
  | n+1 => fun B hn => by
      let hex : ∃ B', Lookup Γ n B' ∧ B = B'.rename Nat.succ := by
        cases hn with
        | succ _ h => exact ⟨_, h, rfl⟩
      let tt := (ts _ _ hex.choose_spec.1).rename (.cons hA.valid hA) Nat.succ (DeclRenaming.weaken _)
      have he : B.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          B.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]
            rfl
      exact tt.retarget (he.symm ▸ tt.typing) (by rw [he]; exact .refl _)

end StoredSubstitution

/-- Capture-avoiding substitution in a typing tree, which grafts the given trees at the variables.
It keeps the stored generation data and also substitutes in the annotation at each binder. -/
noncomputable def subst (t : TypingTreeBE P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContextBE P Δ) (σ : Nat → Expr S) (ts : StoredSubstitution P Γ Δ σ) :
    TypingTreeBE P Δ (M.subst σ) (T.subst σ) := by
  induction t generalizing Δ σ with
  | var h hd hc => exact (ts _ _ hd).retarget (h.subst hΔ σ ts.typed) (hc.subst σ)
  | sort h ha hc => exact .sort (h.subst hΔ σ ts.typed) ha (hc.subst σ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasTypeBE P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .product (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) hr (hc.subst σ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasTypeBE P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .abstraction (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) (hp.subst hΔ σ ts.typed) (hc.subst σ)
  | application h f a hc ihf iha =>
      apply TypingTreeBE.application (h.subst hΔ σ ts.typed) (ihf hΔ σ ts) (iha hΔ σ ts)
      simpa only [Expr.instantiate_subst] using hc.subst σ

end TypingTreeBE

namespace HasTypeBE
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
theorem spine_shape {M T : Expr S} (h : HasTypeBE P Γ M T) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b ns, M = (Expr.lam A b).apps ns) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b => exact .inr (.inr (.inr ⟨A,b,[],rfl⟩))
  | pi A B => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
    obtain ⟨D,E,hf,_,_⟩ := h.generation_app
    rcases ihf hf with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
    · exact False.elim hf.sort_cannot_have_product_type
    · exact .inr (.inl (.app hn))
    · exact False.elim hf.product_cannot_have_product_type
    · exact .inr (.inr (.inr ⟨A,b,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩))

theorem app_spine {f a T : Expr S} (h : HasTypeBE P Γ (.app f a) T) :
    Neutral f ∨ ∃ D b n ns, Expr.app f a = (Expr.app (.lam D b) n).apps ns := by
  obtain ⟨D,E,hf,_,_⟩ := h.generation_app
  rcases hf.spine_shape with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
  · exact False.elim hf.sort_cannot_have_product_type
  · exact .inl hn
  · exact False.elim hf.product_cannot_have_product_type
  · right
    cases ns with
    | nil => exact ⟨A,b,a,[],rfl⟩
    | cons n ns => exact ⟨A,b,n,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩

theorem apps_head {M T : Expr S} {ns : List (Expr S)} (h : HasTypeBE P Γ (M.apps ns) T) :
    ∃ A, HasTypeBE P Γ M A := by
  induction ns generalizing M T with
  | nil => exact ⟨T,h⟩
  | cons n ns ih =>
    obtain ⟨A,hA⟩ := ih h
    obtain ⟨D,E,hf,_,_⟩ := hA.generation_app
    exact ⟨_,hf⟩

theorem apps_arg {M T n : Expr S} {ns : List (Expr S)}
    (h : HasTypeBE P Γ (M.apps ns) T) (hn : n ∈ ns) : ∃ A, HasTypeBE P Γ n A := by
  induction ns generalizing M T with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · obtain ⟨T,hT⟩ := h.apps_head (M := .app M n) (ns := ns)
      obtain ⟨D,E,_,ha,_⟩ := hT.generation_app
      exact ⟨D,ha⟩
    · exact ih h hn
end HasTypeBE

/-- The application principle implies strong normalization.
If every well-typed application of strongly normalizing terms is strongly normalizing, then every legal term is.
The principle itself is proved later from candidate interfaces, and it is not an assumption of the main theorem. -/
theorem stronglyNormalizing_of_applicationBE
    {S : Type u} {P : Specification S}
    (applySN : ∀ {Γ f a D E}, HasTypeBE P Γ f (.pi D E) → HasTypeBE P Γ a D →
      StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)) :
    SystemBetaSNBE P := by
  have typed : ∀ M : Expr S, ∀ {Γ A}, HasTypeBE P Γ M A → StronglyNormalizing M := by
    intro M
    induction M with
    | var n => intro Γ A h; exact (Normal.var n).stronglyNormalizing
    | sort s => intro Γ A h; exact (Normal.sort s).stronglyNormalizing
    | app f a ihf iha =>
        intro Γ A h
        obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
        exact applySN hf ha (ihf hf) (iha ha)
    | lam D b ihD ihb =>
        intro Γ A h
        obtain ⟨E, s, hb, hpi, _⟩ := h.generation_lam
        obtain ⟨s₁, s₂, s₃, hD, _, _, _⟩ := hpi.generation_pi
        exact (ihD hD).lam (ihb hb)
    | pi D E ihD ihE =>
        intro Γ A h
        obtain ⟨s₁, s₂, s₃, hD, hE, _, _⟩ := h.generation_pi
        exact (ihD hD).pi (ihE hE)
  intro Γ _ M h
  obtain ⟨A, h | h⟩ := h
  · exact typed M h
  · obtain ⟨s, rfl⟩ | ⟨s, hs⟩ := h.regularity
    · exact (Normal.sort s).stronglyNormalizing
    · exact typed M hs

/-- If not every legal term is strongly β-normalizing, then there is a well-typed application `f a` that is not strongly normalizing, while `f` and `a` are. -/
theorem exists_bad_applicationBE {S : Type u} {P : Specification S}
    (h : ¬ SystemBetaSNBE P) :
    ∃ Γ f a D E, HasTypeBE P Γ f (.pi D E) ∧ HasTypeBE P Γ a D ∧
      StronglyNormalizing f ∧ StronglyNormalizing a ∧ ¬ StronglyNormalizing (.app f a) := by
  classical
  by_contra hn
  apply h
  apply stronglyNormalizing_of_applicationBE
  intro Γ f a D E hf ha hfs has
  by_contra hb
  exact hn ⟨Γ, f, a, D, E, hf, ha, hfs, has, hb⟩

/-- Two valid contexts are equivalent when they give exactly the same judgments on the same terms.
This auxiliary relation carries no semantic or normalization assumption. -/
structure ContextEquivalentBE {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) : Prop where
  valid_left : ValidContextBE P Γ
  valid_right : ValidContextBE P Δ
  typing : ∀ (M A : Expr S), HasTypeBE P Γ M A ↔ HasTypeBE P Δ M A

namespace ContextEquivalentBE
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem symm (h : ContextEquivalentBE P Γ Δ) : ContextEquivalentBE P Δ Γ :=
  ⟨h.valid_right, h.valid_left, fun _ _ => (h.typing _ _).symm⟩


theorem cons (h : ContextEquivalentBE P Γ Δ) {A : Expr S} {s : S}
    (hA : HasTypeBE P Γ A (.sort s)) : ContextEquivalentBE P (A :: Γ) (A :: Δ) := by
  have lift_dir {Γ Δ : List (Expr S)} (h : ContextEquivalentBE P Γ Δ)
      (hA : HasTypeBE P Γ A (.sort s)) :
      ∀ M B, HasTypeBE P (A :: Γ) M B → HasTypeBE P (A :: Δ) M B := by
    intro M B ht
    have hA' := (h.typing _ _).1 hA
    have hs : TypedSubstitutionBE P (A :: Γ) (A :: Δ) Expr.var := by
      intro n D hn
      rw [Expr.subst_var]
      cases hn with
      | zero => exact .var hA'
      | succ _ hn => exact .weaken ((h.typing _ _).1 (HasTypeBE.lookup h.valid_left hn)) hA'
    simpa only [Expr.subst_var] using ht.subst (.cons h.valid_right hA') _ hs
  have hA' := (h.typing _ _).1 hA
  exact ⟨.cons h.valid_left hA, .cons h.valid_right hA',
    fun M B => ⟨lift_dir h hA M B, lift_dir h.symm hA' M B⟩⟩

theorem head_conversion {A B : Expr S} {s t : S}
    (hA : HasTypeBE P Γ A (.sort s)) (hB : HasTypeBE P Γ B (.sort t))
    (hc : ConvertsBE A B) : ContextEquivalentBE P (A :: Γ) (B :: Γ) :=
  ⟨.cons hA.valid hA, .cons hB.valid hB, fun _ _ =>
    ⟨fun h => h.context_head_conversion hA hB hc,
      fun h => h.context_head_conversion hB hA (.symm _ _ hc)⟩⟩
end ContextEquivalentBE

namespace TypingTreeBE
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {M T : Expr S}
/-- Moves a typing tree to an equivalent context.
The stored generation data at every node that is not a variable stays the same, and so does every choice of sort. -/
noncomputable def recontext (t : TypingTreeBE P Γ M T) (h : ContextEquivalentBE P Γ Δ) :
    TypingTreeBE P Δ M T := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      exact .var ht' g.choose_spec.1 g.choose_spec.2
  | sort ht ha hc => exact .sort ((h.typing _ _).mp ht) ha hc
  | product ht d b hr hc ihd ihb =>
      exact .product ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) hr hc
  | abstraction ht d b hp hc ihd ihb =>
      exact .abstraction ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing))
        ((h.typing _ _).mp hp) hc
  | application ht g n hc ihg ihn =>
      exact .application ((h.typing _ _).mp ht) (ihg h) (ihn h) hc
end TypingTreeBE

/-- An expected type is a sort, or a term that has a sort as its type.
The first case covers sorts that have no type themselves, as in the correctness of types. -/
def ExpectedBE {S : Type u} (P : Specification S) (Γ : List (Expr S)) (A : Expr S) : Prop :=
  (∃ s, A = .sort s) ∨ ∃ s, HasTypeBE P Γ A (.sort s)
namespace ExpectedBE
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {A D : Expr S}
theorem of_type {M : Expr S} (h : HasTypeBE P Γ M A) : ExpectedBE P Γ A := h.regularity
theorem sorted {s : S} (h : HasTypeBE P Γ A (.sort s)) : ExpectedBE P Γ A := .inr ⟨s,h⟩
theorem weaken {s : S} (h : ExpectedBE P Γ A) (hD : HasTypeBE P Γ D (.sort s)) :
    ExpectedBE P (D :: Γ) (A.rename Nat.succ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inl ⟨s,rfl⟩
  · exact .inr ⟨s,.weaken h hD⟩
end ExpectedBE

end PureTypeSystem

