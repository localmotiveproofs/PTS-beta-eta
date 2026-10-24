/- Adapted to typing with βη-conversion from OpenAI's `Values.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Plain

@[expose] public section

/-!
# Candidate bases and observation values over keys

This file adapts OpenAI's `Values.lean` (`PTSBetaEta.Beta.Values`) to typing with βη-conversion.
Actual types, active types and the arguments of frames are keys.
The images of an environment are typed in the tower, with their types given up to keys.
Two images are compatible when they have equal keys (`KConverts`), and then all keys of substitutions agree.
A value at an active type is plain, or it lives at a free type of sign `+` (OpenAI's "plus" values) or of sign `−` (OpenAI's "minus" values).
See the terminology in `PTSBetaEta` for these words.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem

universe u

namespace Expr.Scoped
variable {S : Type u} [Nonempty S] {n : Nat} {M : Expr S}

/-- The key of a substitution instance depends only on the keys of the images. -/
theorem subst_kconverts (hM : Scoped n M) {σ τ : Nat → Expr S}
    (hc : ∀ i, i < n → KConverts (σ i) (τ i)) : KConverts (M.subst σ) (M.subst τ) := by
  unfold KConverts
  rw [Expr.erase_subst, Expr.erase_subst]
  exact (Expr.Scoped.erase hM).subst_convertsBE hc

end Expr.Scoped

namespace ContextTowerBE.THasTypeBE
variable {S : Type u} [Nonempty S] {P : Specification S} [hE : Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P} {M A : Expr S}

theorem actual_type (h : Ω.THasTypeBE M A) (hw : SystemENormalizing' P) :
    KP.Candidates.ActualType Ω A.knf := by
  obtain ⟨A₀, h₀, hA⟩ := h
  rcases h₀.regularity with ⟨s, rfl⟩ | ⟨s, hs⟩
  · rw [Expr.knf_sort] at hA
    exact .inr ⟨s, hA.symm⟩
  · have hk : Ω.KHasTypeBE A (.sort s) := (KHasTypeBE.of hs).of_knf_eq hA rfl
    exact .inl ⟨(Expr.knf_spec (hk.kwn hw)).2, s, hk.knf hw⟩

theorem actual_expression {s : S} (h : Ω.THasTypeBE M (.sort s)) (hw : SystemENormalizing' P) :
    KP.Candidates.ActualType Ω M.knf :=
  .inl ⟨(Expr.knf_spec (h.kwn hw)).2, s, h.toK.knf hw⟩

end ContextTowerBE.THasTypeBE

namespace KP

namespace ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)

abbrev Candidate (T : Expr S) := {A : Set (Expr S) // Candidates.IsCandidate Ω T A}
abbrev ActualType := {T : Expr S // Candidates.ActualType Ω T}
abbrev Base := (T : ActualType Ω) → Candidate Ω T.val

def topBase : Base Ω := fun T => ⟨Candidates.Top Ω T.val, Candidates.top_candidate⟩

/-- Replaces the candidate at one actual type in a base observation. This is the update used at product syntax. -/
noncomputable def Base.update (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) : Base Ω :=
  Function.update b T A

@[simp] theorem Base.update_same (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) :
    Base.update Ω b T A T = A := by simp [Base.update]

@[simp] theorem Base.update_other (b : Base Ω) (T U : ActualType Ω) (A : Candidate Ω T.val)
    (h : U ≠ T) : Base.update Ω b T A U = b U := by simp [Base.update, h]

variable [Fintype S] (C : Set (Set S)) {hw : SystemENormalizing' P}
variable (hno : ¬ ForbiddenConfiguration P C)

abbrev PlainValue := (T : ActualPlain.Node Ω C) × ActualPlain.Space (hw := hw) hno (Base Ω) T
abbrev Plus := FreeObservations.Plus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))
abbrev Minus := FreeObservations.Minus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))

inductive RawValue : Type u
  | plain : PlainValue (hw := hw) Ω C hno → RawValue
  | plus : Plus (hw := hw) Ω C hno → RawValue
  | minus : Minus (hw := hw) Ω C hno → RawValue

/-- `Fits T v` says that `v`, an element of `RawValue` whose type is not yet fixed, is a value at the key `T`.
A plain value must live at `T` itself, and a value of sign `+` or `−` needs `T` to be free with that sign. -/
def Fits (T : Expr S) : RawValue (hw := hw) Ω C hno → Prop
  | .plain x => x.1.type = T
  | .plus _ => FreeLayer P C (Ω.kprofile T) false
  | .minus _ => FreeLayer P C (Ω.kprofile T) true

abbrev Value (T : Expr S) := {v : RawValue (hw := hw) Ω C hno // Fits (hw := hw) Ω C hno T v}

structure ActiveType where
  type : Expr S
  normal : KNormal type
  sorted : ∃ s, Ω.KHasTypeBE type (.sort s)
  active : ActiveLayer P C (Ω.kprofile type)

namespace ActiveType
variable {Ω C hno}
noncomputable abbrev ofActual (T : ActualType Ω) (ha : ActiveLayer P C (Ω.kprofile T.val)) :
    ActiveType Ω C where
  type := T.val
  normal := by rcases T.property with h | ⟨s, h⟩; exact h.1; exact h ▸ KNormal.sort s
  sorted := by
    obtain ⟨s, hs⟩ := ha.nonempty
    exact ⟨s, hs⟩
  active := ha

def actual (T : ActiveType Ω C) : ActualType Ω := ⟨T.type, .inl ⟨T.normal, T.sorted⟩⟩
end ActiveType

noncomputable def plainDefault (T : ActualPlain.Node Ω C) : ActualPlain.Space (hw := hw) hno (Base Ω) T :=
  (ActualPlain.schema hw).distinguished (ActualPlain.dependency_wellFounded hno) (topBase Ω) T

noncomputable def distinguished (T : ActiveType Ω C) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.kprofile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    exact ⟨.plain ⟨n, plainDefault (hw := hw) Ω C hno n⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.kprofile T.type) false
    · exact ⟨.plus (FreeObservations.plusDefault _ _ (topBase Ω) none), hf⟩
    · have hm : FreeLayer P C (Ω.kprofile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.minusDefault _ _ (topBase Ω) none), hm⟩

noncomputable def RawValue.base : RawValue (hw := hw) Ω C hno → Base Ω
  | .plain p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1
  | .plus p => p.continuing []
  | .minus m => (FreeObservations.behavior _ _ _ _ m).continuing []

/-- Replaces the base observation of a value, which is its output on the empty list of frames.
The outputs on all nonempty lists of frames stay as they are. -/
noncomputable def withBase (T : ActiveType Ω C) (b : Base Ω) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.kprofile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    let e := ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n
    exact ⟨.plain ⟨n, e.symm (b, (e (plainDefault (hw := hw) Ω C hno n)).2)⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.kprofile T.type) false
    · exact ⟨.plus ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩, hf⟩
    · have hm : FreeLayer P C (Ω.kprofile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.embed _ _ _ _ 1
        ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩), hm⟩

theorem withBase_base (T : ActiveType Ω C) (b : Base Ω) :
    RawValue.base (hw := hw) Ω C hno (withBase (hw := hw) Ω C hno T b).val = b := by
  unfold withBase
  split
  · simp only [RawValue.base, Equiv.apply_symm_apply]
  · split
    · simp only [RawValue.base, ↓reduceIte]
    · simp only [RawValue.base, FreeObservations.behavior_embed, FreeObservations.stageBehavior,
        FreeObservations.Table.relabel, Function.comp_apply, FreeObservations.mapContinue,
        List.map_nil, ↓reduceIte]

/-- Turns a raw value into a value at `T`.
A raw value that does not fit `T` is replaced by the distinguished value at `T`. -/
noncomputable def project (T : ActiveType Ω C) (v : RawValue (hw := hw) Ω C hno) : Value (hw := hw) Ω C hno T.type :=
  if h : Fits (hw := hw) Ω C hno T.type v then ⟨v, h⟩ else distinguished (hw := hw) Ω C hno T

@[simp] theorem project_valid (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    project (hw := hw) Ω C hno T v.val = v := by
  simp only [project, v.property, dite_true, Subtype.coe_eta]

end ObservationValues
end KP
end PureTypeSystem

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace RawValue

def LevelEq (n : Nat) : RawValue (hw := hw) Ω C hno → RawValue (hw := hw) Ω C hno → Prop
  | .plain p, .plain q => p = q
  | .plus p, .plus q => FreeObservations.Agree n p q
  | .minus p, .minus q => p = q
  | _, _ => False

def Bounded (n : Nat) : RawValue (hw := hw) Ω C hno → Prop
  | .minus p => FreeObservations.InStage n p
  | _ => True

variable {Ω C hno}
theorem level_refl (n : Nat) (v : RawValue (hw := hw) Ω C hno) : LevelEq _ _ _ n v v := by
  cases v <;> exact rfl

theorem level_mono {n m : Nat} (h : n ≤ m) {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ m v w) : LevelEq _ _ _ n v w := by
  cases v <;> cases w <;> try exact he
  exact FreeObservations.Agree.mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {v : RawValue (hw := hw) Ω C hno}
    (hv : Bounded _ _ _ n v) : Bounded _ _ _ m v := by
  cases v <;> try trivial
  exact FreeObservations.InStage.mono h hv

theorem exists_bound (v : RawValue (hw := hw) Ω C hno) : ∃ n, Bounded _ _ _ n v := by
  cases v with
  | plain p => exact ⟨0, trivial⟩
  | plus p => exact ⟨0, trivial⟩
  | minus p => exact FreeObservations.InStage.exists_stage p

theorem level_base {n : Nat} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ n v w) : base _ _ _ v = base _ _ _ w := by
  cases v <;> cases w <;> try exact False.elim he
  · exact congrArg (fun p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1) he
  · exact congrFun (congrArg FreeObservations.Table.continuing he) []
  · exact congrArg (fun p => (FreeObservations.behavior _ _ _ _ p).continuing []) he
end RawValue
end PureTypeSystem.KP.ObservationValues

namespace PureTypeSystem.KP
universe u

namespace ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P)
variable (C : Set (Set S)) (hw : SystemENormalizing' P)

/-- A frame at the active type `T` (OpenAI's "legal frame"), without its payload.
It consists of the domain and codomain of the product `T`, and a key argument of that domain whose instantiated codomain is active. -/
structure FrameKey (T : ActiveType Ω C) where
  domain : Expr S
  body : Expr S
  product : T.type = .pi domain body
  argument : Expr S
  normal : KNormal argument
  typed : Ω.KHasTypeBE argument domain
  active : ActiveLayer P C (Ω.kprofile (body.instantiate argument))

namespace FrameKey
variable {Ω C} {T : ActiveType Ω C} (a : FrameKey Ω C T)

theorem sorted : ∃ s, Ω.KHasTypeBE (.pi a.domain a.body) (.sort s) :=
  a.product ▸ T.sorted

theorem domain_normal : KNormal a.domain := (a.product ▸ T.normal).pi_domain

theorem body_normal : KNormal a.body := (a.product ▸ T.normal).pi_body

theorem domain_sorted : ∃ s, Ω.KHasTypeBE a.domain (.sort s) := by
  obtain ⟨s, hs⟩ := a.sorted
  exact Ω.kdomain_sorted hs

theorem target_sorted : ∃ s, Ω.KHasTypeBE (a.body.instantiate a.argument) (.sort s) := by
  obtain ⟨s, hs⟩ := a.sorted
  exact Ω.kframe_target_sorted hs a.typed

include hw

theorem profile_data : ∃ J,
    ProfileTriple P (Ω.kprofile a.domain) J (Ω.kprofile T.type) ∧
    PositivePath (PrimaryEdge P) (Ω.kprofile (a.body.instantiate a.argument)) J ∧
    ActiveLayer P C J := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hf, hp⟩ := Ω.kframe_profiles hw hs a.typed
  rw [← a.product] at hf
  have hj := ObservationLayers.positive a.active.layer hp
  exact ⟨J, hf, hp, T.active.predecessor (.single (.positive hj T.active.layer (.codomain hf)))⟩

theorem target_path : PositivePath (SecondaryEdge P C)
    (Ω.kprofile (a.body.instantiate a.argument)) (Ω.kprofile T.type) := by
  obtain ⟨J, hf, hp, hj⟩ := a.profile_data hw
  exact .tail (ObservationLayers.secondary a.active.layer hp)
    (.positive hj.layer T.active.layer (.codomain hf))

theorem domain_active (hd : Ω.kprofile a.domain ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.kprofile a.domain) := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact T.active.predecessor (.single (.negative hd hj.layer T.active.layer hf))

theorem domain_edge (hd : ActiveLayer P C (Ω.kprofile a.domain)) :
    SecondaryEdge P C (Ω.kprofile a.domain) (Ω.kprofile T.type) true := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact .negative hd.layer hj.layer T.active.layer hf

noncomputable def target : ActiveType Ω C where
  type := (a.body.instantiate a.argument).knf
  normal := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact (Expr.knf_spec (hs.kwn hw)).2
  sorted := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact ⟨s, hs.knf hw⟩
  active := by simpa only [ContextTowerBE.kprofile_knf] using a.active

def domainType (hd : ActiveLayer P C (Ω.kprofile a.domain)) : ActiveType Ω C :=
  ⟨a.domain, a.domain_normal, a.domain_sorted, hd⟩

theorem plain_target (hp : PlainLayer P C (Ω.kprofile T.type)) :
    PlainLayer P C (Ω.kprofile (a.target hw).type) := by
  simpa only [target, ContextTowerBE.kprofile_knf] using hp.predecessor_path (a.target_path hw).reach

theorem plain_domain (hp : PlainLayer P C (Ω.kprofile T.type))
    (hd : ActiveLayer P C (Ω.kprofile a.domain)) : PlainLayer P C (Ω.kprofile a.domain) :=
  hp.predecessor (a.domain_edge hw hd)

theorem free_target_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.kprofile T.type) s)
    (hL : FreeLayer P C (Ω.kprofile (a.target hw).type) t) : t = s := by
  have hl : FreeLayer P C (Ω.kprofile (a.body.instantiate a.argument)) t := by
    simpa only [target, ContextTowerBE.kprofile_knf] using hL
  simpa using hl.path_sign hT (a.target_path hw).parity

theorem free_domain_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.kprofile T.type) s)
    (hI : FreeLayer P C (Ω.kprofile a.domain) t) : t = !s := by
  have h := hI.edge_sign hT (a.domain_edge hw hI.active)
  simpa using h

/-- The third fact about binders.
Suppose a frame at a product type stays inside the current component.
Then an active domain of the frame is direct, so the parameter of its argument never lives at a free type of sign `−`. -/
theorem domain_direct (hC : IsComponent (PrimaryEdge P) C)
    (hK : Ω.kprofile T.type ∈ C) (hL : Ω.kprofile (a.target hw).type ∈ C)
    (hd : ActiveLayer P C (Ω.kprofile a.domain)) : DirectLayer P C (Ω.kprofile a.domain) := by
  obtain ⟨J, hf, hp, _⟩ := a.profile_data hw
  have hl : Ω.kprofile (a.body.instantiate a.argument) ∈ C := by
    simpa only [target, ContextTowerBE.kprofile_knf] using hL
  have hj : J ∈ C := hC.between hl hK hp.reach (.single (.codomain hf))
  exact ⟨hd.layer, J, hj, Ω.kprofile T.type, hK, hf⟩

theorem domain_not_minus (hC : IsComponent (PrimaryEdge P) C)
    (hK : Ω.kprofile T.type ∈ C) (hL : Ω.kprofile (a.target hw).type ∈ C) :
    ¬ FreeLayer P C (Ω.kprofile a.domain) true := by
  intro hm
  exact Bool.noConfusion (hm.direct_sign (a.domain_direct hw hC hK hL hm.active))
end FrameKey

variable [Fintype S] {hw} (hno : ¬ ForbiddenConfiguration P C)

/-- `PayloadFits D p` says that `p` is a correct payload for an argument of type `D`.
At an inactive domain the payload must be absent, and at an active domain it must be a value at `D`. -/
def PayloadFits (D : Expr S) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  match p with
  | none => ¬ ActiveLayer P C (Ω.kprofile D)
  | some v => Fits Ω C hno D v

namespace Fits
variable {Ω C hno} {T : Expr S} {v : RawValue (hw := hw) Ω C hno}
theorem active (h : Fits Ω C hno T v) : ActiveLayer P C (Ω.kprofile T) := by
  cases v with
  | plain p => exact h ▸ p.1.plain.active
  | plus p => exact h.active
  | minus p => exact h.active
end Fits

abbrev PlusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Minus (hw := hw) Ω C hno)
abbrev MinusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Plus (hw := hw) Ω C hno)

def plusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Minus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite m => some (.minus m)
  | .plain p => some (.plain p)

def minusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Plus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite p => some (.plus p)
  | .plain p => some (.plain p)

/-- The check made when a free abstraction receives an argument `q` with payload `p` (OpenAI's "gate").
It holds when `q` and `p` form a frame at `T`, and `exit` records whether the target of that frame is plain. -/
def Gate (T : ActiveType Ω C) (q : Expr S)
    (p : Option (RawValue (hw := hw) Ω C hno)) (exit : Bool) : Prop :=
  ∃ a : FrameKey Ω C T, a.argument = q ∧ PayloadFits Ω C hno a.domain p ∧
    (PlainLayer P C (Ω.kprofile (a.target hw).type) ↔ exit = true)

end ObservationValues

namespace ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Parameter

def Bounded (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  ∀ v, p = some v → RawValue.Bounded Ω C hno n v

def LevelEq (n : Nat) : Option (RawValue (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno) → Prop
  | none, none => True
  | some v, some w => RawValue.LevelEq Ω C hno n v w
  | _, _ => False

variable {Ω C hno}
theorem level_refl (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : LevelEq _ _ _ n p p := by
  cases p with
  | none => trivial
  | some p => exact p.level_refl n

theorem level_mono {n m : Nat} (h : n ≤ m) {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq _ _ _ m p q) : LevelEq _ _ _ n p q := by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {p : Option (RawValue (hw := hw) Ω C hno)}
    (he : Bounded _ _ _ n p) : Bounded _ _ _ m p := fun v hv => RawValue.bounded_mono h (he v hv)

theorem exists_bound (p : Option (RawValue (hw := hw) Ω C hno)) : ∃ n, Bounded _ _ _ n p := by
  cases p with
  | none => exact ⟨0, fun _ h => by cases h⟩
  | some p =>
    obtain ⟨n, hn⟩ := p.exists_bound
    exact ⟨n, fun _ h => Option.some.inj h ▸ hn⟩
end Parameter

/-- An environment sends the context into the tower by a substitution whose images are typed in the tower and need not be normal.
It has exactly one parameter for each declaration whose actual type is active, and none for the other declarations. -/
structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TTypedSubstitutionBE Γ images
  parameters : Nat → Option (RawValue (hw := hw) Ω C hno)
  lawful : ∀ n A, Lookup Γ n A → PayloadFits Ω C hno (A.subst images).knf (parameters n)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

def Bounded (k : Nat) : Prop := ∀ n, n < Γ.length → Parameter.Bounded Ω C hno k (e.parameters n)

/-- The images of two environments agree up to keys. -/
def ImageCompatible (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ∀ n, n < Γ.length → KConverts (e.images n) (f.images n)

def LevelEq (k : Nat) (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ImageCompatible e f ∧ ∀ n, n < Γ.length → Parameter.LevelEq Ω C hno k (e.parameters n) (f.parameters n)

theorem bounded_mono {k l : Nat} (hkl : k ≤ l) (he : e.Bounded k) : e.Bounded l :=
  fun n hn => Parameter.bounded_mono hkl (he n hn)

theorem exists_bound : ∃ k, e.Bounded k := by
  have hh : ∀ n, ∃ k, ∀ i, i < n → Parameter.Bounded Ω C hno k (e.parameters i) := by
    intro n
    induction n with
    | zero => exact ⟨0, fun _ h => by omega⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨l, hl⟩ := Parameter.exists_bound (e.parameters n)
      refine ⟨max k l, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Parameter.bounded_mono (le_max_left k l) (hk i hi)
      · exact Parameter.bounded_mono (le_max_right k l) hl
  exact hh Γ.length

theorem level_refl (k : Nat) : e.LevelEq k e :=
  ⟨fun _ _ => .refl _, fun _ _ => Parameter.level_refl _ _⟩

theorem level_mono {k l : Nat} {f : Environment (hw := hw) Ω C hno Γ}
    (hkl : k ≤ l) (he : e.LevelEq l f) : e.LevelEq k f :=
  ⟨he.1, fun n hn => Parameter.level_mono hkl (he.2 n hn)⟩

/-- Binding a new term in an environment neither normalizes nor evaluates that term. -/
def cons {A a : Expr S} (ha : Ω.THasTypeBE a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).knf p) :
    Environment (hw := hw) Ω C hno (A :: Γ) where
  images := fun n => match n with | 0 => a | n+1 => e.images n
  typed := e.typed.cons ha
  parameters := fun n => match n with | 0 => p | n+1 => e.parameters n
  lawful := by
    intro n B hn
    cases hn with
    | zero => simpa only [Expr.subst_rename, Function.comp_def] using hp
    | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using e.lawful _ _ hn

theorem bounded_cons {A a : Expr S} (ha : Ω.THasTypeBE a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).knf p)
    {k : Nat} (he : e.Bounded k) (hb : Parameter.Bounded Ω C hno k p) :
    (e.cons ha p hp).Bounded k := by
  intro n hn
  cases n with
  | zero => exact hb
  | succ n => exact he n (Nat.lt_of_succ_lt_succ hn)

theorem actual_expr_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasTypeBE P Γ M A) :
    (M.subst e.images).knf = (M.subst f.images).knf :=
  Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst ht e.typed).kwn hw)
    ((ContextTowerBE.THasTypeBE.subst ht f.typed).kwn hw)
    (ht.scope.1.subst_kconverts he)

theorem actual_type_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasTypeBE P Γ M A) :
    (A.subst e.images).knf = (A.subst f.images).knf :=
  Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst ht e.typed).type_kwn hw)
    ((ContextTowerBE.THasTypeBE.subst ht f.typed).type_kwn hw)
    (ht.scope.2.subst_kconverts he)
end Environment

namespace PayloadFits
variable {Ω C hno}
theorem exists_of_actual (T : ActualType Ω) : ∃ p, PayloadFits (hw := hw) Ω C hno T.val p := by
  by_cases ha : ActiveLayer P C (Ω.kprofile T.val)
  · exact ⟨some (distinguished (hw := hw) Ω C hno (.ofActual T ha)).val,
      (distinguished (hw := hw) Ω C hno (.ofActual T ha)).property⟩
  · exact ⟨none,ha⟩
end PayloadFits

/-- The exact stored formation data of a product, together with its environment. -/
structure ProductInstance where
  context : List (Expr S)
  domain : Expr S
  body : Expr S
  domainSort : S
  bodySort : S
  resultSort : S
  domainTyping : HasTypeBE P context domain (.sort domainSort)
  bodyTyping : HasTypeBE P (domain :: context) body (.sort bodySort)
  rule : P.rule domainSort bodySort resultSort
  environment : Environment (hw := hw) Ω C hno context

namespace ProductInstance
variable {Ω C hno} (t : ProductInstance (hw := hw) Ω C hno)
def rawDomain : Expr S := t.domain.subst t.environment.images
def rawBody : Expr S := t.body.subst (Expr.liftSub t.environment.images)
noncomputable def domainNF : Expr S := t.rawDomain.knf
noncomputable def bodyNF : Expr S := t.rawBody.knf
def rawTarget (n : Expr S) : Expr S :=
  t.body.subst (fun i => match i with | 0 => n | i+1 => t.environment.images i)
noncomputable def targetNF (n : Expr S) : Expr S := (t.rawTarget n).knf

theorem rawDomain_typed : Ω.THasTypeBE t.rawDomain (.sort t.domainSort) :=
  ContextTowerBE.THasTypeBE.subst t.domainTyping t.environment.typed

theorem rawProduct_typed : Ω.THasTypeBE (.pi t.rawDomain t.rawBody) (.sort t.resultSort) :=
  ContextTowerBE.THasTypeBE.subst (HasTypeBE.product t.domainTyping t.bodyTyping t.rule) t.environment.typed

theorem domain_typed : Ω.KHasTypeBE t.domainNF (.sort t.domainSort) := t.rawDomain_typed.toK.knf hw

theorem domain_normal : KNormal t.domainNF := (Expr.knf_spec (t.rawDomain_typed.kwn hw)).2

theorem body_normal : KNormal t.bodyNF :=
  (Expr.knf_spec (KWN.pi_body (t.rawProduct_typed.kwn hw))).2

theorem product_nf : (Expr.pi t.rawDomain t.rawBody).knf = .pi t.domainNF t.bodyNF :=
  Expr.knf_pi (KWN.pi_domain (t.rawProduct_typed.kwn hw))
    (KWN.pi_body (t.rawProduct_typed.kwn hw))

theorem product_typed : Ω.KHasTypeBE (.pi t.domainNF t.bodyNF) (.sort t.resultSort) := by
  rw [← t.product_nf]
  exact t.rawProduct_typed.toK.knf hw

theorem rawArgument {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF) : Ω.THasTypeBE n t.rawDomain :=
  hn.of_type_knf_eq (Expr.knf_idem _)

noncomputable def extend {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.environment.cons (t.rawArgument hn) p hp

theorem rawTarget_typed {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF) :
    Ω.THasTypeBE (t.rawTarget n) (.sort t.bodySort) :=
  ContextTowerBE.THasTypeBE.subst t.bodyTyping (t.environment.typed.cons (t.rawArgument hn))

theorem target_typed {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF) :
    Ω.KHasTypeBE (t.targetNF n) (.sort t.bodySort) := (t.rawTarget_typed hn).toK.knf hw

theorem target_normal {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF) : KNormal (t.targetNF n) :=
  (Expr.knf_spec ((t.rawTarget_typed hn).kwn hw)).2

theorem rawTarget_eq (n : Expr S) : t.rawTarget n = t.rawBody.instantiate n := by
  rw [rawBody, Expr.instantiate_liftSub]
  rfl

/-- The key of the target depends only on the key of the argument. -/
theorem target_eq_k {n : Expr S} (hn : Ω.KHasTypeBE n t.domainNF) :
    (t.rawTarget n).knf = (t.bodyNF.instantiate n).knf := by
  have hr : KConverts (t.rawTarget n) (t.bodyNF.instantiate n) := by
    rw [t.rawTarget_eq n]
    unfold KConverts
    rw [Expr.erase_instantiate, Expr.erase_instantiate]
    exact ConvertsBE.subst (Expr.knf_spec (KWN.pi_body (t.rawProduct_typed.kwn hw))).1.converts _
  obtain ⟨s, hs⟩ := Ω.kframe_target_sorted t.product_typed hn
  exact Expr.knf_converts (KWN.of_kconverts hr (hs.kwn hw)) (hs.kwn hw) hr

theorem target_eq {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF) :
    t.targetNF n = (t.bodyNF.instantiate n).knf := t.target_eq_k hn.toK

/-- The arguments that the product test checks (OpenAI's "testers").
They are the members of the domain candidate `d` when the key profile of the domain lies in the current component, and all of `Top` otherwise. -/
noncomputable def testers (d : Candidate Ω t.domainNF) : Set (Expr S) :=
  if Ω.kprofile t.domainNF ∈ C then d.val else Candidates.Top Ω t.domainNF

theorem testers_top (d : Candidate Ω t.domainNF) : t.testers d ⊆ Candidates.Top Ω t.domainNF := by
  unfold testers
  split
  · exact d.property.upper
  · exact Set.Subset.rfl

/-- For every argument `n` of the domain and every matching payload, a candidate at the instantiated codomain.
The quantification ranges over all payloads, and not only over those that realize the domain semantically. -/
abbrev BodyReads := ∀ (n : Expr S), Ω.THasTypeBE n t.domainNF →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno t.domainNF p → Candidate Ω (t.targetNF n)

noncomputable def fibers (b : t.BodyReads) (n : Expr S) : Set (Set (Expr S)) :=
  if hn : Ω.THasTypeBE n t.domainNF then
    if Ω.kprofile (t.targetNF n) ∈ C then
      {U | ∃ p hp, U = (b n hn p hp).val}
    else {Candidates.Top Ω (t.targetNF n)}
  else ∅

theorem fibers_candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads)
    {n : Expr S} (hn : n ∈ t.testers d) {U : Set (Expr S)} (hU : U ∈ t.fibers b n) :
    Candidates.IsCandidate Ω (t.bodyNF.instantiate n).knf U := by
  have ht := (t.testers_top d hn).1
  rw [← t.target_eq ht]
  simp only [fibers, ht, dite_true] at hU
  split_ifs at hU with hc
  · obtain ⟨p,hp,rfl⟩ := hU
    exact (b n ht p hp).property
  · have he : U = Candidates.Top Ω (t.targetNF n) := hU
    rw [he]
    exact Candidates.top_candidate

noncomputable def candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads) :
    Candidate Ω (.pi t.domainNF t.bodyNF) :=
  ⟨Candidates.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b),
    Candidates.productTest_candidate hw (t.testers_top d) (fun _ hn _ hU => t.fibers_candidate d b hn hU)⟩

theorem candidate_top (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M : Expr S}
    (hM : M ∈ (t.candidate d b).val) : M ∈ Candidates.Top Ω (.pi t.domainNF t.bodyNF) := hM.1

theorem candidate_body (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.kprofile (t.targetNF n) ∈ C)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Expr.app M n ∈ (b n (t.testers_top d hn).1 p hp).val := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_true, Set.mem_ofPred_eq]
  exact ⟨p,hp,rfl⟩

theorem candidate_outside (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.kprofile (t.targetNF n) ∉ C) :
    Expr.app M n ∈ Candidates.Top Ω (t.targetNF n) := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_false, Set.mem_singleton_iff]
end ProductInstance
end ObservationValues
end PureTypeSystem.KP

