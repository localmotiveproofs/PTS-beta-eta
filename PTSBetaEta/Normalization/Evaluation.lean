/- Adapted to typing with βη-conversion from OpenAI's `Evaluation.lean` (https://github.com/openai/math, commit 1581d4c).
   Apache License 2.0. See LICENSE, and the README for the changes. -/

module

public import PTSBetaEta.Normalization.Canon

@[expose] public section

/-!
# The operations on observation values, over keys

This file adapts OpenAI's `Evaluation.lean` (`PTSBetaEta.Beta.Evaluation`) to typing with βη-conversion.
The arguments of frames are keys.
The environment of a frame binds the canonical typed representative `Ω.carg D k` of the key.
Any two typed representatives of a key are compatible as images, because they have equal keys.
An abstraction at a free type of sign `−` (OpenAI's "minus" type) is stored as its table of outputs, with a fallback value when the table is not the behaviour of a value of sign `−`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem
universe u

theorem KConverts.instantiate_right {S : Type u} [Nonempty S] {a b : Expr S}
    (h : KConverts a b) (M : Expr S) : KConverts (M.instantiate a) (M.instantiate b) := by
  unfold KConverts
  rw [Expr.erase_instantiate, Expr.erase_instantiate]
  exact ConvertsBE.instantiate_right h _

namespace ContextTowerBE
variable {S : Type u} [Nonempty S] {P : Specification S} (Ω : ContextTowerBE P)

/-- A canonical representative, typed in the tower, of a term that is typed up to keys. -/
noncomputable def carg (D k : Expr S) : Expr S := by
  classical
  exact if h : ∃ n, Ω.THasTypeBE n D ∧ n.knf = k.knf then h.choose else k

variable {Ω}

theorem carg_spec {D k : Expr S} (h : Ω.KHasTypeBE k D) :
    Ω.THasTypeBE (Ω.carg D k) D ∧ (Ω.carg D k).knf = k.knf := by
  classical
  obtain ⟨M₀, A₀, h₀, hM, hA⟩ := h
  have hex : ∃ n, Ω.THasTypeBE n D ∧ n.knf = k.knf := ⟨M₀, ⟨A₀, h₀, hA⟩, hM⟩
  unfold carg
  rw [dif_pos hex]
  exact hex.choose_spec

end ContextTowerBE

namespace KP

namespace ActualPlain.Node
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P} {C : Set (Set S)}
@[ext] theorem ext {n m : ActualPlain.Node Ω C} (h : n.type = m.type) : n = m := by
  cases n; cases m; cases h; rfl
end ActualPlain.Node

namespace ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace ActiveType
variable {Ω C}
abbrev plainNode (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type)) : ActualPlain.Node Ω C :=
  ⟨T.type, T.normal, T.sorted, hp⟩
omit [Fintype S] in
@[ext] theorem ext {T U : ActiveType Ω C} (h : T.type = U.type) : T = U := by
  cases T; cases U; cases h; rfl
end ActiveType

namespace Value
variable {Ω C hno}
def plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    Value (hw := hw) Ω C hno n.type := ⟨.plain ⟨n,p⟩, rfl⟩

theorem plain_exists (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ∃ p, plain n p = v := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p =>
    have he : p.1 = n := ActualPlain.Node.ext hv
    rcases p with ⟨m,p⟩
    dsimp at he
    subst m
    exact ⟨p,rfl⟩
  | plus p => exact False.elim (hv.1 n.plain)
  | minus p => exact False.elim (hv.1 n.plain)

noncomputable def asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ActualPlain.Space (hw := hw) hno (Base Ω) n := (plain_exists n v).choose

@[simp] theorem plain_asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    plain n (asPlain n v) = v := (plain_exists n v).choose_spec

@[simp] theorem asPlain_plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    asPlain n (plain n p) = p := by
  have he := congrArg Subtype.val (plain_asPlain n (plain n p))
  exact eq_of_heq (Sigma.mk.inj (RawValue.plain.inj he)).2

theorem plus_exists {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) false)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .plus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact ⟨p,rfl⟩
  | minus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))

theorem minus_exists {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) true)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .minus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))
  | minus p => exact ⟨p,rfl⟩

noncomputable def asPlus {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) false)
    (v : Value (hw := hw) Ω C hno T) : Plus (hw := hw) Ω C hno := (plus_exists hT v).choose
noncomputable def asMinus {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) true)
    (v : Value (hw := hw) Ω C hno T) : Minus (hw := hw) Ω C hno := (minus_exists hT v).choose

@[simp] theorem asPlus_spec {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) false)
    (v : Value (hw := hw) Ω C hno T) : v.val = .plus (asPlus hT v) := (plus_exists hT v).choose_spec
@[simp] theorem asMinus_spec {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) true)
    (v : Value (hw := hw) Ω C hno T) : v.val = .minus (asMinus hT v) := (minus_exists hT v).choose_spec
end Value

namespace ActualPlainKey
variable {Ω C hno}
def frame {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n) :
    FrameKey Ω C (⟨n.type,n.normal,n.sorted,n.plain.active⟩ : ActiveType Ω C) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩

/-- The payload of a frame at a plain type, which is present exactly when the domain of the frame is active. -/
noncomputable def payload {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    Option (RawValue (hw := hw) Ω C hno) :=
  if h : ActiveLayer P C (Ω.kprofile a.domain) then
    some (.plain ⟨a.domainNode hw h, p _ (by simp only [ActualPlain.schema, h, dite_true])⟩)
  else none

theorem payload_fits {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    PayloadFits Ω C hno a.domain (payload a p) := by
  unfold payload
  split
  · rfl
  · assumption

/-- Turns a payload that fits the domain of a plain frame back into the parameters of that frame. -/
noncomputable def parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a := by
  cases p with
  | none =>
    intro d hd
    exact False.elim (hp (ActualPlain.Schema.domain_eq hd).choose)
  | some v =>
    intro d hd
    apply Value.asPlain d
    refine ⟨v,?_⟩
    obtain ⟨ha,rfl⟩ := ActualPlain.Schema.domain_eq hd
    exact hp

@[simp] theorem payload_parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    payload a (parameters a p hp) = p := by
  unfold payload
  split
  · rename_i ha
    cases p with
    | none => exact False.elim (hp ha)
    | some v =>
      simpa only [parameters, Value.plain] using
        congrArg (fun w : Value (hw := hw) Ω C hno a.domain => some w.val)
          (Value.plain_asPlain (a.domainNode hw ha) ⟨v,hp⟩)
  · rename_i ha
    cases p with
    | none => rfl
    | some v => exact False.elim (ha hp.active)
theorem payload_injective {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n) :
    Function.Injective (payload (hw := hw) (hno := hno) a) := by
  intro p q he
  funext d hd
  obtain ⟨ha,rfl⟩ := ActualPlain.Schema.domain_eq hd
  simp only [payload, ha, dite_true, Option.some.injEq, RawValue.plain.injEq] at he
  exact eq_of_heq (Sigma.mk.inj he).2

@[simp] theorem parameters_payload {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    parameters a (payload a p) (payload_fits a p) = p :=
  payload_injective a (payload_parameters a (payload a p) (payload_fits a p))

end ActualPlainKey

namespace FrameKey
variable {Ω C hno}
omit [Fintype S] in
@[ext] theorem ext {T : ActiveType Ω C} {a b : FrameKey Ω C T}
    (h : a.argument = b.argument) : a = b := by
  cases a with
  | mk D E ht q hn hh hact =>
    cases b with
    | mk D' E' ht' q' hn' hh' hact' =>
      obtain ⟨rfl,rfl⟩ := Expr.pi.inj (ht.symm.trans ht')
      cases h
      rfl

abbrev plainKey {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hT : PlainLayer P C (Ω.kprofile T.type)) : ActualPlain.Key Ω C (T.plainNode hT) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩

omit [Fintype S] in
theorem free_target {T : ActiveType Ω C} (a : FrameKey Ω C T) {sgn : Bool}
    (hT : FreeLayer P C (Ω.kprofile T.type) sgn)
    (ht : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    FreeLayer P C (Ω.kprofile (a.target hw).type) sgn := by
  rcases (a.target hw).active.classify with h | h | h
  · exact False.elim (ht h)
  · exact a.free_target_sign hw hT h ▸ h
  · exact a.free_target_sign hw hT h ▸ h
end FrameKey

/-- Stores a table of outputs as a value of sign `−`.
When the table is the behaviour of some value of sign `−`, that value is returned, so no observation changes.
Otherwise the default value of sign `−` is returned. -/
noncomputable def packMinus
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno)) : Minus (hw := hw) Ω C hno :=
  if h : ∃ x, FreeObservations.behavior _ _ _ _ x = t then h.choose
  else FreeObservations.minusDefault _ _ (topBase Ω) none

theorem packMinus_spec
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.behavior _ _ _ _ (packMinus Ω C hno t) = t := by
  simp only [packMinus, h, dite_true]
  exact h.choose_spec

theorem packMinus_stage {n : Nat}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.InStage n x ∧ FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.InStage n (packMinus Ω C hno t) := by
  obtain ⟨x,hx,he⟩ := h
  have hp := packMinus_spec Ω C hno t ⟨x,he⟩
  have hh := FreeObservations.behavior_injective (topBase Ω) (none : Option (PlainValue (hw := hw) Ω C hno))
    (hp.trans he.symm)
  exact hh ▸ hx
end ObservationValues
end KP
end PureTypeSystem


namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Gate
variable {Ω C hno} {T : ActiveType Ω C} {q : Expr S}
variable {p : Option (RawValue (hw := hw) Ω C hno)} {exit : Bool}
noncomputable def frame (h : Gate Ω C hno T q p exit) : FrameKey Ω C T := h.choose

theorem argument (h : Gate Ω C hno T q p exit) : h.frame.argument = q := h.choose_spec.1
theorem payload (h : Gate Ω C hno T q p exit) : PayloadFits Ω C hno h.frame.domain p := h.choose_spec.2.1

theorem plain (h : Gate Ω C hno T q p true) :
    PlainLayer P C (Ω.kprofile (h.frame.target hw).type) := h.choose_spec.2.2.mpr rfl

theorem not_plain (h : Gate Ω C hno T q p false) :
    ¬ PlainLayer P C (Ω.kprofile (h.frame.target hw).type) := fun hp => Bool.noConfusion (h.choose_spec.2.2.mp hp)

theorem unique (h : Gate Ω C hno T q p exit) (a : FrameKey Ω C T) (ha : a.argument = q) :
    h.frame = a := FrameKey.ext (h.argument.trans ha.symm)
end Gate

abbrev LambdaAction (T : ActiveType Ω C) := (a : FrameKey Ω C T) →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno a.domain p →
  Value (hw := hw) Ω C hno (a.target hw).type

noncomputable def tagPlain (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : PlainValue (hw := hw) Ω C hno :=
  ⟨T.plainNode hp, Value.asPlain (T.plainNode hp) v⟩

theorem tagPlain_spec (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : RawValue.plain (tagPlain Ω C hno T hp v) = v.val :=
  congrArg Subtype.val (Value.plain_asPlain (T.plainNode hp) v)

/-- The value of an abstraction at a plain type.
Its base observation is the top one, and its output after each frame is the value of the body at that frame. -/
noncomputable def plainLambda (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) : Value (hw := hw) Ω C hno T.type := by
  let n := T.plainNode hp
  apply Value.plain n
  refine (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n).symm ⟨topBase Ω, fun a p => ?_⟩
  let a' : FrameKey Ω C T := ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
  exact Value.asPlain (a.target hw)
    (act a' (ActualPlainKey.payload a p) (ActualPlainKey.payload_fits a p))

/-- The output of an abstraction at a free type on a frame that exits, which means that its target is plain.
The same check is used at types of sign `+` and of sign `−`. Only the space of payloads of the opposite sign differs, and the output always records its exact plain target. -/
noncomputable def lambdaExit {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    Option (PlainValue (hw := hw) Ω C hno) :=
  if h : Gate Ω C hno T a.1 (decode a.2) true then
    some (tagPlain Ω C hno (h.frame.target hw) h.plain (act h.frame (decode a.2) h.payload))
  else none

noncomputable def plusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) : Plus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (plusPayload Ω C hno a.2) false then
    Value.asPlus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.plusDefault _ _ (topBase Ω) none

noncomputable def minusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) : Minus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false then
    Value.asMinus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.minusDefault _ _ (topBase Ω) none

noncomputable def plusLambda (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T) :
    Plus (hw := hw) Ω C hno where
  continuing
    | [] => topBase Ω
    | a :: as => (plusContinue Ω C hno T hT act a).continuing as
  exiting
    | ([], a) => lambdaExit Ω C hno (plusPayload Ω C hno) T act a
    | (a :: as, e) => (plusContinue Ω C hno T hT act a).exiting (as,e)

noncomputable def minusLambdaBehavior (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T) :=
  FreeObservations.lambdaTable (topBase Ω) (minusContinue Ω C hno T hT act)
    (lambdaExit Ω C hno (minusPayload Ω C hno) T act)

noncomputable def lambdaValue (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T) :
    Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.kprofile T.type)
  · exact plainLambda Ω C hno T hp act
  · by_cases hf : FreeLayer P C (Ω.kprofile T.type) false
    · exact ⟨.plus (plusLambda Ω C hno T hf act),hf⟩
    · have hm : FreeLayer P C (Ω.kprofile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hm act)),hm⟩

namespace FrameKey
variable {Ω C hno} {T : ActiveType Ω C} (a : FrameKey Ω C T)

noncomputable def plusParameter (hT : FreeLayer P C (Ω.kprofile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Minus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | minus m => exact .opposite m
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

noncomputable def minusParameter (hT : FreeLayer P C (Ω.kprofile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Plus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | plus m => exact .opposite m
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem plusPayload_parameter (hT : FreeLayer P C (Ω.kprofile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plusPayload Ω C hno (a.plusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | minus m => rfl
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem minusPayload_parameter (hT : FreeLayer P C (Ω.kprofile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    minusPayload Ω C hno (a.minusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | plus m => rfl
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
end FrameKey

noncomputable def exitValue (T : ActiveType Ω C) (out : Option (PlainValue (hw := hw) Ω C hno)) :
    Value (hw := hw) Ω C hno T.type :=
  match out with
  | none => distinguished (hw := hw) Ω C hno T
  | some p => project (hw := hw) Ω C hno T (.plain p)

/-- Application of a value at a plain type to a frame.
It is a separate definition so that the dependent casts between prefixes stay abstract. -/
noncomputable def plainApply (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    Value (hw := hw) Ω C hno (a.target hw).type := by
  let n := T.plainNode hT
  let a' := a.plainKey hT
  let ps := ActualPlainKey.parameters a' p hp
  exact Value.plain (a'.target hw)
    ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n (Value.asPlain n v)).2 a' ps)

/-- Application of a value to a frame.
At a plain type it takes the next plain value.
At a free type it fixes the first frame of the table (OpenAI's "slice") when the target is free, and it reads the exit output when the target is plain. -/
noncomputable def applyValue (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Value (hw := hw) Ω C hno (a.target hw).type := by
  by_cases hT : PlainLayer P C (Ω.kprofile T.type)
  · exact plainApply Ω C hno T hT v a p hp
  · by_cases hF : FreeLayer P C (Ω.kprofile T.type) false
    · let f := Value.asPlus hF v
      let key : PlusFrame (hw := hw) Ω C hno := (a.argument, a.plusParameter hF p hp)
      by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) (f.exiting ([],key))
      · exact ⟨.plus (f.slice key), a.free_target hF hA⟩
    · have hM : FreeLayer P C (Ω.kprofile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      let f := Value.asMinus hM v
      let key : MinusFrame (hw := hw) Ω C hno := (a.argument, a.minusParameter hM p hp)
      by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) ((FreeObservations.behavior _ _ _ _ f).exiting ([],key))
      · exact ⟨.minus (FreeObservations.minusSlice f key), a.free_target hM hA⟩
end PureTypeSystem.KP.ObservationValues


namespace PureTypeSystem.KP
universe u

namespace ObservationValues
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

noncomputable abbrev actualType {M T : Expr S} (h : HasTypeBE P Γ M T) : ActualType Ω :=
  ⟨(T.subst e.images).knf, (ContextTowerBE.THasTypeBE.subst h e.typed).actual_type hw⟩

noncomputable abbrev activeType {M T : Expr S} (h : HasTypeBE P Γ M T)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) : ActiveType Ω C :=
  .ofActual (e.actualType h) ha

noncomputable abbrev actualExpression {M : Expr S} {s : S} (h : HasTypeBE P Γ M (.sort s)) : ActualType Ω :=
  ⟨(M.subst e.images).knf, (ContextTowerBE.THasTypeBE.subst h e.typed).actual_expression hw⟩

theorem type_convert_eq {M T N U : Expr S} (hM : HasTypeBE P Γ M T)
    (hN : HasTypeBE P Γ N U) (hc : ConvertsBE T U) :
    (T.subst e.images).knf = (U.subst e.images).knf :=
  Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hM e.typed).type_kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hN e.typed).type_kwn hw) (hc.subst _).k

theorem expression_convert_eq {M T N U : Expr S} (hM : HasTypeBE P Γ M T)
    (hN : HasTypeBE P Γ N U) (hc : ConvertsBE M N) :
    (M.subst e.images).knf = (N.subst e.images).knf :=
  Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst hM e.typed).kwn hw)
    ((ContextTowerBE.THasTypeBE.subst hN e.typed).kwn hw) (hc.subst _).k
end Environment

namespace ProductInstance
variable {Ω C hno}
noncomputable def ofFormation {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  let h := hp.generation_pi
  { context := Γ
    domain := D
    body := E
    domainSort := h.choose
    bodySort := h.choose_spec.choose
    resultSort := h.choose_spec.choose_spec.choose
    domainTyping := h.choose_spec.choose_spec.choose_spec.1
    bodyTyping := h.choose_spec.choose_spec.choose_spec.2.1
    rule := h.choose_spec.choose_spec.choose_spec.2.2.1
    environment := e }

noncomputable def ofFunction {Γ : List (Expr S)} {f D E : Expr S}
    (hf : HasTypeBE P Γ f (.pi D E)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  ofFormation hf.product_type_sorted.choose_spec e

variable (t : ProductInstance (hw := hw) Ω C hno)

theorem frame_domain {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.domain = t.domainNF := (Expr.pi.inj (a.product.symm.trans he)).1

theorem frame_body {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.body = t.bodyNF := (Expr.pi.inj (a.product.symm.trans he)).2

theorem frame_typed {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : Ω.KHasTypeBE a.argument t.domainNF := t.frame_domain he a ▸ a.typed

/-- The typed representative that is bound for the argument of a frame. -/
noncomputable def frameArgument {T : ActiveType Ω C} (_he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : Expr S := Ω.carg t.domainNF a.argument

theorem frameArgument_spec {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) :
    Ω.THasTypeBE (t.frameArgument he a) t.domainNF ∧ (t.frameArgument he a).knf = a.argument :=
  ⟨(ContextTowerBE.carg_spec (t.frame_typed he a)).1,
    (ContextTowerBE.carg_spec (t.frame_typed he a)).2.trans a.normal.knf⟩

noncomputable def frameEnvironment {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.extend (t.frameArgument_spec he a).1 p (t.frame_domain he a ▸ hp)

/-- Instantiating at two typed arguments with equal keys gives the same key. -/
theorem instantiate_knf_eq {n m : Expr S} (hn : Ω.KHasTypeBE n t.domainNF)
    (hm : Ω.KHasTypeBE m t.domainNF) (he : n.knf = m.knf) :
    (t.bodyNF.instantiate n).knf = (t.bodyNF.instantiate m).knf := by
  obtain ⟨s, hs⟩ := Ω.kframe_target_sorted t.product_typed hn
  obtain ⟨s', hs'⟩ := Ω.kframe_target_sorted t.product_typed hm
  exact Expr.knf_converts (hs.kwn hw) (hs'.kwn hw)
    (KConverts.instantiate_right (KConverts.of_knf_eq (hn.kwn hw) (hm.kwn hw) he) _)

theorem frame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    (t.body.subst (t.frameEnvironment he a p hp).images).knf = (a.target hw).type := by
  change t.targetNF (t.frameArgument he a) = (a.body.instantiate a.argument).knf
  rw [t.target_eq (t.frameArgument_spec he a).1, t.frame_body he a]
  exact t.instantiate_knf_eq (t.frameArgument_spec he a).1.toK (t.frame_typed he a)
    ((t.frameArgument_spec he a).2.trans a.normal.knf.symm)

/-- The frame at which a function is applied to its argument, given by keys and formed at the exact stored product. -/
noncomputable def argumentFrame {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF)
    (ha : ActiveLayer P C (Ω.kprofile (t.targetNF n))) : FrameKey Ω C T where
  domain := t.domainNF
  body := t.bodyNF
  product := he
  argument := n.knf
  normal := (Expr.knf_spec (hn.kwn hw)).2
  typed := hn.toK.knf hw
  active := by
    have h1 : (t.bodyNF.instantiate n).knf = (t.bodyNF.instantiate n.knf).knf :=
      t.instantiate_knf_eq hn.toK (hn.toK.knf hw) (Expr.knf_idem n).symm
    rw [t.target_eq hn, h1] at ha
    simpa only [ContextTowerBE.kprofile_knf] using ha

theorem argumentFrame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.THasTypeBE n t.domainNF)
    (ha : ActiveLayer P C (Ω.kprofile (t.targetNF n))) :
    ((t.argumentFrame he hn ha).target hw).type = t.targetNF n := by
  change (t.bodyNF.instantiate n.knf).knf = t.targetNF n
  rw [t.target_eq hn]
  exact t.instantiate_knf_eq (hn.toK.knf hw) hn.toK (Expr.knf_idem n)
end ProductInstance
end ObservationValues
end PureTypeSystem.KP


/-! Recursion on syntax for `Val` and `Read`. -/
namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace PayloadFits
variable {Ω C hno} {T : Expr S} {p : Option (RawValue (hw := hw) Ω C hno)}
noncomputable def value (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.kprofile T)) :
    Value (hw := hw) Ω C hno T := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => exact ⟨v,hp⟩

theorem value_spec (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.kprofile T)) :
    some (hp.value ha).val = p := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => rfl
end PayloadFits

structure PreResult {Γ : List (Expr S)} (M T : Expr S) (e : Environment (hw := hw) Ω C hno Γ) where
  val : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
    Value (hw := hw) Ω C hno (T.subst e.images).knf
  read : Candidate Ω (M.subst e.images).knf

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S} {e : Environment (hw := hw) Ω C hno Γ}
noncomputable def parameter (r : PreResult Ω C hno M T e) : Option (RawValue (hw := hw) Ω C hno) :=
  if ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) then some (r.val ha).val else none

theorem parameter_fits (r : PreResult Ω C hno M T e) :
    PayloadFits Ω C hno (T.subst e.images).knf r.parameter := by
  unfold parameter
  split
  · exact (r.val _).property
  · assumption

/-- The base clause of `Read` in the preprint. -/
noncomputable def baseRead (h : HasTypeBE P Γ M T)
    (v : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
      Value (hw := hw) Ω C hno (T.subst e.images).knf) :
    Candidate Ω (M.subst e.images).knf :=
  if _hm : Ω.kprofile (M.subst e.images).knf ∈ C then
    if hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C then
      if ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) then
        (RawValue.base Ω C hno (v ha).val) (e.actualExpression (hs.choose_spec.1 ▸ h))
      else ⟨_, Candidates.top_candidate⟩
    else ⟨_, Candidates.top_candidate⟩
  else ⟨_, Candidates.top_candidate⟩

noncomputable def baseResult (h : HasTypeBE P Γ M T)
    (v : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf) →
      Value (hw := hw) Ω C hno (T.subst e.images).knf) : PreResult Ω C hno M T e :=
  ⟨v, baseRead h v⟩

noncomputable def lookup {n : Nat} {A : Expr S} (h : HasTypeBE P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : ConvertsBE T A) (e : Environment (hw := hw) Ω C hno Γ) :
    PreResult Ω C hno (.var n) T e := by
  apply baseResult h
  intro ha
  have he : (T.subst e.images).knf = (A.subst e.images).knf :=
    e.type_convert_eq h (HasTypeBE.lookup h.valid hd) hc
  have hp := e.lawful n A hd
  rw [← he] at hp
  exact canonValue hno (e.activeType h ha) (hp.value ha)

noncomputable def sort {s t : S} (h : HasTypeBE P Γ (.sort s) T)
    (_ha : P.axioms s t) (_hc : ConvertsBE T (.sort t))
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.sort s) T e where
  val ha := distinguished Ω C hno (e.activeType h ha)
  read := ⟨_, Candidates.top_candidate⟩

noncomputable abbrev productData {D E : Expr S} {a b c : S}
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno := ⟨Γ,D,E,a,b,c,hd,hb,hr,e⟩

noncomputable def productCandidate {D E : Expr S} {a b c : S}
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b))
    (hr : P.rule a b c)
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : Candidate Ω (Expr.pi D E |>.subst e.images).knf := by
  let t := productData hd hb hr e
  let pc := t.candidate (ed e).read (fun n hn p hp => (eb (t.extend hn p hp)).read)
  exact ⟨pc.val,t.product_nf.symm ▸ pc.property⟩

noncomputable def product {D E : Expr S} {a b c : S} (h : HasTypeBE P Γ (.pi D E) T)
    (hd : HasTypeBE P Γ D (.sort a)) (hb : HasTypeBE P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (_hc : ConvertsBE T (.sort c))
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.pi D E) T e := by
  let pc := productCandidate hd hb hr ed eb e
  refine ⟨?_, ?_⟩
  · intro ha
    if hh : ({c} : Set S) ∈ C ∧ Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C then
      exact withBase Ω C hno (e.activeType h ha)
        (Base.update Ω (topBase Ω) (e.actualExpression (.product hd hb hr)) pc)
    else exact distinguished Ω C hno (e.activeType h ha)
  · exact if Ω.kprofile (Expr.pi D E |>.subst e.images).knf ∈ C then pc
      else ⟨_, Candidates.top_candidate⟩

noncomputable def abstractionAction {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) :
    LambdaAction (hw := hw) Ω C hno (e.activeType h ha) := by
  let t := ProductInstance.ofFormation hp e
  let A := e.activeType h ha
  have he : A.type = .pi t.domainNF t.bodyNF := by
    exact (Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst h e.typed).type_kwn hw)
      ((ContextTowerBE.THasTypeBE.subst hp e.typed).kwn hw) (hc.subst e.images).k).trans t.product_nf
  intro k p hk
  let e' := t.frameEnvironment he k p hk
  have he' : (E.subst e'.images).knf = (k.target hw).type := t.frame_type he k p hk
  have ha' : ActiveLayer P C (Ω.kprofile (E.subst e'.images).knf) := he' ▸ (k.target hw).active
  exact ⟨((eb e').val ha').val, he' ▸ ((eb e').val ha').property⟩

noncomputable def abstraction {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.lam D m) T e :=
  baseResult h fun ha => lambdaValue Ω C hno (e.activeType h ha) (abstractionAction h hp hc eb e ha)

noncomputable def applicationValue {f n D E : Expr S} (h : HasTypeBE P Γ (.app f n) T)
    (hf : HasTypeBE P Γ f (.pi D E)) (hn : HasTypeBE P Γ n D) (hc : ConvertsBE T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) :
    Value (hw := hw) Ω C hno (T.subst e.images).knf := by
  let Ta := e.activeType h ha
  by_cases hF : ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images).knf)
  · let t := ProductInstance.ofFunction hf e
    let Fa := e.activeType hf hF
    have he : Fa.type = .pi t.domainNF t.bodyNF := t.product_nf
    have hn' : Ω.THasTypeBE (n.subst e.images) t.domainNF :=
      (ContextTowerBE.THasTypeBE.subst hn e.typed).normalize_type hw
    have ht : (T.subst e.images).knf = t.targetNF (n.subst e.images) := by
      have hh := e.type_convert_eq h (HasTypeBE.application hf hn) hc
      rw [ProductInstance.targetNF, t.rawTarget_eq]
      simpa only [ProductInstance.rawBody, t, ProductInstance.ofFunction,
        ProductInstance.ofFormation, ← Expr.instantiate_subst] using hh
    have ha' : ActiveLayer P C (Ω.kprofile (t.targetNF (n.subst e.images))) := ht ▸ ha
    let k := t.argumentFrame he hn' ha'
    have hk : (k.target hw).type = (T.subst e.images).knf :=
      (t.argumentFrame_type he hn' ha').trans ht.symm
    let v := applyValue Ω C hno Fa ((ef e).val hF) k (en e).parameter (en e).parameter_fits
    exact ⟨v.val, hk ▸ v.property⟩
  · exact canonValue hno Ta (distinguished Ω C hno Ta)
noncomputable def application {f n D E : Expr S} (h : HasTypeBE P Γ (.app f n) T)
    (hf : HasTypeBE P Γ f (.pi D E)) (hn : HasTypeBE P Γ n D) (hc : ConvertsBE T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.app f n) T e :=
  baseResult h fun ha => applicationValue h hf hn hc ef en e ha
end PreResult

/-- Evaluation by structural recursion on a typing tree, keeping every stored choice made by the generation lemma.
The annotation child of an abstraction does not affect its observation value. -/
noncomputable def preEvaluate {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) :
    ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno M T e := by
  induction t with
  | var h hd hc => exact PreResult.lookup h hd hc
  | sort h ha hc => exact PreResult.sort h ha hc
  | product h d b hr hc ihd ihb => exact PreResult.product h d.typing b.typing hr hc ihd ihb
  | abstraction h d b hp hc ihd ihb => exact PreResult.abstraction h hp hc ihb
  | application h f a hc ihf iha => exact PreResult.application h f.typing a.typing hc ihf iha

end PureTypeSystem.KP.ObservationValues

