module

public import PTSBetaEta.Normalization.Congruence

@[expose] public section

/-!
# Laws of canonical observation values

This file proves the β-law for values, which was moved here from the adaptation of OpenAI's `ObservationReduction.lean`.
It says that the value of an abstraction, applied to a frame, gives the value of the body at that frame.
The file also proves how canonicalization interacts with application and abstraction, and that every evaluated value is canonical.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

namespace Value
variable {Ω C hno}
@[simp] theorem asPlus_plus {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) false)
    (p : Plus (hw := hw) Ω C hno) : asPlus hT ⟨.plus p,hT⟩ = p :=
  RawValue.plus.inj (asPlus_spec hT ⟨.plus p,hT⟩).symm
@[simp] theorem asMinus_minus {T : Expr S} (hT : FreeLayer P C (Ω.kprofile T) true)
    (p : Minus (hw := hw) Ω C hno) : asMinus hT ⟨.minus p,hT⟩ = p :=
  RawValue.minus.inj (asMinus_spec hT ⟨.minus p,hT⟩).symm
end Value

theorem plain_beta (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plainApply Ω C hno T hT (plainLambda Ω C hno T hT act) a p hp = act a p hp := by
  simp only [plainApply,plainLambda,Value.asPlain_plain,Equiv.apply_symm_apply]
  simp only [ActualPlainKey.payload_parameters]
  exact Value.plain_asPlain (ActualPlain.Key.target hw (a.plainKey hT)) (act a p hp)

theorem exitValue_tag (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) :
    exitValue Ω C hno T (some (tagPlain Ω C hno T hT v)) = v := by
  simp only [exitValue,tagPlain_spec,project_valid]

theorem lambdaExit_parameter {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (q : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) (hq : decode q = p)
    (ht : PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    lambdaExit Ω C hno decode T act (a.argument,q) =
      some (tagPlain Ω C hno (a.target hw) ht (act a p hp)) := by
  have hg : Gate Ω C hno T a.argument (decode q) true :=
    ⟨a,rfl,hq.symm ▸ hp,⟨fun _ => rfl,fun _ => ht⟩⟩
  simp only [lambdaExit,dite_eq_left hg]
  subst p
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (decode q))
        (htk : PlainLayer P C (Ω.kprofile (k.target hw).type)),
      some (tagPlain Ω C hno (k.target hw) htk (act k (decode q) hpk)) =
        some (tagPlain Ω C hno (a.target hw) ht (act a (decode q) hp)) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.plain

theorem plusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : PlusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : plusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    plusContinue Ω C hno T hT act q = Value.asPlus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (plusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [plusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (plusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.kprofile (k.target hw).type)),
      Value.asPlus (k.free_target hT htk) (act k (plusPayload Ω C hno v) hpk) =
        Value.asPlus (a.free_target hT ht) (act a (plusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem plusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    plusContinue Ω C hno T hT act (a.argument,a.plusParameter hT p hp) =
      Value.asPlus (a.free_target hT ht) (act a p hp) :=
  plusContinue_gate Ω C hno T hT act a _ rfl p hp (a.plusPayload_parameter hT p hp) ht

theorem minusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : MinusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : minusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    minusContinue Ω C hno T hT act q = Value.asMinus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (minusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [minusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (minusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.kprofile (k.target hw).type)),
      Value.asMinus (k.free_target hT htk) (act k (minusPayload Ω C hno v) hpk) =
        Value.asMinus (a.free_target hT ht) (act a (minusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem minusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type)) :
    minusContinue Ω C hno T hT act (a.argument,a.minusParameter hT p hp) =
      Value.asMinus (a.free_target hT ht) (act a p hp) :=
  minusContinue_gate Ω C hno T hT act a _ rfl p hp (a.minusPayload_parameter hT p hp) ht

theorem plusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) :
    (plusLambda Ω C hno T hT act).slice a = plusContinue Ω C hno T hT act a := by
  rfl

theorem minusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.kprofile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) :
    (minusLambdaBehavior Ω C hno T hT act).slice a =
      FreeObservations.behavior _ _ _ _ (minusContinue Ω C hno T hT act a) := by
  rfl

/-- **The β-law for values** (OpenAI's "raw lambda equation").
Applying the value of an abstraction to a frame gives the value of the body at that frame.
Its only premise, that the table of an abstraction of sign `−` is the behaviour of an actual value, is supplied below from the uniform finite-bound lemma for an actual body tree. -/
theorem lambda_beta (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (hr : ∀ hT : FreeLayer P C (Ω.kprofile T.type) true,
      ∃ x, FreeObservations.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T (lambdaValue Ω C hno T act) a p hp = act a p hp := by
  by_cases hT : PlainLayer P C (Ω.kprofile T.type)
  · simp only [applyValue,lambdaValue,dite_eq_left hT]
    exact plain_beta Ω C hno T hT act a p hp
  · by_cases hF : FreeLayer P C (Ω.kprofile T.type) false
    · by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_left hA,Value.asPlus_plus,plusLambda]
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.plusPayload_parameter hF p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_right hA,Value.asPlus_plus]
        apply Subtype.ext
        change RawValue.plus ((plusLambda Ω C hno T hF act).slice
          (a.argument,a.plusParameter hF p hp)) = _
        rw [plusLambda_slice,plusContinue_parameter Ω C hno T hF act a p hp hA]
        exact (Value.asPlus_spec (a.free_target hF hA) (act a p hp)).symm
    · have hM : FreeLayer P C (Ω.kprofile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      have hb := packMinus_spec Ω C hno (minusLambdaBehavior Ω C hno T hM act) (hr hM)
      by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_left hA,Value.asMinus_minus]
        rw [hb]
        change exitValue Ω C hno (a.target hw)
          (lambdaExit Ω C hno (minusPayload Ω C hno) T act (a.argument,a.minusParameter hM p hp)) = _
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.minusPayload_parameter hM p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_right hA,Value.asMinus_minus]
        apply Subtype.ext
        change RawValue.minus (FreeObservations.minusSlice
          (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hM act))
          (a.argument,a.minusParameter hM p hp)) = _
        rw [Value.asMinus_spec (a.free_target hM hA) (act a p hp)]
        apply congrArg RawValue.minus
        apply FreeObservations.behavior_injective (topBase Ω) none
        rw [FreeObservations.behavior_minusSlice,hb,minusLambda_slice,
          minusContinue_parameter Ω C hno T hM act a p hp hA]

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
theorem abstraction_beta {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hub : Uniform Ω C hno eb B) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (a : FrameKey Ω C (e.activeType h ha)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno (e.activeType h ha) ((abstraction h hp hc eb e).val ha) a p hpp =
      abstractionAction h hp hc eb e ha a p hpp := by
  apply lambda_beta
  intro hT
  obtain ⟨k,hk⟩ := e.exists_bound
  obtain ⟨v,_,hv⟩ := minusLambda_representable Ω C hno hT (by have := hub.growth k; omega)
    (abstractionAction_bounded h hp hc eb hub k e hk ha)
    (fun a p p' hp' hp'' hbp hbp' hpp =>
      abstractionAction_level h hp hc eb hub k e e hk hk (e.level_refl _) ha ha a a rfl
        p p' hp' hp'' hbp hbp' hpp)
  exact ⟨v,hv⟩
end PreResult

/-! ## Unfolding application -/

section Unfold
variable {Ω C hno}

theorem applyValue_plain (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T v a p hp = plainApply Ω C hno T hT v a p hp := by
  simp only [applyValue, dite_eq_left hT]

theorem applyValue_plus_exit (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : FreeLayer P C (Ω.kprofile T.type) false) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (hA : PlainLayer P C (Ω.kprofile (a.target hw).type))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T v a p hp = exitValue Ω C hno (a.target hw)
      ((Value.asPlus hF v).exiting ([], (a.argument, a.plusParameter hF p hp))) := by
  simp only [applyValue, dite_eq_right hT, dite_eq_left hF, dite_eq_left hA]

theorem applyValue_plus_slice (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : FreeLayer P C (Ω.kprofile T.type) false) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (hA : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    (applyValue Ω C hno T v a p hp).val =
      .plus ((Value.asPlus hF v).slice (a.argument, a.plusParameter hF p hp)) := by
  simp only [applyValue, dite_eq_right hT, dite_eq_left hF, dite_eq_right hA]

theorem applyValue_minus_exit (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : ¬ FreeLayer P C (Ω.kprofile T.type) false) (hM : FreeLayer P C (Ω.kprofile T.type) true)
    (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (hA : PlainLayer P C (Ω.kprofile (a.target hw).type))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T v a p hp = exitValue Ω C hno (a.target hw)
      ((FreeObservations.behavior _ _ _ _ (Value.asMinus hM v)).exiting
        ([], (a.argument, a.minusParameter hM p hp))) := by
  simp only [applyValue, dite_eq_right hT, dite_eq_right hF, dite_eq_left hA]

theorem applyValue_minus_slice (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : ¬ FreeLayer P C (Ω.kprofile T.type) false) (hM : FreeLayer P C (Ω.kprofile T.type) true)
    (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (hA : ¬ PlainLayer P C (Ω.kprofile (a.target hw).type))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    (applyValue Ω C hno T v a p hp).val =
      .minus (FreeObservations.minusSlice (Value.asMinus hM v) (a.argument, a.minusParameter hM p hp)) := by
  simp only [applyValue, dite_eq_right hT, dite_eq_right hF, dite_eq_right hA]

theorem free_minus_of (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : ¬ FreeLayer P C (Ω.kprofile T.type) false) : FreeLayer P C (Ω.kprofile T.type) true := by
  rcases T.active.classify with h | h | h
  · exact False.elim (hT h)
  · exact False.elim (hF h)
  · exact h

end Unfold

/-! ## Canonical forms of plain values and of values at free types -/

section CanonForms
variable {Ω C hno}

theorem asPlain_canon (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (v : Value (hw := hw) Ω C hno T.type) :
    Value.asPlain (T.plainNode hT) (canonValue hno T v) =
      canonSpace hno _ (Value.asPlain (T.plainNode hT) v) := by
  have h1 : canonValue hno T v =
      Value.plain (T.plainNode hT) (canonSpace hno _ (Value.asPlain (T.plainNode hT) v)) := by
    apply Subtype.ext
    rw [canonValue_val]
    have h2 := congrArg Subtype.val (Value.plain_asPlain (T.plainNode hT) v)
    rw [← h2]
    rfl
  rw [h1, Value.asPlain_plain]

theorem asPlus_canon (T : ActiveType Ω C) (hF : FreeLayer P C (Ω.kprofile T.type) false)
    (v : Value (hw := hw) Ω C hno T.type) :
    Value.asPlus hF (canonValue hno T v) = cPlus hno T (Value.asPlus hF v) := by
  have h1 := Value.asPlus_spec hF (canonValue hno T v)
  have h2 : (canonValue hno T v).val = .plus (cPlus hno T (Value.asPlus hF v)) := by
    rw [canonValue_val, Value.asPlus_spec hF v]
    rfl
  exact RawValue.plus.inj (h1.symm.trans h2)

theorem asMinus_canon (T : ActiveType Ω C) (hM : FreeLayer P C (Ω.kprofile T.type) true)
    (v : Value (hw := hw) Ω C hno T.type) :
    Value.asMinus hM (canonValue hno T v) = cMinus hno T (Value.asMinus hM v) := by
  have h1 := Value.asMinus_spec hM (canonValue hno T v)
  have h2 : (canonValue hno T v).val = .minus (cMinus hno T (Value.asMinus hM v)) := by
    rw [canonValue_val, Value.asMinus_spec hM v]
    rfl
  exact RawValue.minus.inj (h1.symm.trans h2)

theorem payload_canon {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (ps : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    ActualPlainKey.payload a (fun d h => canonSpace hno d (ps d h)) =
      canonOpt hno a.domain (ActualPlainKey.payload a ps) := by
  unfold ActualPlainKey.payload
  by_cases ha : ActiveLayer P C (Ω.kprofile a.domain)
  · have hq : KNormal a.domain ∧ (∃ s, Ω.KHasTypeBE a.domain (.sort s)) ∧
        ActiveLayer P C (Ω.kprofile a.domain) :=
      ⟨(a.domainNode hw ha).normal, (a.domainNode hw ha).sorted, ha⟩
    simp only [dif_pos ha, canonOpt, dif_pos hq]
    rfl
  · simp only [dif_neg ha]
    rfl

theorem parameters_canon {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hp' : PayloadFits Ω C hno a.domain (canonOpt hno a.domain p)) :
    ActualPlainKey.parameters a (canonOpt hno a.domain p) hp' =
      fun d h => canonSpace hno d (ActualPlainKey.parameters a p hp d h) := by
  apply ActualPlainKey.payload_injective a
  rw [ActualPlainKey.payload_parameters, payload_canon, ActualPlainKey.payload_parameters]

theorem FrameKey.plusParameter_eq {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hF : FreeLayer P C (Ω.kprofile T.type) false) {p q : Option (RawValue (hw := hw) Ω C hno)}
    (h : p = q) (hp : PayloadFits Ω C hno a.domain p) (hq : PayloadFits Ω C hno a.domain q) :
    a.plusParameter hF p hp = a.plusParameter hF q hq := by
  subst h
  rfl

theorem FrameKey.minusParameter_eq {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hM : FreeLayer P C (Ω.kprofile T.type) true) {p q : Option (RawValue (hw := hw) Ω C hno)}
    (h : p = q) (hp : PayloadFits Ω C hno a.domain p) (hq : PayloadFits Ω C hno a.domain q) :
    a.minusParameter hM p hp = a.minusParameter hM q hq := by
  subst h
  rfl

theorem plusParameter_canon {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hF : FreeLayer P C (Ω.kprofile T.type) false) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (hp' : PayloadFits Ω C hno a.domain (canonOpt hno a.domain p)) :
    a.plusParameter hF (canonOpt hno a.domain p) hp' =
      canonPayload hno a (cMinus hno) (a.plusParameter hF p hp) := by
  cases p with
  | none => rfl
  | some v =>
    have hd : ActiveLayer P C (Ω.kprofile a.domain) := Fits.active hp
    have hc : canonOpt hno a.domain (some v) = some (canonRaw hno (a.domainType hd) v) :=
      canonOpt_active (a.domainType hd) v
    rw [FrameKey.plusParameter_eq a hF hc hp' (hc ▸ hp')]
    cases v with
    | plain q => rfl
    | minus m =>
      show FreeObservations.Payload.opposite (cMinus hno (a.domainType hd) m) =
        canonPayload hno a (cMinus hno) (.opposite m)
      simp only [canonPayload, dif_pos hd]
    | plus t => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hF hp))

theorem minusParameter_canon {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hM : FreeLayer P C (Ω.kprofile T.type) true) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (hp' : PayloadFits Ω C hno a.domain (canonOpt hno a.domain p)) :
    a.minusParameter hM (canonOpt hno a.domain p) hp' =
      canonPayload hno a (cPlus hno) (a.minusParameter hM p hp) := by
  cases p with
  | none => rfl
  | some v =>
    have hd : ActiveLayer P C (Ω.kprofile a.domain) := Fits.active hp
    have hc : canonOpt hno a.domain (some v) = some (canonRaw hno (a.domainType hd) v) :=
      canonOpt_active (a.domainType hd) v
    rw [FrameKey.minusParameter_eq a hM hc hp' (hc ▸ hp')]
    cases v with
    | plain q => rfl
    | plus t =>
      show FreeObservations.Payload.opposite (cPlus hno (a.domainType hd) t) =
        canonPayload hno a (cPlus hno) (.opposite t)
      simp only [canonPayload, dif_pos hd]
    | minus m => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hM hp))

theorem plusParameter_plusPayload {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hF : FreeLayer P C (Ω.kprofile T.type) false)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Minus (hw := hw) Ω C hno))
    (h : PayloadFits Ω C hno a.domain (plusPayload Ω C hno pl)) :
    a.plusParameter hF (plusPayload Ω C hno pl) h = pl := by
  cases pl <;> rfl

theorem minusParameter_minusPayload {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hM : FreeLayer P C (Ω.kprofile T.type) true)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Plus (hw := hw) Ω C hno))
    (h : PayloadFits Ω C hno a.domain (minusPayload Ω C hno pl)) :
    a.minusParameter hM (minusPayload Ω C hno pl) h = pl := by
  cases pl <;> rfl

theorem fits_plusPayload (D : Expr S)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Minus (hw := hw) Ω C hno)) :
    PayloadFits Ω C hno D (plusPayload Ω C hno pl) ↔ PayloadFits Ω C hno D (tagDecode hno false pl) := by
  cases pl <;> exact Iff.rfl

theorem fits_minusPayload (D : Expr S)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Plus (hw := hw) Ω C hno)) :
    PayloadFits Ω C hno D (minusPayload Ω C hno pl) ↔ PayloadFits Ω C hno D (tagDecode hno true pl) := by
  cases pl <;> exact Iff.rfl

theorem exitValue_val (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) :
    (exitValue Ω C hno T o).val = .plain (exitPlain hno T hT o) := by
  cases o with
  | none =>
    simp only [exitValue, distinguished, dif_pos hT]
    rfl
  | some q =>
    by_cases hq : q.1 = ⟨T.type, T.normal, T.sorted, hT⟩
    · have hf : Fits Ω C hno T.type (.plain q) := by
        show q.1.type = T.type
        rw [hq]
      rw [exitPlain_of_fst T hT q hq]
      simp only [exitValue, project, dif_pos hf]
    · have hf : ¬ Fits Ω C hno T.type (.plain q) := fun h => hq (ActualPlain.Node.ext h)
      simp only [exitValue, project, dif_neg hf, distinguished, dif_pos hT, exitPlain, if_neg hq]

theorem canon_exitValue (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) :
    (canonValue hno T (exitValue Ω C hno T o)).val = .plain (canonPV hno (exitPlain hno T hT o)) := by
  rw [canonValue_val, exitValue_val T hT o]
  rfl

theorem tagPlain_canon_exit (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) :
    tagPlain Ω C hno T hT (canonValue hno T (exitValue Ω C hno T o)) =
      canonPV hno (exitPlain hno T hT o) :=
  RawValue.plain.inj ((tagPlain_spec Ω C hno T hT _).trans (canon_exitValue T hT o))

theorem table_ext_slices {Y : Type u}
    (t u : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    (h0 : t.continuing [] = u.continuing [])
    (he : ∀ e, t.exiting ([], e) = u.exiting ([], e))
    (hs : ∀ a, t.slice a = u.slice a) : t = u := by
  apply FreeObservations.Table.ext
  · funext as
    cases as with
    | nil => exact h0
    | cons a as => exact congrArg (fun w => w.continuing as) (hs a)
  · funext x
    obtain ⟨as, e⟩ := x
    cases as with
    | nil => exact he e
    | cons a as => exact congrArg (fun w => w.exiting (as, e)) (hs a)

theorem frameAt_unique {T : ActiveType Ω C} {q : Expr S} {k k' : FrameKey Ω C T}
    (hk : frameAt T q = some k) (hk' : k'.argument = q) : k' = k := by
  have h := frameAt_of k'
  rw [hk', hk] at h
  exact (Option.some.inj h).symm

end CanonForms

/-! ## Application commutes with canonicalization -/

section ApplyCanon
variable {Ω C hno}

theorem applyValue_canon (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T (canonValue hno T v) a p hp =
      canonValue hno (a.target hw) (applyValue Ω C hno T v a (canonOpt hno a.domain p) (canonOpt_fits hp)) := by
  have hk := frameAt_of a
  by_cases hT : PlainLayer P C (Ω.kprofile T.type)
  · rw [applyValue_plain T hT, applyValue_plain T hT]
    apply Subtype.ext
    show RawValue.plain ⟨_, (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) (canonValue hno T v))).2 (a.plainKey hT)
          (ActualPlainKey.parameters (a.plainKey hT) p hp)⟩ =
      RawValue.plain (canonPV hno ⟨_, (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) v)).2 (a.plainKey hT)
          (ActualPlainKey.parameters (a.plainKey hT) (canonOpt hno a.domain p) (canonOpt_fits hp))⟩)
    rw [asPlain_canon T hT v, canonSpace_prefix, parameters_canon (a.plainKey hT) p hp]
    rfl
  · by_cases hF : FreeLayer P C (Ω.kprofile T.type) false
    · have hfit : PayloadFits Ω C hno a.domain (tagDecode hno false (a.plusParameter hF p hp)) :=
        (fits_plusPayload _ _).mp (by rw [a.plusPayload_parameter hF p hp]; exact hp)
      by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · rw [applyValue_plus_exit T hT hF (canonValue hno T v) a hA, applyValue_plus_exit T hT hF v a hA]
        apply Subtype.ext
        rw [canon_exitValue _ hA, asPlus_canon]
        have hx : ExitOK hno a false (a.plusParameter hF p hp) := ⟨hfit, hA⟩
        rw [show (cPlus hno T (Value.asPlus hF v)).exiting ([], (a.argument, a.plusParameter hF p hp)) = _ from
          maskTable_exiting_some false (cMinus hno) (Value.asPlus hF v)
            (as := []) (e := (a.argument, a.plusParameter hF p hp)) rfl hk hx]
        rw [exitValue_val _ hA, canonPV_exitPlain, plusParameter_canon a hF p hp (canonOpt_fits hp)]
        rfl
      · apply Subtype.ext
        rw [applyValue_plus_slice T hT hF (canonValue hno T v) a hA, canonValue_val,
          applyValue_plus_slice T hT hF v a hA, asPlus_canon]
        have hc : ContinueOK hno a false (a.plusParameter hF p hp) := ⟨hfit, hA⟩
        rw [show (cPlus hno T (Value.asPlus hF v)).slice (a.argument, a.plusParameter hF p hp) = _ from
          maskTable_slice_legal false (cMinus hno) (Value.asPlus hF v)
            (a := (a.argument, a.plusParameter hF p hp)) hk hc,
          plusParameter_canon a hF p hp (canonOpt_fits hp)]
        rfl
    · have hM := free_minus_of T hT hF
      have hfit : PayloadFits Ω C hno a.domain (tagDecode hno true (a.minusParameter hM p hp)) :=
        (fits_minusPayload _ _).mp (by rw [a.minusPayload_parameter hM p hp]; exact hp)
      by_cases hA : PlainLayer P C (Ω.kprofile (a.target hw).type)
      · rw [applyValue_minus_exit T hT hF hM (canonValue hno T v) a hA,
          applyValue_minus_exit T hT hF hM v a hA]
        apply Subtype.ext
        rw [canon_exitValue _ hA, asMinus_canon, behavior_cMinus]
        have hx : ExitOK hno a true (a.minusParameter hM p hp) := ⟨hfit, hA⟩
        rw [maskTable_exiting_some true (cPlus hno) _ (as := []) (e := (a.argument, a.minusParameter hM p hp))
          rfl hk hx]
        rw [exitValue_val _ hA, canonPV_exitPlain, minusParameter_canon a hM p hp (canonOpt_fits hp)]
        rfl
      · apply Subtype.ext
        rw [applyValue_minus_slice T hT hF hM (canonValue hno T v) a hA, canonValue_val,
          applyValue_minus_slice T hT hF hM v a hA, asMinus_canon]
        have hc : ContinueOK hno a true (a.minusParameter hM p hp) := ⟨hfit, hA⟩
        show RawValue.minus _ = RawValue.minus (cMinus hno (a.target hw) _)
        congr 1
        apply FreeObservations.behavior_injective (topBase Ω) none
        rw [FreeObservations.behavior_minusSlice, behavior_cMinus, behavior_cMinus,
          FreeObservations.behavior_minusSlice,
          maskTable_slice_legal true (cPlus hno) _ (a := (a.argument, a.minusParameter hM p hp)) hk hc,
          minusParameter_canon a hM p hp (canonOpt_fits hp)]

end ApplyCanon

/-! ## The η law for values -/

section Eta
variable {Ω C hno}

variable (Ω C hno) in
/-- The values of the body of the η-expansion of a value, one for each frame (its "λ-action").
At each frame it applies the value to the canonical form of the payload and makes the result canonical. -/
noncomputable def etaAction (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    LambdaAction (hw := hw) Ω C hno T :=
  fun a p hp => canonValue hno (a.target hw)
    (applyValue Ω C hno T v a (canonOpt hno a.domain p) (canonOpt_fits hp))

theorem gate_none {T : ActiveType Ω C} {q : Expr S}
    {pl : Option (RawValue (hw := hw) Ω C hno)} {exit : Bool}
    (hk : frameAt T q = none) : ¬ Gate Ω C hno T q pl exit := by
  rintro ⟨k, hka, -, -⟩
  rw [← hka, frameAt_of] at hk
  cases hk

theorem plusLambda_eta (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : FreeLayer P C (Ω.kprofile T.type) false) (hns : ¬ IsSortType T)
    (v : Value (hw := hw) Ω C hno T.type) :
    plusLambda Ω C hno T hF (etaAction Ω C hno T v) = cPlus hno T (Value.asPlus hF v) := by
  apply table_ext_slices
  · show topBase Ω = (maskTable hno false (cMinus hno) T (Value.asPlus hF v)).continuing []
    rw [maskTable_nil, if_neg hns]
  · intro e
    obtain ⟨q, pl⟩ := e
    show lambdaExit Ω C hno (plusPayload Ω C hno) T (etaAction Ω C hno T v) (q, pl) =
      (maskTable hno false (cMinus hno) T (Value.asPlus hF v)).exiting ([], (q, pl))
    cases hk : frameAt T q with
    | none =>
      rw [maskTable_exiting_none_frame false (cMinus hno) _ (as := []) (e := (q, pl)) rfl hk]
      simp only [lambdaExit, dif_neg (gate_none hk)]
    | some k =>
      have hke : k.argument = q := frameAt_argument hk
      by_cases hx : ExitOK hno k false pl
      · rw [maskTable_exiting_some false (cMinus hno) _ (as := []) (e := (q, pl)) rfl hk hx]
        have hp : PayloadFits Ω C hno k.domain (plusPayload Ω C hno pl) := (fits_plusPayload _ _).mpr hx.1
        subst hke
        rw [lambdaExit_parameter Ω C hno _ T _ k _ hp pl rfl hx.2]
        congr 1
        show tagPlain Ω C hno (k.target hw) hx.2 (canonValue hno (k.target hw)
          (applyValue Ω C hno T v k (canonOpt hno k.domain (plusPayload Ω C hno pl)) (canonOpt_fits hp))) = _
        rw [applyValue_plus_exit T hT hF v k hx.2, tagPlain_canon_exit,
          plusParameter_canon k hF _ hp, plusParameter_plusPayload]
        rfl
      · rw [maskTable_exiting_none_ok false (cMinus hno) _ (as := []) (e := (q, pl)) rfl hk hx]
        have hg : ¬ Gate Ω C hno T q (plusPayload Ω C hno pl) true := by
          rintro ⟨k', hka, hfit, hpl⟩
          have h' := frameAt_unique hk hka
          subst h'
          exact hx ⟨(fits_plusPayload _ _).mp hfit, hpl.mpr rfl⟩
        simp only [lambdaExit, dif_neg hg]
  · intro fr
    show plusContinue Ω C hno T hF (etaAction Ω C hno T v) fr =
      (maskTable hno false (cMinus hno) T (Value.asPlus hF v)).slice fr
    cases hk : frameAt T fr.1 with
    | none =>
      rw [maskTable_slice_illegal false (cMinus hno) _ (fun k h => by rw [hk] at h; cases h)]
      simp only [plusContinue, dif_neg (gate_none hk)]
      rfl
    | some k =>
      have hke : k.argument = fr.1 := frameAt_argument hk
      by_cases hc : ContinueOK hno k false fr.2
      · rw [maskTable_slice_legal false (cMinus hno) _ hk hc]
        have hp : PayloadFits Ω C hno k.domain (plusPayload Ω C hno fr.2) :=
          (fits_plusPayload _ _).mpr hc.1
        rw [plusContinue_gate Ω C hno T hF _ k fr hke.symm _ hp rfl hc.2]
        show Value.asPlus _ (canonValue hno (k.target hw) (applyValue Ω C hno T v k _ _)) =
          cPlus hno (k.target hw) _
        rw [asPlus_canon]
        congr 1
        apply RawValue.plus.inj
        rw [← Value.asPlus_spec, applyValue_plus_slice T hT hF v k hc.2,
          plusParameter_canon k hF _ hp, plusParameter_plusPayload, hke]
      · rw [maskTable_slice_illegal false (cMinus hno) _ (fun k' h => by
          rw [hk] at h; cases h; exact hc)]
        have hg : ¬ Gate Ω C hno T fr.1 (plusPayload Ω C hno fr.2) false := by
          rintro ⟨k', hka, hfit, hpl⟩
          have h' := frameAt_unique hk hka
          subst h'
          exact hc ⟨(fits_plusPayload _ _).mp hfit, fun h => Bool.noConfusion (hpl.mp h)⟩
        simp only [plusContinue, dif_neg hg]
        rfl

theorem minusLambda_eta (T : ActiveType Ω C) (hT : ¬ PlainLayer P C (Ω.kprofile T.type))
    (hF : ¬ FreeLayer P C (Ω.kprofile T.type) false) (hM : FreeLayer P C (Ω.kprofile T.type) true)
    (hns : ¬ IsSortType T) (v : Value (hw := hw) Ω C hno T.type) :
    minusLambdaBehavior Ω C hno T hM (etaAction Ω C hno T v) =
      maskTable hno true (cPlus hno) T (FreeObservations.behavior _ _ _ _ (Value.asMinus hM v)) := by
  apply table_ext_slices
  · show topBase Ω = _
    rw [maskTable_nil, if_neg hns]
  · intro e
    obtain ⟨q, pl⟩ := e
    show lambdaExit Ω C hno (minusPayload Ω C hno) T (etaAction Ω C hno T v) (q, pl) = _
    cases hk : frameAt T q with
    | none =>
      rw [maskTable_exiting_none_frame true (cPlus hno) _ (as := []) (e := (q, pl)) rfl hk]
      simp only [lambdaExit, dif_neg (gate_none hk)]
    | some k =>
      have hke : k.argument = q := frameAt_argument hk
      by_cases hx : ExitOK hno k true pl
      · rw [maskTable_exiting_some true (cPlus hno) _ (as := []) (e := (q, pl)) rfl hk hx]
        have hp : PayloadFits Ω C hno k.domain (minusPayload Ω C hno pl) :=
          (fits_minusPayload _ _).mpr hx.1
        subst hke
        rw [lambdaExit_parameter Ω C hno _ T _ k _ hp pl rfl hx.2]
        congr 1
        show tagPlain Ω C hno (k.target hw) hx.2 (canonValue hno (k.target hw)
          (applyValue Ω C hno T v k (canonOpt hno k.domain (minusPayload Ω C hno pl)) (canonOpt_fits hp))) = _
        rw [applyValue_minus_exit T hT hF hM v k hx.2, tagPlain_canon_exit,
          minusParameter_canon k hM _ hp, minusParameter_minusPayload]
        rfl
      · rw [maskTable_exiting_none_ok true (cPlus hno) _ (as := []) (e := (q, pl)) rfl hk hx]
        have hg : ¬ Gate Ω C hno T q (minusPayload Ω C hno pl) true := by
          rintro ⟨k', hka, hfit, hpl⟩
          have h' := frameAt_unique hk hka
          subst h'
          exact hx ⟨(fits_minusPayload _ _).mp hfit, hpl.mpr rfl⟩
        simp only [lambdaExit, dif_neg hg]
  · intro fr
    show FreeObservations.behavior _ _ _ _ (minusContinue Ω C hno T hM (etaAction Ω C hno T v) fr) =
      (maskTable hno true (cPlus hno) T _).slice fr
    cases hk : frameAt T fr.1 with
    | none =>
      rw [maskTable_slice_illegal true (cPlus hno) _ (fun k h => by rw [hk] at h; cases h)]
      simp only [minusContinue, dif_neg (gate_none hk)]
      rfl
    | some k =>
      have hke : k.argument = fr.1 := frameAt_argument hk
      by_cases hc : ContinueOK hno k true fr.2
      · rw [maskTable_slice_legal true (cPlus hno) _ hk hc]
        have hp : PayloadFits Ω C hno k.domain (minusPayload Ω C hno fr.2) :=
          (fits_minusPayload _ _).mpr hc.1
        rw [minusContinue_gate Ω C hno T hM _ k fr hke.symm _ hp rfl hc.2]
        show FreeObservations.behavior _ _ _ _
          (Value.asMinus _ (canonValue hno (k.target hw) (applyValue Ω C hno T v k _ _))) = _
        rw [asMinus_canon, behavior_cMinus]
        congr 1
        have hv := applyValue_minus_slice T hT hF hM v k hc.2
          (canonOpt hno k.domain (minusPayload Ω C hno fr.2)) (canonOpt_fits hp)
        have hm : Value.asMinus (k.free_target hM hc.2)
            (applyValue Ω C hno T v k (canonOpt hno k.domain (minusPayload Ω C hno fr.2)) (canonOpt_fits hp)) =
            FreeObservations.minusSlice (Value.asMinus hM v)
              (k.argument, k.minusParameter hM (canonOpt hno k.domain (minusPayload Ω C hno fr.2))
                (canonOpt_fits hp)) :=
          RawValue.minus.inj ((Value.asMinus_spec _ _).symm.trans hv)
        rw [hm, FreeObservations.behavior_minusSlice, minusParameter_canon k hM _ hp,
          minusParameter_minusPayload, hke]
      · rw [maskTable_slice_illegal true (cPlus hno) _ (fun k' h => by
          rw [hk] at h; cases h; exact hc)]
        have hg : ¬ Gate Ω C hno T fr.1 (minusPayload Ω C hno fr.2) false := by
          rintro ⟨k', hka, hfit, hpl⟩
          have h' := frameAt_unique hk hka
          subst h'
          exact hc ⟨(fits_minusPayload _ _).mp hfit, fun h => Bool.noConfusion (hpl.mp h)⟩
        simp only [minusContinue, dif_neg hg]
        rfl

/-- A plain value is determined by its base observation and by its applications to frames. -/
theorem plain_ext (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.kprofile T.type))
    (u w : Value (hw := hw) Ω C hno T.type)
    (hb : (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) u)).1 =
      (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) w)).1)
    (happ : ∀ a p hp, plainApply Ω C hno T hT u a p hp = plainApply Ω C hno T hT w a p hp) :
    u = w := by
  rw [← Value.plain_asPlain (T.plainNode hT) u, ← Value.plain_asPlain (T.plainNode hT) w]
  congr 1
  apply (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)).injective
  apply Prod.ext hb
  funext a ps
  let a' : FrameKey Ω C T := ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
  have h := congrArg (Value.asPlain (ActualPlain.Key.target hw a))
    (happ a' (ActualPlainKey.payload a ps) (ActualPlainKey.payload_fits a ps))
  change Value.asPlain _ (Value.plain _
      ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) u)).2 a
        (ActualPlainKey.parameters a (ActualPlainKey.payload a ps) (ActualPlainKey.payload_fits a ps)))) =
    Value.asPlain _ (Value.plain _
      ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)
        (Value.asPlain (T.plainNode hT) w)).2 a
        (ActualPlainKey.parameters a (ActualPlainKey.payload a ps) (ActualPlainKey.payload_fits a ps)))) at h
  have e := ActualPlainKey.parameters_payload (hw := hw) (hno := hno)
    (a : ActualPlain.Key Ω C (T.plainNode hT)) ps
  rw [Value.asPlain_plain, Value.asPlain_plain, e] at h
  exact h

/-- **η for values.**
At a type that is not a sort, the λ-value of the η-expansion of a value is the canonical form of that value. -/
theorem lambdaValue_eta (T : ActiveType Ω C) (hns : ¬ IsSortType T)
    (v : Value (hw := hw) Ω C hno T.type) :
    lambdaValue Ω C hno T (etaAction Ω C hno T v) = canonValue hno T v := by
  by_cases hT : PlainLayer P C (Ω.kprofile T.type)
  · have hn : ¬ IsSortNode (T.plainNode hT) := hns
    have hl : lambdaValue Ω C hno T (etaAction Ω C hno T v) =
        plainLambda Ω C hno T hT (etaAction Ω C hno T v) := by
      simp only [lambdaValue, dite_eq_left hT]
    apply plain_ext T hT
    · rw [hl, asPlain_canon T hT v, canonSpace_prefix, if_neg hn]
      simp only [plainLambda, Value.asPlain_plain, Equiv.apply_symm_apply]
    · intro a p hp
      rw [hl, plain_beta, ← applyValue_plain T hT, applyValue_canon]
      rfl
  · by_cases hF : FreeLayer P C (Ω.kprofile T.type) false
    · apply Subtype.ext
      simp only [lambdaValue, dite_eq_right hT, dite_eq_left hF]
      rw [canonValue_val, Value.asPlus_spec hF v]
      exact congrArg RawValue.plus (plusLambda_eta T hT hF hns v)
    · have hM := free_minus_of T hT hF
      apply Subtype.ext
      simp only [lambdaValue, dite_eq_right hT, dite_eq_right hF]
      rw [canonValue_val, Value.asMinus_spec hM v]
      show RawValue.minus _ = RawValue.minus (cMinus hno T (Value.asMinus hM v))
      congr 1
      have hb : FreeObservations.behavior _ _ _ _ (cMinus hno T (Value.asMinus hM v)) =
          minusLambdaBehavior Ω C hno T hM (etaAction Ω C hno T v) :=
        (behavior_cMinus T _).trans (minusLambda_eta T hT hF hM hns v).symm
      apply FreeObservations.behavior_injective (topBase Ω) none
      rw [packMinus_spec Ω C hno _ ⟨_, hb⟩, hb]

end Eta

/-! ## Values at sort types are canonical -/

section SortCanon
variable {Ω C hno}

theorem noFrame {T : ActiveType Ω C} (hs : IsSortType T) (k : FrameKey Ω C T) : False := by
  obtain ⟨s, h⟩ := hs
  have hp := k.product
  rw [h] at hp
  cases hp

theorem frameAt_sortType {T : ActiveType Ω C} (hs : IsSortType T) (q : Expr S) : frameAt T q = none := by
  cases h : frameAt T q with
  | none => rfl
  | some k => exact (noFrame hs k).elim

theorem maskTable_sortType {Y : Type u} (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    (hs : IsSortType T)
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    (h1 : ∀ fr as, t.continuing (fr :: as) = topBase Ω) (h2 : ∀ x, t.exiting x = none) :
    maskTable hno sgn g T t = t := by
  apply FreeObservations.Table.ext
  · funext as
    cases as with
    | nil => rw [maskTable_nil, if_pos hs]
    | cons fr as =>
      rw [maskTable_continuing_none sgn g t (walk_cons_illegal sgn as (fun k _ => (noFrame hs k).elim)), h1]
  · funext x
    obtain ⟨as, e⟩ := x
    cases as with
    | nil => rw [maskTable_exiting_none_frame sgn g t (as := []) rfl (frameAt_sortType hs e.1), h2]
    | cons fr as =>
      rw [maskTable_exiting_none_walk sgn g t e (walk_cons_illegal sgn as (fun k _ => (noFrame hs k).elim)), h2]

theorem canonSpace_sortNode (n : ActualPlain.Node Ω C) (hs : IsSortNode n)
    (x : ActualPlain.Space (hw := hw) hno (Base Ω) n) : canonSpace hno n x = x := by
  apply ((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n).injective
  funext p xs
  cases p with
  | nil =>
    refine (canonSpace_unfold n x _ xs).trans ?_
    split
    · refine congrArg (fun z => (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno)
        (Base Ω) n x (.nil n) z) ?_
      funext d sl
      cases sl
    · exact absurd hs ‹_›
  | cons a p =>
    exfalso
    obtain ⟨s, h⟩ := hs
    have hp := a.product
    rw [h] at hp
    cases hp

theorem canon_distinguished_sort (T : ActiveType Ω C) (hs : IsSortType T) :
    canonValue hno T (distinguished (hw := hw) Ω C hno T) = distinguished Ω C hno T := by
  apply Subtype.ext
  rw [canonValue_val]
  unfold distinguished
  by_cases hp : PlainLayer P C (Ω.kprofile T.type)
  · simp only [dif_pos hp]
    show RawValue.plain (canonPV hno _) = _
    exact congrArg RawValue.plain (Sigma.ext rfl (heq_of_eq
      (canonSpace_sortNode ⟨T.type, T.normal, T.sorted, hp⟩ hs _)))
  · by_cases hf : FreeLayer P C (Ω.kprofile T.type) false
    · simp only [dif_neg hp, dif_pos hf]
      exact congrArg RawValue.plus (maskTable_sortType false _ hs _ (fun _ _ => rfl) (fun _ => rfl))
    · simp only [dif_neg hp, dif_neg hf]
      show RawValue.minus (cMinus hno T _) = _
      congr 1
      apply FreeObservations.behavior_injective (topBase Ω) none
      rw [behavior_cMinus]
      exact maskTable_sortType true _ hs _ (fun _ _ => rfl) (fun _ => rfl)

theorem canon_withBase_sort (T : ActiveType Ω C) (hs : IsSortType T) (b : Base Ω) :
    canonValue hno T (withBase (hw := hw) Ω C hno T b) = withBase Ω C hno T b := by
  apply Subtype.ext
  rw [canonValue_val]
  unfold withBase
  by_cases hp : PlainLayer P C (Ω.kprofile T.type)
  · simp only [dif_pos hp]
    show RawValue.plain (canonPV hno _) = _
    exact congrArg RawValue.plain (Sigma.ext rfl (heq_of_eq
      (canonSpace_sortNode ⟨T.type, T.normal, T.sorted, hp⟩ hs _)))
  · by_cases hf : FreeLayer P C (Ω.kprofile T.type) false
    · simp only [dif_neg hp, dif_pos hf]
      exact congrArg RawValue.plus (maskTable_sortType false _ hs _
        (fun fr as => if_neg (t := b) (List.cons_ne_nil fr as)) (fun _ => rfl))
    · simp only [dif_neg hp, dif_neg hf]
      show RawValue.minus (cMinus hno T _) = _
      congr 1
      apply FreeObservations.behavior_injective (topBase Ω) none
      rw [behavior_cMinus]
      apply maskTable_sortType true _ hs
      · intro fr as
        simp only [FreeObservations.behavior_embed, FreeObservations.stageBehavior,
          FreeObservations.Table.relabel, Function.comp_apply, FreeObservations.mapContinue,
          List.map_cons, reduceCtorEq, ↓reduceIte]
      · intro _
        rfl

end SortCanon

end PureTypeSystem.KP.ObservationValues

namespace PureTypeSystem.TypingTreeBE
universe u
variable {S : Type u} {P : Specification S}

/-- Moving a typing tree into the same context gives back the same tree. -/
theorem recontext_self {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T) :
    ∀ h : ContextEquivalentBE P Γ Γ, t.recontext h = t := by
  induction t with
  | @var Γ n A T ht hd hc =>
    intro h
    have key : ∀ {A' : Expr S} (hd' : Lookup Γ n A') (hc' : ConvertsBE T A'),
        (TypingTreeBE.var ((h.typing _ _).mp ht) hd' hc' : TypingTreeBE P Γ (.var n) T) =
          TypingTreeBE.var ht hd hc := by
      intro A' hd' hc'
      obtain rfl := Lookup.unique hd' hd
      rfl
    exact key _ _
  | sort ht ha hc => intro h; rfl
  | product ht d b hr hc ihd ihb =>
    intro h
    change TypingTreeBE.product ((h.typing _ _).mp ht) (d.recontext h) (b.recontext (h.cons d.typing))
      hr hc = _
    rw [ihd h, ihb (h.cons d.typing)]
  | abstraction ht d b hp hc ihd ihb =>
    intro h
    change TypingTreeBE.abstraction ((h.typing _ _).mp ht) (d.recontext h)
      (b.recontext (h.cons d.typing)) ((h.typing _ _).mp hp) hc = _
    rw [ihd h, ihb (h.cons d.typing)]
  | application ht g n hc ihg ihn =>
    intro h
    change TypingTreeBE.application ((h.typing _ _).mp ht) (g.recontext h) (n.recontext h) hc = _
    rw [ihg h, ihn h]

end PureTypeSystem.TypingTreeBE

namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)] (Ω : ContextTowerBE P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemENormalizing' P} (hno : ¬ ForbiddenConfiguration P C)

/-! ## Every evaluated value is canonical -/

/-- Evaluation sees parameters only through their canonical forms. -/
theorem preEvaluate_sameData {Γ : List (Expr S)} {M T : Expr S} (t : TypingTreeBE P Γ M T)
    (e f : Environment (hw := hw) Ω C hno Γ) (hef : e.SameData f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t f).read.val := by
  have hctx : ContextEquivalentBE P Γ Γ := ⟨t.typing.valid, t.typing.valid, fun _ _ => Iff.rfl⟩
  have h := preEvaluate_recontext Ω C hno t hctx e f hef
  rw [TypingTreeBE.recontext_self] at h
  exact h

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}

theorem abstractionAction_val {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (k : FrameKey Ω C (e.activeType h ha)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hk : PayloadFits Ω C hno k.domain p) :
    ∃ (e' : Environment (hw := hw) Ω C hno (D :: Γ)) (ha' : ActiveLayer P C (Ω.kprofile (E.subst e'.images).knf)),
      e' = (ProductInstance.ofFormation hp e).frameEnvironment (abstraction_type h hp hc e) k p hk ∧
      (abstractionAction h hp hc eb e ha k p hk).val = ((eb e').val ha').val ∧
      (k.target hw).type = (E.subst e'.images).knf := by
  have he' := (ProductInstance.ofFormation hp e).frame_type (abstraction_type h hp hc e) k p hk
  exact ⟨_, he' ▸ (k.target hw).active, rfl, rfl, he'.symm⟩

/-- The action of an abstraction sees only the canonical form of its payload. -/
theorem abstractionAction_canonOpt {D m E : Expr S} {s : S} (h : HasTypeBE P Γ (.lam D m) T)
    (hp : HasTypeBE P Γ (.pi D E) (.sort s)) (hc : ConvertsBE T (.pi D E))
    (b : TypingTreeBE P (D :: Γ) m E) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (k : FrameKey Ω C (e.activeType h ha)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hk : PayloadFits Ω C hno k.domain p) :
    (abstractionAction h hp hc (preEvaluate Ω C hno b) e ha k (canonOpt hno k.domain p)
      (canonOpt_fits hk)).val = (abstractionAction h hp hc (preEvaluate Ω C hno b) e ha k p hk).val := by
  obtain ⟨e1, ha1, he1, hv1, -⟩ := abstractionAction_val h hp hc (preEvaluate Ω C hno b) e ha k
    (canonOpt hno k.domain p) (canonOpt_fits hk)
  obtain ⟨e2, ha2, he2, hv2, -⟩ := abstractionAction_val h hp hc (preEvaluate Ω C hno b) e ha k p hk
  rw [hv1, hv2]
  apply val_congr
  have hdom : k.domain = (ProductInstance.ofFormation hp e).domainNF :=
    ProductInstance.frame_domain _ (abstraction_type h hp hc e) k
  refine (preEvaluate_sameData Ω C hno b e1 e2 ⟨by rw [he1, he2]; rfl, ?_⟩).1
  intro i A hi
  subst he1 he2
  cases hi with
  | zero =>
    have hD : ((D.rename Nat.succ).subst ((ProductInstance.ofFormation hp e).frameEnvironment
        (abstraction_type h hp hc e) k (canonOpt hno k.domain p) (canonOpt_fits hk)).images).knf =
          k.domain := by
      show ((D.rename Nat.succ).subst
        (Expr.consSub ((ProductInstance.ofFormation hp e).frameArgument (abstraction_type h hp hc e) k)
          e.images)).knf = k.domain
      rw [Expr.raise_subst_cons, hdom]
      rfl
    rw [hD]
    exact canonOpt_idem k.domain p
  | succ _ hi => rfl

theorem application_canonical {f n D E : Expr S} (h : HasTypeBE P Γ (.app f n) T)
    (hf : HasTypeBE P Γ f (.pi D E)) (hn : HasTypeBE P Γ n D) (hc : ConvertsBE T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf))
    (hV : ∀ hF, canonValue hno (e.activeType hf hF) ((ef e).val hF) = (ef e).val hF) :
    canonValue hno (e.activeType h ha) ((application h hf hn hc ef en e).val ha) =
      (application h hf hn hc ef en e).val ha := by
  unfold application baseResult applicationValue
  by_cases hF : ActiveLayer P C (Ω.kprofile (Expr.pi D E |>.subst e.images).knf)
  · simp only [dite_eq_left hF]
    apply Subtype.ext
    let t := ProductInstance.ofFunction hf e
    have he : (e.activeType hf hF).type = .pi t.domainNF t.bodyNF := t.product_nf
    have hn' : Ω.THasTypeBE (n.subst e.images) t.domainNF :=
      (ContextTowerBE.THasTypeBE.subst hn e.typed).normalize_type hw
    have ht : (T.subst e.images).knf = t.targetNF (n.subst e.images) := by
      have hh := e.type_convert_eq h (HasTypeBE.application hf hn) hc
      rw [ProductInstance.targetNF, t.rawTarget_eq]
      simpa only [ProductInstance.rawBody, t, ProductInstance.ofFunction,
        ProductInstance.ofFormation, ← Expr.instantiate_subst] using hh
    have ha' : ActiveLayer P C (Ω.kprofile (t.targetNF (n.subst e.images))) := ht ▸ ha
    have hk : ((t.argumentFrame he hn' ha').target hw).type = (T.subst e.images).knf :=
      (t.argumentFrame_type he hn' ha').trans ht.symm
    have key := applyValue_canon (e.activeType hf hF) ((ef e).val hF) (t.argumentFrame he hn' ha')
      (en e).parameter (en e).parameter_fits
    rw [hV hF] at key
    have hA := ActiveType.ext (T := e.activeType h ha)
      (U := (t.argumentFrame he hn' ha').target hw) hk.symm
    refine (congrArg (fun z => canonRaw hno (e.activeType h ha) z.val) key).trans ?_
    refine Eq.trans ?_ (congrArg Subtype.val key).symm
    rw [canonValue_val, hA, canonRaw_idem]
  · simp only [dite_eq_right hF]
    exact canonValue_idem _ _
end PreResult

theorem sortType_of_converts {Γ : List (Expr S)} {M T : Expr S} {c : S} (h : HasTypeBE P Γ M T)
    (hc : ConvertsBE T (.sort c)) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)) : IsSortType (e.activeType h ha) := by
  refine ⟨c, ?_⟩
  show (T.subst e.images).knf = .sort c
  exact (Expr.knf_converts ((ContextTowerBE.THasTypeBE.subst h e.typed).type_kwn hw)
    (KWN.of_normal_knf (by show NormalBE (Expr.sort c).knf; rw [Expr.knf_sort]; exact NormalBE.sort c))
      (hc.subst e.images).k).trans
    (Expr.knf_sort c)

/-- **Canonicity.** Every evaluated value is canonical. -/
theorem preEvaluate_canonical (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTreeBE P Γ M T) :
    ∀ (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)),
      canonValue hno (e.activeType t.typing ha) ((preEvaluate Ω C hno t e).val ha) =
        (preEvaluate Ω C hno t e).val ha := by
  induction t with
  | var ht hd hc =>
    intro e ha
    exact canonValue_idem _ _
  | @sort Γ s₀ t₀ T ht hax hc =>
    intro e ha
    exact canon_distinguished_sort _ (sortType_of_converts Ω C hno ht hc e ha)
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
    intro e ha
    have hs := sortType_of_converts Ω C hno ht hc e ha
    show canonValue hno (e.activeType ht ha) ((PreResult.product ht d.typing bt.typing hr hc
      (preEvaluate Ω C hno d) (preEvaluate Ω C hno bt) e).val ha) =
      (PreResult.product ht d.typing bt.typing hr hc
        (preEvaluate Ω C hno d) (preEvaluate Ω C hno bt) e).val ha
    dsimp only [PreResult.product]
    split
    · exact canon_withBase_sort _ hs _
    · exact canon_distinguished_sort _ hs
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
    intro e ha
    obtain ⟨B, hB⟩ := preEvaluate_uniform Ω C hno hC b
    let A := e.activeType ht ha
    let act := PreResult.abstractionAction ht hp hc (preEvaluate Ω C hno b) e ha
    change canonValue hno A (lambdaValue Ω C hno A act) = lambdaValue Ω C hno A act
    have hns : ¬ IsSortType A := by
      rintro ⟨s', hs'⟩
      have hh := PreResult.abstraction_type ht hp hc e
      have hs'' : (T.subst e.images).knf = .sort s' := hs'
      rw [hs''] at hh
      cases hh
    rw [← lambdaValue_eta A hns]
    congr 1
    funext k p hk
    show canonValue hno (k.target hw)
      (applyValue Ω C hno A ((PreResult.abstraction ht hp hc (preEvaluate Ω C hno b) e).val ha) k
        (canonOpt hno k.domain p) (canonOpt_fits hk)) = act k p hk
    rw [PreResult.abstraction_beta ht hp hc _ hB e ha k _ _]
    apply Subtype.ext
    rw [canonValue_val, PreResult.abstractionAction_canonOpt ht hp hc b e ha k p hk]
    obtain ⟨e', ha', -, hv, hty⟩ := PreResult.abstractionAction_val ht hp hc (preEvaluate Ω C hno b) e ha k p hk
    rw [hv, ActiveType.ext (T := k.target hw) (U := e'.activeType b.typing ha') hty]
    exact congrArg Subtype.val (ihb e' ha')
  | @application Γ g n D E T ht gt nt hc ihg ihn =>
    intro e ha
    exact PreResult.application_canonical ht gt.typing nt.typing hc _ _ e ha (fun hF => ihg e hF)

/-- Evaluated parameters are canonical. -/
theorem preEvaluate_parameter_canonical (hC : IsComponent (PrimaryEdge P) C) {Γ : List (Expr S)}
    {M T : Expr S} (t : TypingTreeBE P Γ M T) (e : Environment (hw := hw) Ω C hno Γ) :
    canonOpt hno (T.subst e.images).knf (preEvaluate Ω C hno t e).parameter =
      (preEvaluate Ω C hno t e).parameter := by
  by_cases ha : ActiveLayer P C (Ω.kprofile (T.subst e.images).knf)
  · rw [PreResult.parameter_eq _ ha]
    exact (canonOpt_active (e.activeType t.typing ha) _).trans
      (congrArg some (congrArg Subtype.val (preEvaluate_canonical Ω C hno hC t e ha)))
  · rw [show (preEvaluate Ω C hno t e).parameter = none from dite_eq_right ha]
    rfl

end PureTypeSystem.KP.ObservationValues

