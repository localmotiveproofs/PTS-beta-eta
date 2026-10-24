module

public import PTSBetaEta.Normalization.Values

@[expose] public section

/-!
# η-canonical observation values

OpenAI's observation values carry data that no observation ever reads.
A table of a value records an output for every list of argument–payload pairs, but evaluation only reads some of these outputs.
It reads a base observation only when the list reaches a type that is a sort, and it never reads past an element of the list that is not a frame at the type reached so far.
We call such an element an illegal frame, and the type that a list of frames reaches its position.
With β-conversion the unread data does no harm.
With βη-conversion it does, because it can distinguish `Val (λx. F x)` from `Val F`, and a parameter that receives one of them as input could tell them apart.

`canonValue T v` keeps only what observations read.
It resets every base observation at a position that is not a sort, resets every output after an illegal frame, and makes every payload canonical, recursively.
Plain values are handled by well-founded recursion on the dependency order of plain spaces.
Values at free types are handled by recursion on the stages of values of sign `−` (OpenAI's "minus" values), since the inputs of a table at stage `n+1` lie at stage `n`.
The result passes to the union of all stages by a lemma saying that canonicalization commutes with relabelling.
See the terminology in `PTSBetaEta` for plain and free types, frames, payloads and stages.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace PureTypeSystem.KP.ObservationValues
universe u
open Classical
variable {S : Type u} [Nonempty S] {P : Specification S} [Fact (SystemENormalizing' P)]
variable {Ω : ContextTowerBE P} [Fintype S]
variable {C : Set (Set S)} {hw : SystemENormalizing' P} {hno : ¬ ForbiddenConfiguration P C}

/-! ## Plain values -/

/-- The type that a path of plain frames reaches. -/
noncomputable def pathEnd : {n : ActualPlain.Node Ω C} → (ActualPlain.schema hw).Path n →
    ActualPlain.Node Ω C
  | n, .nil _ => n
  | _, .cons _ p => pathEnd p

/-- The plain type `n` is a sort. Base observations are only read at such types. -/
def IsSortNode (n : ActualPlain.Node Ω C) : Prop := ∃ s, n.type = .sort s

variable (hno) in
/-- One step of plain canonicalization. -/
noncomputable def canonSpaceF (n : ActualPlain.Node Ω C)
    (rec : ∀ d, (ActualPlain.schema hw).Dependency d n →
      ActualPlain.Space (hw := hw) hno (Base Ω) d → ActualPlain.Space (hw := hw) hno (Base Ω) d)
    (x : ActualPlain.Space (hw := hw) hno (Base Ω) n) : ActualPlain.Space (hw := hw) hno (Base Ω) n :=
  ((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n).symm
    fun p xs => if IsSortNode (pathEnd p) then
      (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n x p
        (fun d sl => rec d sl.dependency (xs d sl))
    else topBase Ω

variable (hno) in
/-- Canonical plain values, in which unread base observations are reset and payloads are made canonical. -/
noncomputable def canonSpace : (n : ActualPlain.Node Ω C) →
    ActualPlain.Space (hw := hw) hno (Base Ω) n → ActualPlain.Space (hw := hw) hno (Base Ω) n :=
  (ActualPlain.dependency_wellFounded (Ω := Ω) (C := C) (hw := hw) hno).fix (canonSpaceF hno)

theorem canonSpace_eq (n : ActualPlain.Node Ω C) (x : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    canonSpace hno n x = canonSpaceF hno n (fun d _ => canonSpace hno d) x :=
  congrFun (WellFounded.fix_eq _ (canonSpaceF hno) n) x

theorem canonSpace_unfold (n : ActualPlain.Node Ω C) (x : ActualPlain.Space (hw := hw) hno (Base Ω) n)
    (p : (ActualPlain.schema hw).Path n)
    (xs : (ActualPlain.schema hw).Parameters (ActualPlain.Space (hw := hw) hno (Base Ω)) p) :
    (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n
        (canonSpace hno n x) p xs =
      if IsSortNode (pathEnd p) then
        (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n x p
          (fun d sl => canonSpace hno d (xs d sl))
      else topBase Ω := by
  rw [canonSpace_eq]
  simp only [canonSpaceF, Equiv.apply_symm_apply]

variable (hno) in
/-- The canonical form of a plain value at its own type. -/
noncomputable def canonPV (v : PlainValue (hw := hw) Ω C hno) : PlainValue (hw := hw) Ω C hno :=
  ⟨v.1, canonSpace hno v.1 v.2⟩

@[simp] theorem canonPV_fst (v : PlainValue (hw := hw) Ω C hno) : (canonPV hno v).1 = v.1 := rfl

/-! ## Values at free types: positions and masks -/

/-- The frame at a given key argument, if there is one. It is unique. -/
noncomputable def frameAt (T : ActiveType Ω C) (q : Expr S) : Option (FrameKey Ω C T) :=
  if h : ∃ a : FrameKey Ω C T, a.argument = q then some h.choose else none

theorem frameAt_argument {T : ActiveType Ω C} {q : Expr S} {k : FrameKey Ω C T}
    (h : frameAt T q = some k) : k.argument = q := by
  unfold frameAt at h
  split at h
  · rename_i hx
    cases h
    exact hx.choose_spec
  · cases h

theorem FrameKey.eq_of_argument {T : ActiveType Ω C} {a b : FrameKey Ω C T}
    (h : a.argument = b.argument) : a = b := by
  cases a with
  | mk D E ht q hn hh hact =>
    cases b with
    | mk D' E' ht' q' hn' hh' hact' =>
      obtain ⟨rfl,rfl⟩ := Expr.pi.inj (ht.symm.trans ht')
      cases h
      rfl

theorem frameAt_of {T : ActiveType Ω C} (k : FrameKey Ω C T) : frameAt T k.argument = some k := by
  have hx : ∃ a : FrameKey Ω C T, a.argument = k.argument := ⟨k, rfl⟩
  unfold frameAt
  rw [dif_pos hx]
  exact congrArg some (FrameKey.eq_of_argument hx.choose_spec)

section Free
variable {Y X : Type u}

variable (hno) in
/-- Decodes a payload using only its tag. Whether a payload fits depends only on its tag. -/
noncomputable def tagDecode (sgn : Bool) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .plain v => some (.plain v)
  | .opposite _ => some (if sgn then .plus (FreeObservations.plusDefault _ _ (topBase Ω) none)
      else .minus (FreeObservations.minusDefault _ _ (topBase Ω) none))

@[simp] theorem tagDecode_map (sgn : Bool) (F : X → Y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) :
    tagDecode hno sgn (FreeObservations.Payload.map F pl) = tagDecode hno sgn pl := by
  cases pl <;> rfl

variable (hno) in
/-- A continuing frame is a legal frame whose payload fits and whose target is not plain. -/
def ContinueOK {T : ActiveType Ω C} (k : FrameKey Ω C T) (sgn : Bool)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y) : Prop :=
  PayloadFits Ω C hno k.domain (tagDecode hno sgn pl) ∧ ¬ PlainLayer P C (Ω.kprofile (k.target hw).type)

variable (hno) in
/-- An exiting frame is a legal frame whose payload fits and whose target is plain. -/
def ExitOK {T : ActiveType Ω C} (k : FrameKey Ω C T) (sgn : Bool)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y) : Prop :=
  PayloadFits Ω C hno k.domain (tagDecode hno sgn pl) ∧ PlainLayer P C (Ω.kprofile (k.target hw).type)

@[simp] theorem continueOK_map {T : ActiveType Ω C} (k : FrameKey Ω C T) (sgn : Bool) (F : X → Y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) :
    ContinueOK hno k sgn (FreeObservations.Payload.map F pl) ↔ ContinueOK hno k sgn pl := by
  simp only [ContinueOK, tagDecode_map]

@[simp] theorem exitOK_map {T : ActiveType Ω C} (k : FrameKey Ω C T) (sgn : Bool) (F : X → Y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) :
    ExitOK hno k sgn (FreeObservations.Payload.map F pl) ↔ ExitOK hno k sgn pl := by
  simp only [ExitOK, tagDecode_map]

variable (hno) in
/-- The type that a list of continuing frames reaches, if every frame of the list is legal. -/
noncomputable def walk (sgn : Bool) : ActiveType Ω C →
    List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y) → Option (ActiveType Ω C)
  | T, [] => some T
  | T, a :: as => match frameAt T a.1 with
    | some k => if ContinueOK hno k sgn a.2 then walk sgn (k.target hw) as else none
    | none => none

theorem walk_map (sgn : Bool) (F : X → Y) :
    ∀ (T : ActiveType Ω C) (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X)),
    walk hno sgn T (FreeObservations.mapContinue F as) = walk hno sgn T as
  | T, [] => rfl
  | T, a :: as => by
    simp only [FreeObservations.mapContinue, List.map_cons, walk, FreeObservations.mapFrame]
    cases frameAt T a.1 with
    | none => rfl
    | some k =>
      simp only [continueOK_map]
      split
      · exact walk_map sgn F _ as
      · rfl

variable (hno) in
/-- Makes the payload of one legal frame canonical. -/
noncomputable def canonPayload {T : ActiveType Ω C} (k : FrameKey Ω C T) (g : ActiveType Ω C → Y → Y) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y →
      FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y
  | .none => .none
  | .plain v => .plain (canonPV hno v)
  | .opposite y => if hd : ActiveLayer P C (Ω.kprofile k.domain) then
      .opposite (g (k.domainType hd) y) else .opposite y

theorem canonPayload_map {T : ActiveType Ω C} (k : FrameKey Ω C T) (F : X → Y)
    (g : ActiveType Ω C → Y → Y) (g' : ActiveType Ω C → X → X)
    (hF : ∀ D x, F (g' D x) = g D (F x))
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) :
    canonPayload hno k g (FreeObservations.Payload.map F pl) =
      FreeObservations.Payload.map F (canonPayload hno k g' pl) := by
  cases pl with
  | none => rfl
  | plain v => rfl
  | opposite x =>
    by_cases hd : ActiveLayer P C (Ω.kprofile k.domain)
    · simp only [FreeObservations.Payload.map, canonPayload, dif_pos hd, hF]
    · simp only [FreeObservations.Payload.map, canonPayload, dif_neg hd]

variable (hno) in
/-- Makes every payload of a legal list of continuing frames canonical. -/
noncomputable def canonFrames (sgn : Bool) (g : ActiveType Ω C → Y → Y) : ActiveType Ω C →
    List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y) →
    List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)
  | _, [] => []
  | T, a :: as => match frameAt T a.1 with
    | some k => if ContinueOK hno k sgn a.2 then
        (a.1, canonPayload hno k g a.2) :: canonFrames sgn g (k.target hw) as else a :: as
    | none => a :: as

theorem canonFrames_map (sgn : Bool) (F : X → Y) (g : ActiveType Ω C → Y → Y)
    (g' : ActiveType Ω C → X → X) (hF : ∀ D x, F (g' D x) = g D (F x)) :
    ∀ (T : ActiveType Ω C) (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X)),
    canonFrames hno sgn g T (FreeObservations.mapContinue F as) =
      FreeObservations.mapContinue F (canonFrames hno sgn g' T as)
  | T, [] => rfl
  | T, a :: as => by
    simp only [FreeObservations.mapContinue, List.map_cons, canonFrames, FreeObservations.mapFrame]
    cases frameAt T a.1 with
    | none => rfl
    | some k =>
      simp only [continueOK_map]
      split
      · have ih := canonFrames_map sgn F g g' hF (k.target hw) as
        simp only [FreeObservations.mapContinue] at ih
        rw [ih, canonPayload_map k F g g' hF]
        rfl
      · rfl

variable (hno) in
/-- Makes the final frame of an exiting list canonical. -/
noncomputable def canonLast (sgn : Bool) (g : ActiveType Ω C → Y → Y) (T : ActiveType Ω C)
    (e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y) :
    FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y :=
  match frameAt T e.1 with
  | some k => if ExitOK hno k sgn e.2 then (e.1, canonPayload hno k g e.2) else e
  | none => e

theorem canonLast_map (sgn : Bool) (F : X → Y) (g : ActiveType Ω C → Y → Y)
    (g' : ActiveType Ω C → X → X) (hF : ∀ D x, F (g' D x) = g D (F x)) (T : ActiveType Ω C)
    (e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    canonLast hno sgn g T (FreeObservations.mapFrame F e) =
      FreeObservations.mapFrame F (canonLast hno sgn g' T e) := by
  simp only [canonLast, FreeObservations.mapFrame]
  cases frameAt T e.1 with
  | none => rfl
  | some k =>
    simp only [exitOK_map]
    split
    · rw [canonPayload_map k F g g' hF]
    · rfl

variable (hno) in
/-- Makes an exiting list canonical. -/
noncomputable def canonExit (sgn : Bool) (g : ActiveType Ω C → Y → Y) (T : ActiveType Ω C)
    (a : FreeObservations.ExitStack (Expr S) (PlainValue (hw := hw) Ω C hno) Y) :
    FreeObservations.ExitStack (Expr S) (PlainValue (hw := hw) Ω C hno) Y :=
  (canonFrames hno sgn g T a.1, match walk hno sgn T a.1 with
    | some T' => canonLast hno sgn g T' a.2
    | none => a.2)

theorem canonExit_map (sgn : Bool) (F : X → Y) (g : ActiveType Ω C → Y → Y)
    (g' : ActiveType Ω C → X → X) (hF : ∀ D x, F (g' D x) = g D (F x)) (T : ActiveType Ω C)
    (a : FreeObservations.ExitStack (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    canonExit hno sgn g T (FreeObservations.mapExit F a) =
      FreeObservations.mapExit F (canonExit hno sgn g' T a) := by
  simp only [canonExit, FreeObservations.mapExit, walk_map, canonFrames_map sgn F g g' hF]
  congr 1
  cases walk hno sgn T a.1 with
  | none => rfl
  | some T' => exact canonLast_map sgn F g g' hF T' a.2

variable (hno) in
/-- Whether the last frame of an exiting list is a legal exit at the type that the list reaches. -/
def ExitAt (sgn : Bool) (T : ActiveType Ω C)
    (e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y) : Prop :=
  ∃ k, frameAt T e.1 = some k ∧ ExitOK hno k sgn e.2

@[simp] theorem exitAt_map (sgn : Bool) (F : X → Y) (T : ActiveType Ω C)
    (e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    ExitAt hno sgn T (FreeObservations.mapFrame F e) ↔ ExitAt hno sgn T e := by
  simp only [ExitAt, FreeObservations.mapFrame, exitOK_map]

/-- The active type `T` is a sort. Base observations are only read at such types. -/
def IsSortType (T : ActiveType Ω C) : Prop := ∃ s, T.type = .sort s

variable (hno) in
/-- The plain value that an exit output stands for at a plain target.
A missing output, or one that does not fit the target, stands for the distinguished value. -/
noncomputable def exitPlain (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) : PlainValue (hw := hw) Ω C hno :=
  match o with
  | some q => if q.1 = ⟨T.type, T.normal, T.sorted, hp⟩ then q
      else ⟨⟨T.type, T.normal, T.sorted, hp⟩, plainDefault (hw := hw) Ω C hno _⟩
  | none => ⟨⟨T.type, T.normal, T.sorted, hp⟩, plainDefault (hw := hw) Ω C hno _⟩

theorem exitPlain_fst (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) :
    (exitPlain hno T hp o).1 = ⟨T.type, T.normal, T.sorted, hp⟩ := by
  unfold exitPlain
  split
  · split
    · assumption
    · rfl
  · rfl

theorem exitPlain_of_fst (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (q : PlainValue (hw := hw) Ω C hno) (hq : q.1 = ⟨T.type, T.normal, T.sorted, hp⟩) :
    exitPlain hno T hp (some q) = q := by
  simp only [exitPlain, hq, ite_true]

variable (hno) in
/-- Masks a table.
It keeps only the base observations at legal positions that are sorts and the outputs of legal exits, and it makes the payloads canonical. -/
noncomputable def maskTable (sgn : Bool) (g : ActiveType Ω C → Y → Y) (T : ActiveType Ω C)
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y) :
    FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y where
  continuing as := match walk hno sgn T as with
    | some T' => if IsSortType T' then t.continuing (canonFrames hno sgn g T as) else topBase Ω
    | none => topBase Ω
  exiting a := match walk hno sgn T a.1 with
    | some T' => match frameAt T' a.2.1 with
      | some k => if h : ExitOK hno k sgn a.2.2 then
          some (canonPV hno (exitPlain hno (k.target hw) h.2 (t.exiting (canonExit hno sgn g T a))))
        else none
      | none => none
    | none => none

theorem maskTable_relabel (sgn : Bool) (F : X → Y) (g : ActiveType Ω C → Y → Y)
    (g' : ActiveType Ω C → X → X) (hF : ∀ D x, F (g' D x) = g D (F x)) (T : ActiveType Ω C)
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y) :
    FreeObservations.Table.relabel F (maskTable hno sgn g T t) =
      maskTable hno sgn g' T (FreeObservations.Table.relabel F t) := by
  apply FreeObservations.Table.ext
  · funext as
    simp only [FreeObservations.Table.relabel, maskTable, Function.comp_apply, walk_map,
      canonFrames_map sgn F g g' hF]
  · funext a
    simp only [FreeObservations.Table.relabel, maskTable, Function.comp_apply]
    have hw1 : walk hno sgn T (FreeObservations.mapExit F a).1 = walk hno sgn T a.1 := by
      simp only [FreeObservations.mapExit, walk_map]
    have hf1 : (FreeObservations.mapExit F a).2.1 = a.2.1 := rfl
    rw [hw1, hf1]
    cases walk hno sgn T a.1 with
    | none => rfl
    | some T' =>
      dsimp only
      cases frameAt T' a.2.1 with
      | none => rfl
      | some k =>
        dsimp only
        by_cases hx : ExitOK hno k sgn a.2.2
        · have hx' : ExitOK hno k sgn (FreeObservations.mapExit F a).2.2 :=
            (exitOK_map k sgn F a.2.2).mpr hx
          simp only [dif_pos hx, dif_pos hx']
          rw [canonExit_map sgn F g g' hF]
        · have hx' : ¬ ExitOK hno k sgn (FreeObservations.mapExit F a).2.2 :=
            fun h => hx ((exitOK_map k sgn F a.2.2).mp h)
          simp only [dif_neg hx, dif_neg hx']

end Free

/-! ## Recursion on stages -/

local notation "SN" n => FreeObservations.Stage (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
    (Option (PlainValue (hw := hw) Ω C hno)) n

local notation "TB" Y => FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
    (Option (PlainValue (hw := hw) Ω C hno)) Y

variable (hno) in
/-- Canonicalization at stage `n`, both for values of sign `−` in stage `n` and for tables of sign `+` over stage `n`. -/
noncomputable def canonStage : (n : ℕ) →
    (ActiveType Ω C → (SN n) → (SN n)) × (ActiveType Ω C → (TB (SN n)) → (TB (SN n)))
  | 0 => (fun _ x => x, fun T u => maskTable hno false (fun _ x => x) T u)
  | n+1 =>
    let cm : ActiveType Ω C → (SN (n+1)) → (SN (n+1)) :=
      fun T y => maskTable hno true (canonStage n).2 T y
    (cm, fun T u => maskTable hno false cm T u)

theorem canonStage_succ_fst (n : ℕ) (T : ActiveType Ω C) (y : SN (n+1)) :
    (canonStage hno (n+1)).1 T y = maskTable hno true (canonStage hno n).2 T y := rfl

theorem canonStage_snd (n : ℕ) (T : ActiveType Ω C) (u : TB (SN n)) :
    (canonStage hno n).2 T u = maskTable hno false (canonStage hno n).1 T u := by
  cases n <;> rfl

/-- Canonicalization commutes with the inclusions between stages. -/
theorem canonStage_step : ∀ n : ℕ,
    (∀ (T : ActiveType Ω C) (x : SN n),
      (canonStage hno (n+1)).1 T (FreeObservations.step _ _ _ _ n x) =
        FreeObservations.step _ _ _ _ n ((canonStage hno n).1 T x)) ∧
    (∀ (T : ActiveType Ω C) (u : TB (SN (n+1))),
      FreeObservations.Table.relabel (FreeObservations.step _ _ _ _ n) ((canonStage hno (n+1)).2 T u) =
        (canonStage hno n).2 T (FreeObservations.Table.relabel (FreeObservations.step _ _ _ _ n) u))
  | 0 => by
    refine ⟨fun T x => x.elim, fun T u => ?_⟩
    rw [canonStage_snd, canonStage_snd]
    exact maskTable_relabel false _ _ _ (fun D x => x.elim) T u
  | n+1 => by
    obtain ⟨_, ih2⟩ := canonStage_step n
    have h1 : ∀ (T : ActiveType Ω C) (x : SN (n+1)),
        (canonStage hno (n+2)).1 T (FreeObservations.step _ _ _ _ (n+1) x) =
          FreeObservations.step _ _ _ _ (n+1) ((canonStage hno (n+1)).1 T x) := by
      intro T x
      rw [canonStage_succ_fst, canonStage_succ_fst]
      exact (maskTable_relabel true _ _ _ (fun D u => ih2 D u) T x).symm
    refine ⟨h1, fun T u => ?_⟩
    rw [canonStage_snd, canonStage_snd]
    exact maskTable_relabel false _ _ _ (fun D x => (h1 D x).symm) T u

theorem canonStage_inclusion {n m : ℕ} (h : n ≤ m) (T : ActiveType Ω C) (x : SN n) :
    (canonStage hno m).1 T (FreeObservations.inclusion _ _ _ _ n m h x) =
      FreeObservations.inclusion _ _ _ _ n m h ((canonStage hno n).1 T x) := by
  induction m, h using Nat.le_induction with
  | base => simp only [FreeObservations.inclusion_self]
  | succ m hm ih =>
    rw [← FreeObservations.inclusion_trans hm (Nat.le_succ m), FreeObservations.inclusion_succ,
      ← FreeObservations.inclusion_trans hm (Nat.le_succ m), FreeObservations.inclusion_succ,
      (canonStage_step m).1, ih]

/-! ## Canonicalization of values at free types, in the union of all stages -/

variable (hno) in
/-- The canonical form of a value of sign `−`, computed at a stage that contains it. -/
noncomputable def cMinus (T : ActiveType Ω C) (m : Minus (hw := hw) Ω C hno) : Minus (hw := hw) Ω C hno :=
  FreeObservations.embed _ _ _ _ (FreeObservations.exists_embed m).choose
    ((canonStage hno (FreeObservations.exists_embed m).choose).1 T
      (FreeObservations.exists_embed m).choose_spec.choose)

theorem embed_canon_eq (T : ActiveType Ω C) {k n : ℕ} (y : SN k) (x : SN n)
    (h : FreeObservations.embed (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
        (Option (PlainValue (hw := hw) Ω C hno)) k y = FreeObservations.embed _ _ _ _ n x) :
    FreeObservations.embed (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
        (Option (PlainValue (hw := hw) Ω C hno)) k ((canonStage hno k).1 T y) =
      FreeObservations.embed _ _ _ _ n ((canonStage hno n).1 T x) := by
  have hkj : k ≤ max k n := le_max_left _ _
  have hnj : n ≤ max k n := le_max_right _ _
  have he : FreeObservations.inclusion _ _ _ _ k (max k n) hkj y =
      FreeObservations.inclusion _ _ _ _ n (max k n) hnj x := by
    apply FreeObservations.embed_injective (topBase Ω) (none : Option (PlainValue (hw := hw) Ω C hno))
    rw [FreeObservations.embed_inclusion, FreeObservations.embed_inclusion]
    exact h
  rw [← FreeObservations.embed_inclusion hkj, ← canonStage_inclusion hkj, he, canonStage_inclusion hnj,
    FreeObservations.embed_inclusion]

theorem cMinus_embed (T : ActiveType Ω C) (n : ℕ) (x : SN n) :
    cMinus hno T (FreeObservations.embed _ _ _ _ n x) =
      FreeObservations.embed _ _ _ _ n ((canonStage hno n).1 T x) := by
  unfold cMinus
  exact embed_canon_eq T _ x (FreeObservations.exists_embed _).choose_spec.choose_spec

variable (hno) in
/-- The canonical form of a table of sign `+`. -/
noncomputable def cPlus (T : ActiveType Ω C) (t : Plus (hw := hw) Ω C hno) : Plus (hw := hw) Ω C hno :=
  maskTable hno false (cMinus hno) T t

theorem restrict_cPlus (n : ℕ) (T : ActiveType Ω C) (t : Plus (hw := hw) Ω C hno) :
    FreeObservations.restrict _ _ _ _ n (cPlus hno T t) =
      (canonStage hno n).2 T (FreeObservations.restrict _ _ _ _ n t) := by
  rw [canonStage_snd]
  exact maskTable_relabel false _ _ _ (fun D x => (cMinus_embed D n x).symm) T t

theorem behavior_cMinus (T : ActiveType Ω C) (m : Minus (hw := hw) Ω C hno) :
    FreeObservations.behavior _ _ _ _ (cMinus hno T m) =
      maskTable hno true (cPlus hno) T (FreeObservations.behavior _ _ _ _ m) := by
  obtain ⟨n, y, rfl⟩ := FreeObservations.exists_embed_succ m
  rw [cMinus_embed, FreeObservations.behavior_embed, FreeObservations.behavior_embed]
  change FreeObservations.Table.relabel (FreeObservations.restrict _ _ _ _ n)
      ((canonStage hno (n+1)).1 T y) =
    maskTable hno true (cPlus hno) T (FreeObservations.Table.relabel
      (FreeObservations.restrict _ _ _ _ n) y)
  rw [canonStage_succ_fst]
  exact maskTable_relabel true _ _ _ (fun D t => restrict_cPlus n D t) T y

/-! ## Canonical values -/

variable (hno) in
/-- The canonical form of an element of `RawValue` at an active type. -/
noncomputable def canonRaw (T : ActiveType Ω C) : RawValue (hw := hw) Ω C hno → RawValue (hw := hw) Ω C hno
  | .plain p => .plain (canonPV hno p)
  | .plus t => .plus (cPlus hno T t)
  | .minus m => .minus (cMinus hno T m)

theorem canonRaw_fits (T : ActiveType Ω C) {D : Expr S} (v : RawValue (hw := hw) Ω C hno)
    (hv : Fits Ω C hno D v) : Fits Ω C hno D (canonRaw hno T v) := by
  cases v <;> exact hv

variable (hno) in
/-- The canonical form of a value at an active type. -/
noncomputable def canonValue (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    Value (hw := hw) Ω C hno T.type :=
  ⟨canonRaw hno T v.val, canonRaw_fits T v.val v.property⟩

@[simp] theorem canonValue_val (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    (canonValue hno T v).val = canonRaw hno T v.val := rfl

variable (hno) in
/-- The canonical form of an optional payload at a key type. -/
noncomputable def canonOpt (D : Expr S) :
    Option (RawValue (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | none => none
  | some v => if h : KNormal D ∧ (∃ s, Ω.KHasTypeBE D (.sort s)) ∧ ActiveLayer P C (Ω.kprofile D) then
      some (canonRaw hno ⟨D, h.1, h.2.1, h.2.2⟩ v) else some v

@[simp] theorem canonOpt_none (D : Expr S) : canonOpt (hw := hw) (Ω := Ω) (C := C) hno D none = none := rfl

theorem canonOpt_active (T : ActiveType Ω C) (v : RawValue (hw := hw) Ω C hno) :
    canonOpt hno T.type (some v) = some (canonRaw hno T v) := by
  simp only [canonOpt, dif_pos (⟨T.normal, T.sorted, T.active⟩ :
    KNormal T.type ∧ (∃ s, Ω.KHasTypeBE T.type (.sort s)) ∧ ActiveLayer P C (Ω.kprofile T.type))]

theorem canonOpt_fits {D : Expr S} {p : Option (RawValue (hw := hw) Ω C hno)}
    (hp : PayloadFits Ω C hno D p) : PayloadFits Ω C hno D (canonOpt hno D p) := by
  cases p with
  | none => exact hp
  | some v =>
    by_cases h : KNormal D ∧ (∃ s, Ω.KHasTypeBE D (.sort s)) ∧ ActiveLayer P C (Ω.kprofile D)
    · simp only [canonOpt, dif_pos h]
      exact canonRaw_fits _ v hp
    · simp only [canonOpt, dif_neg h]
      exact hp

/-! ## Structure of plain values -/

theorem canonSpace_prefix (n : ActualPlain.Node Ω C) (x : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n (canonSpace hno n x) =
      (if IsSortNode n then (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n x).1 else topBase Ω,
       fun a ps => canonSpace hno _ ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n x).2 a
         (fun d h => canonSpace hno d (ps d h)))) := by
  apply Prod.ext
  · show (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n
        (canonSpace hno n x) (.nil n) PlainSpaces.Schema.Parameters.nil =
      if IsSortNode n then (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno)
        (Base Ω) n x (.nil n) PlainSpaces.Schema.Parameters.nil else topBase Ω
    refine (canonSpace_unfold n x (.nil n) PlainSpaces.Schema.Parameters.nil).trans ?_
    refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
    refine congrArg (fun z => (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno)
      (Base Ω) n x (.nil n) z) ?_
    funext d sl
    cases sl
  · funext a ps
    show ((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω)
        ((ActualPlain.schema hw).target n a)).symm (fun p xs =>
          (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n
            (canonSpace hno n x) (.cons a p) (PlainSpaces.Schema.Parameters.cons ps xs)) =
      canonSpace hno _ (((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω)
        ((ActualPlain.schema hw).target n a)).symm (fun p xs =>
          (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n
            x (.cons a p) (PlainSpaces.Schema.Parameters.cons (fun d h => canonSpace hno d (ps d h)) xs)))
    apply ((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) _).injective
    funext p xs
    refine Eq.trans ?_ (canonSpace_unfold _ _ p xs).symm
    simp only [Equiv.apply_symm_apply]
    refine (canonSpace_unfold n x (.cons a p) (PlainSpaces.Schema.Parameters.cons ps xs)).trans ?_
    refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
    refine congrArg (fun z => (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno)
      (Base Ω) n x (.cons a p) z) ?_
    funext d sl
    cases sl <;> rfl

theorem canonSpace_idem (n : ActualPlain.Node Ω C) : ∀ x : ActualPlain.Space (hw := hw) hno (Base Ω) n,
    canonSpace hno n (canonSpace hno n x) = canonSpace hno n x := by
  refine (ActualPlain.dependency_wellFounded (Ω := Ω) (C := C) (hw := hw) hno).induction
    (C := fun n => ∀ x : ActualPlain.Space (hw := hw) hno (Base Ω) n,
      canonSpace hno n (canonSpace hno n x) = canonSpace hno n x) n ?_
  intro n ih x
  apply ((ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno) (Base Ω) n).injective
  funext p xs
  rw [canonSpace_unfold n (canonSpace hno n x) p xs, canonSpace_unfold n x p xs,
    canonSpace_unfold n x p (fun d sl => canonSpace hno d (xs d sl))]
  split_ifs
  · refine congrArg (fun z => (ActualPlain.schema hw).unfold (ActualPlain.dependency_wellFounded hno)
      (Base Ω) n x p z) ?_
    funext d sl
    exact ih d sl.dependency _
  · rfl

theorem canonPV_idem (v : PlainValue (hw := hw) Ω C hno) : canonPV hno (canonPV hno v) = canonPV hno v := by
  show (⟨v.1, canonSpace hno v.1 (canonSpace hno v.1 v.2)⟩ : PlainValue (hw := hw) Ω C hno) =
    ⟨v.1, canonSpace hno v.1 v.2⟩
  rw [canonSpace_idem]

/-! ## Structure of values at free types -/

section FreeLemmas
variable {Y : Type u}

theorem fits_tagDecode_canonPayload {T : ActiveType Ω C} (k : FrameKey Ω C T) (sgn : Bool)
    (g : ActiveType Ω C → Y → Y) (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y)
    (D : Expr S) :
    PayloadFits Ω C hno D (tagDecode hno sgn (canonPayload hno k g pl)) ↔
      PayloadFits Ω C hno D (tagDecode hno sgn pl) := by
  cases pl with
  | none => exact Iff.rfl
  | plain v => exact Iff.rfl
  | opposite y =>
    simp only [canonPayload]
    split <;> exact Iff.rfl

@[simp] theorem continueOK_canon {T T' : ActiveType Ω C} (k : FrameKey Ω C T) (k' : FrameKey Ω C T')
    (sgn : Bool) (g : ActiveType Ω C → Y → Y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y) :
    ContinueOK hno k' sgn (canonPayload hno k g pl) ↔ ContinueOK hno k' sgn pl := by
  simp only [ContinueOK, fits_tagDecode_canonPayload]

@[simp] theorem exitOK_canon {T T' : ActiveType Ω C} (k : FrameKey Ω C T) (k' : FrameKey Ω C T')
    (sgn : Bool) (g : ActiveType Ω C → Y → Y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y) :
    ExitOK hno k' sgn (canonPayload hno k g pl) ↔ ExitOK hno k' sgn pl := by
  simp only [ExitOK, fits_tagDecode_canonPayload]

theorem canonPayload_idem {T : ActiveType Ω C} (k : FrameKey Ω C T) {g : ActiveType Ω C → Y → Y}
    (hg : ∀ D y, g D (g D y) = g D y)
    (pl : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) Y) :
    canonPayload hno k g (canonPayload hno k g pl) = canonPayload hno k g pl := by
  cases pl with
  | none => rfl
  | plain v => exact congrArg FreeObservations.Payload.plain (canonPV_idem v)
  | opposite y =>
    by_cases hd : ActiveLayer P C (Ω.kprofile k.domain)
    · simp only [canonPayload, dif_pos hd, hg]
    · simp only [canonPayload, dif_neg hd]

theorem walk_canonFrames (sgn : Bool) (g : ActiveType Ω C → Y → Y) :
    ∀ (T : ActiveType Ω C) (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)),
    walk hno sgn T (canonFrames hno sgn g T as) = walk hno sgn T as
  | T, [] => rfl
  | T, a :: as => by
    cases hk : frameAt T a.1 with
    | none => simp only [canonFrames, hk]
    | some k =>
      by_cases hc : ContinueOK hno k sgn a.2
      · simp only [canonFrames, hk, if_pos hc, walk, continueOK_canon]
        exact walk_canonFrames sgn g (k.target hw) as
      · simp only [canonFrames, hk, if_neg hc]

theorem canonFrames_idem (sgn : Bool) {g : ActiveType Ω C → Y → Y} (hg : ∀ D y, g D (g D y) = g D y) :
    ∀ (T : ActiveType Ω C) (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)),
    canonFrames hno sgn g T (canonFrames hno sgn g T as) = canonFrames hno sgn g T as
  | T, [] => rfl
  | T, a :: as => by
    cases hk : frameAt T a.1 with
    | none => simp only [canonFrames, hk]
    | some k =>
      by_cases hc : ContinueOK hno k sgn a.2
      · simp only [canonFrames, hk, if_pos hc, continueOK_canon, canonPayload_idem k hg]
        rw [canonFrames_idem sgn hg (k.target hw) as]
      · simp only [canonFrames, hk, if_neg hc]

theorem walk_cons_legal (sgn : Bool) {T : ActiveType Ω C} {k : FrameKey Ω C T}
    {a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y}
    (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y))
    (hk : frameAt T a.1 = some k) (hc : ContinueOK hno k sgn a.2) :
    walk hno sgn T (a :: as) = walk hno sgn (k.target hw) as := by
  simp only [walk, hk, if_pos hc]

theorem walk_cons_illegal (sgn : Bool) {T : ActiveType Ω C}
    {a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y}
    (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y))
    (h : ∀ k, frameAt T a.1 = some k → ¬ ContinueOK hno k sgn a.2) :
    walk hno sgn T (a :: as) = none := by
  cases hk : frameAt T a.1 with
  | none => simp only [walk, hk]
  | some k => simp only [walk, hk, if_neg (h k hk)]

theorem canonFrames_cons_legal (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    {k : FrameKey Ω C T} {a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y}
    (as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y))
    (hk : frameAt T a.1 = some k) (hc : ContinueOK hno k sgn a.2) :
    canonFrames hno sgn g T (a :: as) = (a.1, canonPayload hno k g a.2) :: canonFrames hno sgn g (k.target hw) as := by
  simp only [canonFrames, hk, if_pos hc]

theorem maskTable_continuing_some (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T T' : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    (h : walk hno sgn T as = some T') :
    (maskTable hno sgn g T t).continuing as =
      if IsSortType T' then t.continuing (canonFrames hno sgn g T as) else topBase Ω := by
  simp only [maskTable, h]

theorem maskTable_continuing_none (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    (h : walk hno sgn T as = none) : (maskTable hno sgn g T t).continuing as = topBase Ω := by
  simp only [maskTable, h]

theorem maskTable_exiting_some (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T T' : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    {e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y} {k : FrameKey Ω C T'}
    (h : walk hno sgn T as = some T') (hk : frameAt T' e.1 = some k) (hx : ExitOK hno k sgn e.2) :
    (maskTable hno sgn g T t).exiting (as, e) =
      some (canonPV hno (exitPlain hno (k.target hw) hx.2
        (t.exiting (canonFrames hno sgn g T as, (e.1, canonPayload hno k g e.2))))) := by
  simp only [maskTable, h, hk, dif_pos hx, canonExit, canonLast, if_pos hx]

theorem maskTable_exiting_none_walk (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    (e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)
    (h : walk hno sgn T as = none) : (maskTable hno sgn g T t).exiting (as, e) = none := by
  simp only [maskTable, h]

theorem maskTable_exiting_none_frame (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T T' : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    {e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y}
    (h : walk hno sgn T as = some T') (hk : frameAt T' e.1 = none) :
    (maskTable hno sgn g T t).exiting (as, e) = none := by
  simp only [maskTable, h, hk]

theorem maskTable_exiting_none_ok (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T T' : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {as : List (FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y)}
    {e : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y} {k : FrameKey Ω C T'}
    (h : walk hno sgn T as = some T') (hk : frameAt T' e.1 = some k) (hx : ¬ ExitOK hno k sgn e.2) :
    (maskTable hno sgn g T t).exiting (as, e) = none := by
  simp only [maskTable, h, hk, dif_neg hx]

theorem canonPV_exitPlain (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.kprofile T.type))
    (o : Option (PlainValue (hw := hw) Ω C hno)) :
    exitPlain hno T hp (some (canonPV hno (exitPlain hno T hp o))) = canonPV hno (exitPlain hno T hp o) :=
  exitPlain_of_fst T hp _ (by rw [canonPV_fst, exitPlain_fst])

theorem maskTable_idem (sgn : Bool) {g : ActiveType Ω C → Y → Y} (hg : ∀ D y, g D (g D y) = g D y)
    (T : ActiveType Ω C)
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y) :
    maskTable hno sgn g T (maskTable hno sgn g T t) = maskTable hno sgn g T t := by
  apply FreeObservations.Table.ext
  · funext as
    cases hw' : walk hno sgn T as with
    | none => rw [maskTable_continuing_none sgn g _ hw', maskTable_continuing_none sgn g _ hw']
    | some T' =>
      rw [maskTable_continuing_some sgn g _ hw', maskTable_continuing_some sgn g _ hw']
      split_ifs
      · rw [maskTable_continuing_some sgn g _ ((walk_canonFrames sgn g T as).trans hw'),
          if_pos ‹_›, canonFrames_idem sgn hg]
      · rfl
  · funext x
    obtain ⟨as, e⟩ := x
    cases hw' : walk hno sgn T as with
    | none => rw [maskTable_exiting_none_walk sgn g _ e hw', maskTable_exiting_none_walk sgn g _ e hw']
    | some T' =>
      cases hk : frameAt T' e.1 with
      | none => rw [maskTable_exiting_none_frame sgn g _ hw' hk, maskTable_exiting_none_frame sgn g _ hw' hk]
      | some k =>
        by_cases hx : ExitOK hno k sgn e.2
        · have hx' : ExitOK hno k sgn (e.1, canonPayload hno k g e.2).2 := (exitOK_canon k k sgn g e.2).mpr hx
          rw [maskTable_exiting_some sgn g _ hw' hk hx, maskTable_exiting_some sgn g _ hw' hk hx,
            maskTable_exiting_some sgn g _ (e := (e.1, canonPayload hno k g e.2))
              ((walk_canonFrames sgn g T as).trans hw') hk hx']
          simp only [canonFrames_idem sgn hg, canonPayload_idem k hg, canonPV_exitPlain, canonPV_idem]
        · rw [maskTable_exiting_none_ok sgn g _ hw' hk hx, maskTable_exiting_none_ok sgn g _ hw' hk hx]

/-- Fixing the first frame of a masked table, when that frame is a legal continuing frame. -/
theorem maskTable_slice_legal (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y} {k : FrameKey Ω C T}
    (hk : frameAt T a.1 = some k) (hc : ContinueOK hno k sgn a.2) :
    (maskTable hno sgn g T t).slice a =
      maskTable hno sgn g (k.target hw) (t.slice (a.1, canonPayload hno k g a.2)) := by
  apply FreeObservations.Table.ext
  · funext as
    simp only [FreeObservations.Table.slice, maskTable, walk_cons_legal sgn as hk hc,
      canonFrames_cons_legal sgn g as hk hc]
  · funext x
    obtain ⟨as, e⟩ := x
    simp only [FreeObservations.Table.slice, maskTable, walk_cons_legal sgn as hk hc,
      canonExit, canonFrames_cons_legal sgn g as hk hc]

/-- Fixing the first frame of a masked table, when that frame is not a legal continuing frame. -/
theorem maskTable_slice_illegal (sgn : Bool) (g : ActiveType Ω C → Y → Y) {T : ActiveType Ω C}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y)
    {a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) Y}
    (h : ∀ k, frameAt T a.1 = some k → ¬ ContinueOK hno k sgn a.2) :
    (maskTable hno sgn g T t).slice a = FreeObservations.Table.default (topBase Ω) none := by
  apply FreeObservations.Table.ext
  · funext as
    simp only [FreeObservations.Table.slice, FreeObservations.Table.default,
      maskTable_continuing_none sgn g t (walk_cons_illegal sgn as h)]
  · funext x
    obtain ⟨as, e⟩ := x
    simp only [FreeObservations.Table.slice, FreeObservations.Table.default,
      maskTable_exiting_none_walk sgn g t e (walk_cons_illegal sgn as h)]

theorem maskTable_nil (sgn : Bool) (g : ActiveType Ω C → Y → Y) (T : ActiveType Ω C)
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) Y) :
    (maskTable hno sgn g T t).continuing [] = if IsSortType T then t.continuing [] else topBase Ω := rfl

end FreeLemmas

/-! ## Idempotence -/

theorem canonStage_idem : ∀ n : ℕ,
    (∀ (T : ActiveType Ω C) (x : SN n), (canonStage hno n).1 T ((canonStage hno n).1 T x) =
      (canonStage hno n).1 T x) ∧
    (∀ (T : ActiveType Ω C) (u : TB (SN n)), (canonStage hno n).2 T ((canonStage hno n).2 T u) =
      (canonStage hno n).2 T u)
  | 0 => ⟨fun T x => rfl, fun T u => by
      simp only [canonStage_snd]
      exact maskTable_idem false (fun D x => rfl) T u⟩
  | n+1 => by
    have ih := (canonStage_idem n).2
    have h1 : ∀ (T : ActiveType Ω C) (x : SN (n+1)), (canonStage hno (n+1)).1 T
        ((canonStage hno (n+1)).1 T x) = (canonStage hno (n+1)).1 T x := by
      intro T x
      simp only [canonStage_succ_fst]
      exact maskTable_idem true ih T x
    refine ⟨h1, fun T u => ?_⟩
    simp only [canonStage_snd]
    exact maskTable_idem false h1 T u

theorem cMinus_idem (T : ActiveType Ω C) (m : Minus (hw := hw) Ω C hno) :
    cMinus hno T (cMinus hno T m) = cMinus hno T m := by
  obtain ⟨n, y, rfl⟩ := FreeObservations.exists_embed m
  rw [cMinus_embed, cMinus_embed, (canonStage_idem n).1]

theorem cPlus_idem (T : ActiveType Ω C) (t : Plus (hw := hw) Ω C hno) :
    cPlus hno T (cPlus hno T t) = cPlus hno T t :=
  maskTable_idem false (fun D m => cMinus_idem D m) T t

theorem canonRaw_idem (T : ActiveType Ω C) (v : RawValue (hw := hw) Ω C hno) :
    canonRaw hno T (canonRaw hno T v) = canonRaw hno T v := by
  cases v with
  | plain p => exact congrArg RawValue.plain (canonPV_idem p)
  | plus t => exact congrArg RawValue.plus (cPlus_idem T t)
  | minus m => exact congrArg RawValue.minus (cMinus_idem T m)

theorem canonValue_idem (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    canonValue hno T (canonValue hno T v) = canonValue hno T v :=
  Subtype.ext (canonRaw_idem T v.val)

theorem canonOpt_idem (D : Expr S) (p : Option (RawValue (hw := hw) Ω C hno)) :
    canonOpt hno D (canonOpt hno D p) = canonOpt hno D p := by
  cases p with
  | none => rfl
  | some v =>
    by_cases h : KNormal D ∧ (∃ s, Ω.KHasTypeBE D (.sort s)) ∧ ActiveLayer P C (Ω.kprofile D)
    · simp only [canonOpt, dif_pos h, canonRaw_idem]
    · simp only [canonOpt, dif_neg h]

/-! ## Bounds on stages and finite levels -/

theorem canonRaw_bounded (T : ActiveType Ω C) {n : ℕ} {v : RawValue (hw := hw) Ω C hno}
    (h : RawValue.Bounded Ω C hno n v) : RawValue.Bounded Ω C hno n (canonRaw hno T v) := by
  cases v with
  | plain p => trivial
  | plus t => trivial
  | minus m =>
    obtain ⟨y, rfl⟩ := h
    exact ⟨_, (cMinus_embed T n y).symm⟩

theorem canonRaw_level (T : ActiveType Ω C) {n : ℕ} {v w : RawValue (hw := hw) Ω C hno}
    (h : RawValue.LevelEq Ω C hno n v w) :
    RawValue.LevelEq Ω C hno n (canonRaw hno T v) (canonRaw hno T w) := by
  cases v <;> cases w <;> try exact False.elim h
  · exact congrArg (canonPV hno) h
  · change FreeObservations.restrict _ _ _ _ n (cPlus hno T _) =
      FreeObservations.restrict _ _ _ _ n (cPlus hno T _)
    rw [restrict_cPlus, restrict_cPlus]
    exact congrArg _ h
  · exact congrArg (cMinus hno T) h

theorem canonOpt_bounded (D : Expr S) {n : ℕ} {p : Option (RawValue (hw := hw) Ω C hno)}
    (h : Parameter.Bounded Ω C hno n p) : Parameter.Bounded Ω C hno n (canonOpt hno D p) := by
  cases p with
  | none => exact h
  | some v =>
    by_cases hD : KNormal D ∧ (∃ s, Ω.KHasTypeBE D (.sort s)) ∧ ActiveLayer P C (Ω.kprofile D)
    · simp only [canonOpt, dif_pos hD]
      intro w hw'
      cases hw'
      exact canonRaw_bounded _ (h v rfl)
    · simp only [canonOpt, dif_neg hD]
      exact h

theorem canonOpt_level (D : Expr S) {n : ℕ} {p q : Option (RawValue (hw := hw) Ω C hno)}
    (h : Parameter.LevelEq Ω C hno n p q) :
    Parameter.LevelEq Ω C hno n (canonOpt hno D p) (canonOpt hno D q) := by
  cases p with
  | none =>
    cases q with
    | none => trivial
    | some w => exact False.elim h
  | some v =>
    cases q with
    | none => exact False.elim h
    | some w =>
      by_cases hD : KNormal D ∧ (∃ s, Ω.KHasTypeBE D (.sort s)) ∧ ActiveLayer P C (Ω.kprofile D)
      · simp only [canonOpt, dif_pos hD]
        exact canonRaw_level _ h
      · simp only [canonOpt, dif_neg hD]
        exact h

end PureTypeSystem.KP.ObservationValues

