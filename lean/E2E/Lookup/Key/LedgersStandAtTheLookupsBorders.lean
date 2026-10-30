-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: the homes of the verifier's state at the two borders of the key's first thread at which a lookup stands,
  numbers 4 and 10. What the thread's clause on the state says of the homes is their number alone. Which homes they are comes
  out of the thread's clause on the verifier's own fold, block by block from acceptance: this file walks it.

E2E/Lookup/Key/LedgersStandAtTheLookupsBorders.lean. Theorems with proofs.

  `TakesStandAt`                        what `callersHomesAtTheState` spends of `Mid`: the two ledgers' counts and the shapes
  `callersHomesWhereTakesStand`, `theLedgerWhereTakesStand`   the two theorems of E2E/Lookup/Key/LedgerIsTheKeyBook.lean at it
  `takesStandInFrontOfTheFirstCaller`   behind the two sendings and the first link's `lay`: no take of either ledger
  `takesStandBehindACaller`             a caller's two takings move the two counts
  `takesStandInFrontOfTheSecondCaller`  the five steps of link 0 behind its caller touch no ledger
  `homesAtTheLookupsBorders`            **the top**: at 4 and 10, the homes of `theLedgerIsTheKeyBook`

CAN THE PREMISES HOLD TOGETHER AT THE STORED KEY FILE? `fullPub = some data`: `full_two` (E2E/KeyBookPassesNamed.lean) has
`atFull … = true`, which is false where `fullPub` is none. `KeySourced` with `InScope`: `key_sourced` (E2E/KeyPublic.lean) where the
verifier's test on the public files accepts. THAT THE THREAD STANDS AT BORDER 4 OR 10 AT ANY RUN IS NOT SHOWN HERE: `Thr` is the
premise that the top's conclusion is drawn from, by its clause `Made` alone.

Limits. On the verifier's side alone. Nothing on a sender, on what a view shows, or on any property of a protocol. Each statement
holds also where the thread stands at nothing.
-/
import E2E.Lookup.Key.LedgerIsTheKeyBook
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import E2E.KeyMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open ProofFile.Honest.K3 (keyOwners)
open ProofFile.Honest.K3.Parts (maskOf)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyThread
open AtPublicFiles.KeyLookup (takeMasks_laws ledgerAt_same front_laws LeftIs)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K3 (Face faceOfLkp fromKeys homes)
open VerifiableInference.Desc.K13.Law (LedgerAt)
open VerifiableInference.Desc.Key (FirstState Claim Lookup Source LaterPlaces Xi caller lookupsOf firstChain
  pieces sendIndexMasks sendOwnMessage groupsTold rootsAt rootsBefore lookupLink)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open Johnson.RunOne.KeyRows1 (CallGround callerYes clr lay_ok after_ok clear_ok dec_laid0 dec_behind0 dec_cleared0
  dec_laid1)
open OnBytes (Slot takenNo OracleShape)

/-! ## 1 What `Mid` is spent for -/

/-- **The two ledgers stand behind k₁ and k₂ takes**, at messages of these shapes: the two messages differ. -/
structure TakesStandAt (one : OnBytes.Params.OneTime) (s : FirstState) (k₁ k₂ : Nat)
    (ownShape keyShape : OracleShape) : Prop where
  /-- the two messages differ -/
  ne : s.idx ≠ one.ranges.messageId
  /-- the own message's ledger stands behind k₁ takes -/
  ownAt : LedgerAt s.d.st one.ranges.messageId k₁
  /-- the index-mask message's behind k₂ -/
  idxAt : LedgerAt s.d.st s.idx k₂
  /-- the own message's shape -/
  ownIs : ∃ y, s.d.st.oracles[one.ranges.messageId]? = some y ∧ y.shape = ownShape
  /-- the index-mask message's shape -/
  keyIs : ∃ y, s.d.st.oracles[s.idx]? = some y ∧ y.shape = keyShape

theorem shapeOfALedgerLeft {L : Type} {d : _root_.Desc.Plain.DState L} {o n : Nat} {shape : OracleShape}
    (h : LeftIs d o n shape) : ∃ y, d.st.oracles[o]? = some y ∧ y.shape = shape := by
  obtain ⟨y, -, hy, hs, -⟩ := h
  exact ⟨y, hy, hs⟩

/-- `Mid` gives it. -/
theorem takesStandOfMid {one : OnBytes.Params.OneTime} {codes : OnBytes.Codes} {s : FirstState}
    {number a b k₁ k₂ B V : Nat} {ownShape keyShape : OracleShape}
    (mid : AtPublicFiles.KeyLookup.Mid one codes s number a b k₁ k₂ B V ownShape keyShape) :
    TakesStandAt one s k₁ k₂ ownShape keyShape :=
  ⟨mid.ne, mid.ownAt, mid.idxAt, shapeOfALedgerLeft mid.own, shapeOfALedgerLeft mid.idx⟩

/-- It reads the statement's part and the number of the index-mask message alone. -/
theorem TakesStandAt.sameLedgers {one : OnBytes.Params.OneTime} {s s' : FirstState} {k₁ k₂ : Nat}
    {ownShape keyShape : OracleShape} (stand : TakesStandAt one s k₁ k₂ ownShape keyShape)
    (sameStatement : s'.d = s.d) (sameNumber : s'.idx = s.idx) :
    TakesStandAt one s' k₁ k₂ ownShape keyShape := by
  obtain ⟨ne, ownAt, idxAt, ownIs, keyIs⟩ := stand
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [sameStatement, sameNumber] <;> assumption

/-- **What `caller` returns**, off its text. -/
theorem callerReturnsByItsTwoTakings {one : OnBytes.Params.OneTime} {number : Nat} {x : Lookup}
    {s s' : FirstState} {rounds : List Fmt.RoundView} {columns : List (List (Nat × List UInt64))}
    (accepts : (caller one number x).decide s rounds columns = .ok s') :
    ∃ o d₁ k d₂,
      takeMasksP s.d one.ranges.messageId ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) =
        some (o, d₁) ∧
      takeMasksP d₁ s.idx (2 * (faceOfLkp x).parts.length) = some (k, d₂) ∧
      s' = { s with
        d := d₂
        base := { s.base with
          fork := some (({} : OnBytes.Model.Fork).slots (faceOfLkp x).slots), heard := none
          home := homes (faceOfLkp x) (o.map fun j => ⟨one.ranges.messageId, j⟩)
            (k.map fun j => ⟨s.idx, j⟩) } } := by
  have a₁ := needPassesOn accepts
  have a₂ := needPassesOn a₁
  obtain ⟨⟨o, d₁⟩, e₁, a₃⟩ := namedReturnsItsValue a₂
  obtain ⟨⟨k, d₂⟩, e₂, a₄⟩ := namedReturnsItsValue a₃
  have a₅ := needPassesOn a₄
  exact ⟨o, d₁, k, d₂, e₁, e₂, (Except.ok.inj a₅).symm⟩

/-- **The homes that `caller` lays where the takes stand**: `callersHomesAtTheState` at `TakesStandAt`. -/
theorem callersHomesWhereTakesStand (one : OnBytes.Params.OneTime) (number : Nat) (x : Lookup)
    {s s' : FirstState} {k₁ k₂ : Nat} {ownShape keyShape : OracleShape}
    (stand : TakesStandAt one s k₁ k₂ ownShape keyShape)
    (levels : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v) (rounds : List Fmt.RoundView)
    (columns : List (List (Nat × List UInt64)))
    (accepts : (caller one number x).decide s rounds columns = .ok s') (ownTable keyTable : Nat) :
    s'.base.home.toList =
      (unroll (seatOfLookup number)
        (bookEntries (seatOfLookup number) (faceOfLkp x) (ownTable + k₁) (keyTable + k₂))).map
        (homeOfCoin one.ranges.messageId s.idx ownShape.maskRows keyShape.maskRows ownTable keyTable) := by
  obtain ⟨o, d₁, k, d₂, e₁, e₂, rfl⟩ := callerReturnsByItsTwoTakings accepts
  obtain ⟨y, hy, hyShape⟩ := stand.ownIs
  have hNumbersOwn := VerifiableInference.Desc.K13.Honest.takeMasksP_numbers stand.ownAt hy e₁
  obtain ⟨-, -, hSame, -, -⟩ := takeMasks_laws e₁
  have hSameKey := hSame s.idx stand.ne
  have hAtKey := ledgerAt_same stand.idxAt hSameKey
  obtain ⟨z, hz, hzShape⟩ := stand.keyIs
  obtain ⟨z', hz', hShape, -⟩ := hSameKey.2 z hz
  have hNumbersKey := VerifiableInference.Desc.K13.Honest.takeMasksP_numbers hAtKey hz' e₂
  simp only [] at hNumbersOwn hNumbersKey
  rw [hyShape] at hNumbersOwn
  rw [hShape, hzShape] at hNumbersKey
  show (homes (faceOfLkp x) (o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
      (k.map fun j => (⟨s.idx, j⟩ : Slot))).toList = _
  rw [hNumbersOwn, hNumbersKey]
  exact callersHomesAreTheBooksCoins _ levels number _ _ _ _ _ _ _ _

theorem callerKeepsTheIndexMasksNumber {one : OnBytes.Params.OneTime} {number : Nat} {x : Lookup}
    {s s' : FirstState} {rounds : List Fmt.RoundView} {columns : List (List (Nat × List UInt64))}
    (accepts : (caller one number x).decide s rounds columns = .ok s') : s'.idx = s.idx := by
  obtain ⟨o, d₁, k, d₂, -, -, rfl⟩ := callerReturnsByItsTwoTakings accepts
  rfl

theorem shapeRidesPastACaller {s : FirstState} {d' : VerifiableInference.Desc.Key.PlainState} {o : Nat}
    {shape : OracleShape} (ground : CallGround s d')
    (h : ∃ y, s.d.st.oracles[o]? = some y ∧ y.shape = shape) :
    ∃ y, d'.st.oracles[o]? = some y ∧ y.shape = shape := by
  obtain ⟨y, hy, hs⟩ := h
  have e := ground.oracle o
  rw [hy] at e
  cases hz : d'.st.oracles[o]? with
  | none =>
    rw [hz] at e
    cases e
  | some z =>
    rw [hz] at e
    have same : Johnson.RunOne.KeyRows1.unl z = Johnson.RunOne.KeyRows1.unl y := Option.some.inj e
    exact ⟨z, rfl, (congrArg (·.shape) same).trans hs⟩

/-- **A caller's two takings move the two counts**, by just what it takes; the shapes stay. -/
theorem takesStandBehindACaller (one : OnBytes.Params.OneTime) (number : Nat) (x : Lookup)
    {s s' : FirstState} {k₁ k₂ : Nat} {ownShape keyShape : OracleShape}
    (stand : TakesStandAt one s k₁ k₂ ownShape keyShape) (rounds : List Fmt.RoundView)
    (columns : List (List (Nat × List UInt64)))
    (accepts : (caller one number x).decide s rounds columns = .ok s') :
    TakesStandAt one s' (k₁ + ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
      (k₂ + 2 * (faceOfLkp x).parts.length) ownShape keyShape := by
  obtain ⟨d', fork, home, same, ground, -⟩ := callerYes one number x s rounds columns s' accepts
  have hNumber := callerKeepsTheIndexMasksNumber accepts
  obtain ⟨o, d₁, k, d₂, e₁, e₂, hState⟩ := callerReturnsByItsTwoTakings accepts
  have hStatement : d' = d₂ := by
    have h₁ := congrArg (·.d) same
    have h₂ := congrArg (·.d) hState
    exact h₁.symm.trans h₂
  subst hStatement
  have hOther : one.ranges.messageId ≠ s.idx := fun e => stand.ne e.symm
  obtain ⟨-, w₁, c₁, -, -⟩ := takeMasks_laws e₁
  obtain ⟨-, w₂, c₂, -, -⟩ := takeMasks_laws e₂
  have hD : s'.d = d' := congrArg (·.d) hState
  refine ⟨hNumber ▸ stand.ne, ?_, ?_, ?_, ?_⟩
  · rw [hD]
    exact ledgerAt_same (w₁ k₁ stand.ownAt).1 (c₂ _ hOther)
  · rw [hD, hNumber]
    exact (w₂ k₂ (ledgerAt_same stand.idxAt (c₁ _ stand.ne))).1
  · rw [hD]
    exact shapeRidesPastACaller ground stand.ownIs
  · rw [hD, hNumber]
    exact shapeRidesPastACaller ground stand.keyIs

/-! ## 2 The walk along the first chain -/

theorem reachStepsBack {S Cl P : Type} {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {k : Nat}
    {z : P} {s' : S} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ r hb hy => exact ⟨_, _, r, hb, hy⟩

section Walk
variable (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) (first second : Lookup)

theorem blockAtZeroSendsTheIndexMasks (two : lookupsOf one = [first, second])
    (blk : Block FirstState Claim) (found : (firstChain one D told set N).blocksInOrder[0]? = some blk)
    (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    blk.decide s rs gs =
      (sendIndexMasks (Cl := Claim) one pieces (groupsTold told 0 (rootsAt D 0))).decide s rs gs := by
  simp only [firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

theorem blockAtOneSendsTheOwnMessage (two : lookupsOf one = [first, second])
    (blk : Block FirstState Claim) (found : (firstChain one D told set N).blocksInOrder[1]? = some blk)
    (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    blk.decide s rs gs =
      (sendOwnMessage (Cl := Claim) one pieces (groupsTold told (rootsBefore D 2) (rootsAt D 2))).decide
        s rs gs := by
  simp only [firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

theorem blockAtThreeIsTheFirstCaller (two : lookupsOf one = [first, second])
    (blk : Block FirstState Claim) (found : (firstChain one D told set N).blocksInOrder[3]? = some blk)
    (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    blk.decide s rs gs = (caller one 0 first).decide s rs gs := by
  simp only [firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

theorem blockAtNineIsTheSecondCaller (two : lookupsOf one = [first, second])
    (blk : Block FirstState Claim) (found : (firstChain one D told set N).blocksInOrder[9]? = some blk)
    (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    blk.decide s rs gs = (caller one 1 second).decide s rs gs := by
  simp only [firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

variable {one D told set N first second} {ft : Nat} {start : Xi → FirstState} {z : Xi} {s : FirstState}

/-- **In front of the first caller neither ledger has been taken from**: from the acceptance of the two sendings and of the
first link's `lay`. Conditional: both messages have an answer and a mask row. -/
theorem takesStandInFrontOfTheFirstCaller (two : lookupsOf one = [first, second])
    (indexAnswers : one.indexMasks.shape.answers ≠ 0) (indexRows : 0 < one.indexMasks.shape.maskRows)
    (ownAnswers : one.ranges.message.shape.answers ≠ 0) (ownRows : 0 < one.ranges.message.shape.maskRows)
    (reached : Reach ft (firstChain one D told set N).blocksInOrder start 3 (z, s)) :
    TakesStandAt one s 0 0 one.ranges.message.shape one.indexMasks.shape := by
  obtain ⟨s₂, b₂, r₂, f₂, y₂⟩ := reachStepsBack reached
  obtain ⟨s₁, b₁, r₁, f₁, y₁⟩ := reachStepsBack r₂
  obtain ⟨s₀, b₀, -, f₀, y₀⟩ := reachStepsBack r₁
  obtain ⟨rs₀, gs₀, e₀⟩ := stepYes_decide y₀
  obtain ⟨rs₁, gs₁, e₁⟩ := stepYes_decide y₁
  obtain ⟨rs₂, gs₂, e₂⟩ := stepYes_decide y₂
  rw [blockAtZeroSendsTheIndexMasks one D told set N first second two b₀ f₀] at e₀
  rw [blockAtOneSendsTheOwnMessage one D told set N first second two b₁ f₁] at e₁
  obtain ⟨-, -, ne, leftKey, atKey, leftOwn, atOwn, -, -⟩ :=
    front_laws e₀ e₁ indexAnswers indexRows ownAnswers ownRows
  have same : s = s₂ :=
    lay_ok one set 0 first s₂ s ((dec_laid0 one D told set N first second two b₂ f₂ s₂ _ gs₂).symm.trans e₂)
  subst same
  exact ⟨ne, atOwn, atKey, shapeOfALedgerLeft leftOwn, shapeOfALedgerLeft leftKey⟩

/-- **Behind the first caller**: the two counts, and the homes by the deal from 0, 0. -/
theorem standBehindTheFirstCaller (two : lookupsOf one = [first, second])
    (indexAnswers : one.indexMasks.shape.answers ≠ 0) (indexRows : 0 < one.indexMasks.shape.maskRows)
    (ownAnswers : one.ranges.message.shape.answers ≠ 0) (ownRows : 0 < one.ranges.message.shape.maskRows)
    (levels : ∀ v ∈ (faceOfLkp first).parts, 1 ≤ v)
    (reached : Reach ft (firstChain one D told set N).blocksInOrder start 4 (z, s)) :
    TakesStandAt one s ((faceOfLkp first).slots - 2 * (faceOfLkp first).parts.length)
        (2 * (faceOfLkp first).parts.length) one.ranges.message.shape one.indexMasks.shape ∧
      s.base.home.toList = (deal (fromKeys (faceOfLkp first)) 0 0).map
        (homeOfCoin one.ranges.messageId s.idx one.ranges.message.shape.maskRows
          one.indexMasks.shape.maskRows 0 0) := by
  obtain ⟨s₃, b₃, r₃, f₃, y₃⟩ := reachStepsBack reached
  have stand := takesStandInFrontOfTheFirstCaller two indexAnswers indexRows ownAnswers ownRows r₃
  obtain ⟨rs, gs, e⟩ := stepYes_decide y₃
  rw [blockAtThreeIsTheFirstCaller one D told set N first second two b₃ f₃] at e
  have behind := takesStandBehindACaller one 0 first stand rs gs e
  have hHomes := callersHomesWhereTakesStand one 0 first stand levels rs gs e 0 0
  rw [unroll_look, callerKeepsTheIndexMasksNumber e |>.symm] at hHomes
  simp only [Nat.zero_add] at behind hHomes
  exact ⟨behind, hHomes⟩

/-- **In front of the second caller the counts are those behind the first**: the five steps of link 0 behind its caller touch
neither the statement's part nor the message's number: `LookupKeeps`, `LayerKeeps`, the state as it was, `clr`, the state as it
was. -/
theorem takesStandInFrontOfTheSecondCaller (two : lookupsOf one = [first, second])
    (indexAnswers : one.indexMasks.shape.answers ≠ 0) (indexRows : 0 < one.indexMasks.shape.maskRows)
    (ownAnswers : one.ranges.message.shape.answers ≠ 0) (ownRows : 0 < one.ranges.message.shape.maskRows)
    (levels : ∀ v ∈ (faceOfLkp first).parts, 1 ≤ v)
    (reached : Reach ft (firstChain one D told set N).blocksInOrder start 9 (z, s)) :
    TakesStandAt one s ((faceOfLkp first).slots - 2 * (faceOfLkp first).parts.length)
      (2 * (faceOfLkp first).parts.length) one.ranges.message.shape one.indexMasks.shape := by
  obtain ⟨s₈, b₈, r₈, f₈, y₈⟩ := reachStepsBack reached
  obtain ⟨s₇, b₇, r₇, f₇, y₇⟩ := reachStepsBack r₈
  obtain ⟨s₆, b₆, r₆, f₆, y₆⟩ := reachStepsBack r₇
  obtain ⟨s₅, b₅, r₅, f₅, y₅⟩ := reachStepsBack r₆
  obtain ⟨s₄, b₄, r₄, f₄, y₄⟩ := reachStepsBack r₅
  have stand :=
    (standBehindTheFirstCaller two indexAnswers indexRows ownAnswers ownRows levels r₄).1
  obtain ⟨rs₄, gs₄, e₄⟩ := stepYes_decide y₄
  rw [blockAtFourIsTheFirstLookup one D told set N first second two b₄ f₄] at e₄
  obtain ⟨heard, ledger, rfl⟩ := lookupDecisionKeeps e₄
  obtain ⟨fork, rows, keys, rfl⟩ :
      LayerKeeps _ s₆ := keeps_layers one D told set N first second two ft (fun _ _ _ => True) 5
        (by decide) b₅ f₅ _ _ y₅
  obtain ⟨rs₆, gs₆, e₆⟩ := stepYes_decide y₆
  obtain ⟨rs₇, gs₇, e₇⟩ := stepYes_decide y₇
  obtain ⟨rs₈, gs₈, e₈⟩ := stepYes_decide y₈
  have same₇ := after_ok one set 0 first _ s₇
    ((dec_behind0 one D told set N first second two b₆ f₆ _ _ gs₆).symm.trans e₆)
  subst same₇
  have same₈ := clear_ok one set 0 first _ s₈
    ((dec_cleared0 one D told set N first second two b₇ f₇ _ _ gs₇).symm.trans e₇)
  subst same₈
  have same₉ := lay_ok one set 1 second _ s
    ((dec_laid1 one D told set N first second two b₈ f₈ _ _ gs₈).symm.trans e₈)
  subst same₉
  exact stand.sameLedgers rfl rfl

/-- **Behind the second caller**: the homes by the deal from the first lookup's two takings. -/
theorem homesBehindTheSecondCaller (two : lookupsOf one = [first, second])
    (indexAnswers : one.indexMasks.shape.answers ≠ 0) (indexRows : 0 < one.indexMasks.shape.maskRows)
    (ownAnswers : one.ranges.message.shape.answers ≠ 0) (ownRows : 0 < one.ranges.message.shape.maskRows)
    (levels : ∀ v ∈ (faceOfLkp first).parts, 1 ≤ v) (levelsSecond : ∀ v ∈ (faceOfLkp second).parts, 1 ≤ v)
    (reached : Reach ft (firstChain one D told set N).blocksInOrder start 10 (z, s)) :
    s.base.home.toList =
      (deal (fromKeys (faceOfLkp second))
        ((faceOfLkp first).slots - 2 * (faceOfLkp first).parts.length)
        (2 * (faceOfLkp first).parts.length)).map
        (homeOfCoin one.ranges.messageId s.idx one.ranges.message.shape.maskRows
          one.indexMasks.shape.maskRows 0 0) := by
  obtain ⟨s₉, b₉, r₉, f₉, y₉⟩ := reachStepsBack reached
  have stand := takesStandInFrontOfTheSecondCaller two indexAnswers indexRows ownAnswers ownRows levels r₉
  obtain ⟨rs, gs, e⟩ := stepYes_decide y₉
  rw [blockAtNineIsTheSecondCaller one D told set N first second two b₉ f₉] at e
  have hHomes := callersHomesWhereTakesStand one 1 second stand levelsSecond rs gs e 0 0
  rw [unroll_look, callerKeepsTheIndexMasksNumber e |>.symm] at hHomes
  simp only [Nat.zero_add] at hHomes
  exact hHomes

end Walk

/-! ## 3 One number, from the homes -/

/-- **Homes that go by the deal behind the takes in front of the lookup share one number with the coins that `maskOf` reads.**
The body of `theLedgerIsTheKeyBook` (E2E/Lookup/Key/LedgerIsTheKeyBook.lean), at any list of homes. -/
theorem homesAndCoinsShareOneNumber {home : Array Slot} {ownMessage keyMessage ownMaskRows keyMaskRows : Nat}
    (data : KeyPub) (number : Nat) (lookup : K3.At) (stands : LookupStandsAtTheKeyBook data number lookup)
    (homesAre : home.toList =
      (deal (fromKeys lookup.face) (takenBeforeLookup data number).1
        (takenBeforeLookup data number).2).map
        (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0))
    (look : Addr → (d : Due) × Cs d) (first : Nat) :
    ∀ j, j < lookup.face.slots → ∃ n,
      home[j]? = some
        (if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
          ⟨keyMessage, takenNo keyMaskRows n⟩
         else ⟨ownMessage, takenNo ownMaskRows n⟩) ∧
      maskOf (keyOwners lookup.face) lookup.face (keyBookHomes data number) look first (first + j) =
        ProofFile.Honest.K3.Law.rd ((coinsE (look (keyBookHomes data number
                  ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "")).1).2).getD
                ((if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
                    tableAt data.sIdx 0
                  else tableAt data.sMsg 0) + n) OnBytes.zeroE) := by
  intro j hj
  have hMarks := ProofFile.Honest.K3.Parts.unroll_key lookup.face stands.planes
  have hLength : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).length =
      lookup.face.slots := by
    rw [← List.length_map (f := (· == indexMaskRun)), hMarks, AtPublicFiles.KeyLookup.fromKeys_length]
  have hPosition : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).length := by
    rw [hLength]
    exact hj
  rw [← hMarks] at homesAre
  have hDeal := dealAtAPosition
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map (· == indexMaskRun))
    (takenBeforeLookup data number).1 (takenBeforeLookup data number).2 j
    (by rw [List.length_map]; exact hPosition)
  have hAt : home[j]? = (List.map (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows 0 0)
      (deal ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map (· == indexMaskRun))
        (takenBeforeLookup data number).1 (takenBeforeLookup data number).2))[j]? := by
    rw [← homesAre, Array.getElem?_toList]
  rw [List.getElem?_map, hDeal, Option.map_some] at hAt
  have hMark : ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map
      (· == indexMaskRun)).getD j false =
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun) := by
    simp [List.getD_eq_getElem?_getD, hPosition]
  rw [hMark, ← List.map_take] at hAt
  have hMember : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" ∈
      ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face := by
    rw [List.getD_eq_getElem _ _ hPosition]
    exact List.getElem_mem hPosition
  cases hFlag : ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" ==
      indexMaskRun) with
  | true =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" =
        indexMaskRun := by simpa using hFlag
    rw [hFlag, marksCountTheIndexMasks] at hAt
    refine ⟨(takenBeforeLookup data number).2 +
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).take j).count indexMaskRun,
      ?_, ?_⟩
    · rw [hAt]
      simp [homeOfCoin]
    · unfold maskOf
      rw [Nat.add_sub_cancel_left, hOwner, keyBookHomeOfTheSecondOwner, if_pos rfl]
      simp only [Nat.add_assoc]
  | false =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" =
        K3.multRun := by
      rcases membersOfTheKeyLetter lookup.face _ hMember with h | h
      · exact h
      · rw [h] at hFlag
        simp at hFlag
    rw [hFlag, marksCountTheMultiplicities _
      fun w hw => membersOfTheKeyLetter lookup.face w (List.mem_of_mem_take hw)] at hAt
    refine ⟨(takenBeforeLookup data number).1 +
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).take j).count K3.multRun,
      ?_, ?_⟩
    · rw [hAt]
      simp [homeOfCoin]
    · unfold maskOf
      rw [Nat.add_sub_cancel_left, hOwner, keyBookHomeOfTheFirstOwner, if_neg (by simp)]
      simp only [Nat.add_assoc]

/-- **`theLedgerIsTheKeyBook` where the takes stand.** -/
theorem theLedgerWhereTakesStand (one : OnBytes.Params.OneTime) (number : Nat) (x : Lookup)
    {s s' : FirstState} {ownShape keyShape : OracleShape} (data : KeyPub) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) (face : lookup.face = faceOfLkp x)
    (stand : TakesStandAt one s (takenBeforeLookup data number).1 (takenBeforeLookup data number).2
      ownShape keyShape)
    (levels : ∀ v ∈ lookup.face.parts, 1 ≤ v) (rounds : List Fmt.RoundView)
    (columns : List (List (Nat × List UInt64)))
    (accepts : (caller one number x).decide s rounds columns = .ok s')
    (look : Addr → (d : Due) × Cs d) (first : Nat) :
    ∀ j, j < lookup.face.slots → ∃ n,
      s'.base.home[j]? = some
        (if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
          ⟨s.idx, takenNo keyShape.maskRows n⟩
         else ⟨one.ranges.messageId, takenNo ownShape.maskRows n⟩) ∧
      maskOf (keyOwners lookup.face) lookup.face (keyBookHomes data number) look first (first + j) =
        ProofFile.Honest.K3.Law.rd ((coinsE (look (keyBookHomes data number
                  ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "")).1).2).getD
                ((if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
                    tableAt data.sIdx 0
                  else tableAt data.sMsg 0) + n) OnBytes.zeroE) := by
  have hHomes := callersHomesWhereTakesStand one number x stand (face ▸ levels) rounds columns accepts 0 0
  rw [unroll_look, ← face] at hHomes
  simp only [Nat.zero_add] at hHomes
  exact homesAndCoinsShareOneNumber data number lookup stands hHomes look first

/-! ## 4 At the key file's thread -/

/-- **The homes of a state at a lookup's border**: under slot j the mask entry of the slot's owner's message at the number of take
n, and `maskOf` reads that owner's coin number (its table's start + n). -/
def HomesStandAtTheBorder (one : OnBytes.Params.OneTime) (data : KeyPub) (number : Nat) (y : Lookup)
    (s : FirstState) (look : Addr → (d : Due) × Cs d) (first : Nat) : Prop :=
  ∀ j, j < (faceOfLkp y).slots → ∃ n,
    s.base.home[j]? = some
      (if (ProofFile.Honest.K3.Parts.unroll (keyOwners (faceOfLkp y)) (faceOfLkp y)).getD j "" == indexMaskRun then
        ⟨s.idx, takenNo one.indexMasks.shape.maskRows n⟩
       else ⟨one.ranges.messageId, takenNo one.ranges.message.shape.maskRows n⟩) ∧
    maskOf (keyOwners (faceOfLkp y)) (faceOfLkp y) (keyBookHomes data number) look first (first + j) =
      ProofFile.Honest.K3.Law.rd ((coinsE (look (keyBookHomes data number
                ((ProofFile.Honest.K3.Parts.unroll (keyOwners (faceOfLkp y)) (faceOfLkp y)).getD j "")).1).2).getD
              ((if (ProofFile.Honest.K3.Parts.unroll (keyOwners (faceOfLkp y)) (faceOfLkp y)).getD j "" == indexMaskRun then
                  tableAt data.sIdx 0
                else tableAt data.sMsg 0) + n) OnBytes.zeroE)

theorem bindReturns {α β : Type} {value : Option α} {rest : α → Option β} {result : β}
    (returned : (value >>= rest) = some result) : ∃ a, rest a = some result := by
  cases value with
  | none => cases returned
  | some a => exact ⟨a, returned⟩

/-- The faces of a book are those of the lookups that the sizes make. -/
theorem facesOfAKeyPub {z : OnBytes.Plan.KeySized} {a : Nat} {K : KeyPub} (h : KeyPub.of z a = some K) :
    K.faces =
      (OnBytes.Wf.lookupsOf z.ranges.x (OnBytes.Wf.matrixOf z.once.shape)).map faceOfLkp := by
  unfold KeyPub.of at h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  obtain ⟨_, h⟩ := bindReturns h
  have same : _ = K := Option.some.inj h
  subst same
  rfl

/-- At the written sizes both messages have an answer and a mask row. By the kernel. -/
theorem writtenMessagesHaveAnswersAndMaskRows :
    Lk6.AtPlan.keyFull.once.input.shape.answers ≠ 0 ∧ 0 < Lk6.AtPlan.keyFull.once.input.shape.maskRows ∧
      Lk6.AtPlan.keyFull.ranges.x.message.shape.answers ≠ 0 ∧
      0 < Lk6.AtPlan.keyFull.ranges.x.message.shape.maskRows := by
  decide +kernel

section Top
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles}

/-- **THE HOMES AT THE THREAD's TWO BORDERS.** Wherever the key file's first thread stands at border 4 or 10, the state bears under
each slot of the lookup of that number the home that `theLedgerIsTheKeyBook` names, at the written book. Conditional: the
description is sourced from the files in scope; the book is at the written sizes. -/
theorem homesAtTheLookupsBorders (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (data : KeyPub) (written : fullPub = some data)
    (look : Addr → (d : Due) × Cs d) (first : Nat) :
    ∀ b ∈ [4, 10], ∀ k s (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables) b k s m E →
      ∃ y, (lookupsOf (one₀ source))[if b = 4 then 0 else 1]? = some y ∧
        HomesStandAtTheBorder (one₀ source) data (if b = 4 then 0 else 1) y s look first := by
  intro b atLookup k s m E thread
  obtain ⟨public₀, made, fromFiles, maker, madeSource, -, -⟩ := sourced.source
  have reading := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO fromFiles
  obtain ⟨x₀, x₁, two⟩ := LPFD.hl_in_scope scope reading maker madeSource sourced.named.plan
  have five := Johnson.RunOne.Law.KeyInScope.five_in_scope scope reading maker madeSource
    sourced.named.plan
  have hLooks : lookupsOf (one₀ source) =
      OnBytes.Wf.lookupsOf Lk6.AtPlan.keyFull.ranges.x (OnBytes.Wf.matrixOf Lk6.AtPlan.keyFull.once.shape) := by
    show OnBytes.Wf.lookupsOf (one₀ source).ranges (OnBytes.Wf.matrixOf (one₀ source).lin) = _
    rw [five.2.1, five.2.2.1]
  have hFaces : data.faces = [faceOfLkp x₀, faceOfLkp x₁] := by
    rw [facesOfAKeyPub (z := Lk6.AtPlan.keyFull) written, ← hLooks, two]
    rfl
  have hParts : (lookupsOf (one₀ source)).map (fun y => y.parts) =
      [List.replicate 12 36, List.replicate 12 35] := by
    rw [hLooks]
    exact AtPublicFiles.KeyFaces.parts_full
  rw [two] at hParts
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hParts
  have levels₀ : ∀ v ∈ (faceOfLkp x₀).parts, 1 ≤ v := fun v hv => by
    have hv' : v ∈ x₀.parts := hv
    rw [hParts.1] at hv'
    have := List.eq_of_mem_replicate hv'
    omega
  have levels₁ : ∀ v ∈ (faceOfLkp x₁).parts, 1 ≤ v := fun v hv => by
    have hv' : v ∈ x₁.parts := hv
    rw [hParts.2] at hv'
    have := List.eq_of_mem_replicate hv'
    omega
  obtain ⟨a₁, a₂, a₃, a₄⟩ := writtenMessagesHaveAnswersAndMaskRows
  have indexAnswers : (one₀ source).indexMasks.shape.answers ≠ 0 := by
    show source.Y.k.oneTime.indexMasks.shape.answers ≠ 0
    rw [five.2.2.2.1]
    exact a₁
  have indexRows : 0 < (one₀ source).indexMasks.shape.maskRows := by
    show 0 < source.Y.k.oneTime.indexMasks.shape.maskRows
    rw [five.2.2.2.1]
    exact a₂
  have ownAnswers : (one₀ source).ranges.message.shape.answers ≠ 0 := by
    show source.Y.k.oneTime.ranges.message.shape.answers ≠ 0
    rw [five.2.1]
    exact a₃
  have ownRows : 0 < (one₀ source).ranges.message.shape.maskRows := by
    show 0 < source.Y.k.oneTime.ranges.message.shape.maskRows
    rw [five.2.1]
    exact a₄
  have hStand := lookupsStandAtTheWrittenSizes data written
  have planes₀ : 2 ≤ (faceOfLkp x₀).planes := by
    obtain ⟨face, hFace, hp, -⟩ := hStand.2 0 (by decide)
    rw [hFaces] at hFace
    obtain rfl : faceOfLkp x₀ = face := Option.some.inj hFace
    exact hp
  have planes₁ : 2 ≤ (faceOfLkp x₁).planes := by
    obtain ⟨face, hFace, hp, -⟩ := hStand.2 1 (by decide)
    rw [hFaces] at hFace
    obtain rfl : faceOfLkp x₁ = face := Option.some.inj hFace
    exact hp
  have hTaken := takesInFrontOfALookupAreTheBooks data _ _ hFaces levels₀
  have hMade := thread.2.2.2.2.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · have reached := reach_made₁ source numbers later filling w₀ rc x
      (by rw [(AtPublicFiles.KeyThread.lengths scope sourced.named).1]; decide) hMade
    have hBehind := (standBehindTheFirstCaller (one := one₀ source) (D := source.Y.D.1)
      (told := source.Y.told.1) (set := source.set) (N := numbers) two indexAnswers indexRows ownAnswers
      ownRows levels₀ reached).2
    refine ⟨x₀, by rw [two]; rfl, ?_⟩
    show HomesStandAtTheBorder (one₀ source) data 0 x₀ s look first
    have stands : LookupStandsAtTheKeyBook data 0 ⟨lookPlace 0, faceOfLkp x₀, 0⟩ :=
      ⟨rfl, by rw [hFaces]; rfl, by rw [hFaces]; rfl, planes₀⟩
    exact homesAndCoinsShareOneNumber data 0 ⟨lookPlace 0, faceOfLkp x₀, 0⟩ stands
      (by rw [hTaken.1]; exact hBehind) look first
  · have reached := reach_made₁ source numbers later filling w₀ rc x
      (by rw [(AtPublicFiles.KeyThread.lengths scope sourced.named).1]; decide) hMade
    have hBehind := homesBehindTheSecondCaller (one := one₀ source) (D := source.Y.D.1)
      (told := source.Y.told.1) (set := source.set) (N := numbers) two indexAnswers indexRows ownAnswers
      ownRows levels₀ levels₁ reached
    refine ⟨x₁, by rw [two]; rfl, ?_⟩
    show HomesStandAtTheBorder (one₀ source) data 1 x₁ s look first
    have stands : LookupStandsAtTheKeyBook data 1 ⟨lookPlace 1, faceOfLkp x₁, 0⟩ :=
      ⟨rfl, by rw [hFaces]; rfl, by rw [hFaces]; rfl, planes₁⟩
    exact homesAndCoinsShareOneNumber data 1 ⟨lookPlace 1, faceOfLkp x₁, 0⟩ stands
      (by rw [hTaken.2]; exact hBehind) look first

end Top

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.callersHomesWhereTakesStand
#print axioms AtPublicFiles.Lookup.Key.takesStandBehindACaller
#print axioms AtPublicFiles.Lookup.Key.takesStandInFrontOfTheFirstCaller
#print axioms AtPublicFiles.Lookup.Key.standBehindTheFirstCaller
#print axioms AtPublicFiles.Lookup.Key.takesStandInFrontOfTheSecondCaller
#print axioms AtPublicFiles.Lookup.Key.homesBehindTheSecondCaller
#print axioms AtPublicFiles.Lookup.Key.homesAndCoinsShareOneNumber
#print axioms AtPublicFiles.Lookup.Key.theLedgerWhereTakesStand
#print axioms AtPublicFiles.Lookup.Key.facesOfAKeyPub
#print axioms AtPublicFiles.Lookup.Key.writtenMessagesHaveAnswersAndMaskRows
#print axioms AtPublicFiles.Lookup.Key.homesAtTheLookupsBorders
