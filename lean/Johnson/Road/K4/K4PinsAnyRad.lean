-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsAnyRad.lean: WHAT FOUR OF K4's TESTS ON THE PLAN DO NOT READ. `maskPlanB`,
`maskEllP` (Johnson/Road/K4/Rec/PinsBools.lean) and `arrayPlanB` (Johnson/Road/K4/Rec/Arrays.lean)
read of a structure `PinPlan` neither the radii, nor the type of the cells, nor rc and posI;
`arrayPlanB` reads of the built segments' lists of names ONE ENTRY; `indexTieB`
(Johnson/Road/K4/K4PinsAtWide.lean) reads of the members their (shape, seat) and of the numbers two
fields. So each can be asked at a plan without these. Three definitions and ten theorems; nothing is
evaluated.

  `pin0 D f l`: the plan's letters at link l: the radii 0, no cells; f: a member's seat by number.
  `elim_congr`, `dite_calls`: two small rules: under a search's result; under "k is a member of the
    caller's list", where the member's SHAPE alone is read.
  `maskPlanB_pin0`, `maskEllP_pin0`: the two at any radii, cells, rc, posI are the two at `pin0`.
  `armAt`, `arrayArm`: `arrayPlanB`'s own text behind the look-up of the name, written with
    `Option.elim`. `arrayPlanB_arm`: **`arrayPlanB` IS the look-up and then that text**: by cases on
    the four searches, at all letters. `arrayArm_rad`: it does not read the radii. `arrayArm_sent`:
    nor the lists of
    names: by rfl. `arrayPlanB_named`: where the look-up finds bn, the test is `arrayArm` at bn, at
    the radii 0.
  `indexTieB_pairs`, `indexTieB_sameN`.

OBJECT: the tests' texts. USER: Johnson/Road/K4/K4PinsClosed.lean. KIN: `calls_fst`, `calls_len`,
`calls_get_fst`, `sitsIn_rad` (Johnson/Road/K4/K4PlanClosed.lean), called; `memAt_pairs`
(Johnson/Road/K4/K4PlanCarry.lean), called.

Limits. K04_law IS NOT PROVED BY THIS. No test is shown to accept anywhere.
-/
import Johnson.Road.K4.Rec.Arrays
import Johnson.Road.K4.Rec.PinsBools
import Johnson.Road.K4.K4PlanClosed
import Johnson.Road.K4.K4PlanCarry
import Johnson.Road.K4.K4PinsAtWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Params (ReqArray)
open Johnson.Road.K4.SeamBools (blocksOneB)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls messagesAt keptAt blocksB)
open VerifiableInference.Desc.First.FillSent (whereIsP maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP)
open VerifiableInference.Desc.Sound (Mem seatOf)
open OnBytes.Road.K4.Rec (RecPlan maskPlanB maskEllP arrayPlanB memberNo)

/-- The plan's letters at link l, at the radii 0, without cells. f: a member's seat, by number. -/
def pin0 (D : Sent) (f : ℕ → ℕ × ℕ) (l : ℕ) : PinPlan Empty :=
  ⟨D, fun _ => 0, l, fun j => f j.val, fun e _ _ => e.elim, fun _ => (false, 0, 0)⟩

/-- Under a search's result. -/
theorem elim_congr {α β : Type} (X : Option α) (e : β) {G G' : α → β} (h : ∀ a, G a = G' a) :
    X.elim e G = X.elim e G' := by
  cases X with
  | none => rfl
  | some a => exact h a

/-- Under "k is a member of the caller's list", where the member's shape alone is read. -/
theorem dite_calls {β : Type} (D : Sent) (rad rad' : OnBytes.OracleShape → ℕ) (i k : ℕ)
    (F : OnBytes.OracleShape → β) (e : β) :
    (if h : k < (sigListCalls D rad i).length then F ((sigListCalls D rad i).get ⟨k, h⟩).1
      else e) =
      if h : k < (sigListCalls D rad' i).length then F ((sigListCalls D rad' i).get ⟨k, h⟩).1
      else e := by
  by_cases h : k < (sigListCalls D rad i).length
  · have h' : k < (sigListCalls D rad' i).length := by
      rw [← calls_len D rad rad' i]
      exact h
    rw [dif_pos h, dif_pos h', calls_get_fst D rad rad' i h h']
  · have h' : ¬ k < (sigListCalls D rad' i).length := by
      rw [← calls_len D rad rad' i]
      exact h
    rw [dif_neg h, dif_neg h']

section
variable {C : Type} (D : Sent) (rad : OnBytes.OracleShape → ℕ) (i : ℕ) (f : ℕ → ℕ × ℕ)
  (rc : C → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ)

/-- **The test on the mask row at any radii and cells is the test at `pin0`.** -/
theorem maskPlanB_pin0 (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) :
    maskPlanB (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) own R n m =
      maskPlanB (pin0 D f i) own R n m := by
  unfold maskPlanB pin0
  dsimp only
  cases List.findIdx? (fun x => x.shape.maskRows != 0) (messagesAt D i) with
  | none => rfl
  | some mI =>
    cases maskP R.shape R.d m with
    | none =>
      exact dite_calls D rad (fun _ => 0) i ((keptAt D i).length + mI)
        (fun sh => decide (0 < sh.maskRows) && false) false
    | some o =>
      exact dite_calls D rad (fun _ => 0) i ((keptAt D i).length + mI)
        (fun sh => decide (0 < sh.maskRows) &&
          (decide (seatP own R.L.places n o = some (f ((keptAt D i).length + mI))) &&
            decide (rowBitsP R.M n o .mask = 0))) false

/-- **So is the plan's length of the mask row.** -/
theorem maskEllP_pin0 :
    maskEllP (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) = maskEllP (pin0 D f i) := by
  unfold maskEllP pin0
  dsimp only
  cases List.findIdx? (fun x => x.shape.maskRows != 0) (messagesAt D i) with
  | none => rfl
  | some mI =>
    exact dite_calls D rad (fun _ => 0) i ((keptAt D i).length + mI)
      (fun sh => (pMask D.codes sh).ell) 0

end

/-! ## An array -/

/-- `arrayPlanB`'s text at a member's shape. -/
def armAt (D : Sent) (f : ℕ → ℕ × ℕ) (own : List (ℕ × ℕ)) (R : RecPlan) (n m I K : ℕ)
    (bn : ℕ × String) (ar : ReqArray) (k : ℕ) (sh : OnBytes.OracleShape) : Bool :=
  decide (R.layout = D.layout) &&
    (whereIsP R.d m bn.1 ar.message).elim false fun o =>
      decide (seatP own R.L.places n o = some (f k)) &&
        blocksOneB ar.blocks (rowBitsP R.M n o .main) (placeBitsP R.cs R.M n o .main) &&
        decide (I ≤ ar.sizeI) && decide (K ≤ ar.sizeC) &&
        blocksB ar.blocks ar.sizeI ar.sizeC (min sh.mainRows (2 ^ rowBitsP R.M n o .main))
          (pMain D.codes sh).ell

/-- `arrayPlanB`'s text behind the look-up of the array's name. -/
def arrayArm (D : Sent) (rad : OnBytes.OracleShape → ℕ) (i : ℕ) (f : ℕ → ℕ × ℕ)
    (own : List (ℕ × ℕ)) (R : RecPlan) (n m I K : ℕ) (bn : ℕ × String) : Bool :=
  (OnBytes.reqArray D.layout bn.1 bn.2).elim false fun ar =>
    (memberNo D i bn ar).elim false fun k =>
      if h : k < (sigListCalls D rad i).length then
        armAt D f own R n m I K bn ar k ((sigListCalls D rad i).get ⟨k, h⟩).1
      else false

section
variable {C : Type} (D : Sent) (rad rad' : OnBytes.OracleShape → ℕ) (i : ℕ) (f : ℕ → ℕ × ℕ)
  (rc : C → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ) (own : List (ℕ × ℕ)) (R : RecPlan)
  (n m T I K : ℕ)

/-- **The test at an array is the look-up of its name and then that text**: at all letters. -/
theorem arrayPlanB_arm :
    arrayPlanB (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) own R n m T I K =
      ((D.arrayOf.getD i #[])[T]?).elim false (arrayArm D rad i f own R n m I K) := by
  unfold arrayPlanB
  dsimp only
  cases (D.arrayOf.getD i #[])[T]? with
  | none => rfl
  | some bn =>
    dsimp only [Option.elim, arrayArm]
    cases OnBytes.reqArray D.layout bn.1 bn.2 with
    | none => rfl
    | some ar =>
      dsimp only [Option.elim]
      cases memberNo D i bn ar with
      | none => rfl
      | some k =>
        dsimp only [Option.elim, armAt]
        cases whereIsP R.d m bn.1 ar.message with
        | none => rfl
        | some o => rfl

/-- The text does not read the radii. -/
theorem arrayArm_rad (bn : ℕ × String) :
    arrayArm D rad i f own R n m I K bn = arrayArm D rad' i f own R n m I K bn :=
  elim_congr _ false fun ar => elim_congr _ false fun k =>
    dite_calls D rad rad' i k (armAt D f own R n m I K bn ar k) false

/-- **Where the look-up finds bn, the test is the text at bn, at the radii 0.** -/
theorem arrayPlanB_named {bn : ℕ × String} (h : (D.arrayOf.getD i #[])[T]? = some bn) :
    arrayPlanB (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) own R n m T I K =
      arrayArm D (fun _ => 0) i f own R n m I K bn := by
  rw [arrayPlanB_arm D rad i f rc posI own R n m T I K, h]
  exact arrayArm_rad D rad (fun _ => 0) i f own R n m I K bn

end

/-- The text reads of D the codes, the shape and the layout alone. -/
theorem arrayArm_sent (c : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (l : OnBytes.Params.ReqLayout) (a a' : Array (Array (ℕ × String)))
    (rad : OnBytes.OracleShape → ℕ) (i : ℕ) (f : ℕ → ℕ × ℕ) (own : List (ℕ × ℕ)) (R : RecPlan)
    (n m I K : ℕ) (bn : ℕ × String) :
    arrayArm ⟨c, s, l, a⟩ rad i f own R n m I K bn =
      arrayArm ⟨c, s, l, a'⟩ rad i f own R n m I K bn := rfl

/-! ## The test on the index masks' message -/

/-- **It reads of the members their (shape, seat) alone.** -/
theorem indexTieB_pairs {ms ms' : List Mem} (h : SamePairs ms ms') {cs : OnBytes.Codes}
    {M : List OnBytes.OracleShape} {places : List (ℕ × ℕ)} {N : Numbers} {n : ℕ}
    (hT : indexTieB cs M places ms N n = true) : indexTieB cs M places ms' N n = true := by
  obtain ⟨sh, u, hM, hq, hu, hsh, _, _⟩ := indexTie_of_B hT
  obtain ⟨u', hu', e'⟩ := memAt_pairs h hu
  have hu'' : ms'.find? (fun y => decide (seatOf y = N.index)) = some u' := hu'
  have hu0 : ms.find? (fun y => decide (seatOf y = N.index)) = some u := hu
  have e0 : (memPair u').1 = (memPair u).1 := congrArg Prod.fst e'
  have e1 : (u'.1.l.get u'.2).1 = (u.1.l.get u.2).1 := e0
  unfold indexTieB at hT ⊢
  rw [hM, hu0] at hT
  rw [hM, hu'']
  show (decide (places[N.indexNo]? = some N.index) && decide ((u'.1.l.get u'.2).1 = sh) &&
    decide (0 < sh.maskRows) && decide (n ≤ sh.maskRows * (pMask cs sh).ell)) = true
  rw [e1]
  exact hT

/-- It reads of the numbers two fields. -/
theorem indexTieB_sameN {N N' : Numbers} (h1 : N'.indexNo = N.indexNo) (h2 : N'.index = N.index)
    (cs : OnBytes.Codes) (M : List OnBytes.OracleShape) (places : List (ℕ × ℕ)) (ms : List Mem)
    (n : ℕ) : indexTieB cs M places ms N' n = indexTieB cs M places ms N n := by
  unfold indexTieB
  rw [h1, h2]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.dite_calls
#print axioms OnBytes.Road.K4.maskPlanB_pin0
#print axioms OnBytes.Road.K4.maskEllP_pin0
#print axioms OnBytes.Road.K4.arrayPlanB_arm
#print axioms OnBytes.Road.K4.arrayArm_rad
#print axioms OnBytes.Road.K4.arrayPlanB_named
#print axioms OnBytes.Road.K4.arrayArm_sent
#print axioms OnBytes.Road.K4.indexTieB_pairs
#print axioms OnBytes.Road.K4.indexTieB_sameN
