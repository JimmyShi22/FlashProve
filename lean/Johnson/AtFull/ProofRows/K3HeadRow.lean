-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3HeadRow.lean: THE ENTRY TESTS' ROW ON THE OUTPUT HEAD's CALLS
(`K3Asks.headRow`, Johnson/Desc/First/Look/K3AsksHead.lean) AT THE FULL SIZE: FROM ONE FACT ON THE
HEAD's PUBLIC TABLES, WHICH STAYS A PREMISE, AND EQUATIONS ON NUMBERS. Definitions with code and
eleven theorems: two by the kernel (one a negative test).
Why a premise stays. The row asks that the kind's own parameters make the lookup's numbers
(`P.shape`, by `shapeOwn`, Johnson/Desc/First/Look/ShapeOwn.lean). `shapeOwn` first asks `callOk`
of each call, and `callOk` reads a call's written table WHOLE: it has a value for each row, and
each value is below the prime. Three of the head's six calls bear a table of 65,536 rows made of
the parameter file's free numbers: no written value can hold them. BEHIND THAT TEST NOTHING READS
A TABLE: that is the law here.
  `strip c`: the call without its table. `callOk_strip`, `all_strip`: the test still says yes.
    `shapeOwn_strip`: where all calls pass, the numbers made of the stripped calls are the numbers
    made of the calls, their calls stripped.
  `headOne hS calls lid pub`: the row's body, of what it reads. `headB_strip`, `pubOk_strip`,
    `headOne_strip`: it does not feel the tables. `headRow_eq`: the row is `headOne` at the
    place's letters.
  `narrowH`: the eleven numbers of the head's shape that the row reads; `headOne_narrowH`.
  `callsHead`, `pubHead`, `hsFull`: the written values. `head_full`, `head_bend`: by the kernel:
    yes; and no at a floor 64 higher.
  `headRow_full`: THE END.
WHENCE THE VALUES: two runs at `VerifierAndGoals.storedPublicFiles` (no theorem). Limits. hOk (`x.calls.all callOk =
true`) AND THE EQUATIONS ARE HYPOTHESES. No soundness is claimed.

-/
import Johnson.Desc.First.Look.K3AsksDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K3Asks
open VerifiableInference.Desc.First.Look (Place P lookAt shapeOwn pubOk callOk)

/-! ## 1 Behind the test on the calls nothing reads a table -/

/-- The call without its table. -/
def strip (c : Call) : Call := { c with tau := none }

/-- The numbers, their calls stripped. -/
def stripS (s : Forest.Shape) : Forest.Shape := { s with calls := s.calls.map strip }

theorem callOk_strip {c : Call} (h : callOk c = true) : callOk (strip c) = true := by
  unfold callOk at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, h8⟩, h9⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, rfl⟩, h8⟩, h9⟩

theorem all_strip {calls : Array Call} (h : calls.all callOk = true) :
    (calls.map strip).all callOk = true := by
  rw [← Array.all_toList] at h ⊢
  rw [Array.toList_map, List.all_map]
  exact List.all_eq_true.2 fun c hc => callOk_strip (List.all_eq_true.1 h c hc)

/-- **The numbers do not feel the tables.** -/
theorem shapeOwn_strip {calls : Array Call} (h : calls.all callOk = true) (lid : Nat) :
    shapeOwn (calls.map strip) lid = (shapeOwn calls lid).map stripS := by
  have e1 : (calls.map strip).foldl (fun m c => min m c.n) lid =
      calls.foldl (fun m c => min m c.n) lid := by
    rw [Array.foldl_map]
    rfl
  have e2 : (calls.map strip).foldl (fun m c => max m c.k) 0 =
      calls.foldl (fun m c => max m c.k) 0 := by
    rw [Array.foldl_map]
    rfl
  have e3 : ∀ d : Nat, (calls.map strip).map (fun c => c.n - d) = calls.map fun c => c.n - d := by
    intro d
    rw [Array.map_map]
    rfl
  unfold shapeOwn
  rw [h, all_strip h]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [e1, e2, e3, Array.size_map]
  simp only [apply_ite (Option.map stripS), Option.map_map, Option.map_none]
  rfl

/-- The row's body, of what it reads. -/
def headOne (hS : Head.Shape) (calls : Array Call) (lid : Nat) (pub : Array Nat) : Bool :=
  ((shapeOwn calls lid).bind fun h0 =>
    if pubOk h0 pub then some { h0 with pub := pub } else none).any fun h =>
      headB hS (floorAt hS) h

theorem headB_strip (hS : Head.Shape) (floor : Nat) (s : Forest.Shape) :
    headB hS floor (stripS s) = headB hS floor s := by
  unfold headB
  have e : ∀ c, nOf (stripS s) c = nOf s c := by
    intro c
    unfold nOf stripS
    simp only [Array.getElem?_map]
    cases s.calls[c]? <;> rfl
  simp only [e]
  rfl

theorem pubOk_strip (s : Forest.Shape) (pub : Array Nat) : pubOk (stripS s) pub = pubOk s pub := by
  unfold pubOk stripS
  simp only [Array.size_map]

theorem headOne_strip (hS : Head.Shape) {calls : Array Call} (h : calls.all callOk = true)
    (lid : Nat) (pub : Array Nat) :
    headOne hS (calls.map strip) lid pub = headOne hS calls lid pub := by
  unfold headOne
  rw [shapeOwn_strip h]
  cases shapeOwn calls lid with
  | none => rfl
  | some s =>
    show ((if pubOk (stripS s) pub then some { stripS s with pub := pub } else none).any fun h =>
      headB hS (floorAt hS) h) = ((if pubOk s pub then some { s with pub := pub } else none).any
        fun h => headB hS (floorAt hS) h)
    rw [pubOk_strip]
    cases pubOk s pub with
    | false => rfl
    | true => exact headB_strip hS (floorAt hS) { s with pub := pub }

/-- The row is its body at the place's letters. -/
theorem headRow_eq {X : Verify.Public} {x : Place} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hx : lookAt X 24 false = some x) : headRow X = headOne X.hS x.calls x.lid x.pub := by
  unfold headRow headAt headOne
  rw [h4, hN]
  show (((lookAt X 24 false).bind fun x =>
    (P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h => { x with fs := h }).any
      fun x => headB X.hS (floorAt X.hS) x.fs) = _
  rw [hx]
  show (((P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h =>
    ({ x with fs := h } : Place)).any fun x => headB X.hS (floorAt X.hS) x.fs) = _
  unfold P.shape
  show ((((shapeOwn x.calls x.lid).bind fun h0 =>
    if pubOk h0 x.pub then some { h0 with pub := x.pub } else none).map fun h =>
      ({ x with fs := h } : Place)).any fun x => headB X.hS (floorAt X.hS) x.fs) = _
  cases ((shapeOwn x.calls x.lid).bind fun h0 =>
    if pubOk h0 x.pub then some { h0 with pub := x.pub } else none) <;> rfl

/-- The eleven numbers of the head's shape that the row reads; every other field at 0 or empty. -/
def narrowH (h : Head.Shape) : Head.Shape :=
  { lt := h.lt, la := h.la, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
    digSh := h.digSh, famF := h.famF, NMINH := h.NMINH, nmin := h.nmin, lPd := 0, toksrc := 0,
    wbEmb := 0, wbHead := 0, clipC := 0, theta := 0, cap := 0, logS := 0, tabS := 0, lmhf := 0,
    NHf := 0, lmhd := 0, lmhr := 0, lmbH := 0, iotaH := [], LIDB := 0, XL := 0, polCallsH := [] }

theorem headOne_narrowH (hS : Head.Shape) (calls : Array Call) (lid : Nat) (pub : Array Nat) :
    headOne (narrowH hS) calls lid pub = headOne hS calls lid pub := rfl

/-! ## 2 The values and the decision -/

/-- The six calls, without their tables. -/
def callsHead : Array Call :=
  #[{ name := "R16a", n := 28, iota := 1, k := 16, kappa := 5 },
    { name := "R16b", n := 28, iota := 1, k := 16, kappa := 5 },
    { name := "R8", n := 28, iota := 1, k := 8, kappa := 5 },
    { name := "FEa", n := 27, iota := 0, k := 16, kappa := 5, fn := 1 },
    { name := "FEb", n := 27, iota := 0, k := 16, kappa := 5, fn := 1 },
    { name := "FC", n := 27, iota := 0, k := 16, kappa := 5, fn := 1, t0 := 32768 }]

/-- For each tree of the key side its number of padding keys. -/
def pubHead : Array Nat :=
  #[0, 51052544, 0, 61538304, 0, 61415424, 0, 61538304, 128974848]

/-- The eleven numbers. -/
def hsFull : Head.Shape :=
  { lt := 10, la := 16, d := 5120, MF := 44, KF := 30, epsF := 53687, V := 202048, digSh := 8,
    famF := 24, NMINH := 27, nmin := 20, lPd := 0, toksrc := 0, wbEmb := 0, wbHead := 0,
    clipC := 0, theta := 0, cap := 0, logS := 0, tabS := 0, lmhf := 0, NHf := 0, lmhd := 0,
    lmhr := 0, lmbH := 0, iotaH := [], LIDB := 0, XL := 0, polCallsH := [] }

set_option maxRecDepth 1000000 in
/-- **The row's body at the written values.** -/
theorem head_full : headOne hsFull callsHead 28 pubHead = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at a floor 64 higher. -/
theorem head_bend : headOne { hsFull with NMINH := 91 } callsHead 28 pubHead = false := by
  decide +kernel

/-- **THE HEAD's ROW AT THE FULL SIZE.** -/
theorem headRow_full {X : Verify.Public} {x : Place} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hx : lookAt X 24 false = some x) (hOk : x.calls.all callOk = true)
    (hc : x.calls.map strip = callsHead) (hl : x.lid = 28) (hp : x.pub = pubHead)
    (hS : narrowH X.hS = hsFull) : headRow X = true := by
  rw [headRow_eq h4 hN hx, ← headOne_narrowH, ← headOne_strip _ hOk, hc, hl, hp, hS]
  exact head_full

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.callOk_strip
#print axioms Johnson.AtFull.ProofRows.K3.all_strip
#print axioms Johnson.AtFull.ProofRows.K3.shapeOwn_strip
#print axioms Johnson.AtFull.ProofRows.K3.headB_strip
#print axioms Johnson.AtFull.ProofRows.K3.pubOk_strip
#print axioms Johnson.AtFull.ProofRows.K3.headOne_strip
#print axioms Johnson.AtFull.ProofRows.K3.headRow_eq
#print axioms Johnson.AtFull.ProofRows.K3.headOne_narrowH
#print axioms Johnson.AtFull.ProofRows.K3.head_full
#print axioms Johnson.AtFull.ProofRows.K3.head_bend
#print axioms Johnson.AtFull.ProofRows.K3.headRow_full
