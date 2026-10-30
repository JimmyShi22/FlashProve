-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstTests.lean: THE NAMED TESTS BESIDE THE SHARED TABLE's CONSTANT
(Johnson/Desc/K14/Law/SharedConst.lean). The ledger's theorems at the proof file's second chain ask
many small things of the parameters at the seat: that a list can be said, that a shape passes its
own test, that a number is small enough. HERE each of them is ONE Bool WITH A NAME, in three closed
lists sorted by what a test reads, and for each test ONE lemma that gives it in the form in which
the ledger's theorems ask it, under the name of the binder that asks it.

  Sh.tests A                  23 tests that read the parameters at the seat (ShPlan) alone
  Sh.testsO A O lo            3 that read open letters too (fields of ShOpen)
  Sh.tests12 πA rA πB rB      10 on the two proximity tests' parameters (K12's)
  Sh.Tests, Sh.TestsO, Sh.Tests12     all of a list say yes
  Sh.Tests_iff …              all say yes exactly when each says yes
  Sh.tests_hUw …              a lemma a test
  Sh.bk A i                   the kind's sub-protocol number i of the eight
  Sh.tests_hbl, _eight, _hbl8, _hp8, _hsU, _hsO, _hO, _h1a, _hTU, _hTO, _hTS, _shU, _shO
                              what theorems that lie give from the tests: the ledger asks these too,
                              and they need no test of their own
  Sh.paid_hst, Sh.paid_hg     two premises of the ledger's top that the closed letters pay
  Sh.paid_hxW, _hsW, _hsh     three more, from the test on W's member
  Sh.paid_nWU, _nWS, _nIU, _nIS, _hN, _harr, _hap9, _hap10, _hNk     and these, from "five numbers"
  Sh.pm_nothingLeft           the promise's "nothing is left" is the chain's end's own test
  Sh.PlanOk₂                  the counted form's word for Sh.Tests
THE LISTS ARE MEANT TO SHRINK: a test that a theorem in scope pays, or that the verifier's own door
asks, leaves its list.
THE LISTS, THE EQUIVALENCES AND THE LEMMAS ON SINGLE TESTS ARE WRITTEN BY PROGRAM off one table
(name, test, the form asked, how it is had).
NO TOP OF THE LEDGER STANDS BENEATH THIS FILE: the tops are to be stated at the constant.
WHAT IS NOT HERE. No law. The two premises of the ledger's top on the written list of rounds that
are no tests with code (K14Rounds, OursBelow).
What is not claimed. That any test says yes at real parameters: not shown here. No soundness of a
    verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Goal.Numbers.K14BadAt
import Johnson.Goal.Numbers.K14JointAt
import Johnson.Goal.Numbers.K14OwnAt
import Johnson.Desc.Sound.ReadsBelowAt
import Johnson.Desc.Sound.BordersSharedFill
import Johnson.Desc.K12.Law.JohOk
import Johnson.Desc.K12.Law.BatOneOk
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Frame
import Johnson.Desc.K14.Law.LedgerSmpOwed
import Johnson.Desc.K14.Law.LedgerTie
import Johnson.Desc.K14.Law.PlanShapes
import Johnson.Desc.K14.Law.LedgerWMemberOwed
import Johnson.Desc.Sound.SeamNumbersSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

/-- PlanY is six plain clauses on numbers: it can be decided. -/
instance decPlanY (cs : Codes) (sh : OracleShape) : Decidable (PlanY cs sh) := by
  unfold PlanY
  infer_instance

namespace Sh

/-- Where there is a value, it is the value that getD reads. -/
theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => simp at h
  | some x => rfl

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-! ## Tests -/

/-- **The named tests on the parameters at the seat alone.** Each reads ShPlan's fields and nothing
else. -/
def tests : List (String × Bool) :=
  [("hUw: what goes out with o_u can be said",
      (withU A.Q.S).isSome),
   ("hS: the shared split is needed",
      A.Q.S.sharedSplitNeeded),
   ("hm: the masks stand ahead",
      A.Q.par.S.masksAhead),
   ("hok: the shape's own test",
      A.Q.S.ok),
   ("hlU: the trees of \"send o_u\" can be laid",
      (layTrees A.Q.codes (sentU A)).isSome),
   ("hlO: the trees of \"send o_omega\" can be laid",
      (layTrees A.Q.codes (withOmega A.Q.S)).isSome),
   ("hl: every code's message length is a power of two",
      A.Q.codes.lengthsOk),
   ("hlinOk: the linear claims' own test on codes and shape",
      linOk A.Q.codes A.Q.par.S),
   ("hp: each sub-protocol's own test on its parameters",
      (blocksOr A.Q).all (·.planOk)),
   ("hC2: K1's condition at \"send o_u\"",
      condPort (parU A.Q (sentU A)) A.rad2),
   ("hC5: K1's condition at \"send o_omega\"",
      condPort (parO A.Q) A.rad5),
   ("hpS: the last chain's door and the shared chain name one shape for o_omega",
      decide (A.p.S.omega = A.Q.S.omega)),
   ("pyU: what K12's read-back law asks of o_u's shape",
      decide (PlanY A.Q.codes A.Q.S.fold.u)),
   ("pyO: the like of o_omega's",
      decide (PlanY A.Q.codes A.Q.S.omega)),
   ("pyS: the like of o_sp's",
      decide (PlanY A.Q.codes A.Q.S.sharedSplit)),
   ("hix: the index's own test",
      A.Q.par.S.fold.index.ok),
   ("hIx: the index at the seat",
      indexB A.Q.par.S),
   ("ha: the index's code is no longer than 2 ^ 32",
      decide (A.Q.par.S.fold.index.code.logN ≤ 32)),
   ("hroom: the index has room for the matrix",
      decide (A.Q.par.S.matrixRows * 2 ^ A.Q.par.S.kLo ≤ A.Q.par.S.fold.index.plain)),
   ("fU9: o_u has main rows, and no mask's code where it has no mask",
      decide (0 < A.Q.S.fold.u.mainRows ∧ (A.Q.S.fold.u.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.fold.u.maskCode))),
   ("fO10: the like of o_omega",
      decide (0 < A.Q.S.omega.mainRows ∧ (A.Q.S.omega.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.omega.maskCode))),
   ("hN64: \"LIN point\"'s count at 64 slots, on the written list of rounds",
      pointNB A.Q.S A.Wr cMax64 64),
   ("hsL: the two sendings' counts, on the written list of rounds",
      sendsLB A.fl ⟨A.Q.set, A.Q.scope, A.Q.codes, A.Q.S, 0, [(1, 0)]⟩ A.Wr)]

/-- All of them say yes. -/
def Tests : Prop := (tests A).all (·.2) = true

theorem tests_length : (tests A).length = 23 := rfl

/-- All say yes: each says yes. -/
theorem Tests_iff : Tests A ↔
    (withU A.Q.S).isSome = true ∧
    A.Q.S.sharedSplitNeeded = true ∧
    A.Q.par.S.masksAhead = true ∧
    A.Q.S.ok = true ∧
    (layTrees A.Q.codes (sentU A)).isSome = true ∧
    (layTrees A.Q.codes (withOmega A.Q.S)).isSome = true ∧
    A.Q.codes.lengthsOk = true ∧
    linOk A.Q.codes A.Q.par.S = true ∧
    (blocksOr A.Q).all (·.planOk) = true ∧
    condPort (parU A.Q (sentU A)) A.rad2 = true ∧
    condPort (parO A.Q) A.rad5 = true ∧
    decide (A.p.S.omega = A.Q.S.omega) = true ∧
    decide (PlanY A.Q.codes A.Q.S.fold.u) = true ∧
    decide (PlanY A.Q.codes A.Q.S.omega) = true ∧
    decide (PlanY A.Q.codes A.Q.S.sharedSplit) = true ∧
    A.Q.par.S.fold.index.ok = true ∧
    indexB A.Q.par.S = true ∧
    decide (A.Q.par.S.fold.index.code.logN ≤ 32) = true ∧
    decide (A.Q.par.S.matrixRows * 2 ^ A.Q.par.S.kLo ≤ A.Q.par.S.fold.index.plain) = true ∧
    decide (0 < A.Q.S.fold.u.mainRows ∧ (A.Q.S.fold.u.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.fold.u.maskCode)) = true ∧
    decide (0 < A.Q.S.omega.mainRows ∧ (A.Q.S.omega.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.omega.maskCode)) = true ∧
    pointNB A.Q.S A.Wr cMax64 64 = true ∧
    sendsLB A.fl ⟨A.Q.set, A.Q.scope, A.Q.codes, A.Q.S, 0, [(1, 0)]⟩ A.Wr = true := by
  simp only [Tests, tests, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]

/-- What goes out with o_u can be said. -/
theorem tests_hUw (h : Tests A) :
    withU A.Q.S = some (sentU A) :=
  some_getD _ ((Tests_iff A).1 h).1

/-- The shared split is needed. -/
theorem tests_hS (h : Tests A) :
    A.Q.S.sharedSplitNeeded = true :=
  ((Tests_iff A).1 h).2.1

/-- The masks stand ahead. -/
theorem tests_hm (h : Tests A) :
    A.Q.par.S.masksAhead = true :=
  ((Tests_iff A).1 h).2.2.1

/-- The shape's own test. -/
theorem tests_hok (h : Tests A) :
    A.Q.S.ok = true :=
  ((Tests_iff A).1 h).2.2.2.1

/-- The trees of "send o_u" can be laid. -/
theorem tests_hlU (h : Tests A) :
    layTrees A.Q.codes (sentU A) = some (layU A) :=
  some_getD _ ((Tests_iff A).1 h).2.2.2.2.1

/-- The trees of "send o_omega" can be laid. -/
theorem tests_hlO (h : Tests A) :
    layTrees A.Q.codes (withOmega A.Q.S) = some (layO A) :=
  some_getD _ ((Tests_iff A).1 h).2.2.2.2.2.1

/-- Every code's message length is a power of two. -/
theorem tests_hl (h : Tests A) :
    A.Q.codes.lengthsOk = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.1

/-- The linear claims' own test on codes and shape. -/
theorem tests_hlinOk (h : Tests A) :
    linOk A.Q.codes A.Q.par.S = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.1

/-- Each sub-protocol's own test on its parameters. -/
theorem tests_hp (h : Tests A) :
    ∀ b ∈ blocksOr A.Q, b.planOk = true :=
  fun b hb => List.all_eq_true.1 ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.1 b hb

/-- K1's condition at "send o_u". -/
theorem tests_hC2 (h : Tests A) :
    condPort (parU A.Q (sentU A)) A.rad2 = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.1

/-- K1's condition at "send o_omega". -/
theorem tests_hC5 (h : Tests A) :
    condPort (parO A.Q) A.rad5 = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.1

/-- The last chain's door and the shared chain name one shape for o_omega. -/
theorem tests_hpS (h : Tests A) :
    A.p.S.omega = A.Q.S.omega :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.1

/-- What K12's read-back law asks of o_u's shape. -/
theorem tests_pyU (h : Tests A) :
    PlanY A.Q.codes A.Q.S.fold.u :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The like of o_omega's. -/
theorem tests_pyO (h : Tests A) :
    PlanY A.Q.codes A.Q.S.omega :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The like of o_sp's. -/
theorem tests_pyS (h : Tests A) :
    PlanY A.Q.codes A.Q.S.sharedSplit :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The index's own test. -/
theorem tests_hix (h : Tests A) :
    A.Q.par.S.fold.index.ok = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The index at the seat. -/
theorem tests_hIx (h : Tests A) :
    indexB A.Q.par.S = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The index's code is no longer than 2 ^ 32. -/
theorem tests_ha (h : Tests A) :
    A.Q.par.S.fold.index.code.logN ≤ 32 :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The index has room for the matrix. -/
theorem tests_hroom (h : Tests A) :
    A.Q.par.S.matrixRows * 2 ^ A.Q.par.S.kLo ≤ A.Q.par.S.fold.index.plain :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- O_u has main rows, and no mask's code where it has no mask. -/
theorem tests_fU9 (h : Tests A) :
    0 < A.Q.S.fold.u.mainRows ∧ (A.Q.S.fold.u.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.fold.u.maskCode) :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The like of o_omega. -/
theorem tests_fO10 (h : Tests A) :
    0 < A.Q.S.omega.mainRows ∧ (A.Q.S.omega.maskRows = 0 →
      A.Q.codes.mask.size ≤ A.Q.S.omega.maskCode) :=
  of_decide_eq_true ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- "LIN point"'s count at 64 slots, on the written list of rounds. -/
theorem tests_hN64 (h : Tests A) :
    pointNB A.Q.S A.Wr cMax64 64 = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The two sendings' counts, on the written list of rounds. -/
theorem tests_hsL (h : Tests A) :
    sendsLB A.fl ⟨A.Q.set, A.Q.scope, A.Q.codes, A.Q.S, 0, [(1, 0)]⟩ A.Wr = true :=
  ((Tests_iff A).1 h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


/-! ## What follows from the tests by theorems that lie: no test of its own -/

/-- Where what goes out with o_u can be said, the kind's eight sub-protocols can be said. -/
theorem blocks_isSome_of {Q : P14} {s : Array OracleNotice} (h : withU Q.S = some s) :
    (blocks Q).isSome = true := by
  unfold blocks
  simp [h]

/-- What `blocks` returns has just eight members. -/
theorem blocks_eight_of {Q : P14} {l : List (Block St Unit)} (h : blocks Q = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **The kind's sub-protocol number i**, from 0, of the eight. -/
def bk (i : ℕ) : Block St Unit := (blocksOr A.Q).getD i
  (VerifiableInference.Desc.roundlessBlock "there is no such sub-protocol" 2 none 1 .ok)

theorem tests_hbl (h : Tests A) : blocks A.Q = some (blocksOr A.Q) :=
  some_getD _ (blocks_isSome_of (tests_hUw A h))

/-- The eight by name. -/
theorem tests_eight (h : Tests A) : blocksOr A.Q =
    [bk A 0, bk A 1, bk A 2, bk A 3, bk A 4, bk A 5, bk A 6, bk A 7] := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, e⟩ := blocks_eight_of (tests_hbl A h)
  unfold bk
  rw [e]
  rfl

/-- **In the form in which the ledger's theorems ask it.** -/
theorem tests_hbl8 (h : Tests A) : blocks A.Q =
    some [bk A 0, bk A 1, bk A 2, bk A 3, bk A 4, bk A 5, bk A 6, bk A 7] := by
  rw [← tests_eight A h]
  exact tests_hbl A h

theorem tests_hp8 (h : Tests A) :
    ∀ b ∈ [bk A 0, bk A 1, bk A 2, bk A 3, bk A 4, bk A 5, bk A 6, bk A 7], b.planOk = true := by
  rw [← tests_eight A h]
  exact tests_hp A h

/-- "send o_u" sends two messages. -/
theorem tests_hsU (h : Tests A) : (sentU A).size = 2 :=
  sizeU A.Q.S (sentU A) (tests_hUw A h) (tests_hm A h)

/-- "send o_omega" sends two messages. -/
theorem tests_hsO (h : Tests A) : (withOmega A.Q.S).size = 2 :=
  sizeOmega A.Q.S (tests_hS A h)

/-- Something goes out with o_omega. -/
theorem tests_hO (h : Tests A) : 0 < (withOmega A.Q.S).size := by
  rw [tests_hsO A h]
  decide

/-- o_omega has one answer. -/
theorem tests_h1a (h : Tests A) : A.Q.S.omega.answers = 1 := (tests_pyO A h).1

/-- K1's tie of codes and shape at the three sampled messages. -/
theorem tests_hTU (h : Tests A) : VerifiableInference.Desc.K1.Tie A.Q.codes A.Q.S.fold.u :=
  (tiesOfCond A.Q (sentU A) A.rad2 A.rad5 (tests_hUw A h) (tests_hok A h) (tests_hC2 A h)
    (tests_hC5 A h)).1

theorem tests_hTO (h : Tests A) : VerifiableInference.Desc.K1.Tie A.Q.codes A.Q.S.omega :=
  (tiesOfCond A.Q (sentU A) A.rad2 A.rad5 (tests_hUw A h) (tests_hok A h) (tests_hC2 A h)
    (tests_hC5 A h)).2.1

theorem tests_hTS (h : Tests A) : VerifiableInference.Desc.K1.Tie A.Q.codes A.Q.S.sharedSplit :=
  (tiesOfCond A.Q (sentU A) A.rad2 A.rad5 (tests_hUw A h) (tests_hok A h) (tests_hC2 A h)
    (tests_hC5 A h)).2.2 (tests_hS A h)

/-- The three shapes as K1's lists name them are the parameters' own. -/
theorem tests_shU (h : Tests A) :
    shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 (tests_hUw A h)⟩ = A.Q.S.fold.u :=
  shapeAtU A.Q (sentU A) (tests_hUw A h) _

theorem tests_shO :
    shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩ = A.Q.S.omega :=
  shapeAt_of (k := ⟨0, (places A.Q (sentU A)).2.1⟩) (o0 A.Q "o_omega and o_sp")

/-! ## What the closed letters pay by themselves: premises of the ledger's top that are no premises
at the constant -/

/-- The top's hst. -/
theorem paid_hst : ∀ a : P₀ × First.S, stOf₁ a = a.2.st := fun _ => rfl

/-- The top's hg: the row weights are those of the laid row. -/
theorem paid_hg : ∀ p y' D, own A O p y' → (O.get p).2.failed = none →
    laidOf O.Pw (O.get p).2 = some D → ∀ y < A.Q.par.S.matrixRows,
    gOf A O p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum :=
  fun p _ D _ _ hD y _ => gLaid_is O.Pw O.get p D hD y

/-! ## TestsO -/

section

variable (lo : ℕ)

/-- The numbers that the one numbering over all three chains gives to the five tenants that the
shared chain's laws read: W, the index masks, o_u, o_omega, o_sp. -/
def fiveNums : List ℕ :=
  [(nums A O).w, (nums A O).index, (nums A O).tenant .oU, (nums A O).tenant .oOmega,
    (nums A O).tenant .oSp].map fun q => O.arr q.1 q.2

/-- **The named tests that read open letters** (the first table's numbers, links and places; the
numbering over all three chains). They can be evaluated only when those letters are closed. -/
def testsO : List (String × Bool) :=
  [("hbelow: what is open at the first table's last border is sampled below lo",
      sampledBelow lo O.N₁
      ((openSets O.links (ps A O) (start O.links))[(ps A O).length]?.getD [])),
   ("hxWB: the first of the first chain's sampled members at W's number is there, with W's shape",
      wMemberB O.ms₁ O.N₁.w O.Pw.lin.w),
   ("five: the numbering gives five numbers to W, the index masks, o_u, o_omega and o_sp",
      decide (fiveNums A O).Nodup)]

/-- All of them say yes. -/
def TestsO : Prop := (testsO A O lo).all (·.2) = true

theorem testsO_length : (testsO A O lo).length = 3 := rfl

/-- All say yes: each says yes. -/
theorem TestsO_iff : TestsO A O lo ↔
    sampledBelow lo O.N₁
      ((openSets O.links (ps A O) (start O.links))[(ps A O).length]?.getD []) = true ∧
    wMemberB O.ms₁ O.N₁.w O.Pw.lin.w = true ∧
    decide (fiveNums A O).Nodup = true := by
  simp only [TestsO, testsO, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]

/-- What is open at the first table's last border is sampled below lo. -/
theorem testsO_hbelow (h : TestsO A O lo) :
    sampledBelow lo O.N₁
      ((openSets O.links (ps A O) (start O.links))[(ps A O).length]?.getD []) = true :=
  ((TestsO_iff A O lo).1 h).1

/-- The first of the first chain's sampled members at W's number is there, with W's shape. -/
theorem testsO_hxWB (h : TestsO A O lo) :
    wMemberB O.ms₁ O.N₁.w O.Pw.lin.w = true :=
  ((TestsO_iff A O lo).1 h).2.1

/-- The numbering gives five numbers to W, the index masks, o_u, o_omega and o_sp. -/
theorem testsO_five (h : TestsO A O lo) :
    (fiveNums A O).Nodup :=
  of_decide_eq_true ((TestsO_iff A O lo).1 h).2.2

end


/-! ## What the test on W's member gives: three premises of the ledger's top -/

/-- W's member is what the search finds. -/
theorem xW_found (lo : ℕ) (h : TestsO A O lo) :
    (O.ms₁.find? fun m => decide (m.1.seat m.2 = O.N₁.w)) = some (xW A O) := by
  have h := testsO_hxWB A O lo h
  unfold wMemberB at h
  unfold xW
  cases hf : O.ms₁.find? fun m => decide (m.1.seat m.2 = O.N₁.w) with
  | none =>
    rw [hf] at h
    cases h
  | some x => rfl

/-- The top's hxW. -/
theorem paid_hxW (lo : ℕ) (h : TestsO A O lo) : xW A O ∈ O.ms₁ :=
  List.mem_of_find?_eq_some (xW_found A O lo h)

/-- The top's hsW. -/
theorem paid_hsW (lo : ℕ) (h : TestsO A O lo) : SitsAt (xW A O) O.N₁.w.1 O.N₁.w.2 := by
  have h1 := List.find?_some (xW_found A O lo h)
  have hs : (xW A O).1.seat (xW A O).2 = O.N₁.w := of_decide_eq_true h1
  exact hs

/-- The top's hsh. -/
theorem paid_hsh (lo : ℕ) (h : TestsO A O lo) :
    O.Pw.lin.w = ((xW A O).1.l.get (xW A O).2).1 := by
  have h' := testsO_hxWB A O lo h
  unfold wMemberB at h'
  rw [xW_found A O lo h] at h'
  exact (of_decide_eq_true h').symm

/-- **The promise's "nothing is left" at the constant** is the chain's end's own test. -/
theorem pm_nothingLeft : (pm A O).nothingLeft = fun s : St => (untestedL s.st).all (·.2) := rfl

/-- The counted form's word for the named tests on the parameters. -/
abbrev PlanOk₂ : Prop := Tests A

/-! ## What "five numbers" gives: nine premises of the ledger's top -/

/-- The ten inequalities. -/
theorem five_apart (lo : ℕ) (h : TestsO A O lo) :
    (O.arr (nums A O).w.1 (nums A O).w.2 ≠
        O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 ∧
      O.arr (nums A O).w.1 (nums A O).w.2 ≠
        O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2 ∧
      O.arr (nums A O).index.1 (nums A O).index.2 ≠
        O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 ∧
      O.arr (nums A O).index.1 (nums A O).index.2 ≠
        O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2) ∧
    O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 ≠
        O.arr ((nums A O).tenant .oOmega).1 ((nums A O).tenant .oOmega).2 ∧
      O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 ≠
        O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2 ∧
      O.arr ((nums A O).tenant .oOmega).1 ((nums A O).tenant .oOmega).2 ≠
        O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2 := by
  have H := testsO_five A O lo h
  simp only [fiveNums, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at H
  obtain ⟨⟨_, a2, _, a4⟩, ⟨b2, _, b4⟩, ⟨c3, c4⟩, d4, _⟩ := H
  exact ⟨⟨a2, a4, b2, b4⟩, c3, c4, d4⟩

/-- The top's nWU, nWS, nIU, nIS. -/
theorem paid_nWU (lo : ℕ) (h : TestsO A O lo) :
    O.arr (nums A O).w.1 (nums A O).w.2 ≠
      O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 := (five_apart A O lo h).1.1
theorem paid_nWS (lo : ℕ) (h : TestsO A O lo) :
    O.arr (nums A O).w.1 (nums A O).w.2 ≠
      O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2 := (five_apart A O lo h).1.2.1
theorem paid_nIU (lo : ℕ) (h : TestsO A O lo) :
    O.arr (nums A O).index.1 (nums A O).index.2 ≠
      O.arr ((nums A O).tenant .oU).1 ((nums A O).tenant .oU).2 := (five_apart A O lo h).1.2.2.1
theorem paid_nIS (lo : ℕ) (h : TestsO A O lo) :
    O.arr (nums A O).index.1 (nums A O).index.2 ≠
      O.arr ((nums A O).tenant .oSp).1 ((nums A O).tenant .oSp).2 := (five_apart A O lo h).1.2.2.2

/-- The top's hN: the numbers' tenants are the members' own. -/
theorem paid_hN : (nums A O).tenant = tenantSh (t₁ A) (layU A) (layO A) := rfl

/-- The top's harr: the numbering tells the shared chain's three tenants apart. -/
theorem paid_harr (lo : ℕ) (h : TestsO A O lo) : ∀ m m' : Msg2,
    O.arr (tenantSh (t₁ A) (layU A) (layO A) m).1 (tenantSh (t₁ A) (layU A) (layO A) m).2 =
      O.arr (tenantSh (t₁ A) (layU A) (layO A) m').1 (tenantSh (t₁ A) (layU A) (layO A) m').2 →
    m = m' := by
  obtain ⟨_, c3, c4, d4⟩ := five_apart A O lo h
  intro m m' e
  cases m <;> cases m' <;>
    first
      | rfl
      | exact absurd e c3 | exact absurd e c4 | exact absurd e d4
      | exact absurd e.symm c3 | exact absurd e.symm c4 | exact absurd e.symm d4

/-- The top's hapSA, hapOA (border 9) and hapOB (border 10). -/
theorem paid_hap9 (hT : Tests A) (lo : ℕ) (h : TestsO A O lo) :
    apartAt (nums A O) O.arr true 9 (.msg .oSp) = true ∧
      apartAt (nums A O) O.arr true 9 (.msg .oOmega) = true :=
  Fence.hap_nine (t₁ A) (layU A) (layO A) A.Q.codes (sentU A) (withOmega A.Q.S) (tests_hlU A hT)
    (tests_hlO A hT) (by rw [tests_hsU A hT]; decide) (by rw [tests_hsO A hT]; decide) (nums A O)
    (paid_hN A O) O.arr (paid_harr A O lo h)

theorem paid_hap10 (hT : Tests A) (lo : ℕ) (h : TestsO A O lo) :
    apartAt (nums A O) O.arr true 10 (.msg .oOmega) = true :=
  Fence.hap_ten (t₁ A) (layU A) (layO A) A.Q.codes (sentU A) (withOmega A.Q.S) (tests_hlU A hT)
    (tests_hlO A hT) (by rw [tests_hsU A hT]; decide) (by rw [tests_hsO A hT]; decide) (nums A O)
    (paid_hN A O) O.arr (paid_harr A O lo h)

/-- The top's hNA, hNB. -/
theorem paid_hNk (lo : ℕ) (h : TestsO A O lo) (k : ℕ) :
    ((mineS (nums A O) (ms A) true k).map (VerifiableInference.Desc.Sound.numOf O.arr)).Nodup :=
  Fence.hN_sh A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (t₁ A) (layU A) (layO A) (nums A O) O.arr
    (paid_harr A O lo h) k

/-! ## Tests12 -/

section

variable (πA : P12) (rA : Fmt.M1.Stage → ℕ) (πB : P12) (rB : Fmt.M1.Stage → ℕ)

/-- **The named tests on the two proximity tests' parameters** (K12's, at the chain's pieces 9 and
10). The parameters come with the chain's pieces: they are no letters of the table. -/
def tests12 : List (String × Bool) :=
  [("heA: on G_u: the early form",
      πA.early),
   ("hjA: on G_u: the radii lie in the Johnson range",
      johOk πA rA),
   ("hb1A: on G_u: the batching round's form",
      batOneOk πA),
   ("hPA: on G_u: the own labels",
      ownLabelsB πA),
   ("hpA: on G_u: the sub-protocol's own test on its parameters",
      (proximityTestKind guardedProximityTestParts πA : Block T12 Unit).planOk),
   ("heB: on G_omega: the early form",
      πB.early),
   ("hoB: on G_omega: it has its own mask",
      πB.nums.ownMask),
   ("hPB: on G_omega: the own labels",
      ownLabelsB πB),
   ("hjB: on G_omega: the radii lie in the Johnson range",
      johOk πB rB),
   ("hpB: on G_omega: the sub-protocol's own test on its parameters",
      (proximityTestKind guardedProximityTestParts πB : Block T12 Unit).planOk)]

/-- All of them say yes. -/
def Tests12 : Prop := (tests12 πA rA πB rB).all (·.2) = true

theorem tests12_length : (tests12 πA rA πB rB).length = 10 := rfl

/-- All say yes: each says yes. -/
theorem Tests12_iff : Tests12 πA rA πB rB ↔
    πA.early = true ∧
    johOk πA rA = true ∧
    batOneOk πA = true ∧
    ownLabelsB πA = true ∧
    (proximityTestKind guardedProximityTestParts πA : Block T12 Unit).planOk = true ∧
    πB.early = true ∧
    πB.nums.ownMask = true ∧
    ownLabelsB πB = true ∧
    johOk πB rB = true ∧
    (proximityTestKind guardedProximityTestParts πB : Block T12 Unit).planOk = true := by
  simp only [Tests12, tests12, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]

/-- On G_u: the early form. -/
theorem tests12_heA (h : Tests12 πA rA πB rB) :
    πA.early = true :=
  ((Tests12_iff πA rA πB rB).1 h).1

/-- On G_u: the radii lie in the Johnson range. -/
theorem tests12_hjA (h : Tests12 πA rA πB rB) :
    johOk πA rA = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.1

/-- On G_u: the batching round's form. -/
theorem tests12_hb1A (h : Tests12 πA rA πB rB) :
    batOneOk πA = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.1

/-- On G_u: the own labels. -/
theorem tests12_hPA (h : Tests12 πA rA πB rB) :
    ownLabelsB πA = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.1

/-- On G_u: the sub-protocol's own test on its parameters. -/
theorem tests12_hpA (h : Tests12 πA rA πB rB) :
    (proximityTestKind guardedProximityTestParts πA : Block T12 Unit).planOk = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.1

/-- On G_omega: the early form. -/
theorem tests12_heB (h : Tests12 πA rA πB rB) :
    πB.early = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.2.1

/-- On G_omega: it has its own mask. -/
theorem tests12_hoB (h : Tests12 πA rA πB rB) :
    πB.nums.ownMask = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.2.2.1

/-- On G_omega: the own labels. -/
theorem tests12_hPB (h : Tests12 πA rA πB rB) :
    ownLabelsB πB = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.2.2.2.1

/-- On G_omega: the radii lie in the Johnson range. -/
theorem tests12_hjB (h : Tests12 πA rA πB rB) :
    johOk πB rB = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.2.2.2.2.1

/-- On G_omega: the sub-protocol's own test on its parameters. -/
theorem tests12_hpB (h : Tests12 πA rA πB rB) :
    (proximityTestKind guardedProximityTestParts πB : Block T12 Unit).planOk = true :=
  ((Tests12_iff πA rA πB rB).1 h).2.2.2.2.2.2.2.2.2

end

end Sh

end Desc.K14.Law
