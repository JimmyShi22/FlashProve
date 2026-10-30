-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSmpOwed.lean: A TEST ON THE SHARED CHAIN's RECORD, AND EIGHT STATEMENTS
ON IT THAT ARE OWED FOR K14's LAW, AS PROPOSITIONS BY def: NO PROOF HERE. The two proximity tests of
the shared chain (blocks 9 and 10) want of each member of their groups that its one sample row is a
row that a sending made at a seed. In K12's files a test with code reads the seed back off the
row (H2K.Pin.sampleL, Johnson/Desc/K12/Law/SampleOk.lean). Here that test is laid by borders, in the
form of msgY (Johnson/Desc/K14/Law/LedgerNew.lean), to stand beside it in the chain's promise.

  seatY sh o     a seat with the shape sh and the number o; its other fields are idle
  PlanY cs sh    what K12's read-back law asks of the shape and the codes: a test on the plan
  smpY cs sh o k₀   behind border k₀: the record's message number o passes sampleL at seatY sh o
  SmpSeatOwed    sampleL reads of a seat its shape and its number alone
  SmpOfPartOwed  smpY stands where (shape, sampled, sampleRows) at the number stand
  SmpHandsOwed   HandsOn for a test with smpY beside it, where the sending's decision earns it
  SmpHandsAtOwed the like in the form HandsAt, where the sending's piece earns it
  SmpOnGuOwed, SmpOnGomegaOwed   the two proximity tests hand it on
  SmpEarnOwed    a yes of the sending's DECISION earns it (at rounds of whatever form)
  SmpEarnAtOwed  a yes of the sending's PIECE earns it
What is not claimed. That they hold: SmpEarnOwed above all: a bare decision is handed rounds of
whatever form.
(Seven of the eight are proved: smpSeat, smpOfPart, smpHands, smpHandsAt, smpOnGu, smpOnGomega in
Johnson/Desc/K14/Law/LedgerSmp.lean; smpEarnAt in Johnson/Desc/K14/Law/LedgerSmpEarn.lean. No
theorem of this tree has the type SmpEarnOwed.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerNew
import Johnson.Desc.K12.Law.SampleOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)

/-- A seat with the shape sh and the number o. The other fields are idle: SmpSeatOwed. -/
def seatY (sh : OracleShape) (o : ℕ) : H2K.First.Seat1 :=
  { id := o, sh := sh, t := 0, part := 0, tsh := default, num := 0 }

/-- **"The message number o passes K12's test on a member's sample"**, behind border k₀. -/
def smpY (cs : Codes) (sh : OracleShape) (o k₀ : ℕ) : ℕ → St → Bool := fun k s =>
  decide (k ≤ k₀) || match s.st.oracles[o]? with
    | some x => H2K.Pin.ok (H2K.Pin.sampleL cs (seatY sh o) x)
    | none => false

/-- What K12's read-back law (sampleL_of_seed, Johnson/Desc/K12/Law/SampleOfSeed.lean) asks of the
shape and the codes: one answer; rows of one kind alone, and some; the case; lengths that are powers
of two. A test on the plan. -/
def PlanY (cs : Codes) (sh : OracleShape) : Prop :=
  sh.answers = 1 ∧ ¬ (0 < sh.mainRows ∧ 0 < sh.maskRows) ∧ (0 < sh.mainRows ∨ 0 < sh.maskRows) ∧
    ((0 < sh.maskRows ∨ sh.mainDeg = 3) ∨ (sh.maskRows = 0 ∧ sh.mainDeg = 1)) ∧
    (sh.mainRows = 0 ∨ 2 ^ ceilLog2 (H2K.Pin.mainB cs sh).ell = (H2K.Pin.mainB cs sh).ell) ∧
    (sh.maskRows = 0 ∨ 2 ^ ceilLog2 (H2K.Pin.maskB cs sh).ell = (H2K.Pin.maskB cs sh).ell)

/-- OWED: the test reads of a seat its shape and its number alone. -/
def SmpSeatOwed : Prop :=
  ∀ (cs : Codes) (m m' : H2K.First.Seat1) (x : OnBytes.Oracle), m'.sh = m.sh → m'.id = m.id →
    H2K.Pin.sampleL cs m' x = H2K.Pin.sampleL cs m x

/-- OWED: what a reader of a sample reads of a message stands: so does smpY. -/
def SmpOfPartOwed : Prop :=
  ∀ (cs : Codes) (sh : OracleShape) (o k₀ j k : ℕ), k₀ < j → ∀ d d' : St,
    (d'.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (d.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) →
    smpY cs sh o k₀ j d = true → smpY cs sh o k₀ k d' = true

/-- OWED: earned at the sending that writes the message (a premise, in the decision's form), it is
handed on by every later block of the kind. The binders are hands_msgY's. -/
def SmpHandsOwed : Prop :=
  ∀ (cs : Codes) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit),
    blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] → ∀ X : ℕ → St → Bool,
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] X → ∀ (i₀ : ℕ) (n : String)
    (K : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St),
    (∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots) →
    [b1, b2, b3, b4, b5, b6, b7, b8][i₀]? = some (sendAt Q n K inFront groups behind) →
    ∀ base : ℕ, (∀ d, X (i₀ + 1) d = true → d.st.oracles.size = base) →
    ∀ k : Fin (shapesOf K).length, sampledAt K k → i₀ + 1 ≤ 6 →
    (∀ d d' rs gs, (sendAt Q n K inFront groups behind).decide d rs gs = .ok d' →
      X (i₀ + 1) d = true → smpY cs (shapeAt K k) (base + k.val) (i₀ + 1) (i₀ + 2) d' = true) →
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8]
      fun j s => X j s && smpY cs (shapeAt K k) (base + k.val) (i₀ + 1) j s

/-- OWED: the like at the pieces, inside the promise. -/
def SmpHandsAtOwed : Prop :=
  ∀ (P₁ Cl Cells Tok : Type) (Fr : Frame) (cs : Codes) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    ∀ (on : ℕ → (P₁ × St) × Fr.E.Str → Prop) (X : ℕ → St → Bool),
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8] X →
    ∀ (sh : OracleShape) (o i₀ : ℕ) (b : Block St Unit),
    [b1, b2, b3, b4, b5, b6, b7, b8][i₀]? = some b →
    1 ≤ i₀ → i₀ + 1 ≤ 6 → (∀ k a, on k a → smpY cs sh o (i₀ + 1) k a.1.2 = true) →
    (∀ c : Block St Cl, DecidesAs c b → c.rounds = b.rounds →
      ∀ x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT), x.b = heldW c → ∀ a τ y,
        on (i₀ + 1) a → x.ior.red.out a τ = some y →
        smpY cs sh o (i₀ + 1) (i₀ + 2) y.1.2 = true) →
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      fun j s => X j s && smpY cs sh o (i₀ + 1) j s

/-- OWED: the test on G_u hands smpY on, where the first mask is not that message. -/
def SmpOnGuOwed : Prop :=
  ∀ (cs : Codes) (sh : OracleShape) (o k₀ : ℕ), k₀ < 9 → ∀ p : P12, p.early = true →
    p.answers = 1 → ∀ (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d' →
    d.loc.firstMask ≠ some o → smpY cs sh o k₀ 9 d = true → smpY cs sh o k₀ 10 d' = true

/-- OWED: the test on G_omega hands smpY on. -/
def SmpOnGomegaOwed : Prop :=
  ∀ (cs : Codes) (sh : OracleShape) (o k₀ : ℕ), k₀ < 10 → ∀ p : P12, p.early = true →
    p.answers = 1 → ∀ (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d' →
    smpY cs sh o k₀ 10 d = true → smpY cs sh o k₀ 11 d' = true

/-- OWED, AND THE LEAST SURE (a refutation serves): a yes of the sending's decision, at rounds of
whatever form, earns it: under the plan's tests on the sending and PlanY at the message. -/
def SmpEarnOwed : Prop :=
  ∀ (Q : P14) (n : String) (K : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : St → Array Nat → Option St),
    (∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots) →
    (sendAt Q n K inFront groups behind).planOk = true →
    ∀ rad : ℕ → ℕ, VerifiableInference.Desc.K1.condPort K rad = true →
    ∀ k : Fin (shapesOf K).length, sampledAt K k → PlanY K.codes (shapeAt K k) →
    ∀ (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (sendAt Q n K inFront groups behind).decide d rs gs = .ok d' → ∀ k₀ j : ℕ,
    smpY K.codes (shapeAt K k) (d.st.oracles.size + k.val) k₀ j d' = true

/-- OWED: the like of a yes of the sending's piece: its rounds have the declared form. -/
def SmpEarnAtOwed : Prop :=
  ∀ (P₁ Cl Cells Tok : Type) (Fr : Frame) (Q : P14) (n : String)
    (K : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St),
    (∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots) →
    (sendAt Q n K inFront groups behind).planOk = true →
    ∀ rad : ℕ → ℕ, VerifiableInference.Desc.K1.condPort K rad = true →
    ∀ k : Fin (shapesOf K).length, sampledAt K k → PlanY K.codes (shapeAt K k) →
    ∀ c : Block St Cl, DecidesAs c (sendAt Q n K inFront groups behind) →
    c.rounds = (sendAt Q n K inFront groups behind).rounds →
    ∀ x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT), x.b = heldW c → ∀ a τ y,
    x.ior.red.out a τ = some y → ∀ k₀ j : ℕ,
    smpY K.codes (shapeAt K k) (a.1.2.st.oracles.size + k.val) k₀ j y.1.2 = true

end Desc.K14.Law
