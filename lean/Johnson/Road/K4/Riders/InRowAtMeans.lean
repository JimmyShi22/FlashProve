-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/InRowAtMeans.lean: THE LINES hIn AND hRow OF `make_of_means`
(Riders/MakeOfMeans.lean): behind an accept of K4's sub-protocol the public items lookIn m 7 and
hasRow m hold of the verifier's state, AT A MEANING WITH `K4Means`: out of `lookIn_made_B`
(Riders/LookInPlanB.lean) and `hasRow_of_plan` (Total/RowOfPlan.lean). Statements and proofs: the
equations, the promise in front, a call each.

  `link_of_shape`: where the book-keeping holds in front of K4's sub-protocol, the open segment's
    own number is m.
  **`hIn_of_means`**: `K4Means` · the table's test pubFit · ONE TEST ON THE PUBLIC PARAMETERS
    (`lookInPlanB` at n, ns) · four equations on letters and the plan (the digits' lookup stands at
    piece 7; nextOf m = some n; nsOf m = some ns; the lookup's place's link is m) ⟹ the line. THE
    FOUR Bools OF THE VERIFIER's STATE IN FRONT (ledger · freeAbove · linkFresh · callerIn) COME OUT
    OF THE PROMISE.
  **`hRow_of_means`**: `K4Means` · ONE TEST ON THE PUBLIC PARAMETERS (`rowB`) · two equations on
    letters (the pending row's layout and count are K4's) · hroom (in front: room for at least one
    entry of the index masks' ledger) ⟹ the line.

Limits. hroom IS A PREMISE: the table's name "pile.room" is to say it; no layer lays that name yet.
The two tests on the public parameters have not run. K04_law, the law of K4's sub-protocol itself,
IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.Riders.LookInPlanB
import Johnson.Road.K4.Total.RowOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Total (rowB roomFor hasRow_of_plan)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning shapeAt pubFit)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- Where the book-keeping holds in front of K4's sub-protocol, the open segment's own number is m.
-/
theorem link_of_shape (H : AtK4 links ps k m pl) {s : S} (hs : shapeAt links (some pl) s = true)
    {Lk : LinkCtx} (hl : s.link? = some Lk) : Lk.link = m := by
  simp only [shapeAt, Bool.and_eq_true] at hs
  have h := hs.2
  rw [hl, H.link] at h
  have e : m = Lk.link := by simpa using h
  exact e.symm

/-- **Behind an accept of K4's sub-protocol the public item lookIn m 7 holds.** -/
theorem hIn_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hfit : pubFit Mg.more links ps = true)
    (hpc : VerifiableInference.Desc.K3.pieceAt X m true = 7) {n ns : ℕ}
    (hn : D.nextOf m = some n) (hns : D.nsOf m = some ns)
    (hB : lookInPlanB par X m n ns = true)
    (hpl : ∀ p, placeAt X m true = some p → p.link = m) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.lookIn m 7) (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y
  have hl : isLay D.links m = true := by
    rw [hlinks]
    unfold isLay
    rw [H.sub]
    rfl
  have f := k4_pub_front D.N Mg Z H hfit ha hu
  have f1 := f (.ledger m) (by simp)
  have f2 := f (.freeAbove m) (by simp)
  have f3 := f (.linkFresh m) (by simp)
  have f4 := f (.callerIn m) (by simp)
  rw [E.ledger] at f1
  rw [E.freeAbove, hns] at f2
  rw [E.linkFresh] at f3
  rw [E.callerIn m _ hl, hn] at f4
  obtain ⟨b1, _, _⟩ := bools_of_onQ D.N Mg Z ha hu
  rw [H.here] at b1
  rw [← hpc, E.lookIn]
  exact lookIn_made_B (kept_of_yes y) hB f1 (by simpa using f2) f3 (by simpa using f4)
    fun p hp Lk hLk => (link_of_shape H b1 hLk).trans (hpl p hp).symm

/-- **Behind an accept of K4's sub-protocol the public item hasRow m holds.** -/
theorem hRow_of_means (E : K4Means Mg D) (hlay : D.d1.lay = par.P.wsLay)
    (hncl : D.d1.ncl m = par.hp.NCL) (hB : rowB par.P par.g par.hp.NCL D.d1.lin = true)
    (hroom : ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      ∃ n, 1 ≤ n ∧ roomFor n a.1 = true) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.hasRow m) (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y
  obtain ⟨n, h1, h2⟩ := hroom a ha hu
  rw [E.hasRow, hlay, hncl]
  exact hasRow_of_plan (kept_of_yes y) hB h1 h2

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.hIn_of_means
#print axioms OnBytes.Road.K4.Riders.hRow_of_means
