-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Honest/Law/K7Rows.lean: CONDITIONAL: THE YES OF THE FIRST CHAIN's MEMBER NUMBER
338 (kind K7: the entry into the head's segment and the next token's block, as one block) LEAVES THE
ROWS ON THE TABLE (S.rows, Johnson/Desc/First/State.lean) AS THEY WERE. Three statements with their
proofs. Over the library alone. On the verifier's own data: no prover is in this file.

  front_rows    where the entry into the head's segment says yes: s0.rows = s.rows
  place_rows    where the entry and the next token's block, as one block, say yes: t.rows = s.rows
  k7_rows_at    CONDITIONAL: **∀ blk, cF.blocksInOrder[338]? = some blk → ∀ s s', StepYes 0 blk s s' →
                s'.rows = s.rows**

What for. A relation of other authors between the states in front of and behind a member asks, at
this kind, that the rows on the table stay. The last statement has the form in which such a clause
is paid from a member's yes (StepYes, Johnson/Top/H0/Walk/Reach.lean).

WHY IT HOLDS. S.rows reads two things of a state: where it stands, and the pile. It parts from the
pile at one stand alone: in a member's part whose batching has been done. The entry refuses unless
the state stands between two segments, and what it returns stands in the head's segment (headFrontQ,
Johnson/Top/H0/Tw/K2C/Head.lean; HeadFrontAsks, headFrontQ_iff, K2C/Asks.lean): neither is a
member's part. It leaves the record that holds the pile whole (headFrontQ_rest,
K2C/FrontGroup.lean). The next token's block leaves the stand and the pile (reply_rest,
Johnson/Desc/Kinds/Law/ReplyRest.lean).

The premise of k7_rows_at: h: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): under it the
member number 338 is, for its yes, that one block (P4.k7_left_seat, Johnson/P4R/ReplyTiedN.lean).
front_rows has no premise but the yes; place_rows has one more, on its letter front: that the
front's yes is the entry's.

Limits. Conditional: h is a hypothesis (it has a member at the library's written copy of the
full-size public files, AtFullSide.Top.headMember_zFull, which no theorem ties to the package's
files). The member is named by its number in the chain's list, not by its place. Of the other things
that such a relation may ask at this kind (the statement, the book) nothing is said here. That the
member says yes at any state is not said. Through its imports the file stands above the library's
folder ThirdParty/. At the library's full size and the format's second hash function alone. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Kinds.Law.K7Rides
import Johnson.Desc.Kinds.Law.ReplyRest
import Johnson.Desc.First.Close.Law.HandsOfK10
import Johnson.Top.H0.Tw.K2C.FrontGroup
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Walk.Reach
import Johnson.P4R.ReplyTiedN
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K7
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_iff headFrontQ_rest)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (StepYes)
open P5J (AtMgA TS)

/-- The entry into the head's segment leaves the rows on the table. -/
theorem front_rows {tl : HTailF2} {s s0 : S} (h : headFrontQ tl s = .ok s0) : s0.rows = s.rows := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s0).1 h
  have ho : s0.out = s.out := (headFrontQ_rest h).2.2.2.2.2.1
  have hh0 : s0.here = .head { a with fr := x.f } := by rw [k.out]
  have hb := k.between
  unfold S.atBetween at hb
  unfold S.rows
  rw [hh0, ho]
  cases hs : s.here <;> first | rfl | (rw [hs] at hb; cases hb)

/-- **The entry and the next token's block, as one block, leave the rows on the table.** hfront: the
front's yes is the entry's. -/
theorem place_rows (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      t.rows = s.rows := by
  intro s rs gs t h
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind fun s1 =>
      (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings))
      = .ok t := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e =>
    rw [hp] at h'
    cases h'
  | ok s1 =>
    rw [hp] at h'
    obtain ⟨_, _, _, _, _, _, a7, _, _, a10⟩ := reply_rest l W.hS.V h'
    have e : t.rows = s1.rows := by
      unfold S.rows
      rw [a7, a10]
    exact e.trans (front_rows (hfront _ _ _ _ hp))

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE YES OF THE MEMBER NUMBER 338 LEAVES THE ROWS ON THE TABLE.** CONDITIONAL: under the
hypothesis h. -/
theorem k7_rows_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk, cF.blocksInOrder[338]? = some blk → ∀ s s', StepYes 0 blk s s' → s'.rows = s.rows := by
  intro blk hblk s s' hy0
  obtain ⟨R, c, -, hs⟩ := hy0
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, -, -, hyes, hfront⟩ := P4.k7_left_seat h.scope h.reads O
  have f1 : cF.blocksInOrder[338]? = some b := by
    have q' := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope h.scope h.reads O (by decide) 0] at q'
  obtain rfl : b = blk := Option.some.inj (f1.symm.trans hblk)
  obtain ⟨rs0, gs0, hd0⟩ := VerifiableInference.Desc.First.Close.step_decide b 0 s s' R c _ hs
  obtain ⟨rs, gs, hy⟩ := hyes _ _ _ _ hd0
  exact place_rows Bs.G₀.W 24 "H:1" (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hfront _ _ _ _ hy

end H2K7

#print axioms H2K7.front_rows
#print axioms H2K7.place_rows
#print axioms H2K7.k7_rows_at
