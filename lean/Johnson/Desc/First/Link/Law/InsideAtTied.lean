-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/InsideAtTied.lean: `InsideAt` AT A STATE WITH THE PROMISE AND "REACHED":
`insideAt_reached` (PartFitsReached.lean) WITH ITS TWO FACTS ON THE LEDGER PAID by the invariant
`SlotsInv` (SlotsWalk.lean; along "reached": Johnson/LPFK9R/SlotsSeat.lean) and by the promise's
Bool `shapeAt` ("the open link's number is the place's"). A joining: two theorems.

What is said.
  `link_of_shape`: shapeAt's yes at a place of link m: the open link's number is m.
  `insideAt_tied`: **FoldFacts · reached · no mark · the place (piece ≤ 11 + 2 · shift) · the open
    segment's part pa · the promise's bookAt and shapeAt · SlotsInv nsOf at the state · nsOf m =
    (ns, ns) · PlanFits … ns ⊢ InsideAt d.sent.codes ms own pa.** No premise on the state is left
    that is not a field of FoldFacts, a Bool of the promise, or the invariant.

Limits. FoldFacts, SlotsInv at "reached", PlanFits at the release's values: premises. No soundness
statement.

-/
import Johnson.Desc.First.Link.Law.PartFitsReached
import Johnson.Desc.First.Link.Law.SlotsWalk
import Johnson.Desc.First.Batch.Law.RowsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers FoldData FoldFacts momentAt shiftAt bookAt
  shapeAt)

/-- The promise's Bool on where the chain stands: the open link's number is the place's. -/
theorem link_of_shape {links : List ModelPart} {p : Place} {s : S} {L : LinkCtx} {m : ℕ}
    (h : shapeAt links (some p) s = true) (hl : p.link = some m) (hL : s.link? = some L) :
    L.link = m := by
  unfold shapeAt at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  rw [hL, Option.all_some, hl] at h2
  exact (Option.some.inj (eq_of_beq h2)).symm

/-- **`InsideAt` AT A STATE WITH THE PROMISE AND "REACHED".** -/
theorem insideAt_tied {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (N : Numbers) (ms : List Mem) (own : List (ℕ × ℕ))
    (nsOf : ℕ → ℕ × ℕ) {k : ℕ} {a : X} {p : Place} {m ns : ℕ} {pa : K9.Part} (hR : Rch k a)
    (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links m) (hpa : atS.get? (at_ a).2 = some pa)
    (hB : bookAt N ps[k]? (at_ a).2 = true) (hSh : shapeAt links ps[k]? (at_ a).2 = true)
    (hSl : SlotsInv nsOf (at_ a).2) (hn : nsOf m = (ns, ns))
    (T : PlanFits d ms own m (momentAt (shiftAt links m) p.piece) (N.msgsAt ps[k]?) ns) :
    InsideAt d.sent.codes ms own pa := by
  have hL := (part_reads _ pa hpa).1
  have hF := fork_part _ pa hpa
  rw [hp] at hSh
  have hm := link_of_shape hSh hl hL
  have h1 := hSl pa.F pa.L hF hL
  rw [hm, hn] at h1
  obtain ⟨e1, e2⟩ := (slotsAre_iff ns pa.F).1 h1
  exact insideAt_reached FF N ms own hR hu hp hl hpc hpa hB T e1 (Nat.le_of_eq e2)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_of_shape
#print axioms VerifiableInference.Desc.LinkJoin.insideAt_tied
