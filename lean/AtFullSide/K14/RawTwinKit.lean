-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTwinKit.lean: WHAT THE FILES ON THE TWINS OF FOUR OF THE BOOK's TESTS AT THE RAW
BOOK's ENTRIES SHARE: A FUNCTION posW THAT NAMES THE POSITION OF EVERY ONE OF THE 374 PLACES OF
orderOf WP (posW_at_order: by an evaluation in Lean's kernel); THAT ORDER HAS NO PLACE TWICE
(orderW_nodup); rawAheadW CUT IN THREE (rawAhead_three); two small general laws on the twins. A
WORKING FILE. Definitions with code; statements with their proofs.

  posW            a place's position, by arithmetic: chain 1: no link, piece 0: 0; link l, piece q:
                  1 + 14 l + q; no link, piece q from 1 on: 352 + q; chain 2: 358 + q; else 370 + q
  posW_at_order   **orderOf WP has 374 places; each stands at the position that posW names; placedAt
                  posW (orderOf WP) accepts at each** (placedAt: Honest/BookLinear/Positions.lean)
  posW_bent       with posW one off, placedAt does not accept at all places
  orderW_nodup    the frame's orderOf_nodup (Honest/Law/Rule/Tests.lean) at the sealed wp_placesOk
                  (Johnson/AtFull/ProofPlan/At/PlacesOk.lean)
  rawSpentW, rawCarriedShortW   the pieces of rawAheadW in front of rawSegW (the stretches' entries,
                  the folds', the split's) and behind it (four short written lists)
  rawAhead_three  rawAheadW = rawSpentW ++ rawSegW ++ rawCarriedShortW: by the lists' associativity
  clause5P_append   clause5P (Honest/BookLinear/Fifth.lean) at an append is the "and" of clause5P at
                  the two
  clause7S_filter   clause7S (Honest/BookLinear/Seventh.lean) reads the spending entries alone

Where posW comes from: the arithmetic was read off the sealed written cut by two programs of other
authors; here it is held by Lean at every place. It fits this one order.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. No test of the book's and no twin is evaluated here. Nothing on any
property.
-/
import AtFullSide.K14.RawAheadWritten
import Johnson.Desc.ProofFile.Honest.BookLinear.Fifth
import Johnson.Desc.ProofFile.Honest.BookLinear.Seventh
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

/-- A place's position in orderOf WP, by arithmetic. -/
def posW (p : Place) : Nat :=
  if p.chain == 1 then
    match p.link with
    | some l => 1 + 14 * l + p.piece
    | none => if p.piece == 0 then 0 else 352 + p.piece
  else if p.chain == 2 then 358 + p.piece else 370 + p.piece

/-- **posW names the position of every place of orderOf WP.** -/
theorem posW_at_order : (orderOf WP).length = 374 ∧
    (orderOf WP).zipIdx.all (fun x => posW x.1 == x.2) = true ∧
    (orderOf WP).all (placedAt posW (orderOf WP)) = true := by
  decide +kernel

/-- With posW one off, placedAt does not accept at all places. -/
theorem posW_bent : (orderOf WP).all (placedAt (fun p => posW p + 1) (orderOf WP)) = false := by
  decide +kernel

/-- orderOf WP has no place twice. -/
theorem orderW_nodup : (orderOf WP).Nodup := orderOf_nodup P2Law.ProofPlan.wp_placesOk

/-- The pieces of rawAheadW in front of rawSegW: all its spending entries are among them. -/
def rawSpentW : List Ahead :=
  rawWantsW.map (·.entry) ++ foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten]

/-- The pieces of rawAheadW behind rawSegW: four short written lists. -/
def rawCarriedShortW : List Ahead :=
  rawCarriesFoldedW ++ rawCarriesOmegaW ++ rawCarriesWW ++ rawOwnCarryW

/-- rawAheadW, cut in three. -/
theorem rawAhead_three : rawAheadW = rawSpentW ++ rawSegW ++ rawCarriedShortW := by
  unfold rawAheadW rawSpentW rawCarriedShortW
  simp only [List.append_assoc]

/-- The fifth test's twin at an append. -/
theorem clause5P_append (g : Place → Nat) (all : List Place) (l₁ l₂ : List Ahead) :
    clause5P g all (l₁ ++ l₂) = (clause5P g all l₁ && clause5P g all l₂) := List.all_append

/-- The seventh test's twin reads the spending entries alone. -/
theorem clause7S_filter (d : Nat) (l : List Ahead) :
    clause7S d l = clause7S d (l.filter (·.once)) := by
  unfold clause7S
  simp only [List.filter_filter, Bool.and_self]

end AtFullSide.K14

#print axioms AtFullSide.K14.posW_at_order
#print axioms AtFullSide.K14.posW_bent
#print axioms AtFullSide.K14.orderW_nodup
#print axioms AtFullSide.K14.rawAhead_three
#print axioms AtFullSide.K14.clause5P_append
#print axioms AtFullSide.K14.clause7S_filter
