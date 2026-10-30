-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawK3Sites.lean: THE FIFTY PLACES OF THE KIND K3 (the lookups on a link's calls and
on the digits of its smallness test) OF THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean),
EACH WRITTEN WITH WHAT THE LOOKUPS' THREE TESTS ON THE BOOK READ THERE; AND FIVE CLOSED FACTS ON
THESE WRITTEN VALUES: THE LESSER PREMISES OF fits_of_stated (AtFullSide/K14/K3FitsOfStated.lean) AT
THE BOOK's WRITTEN ROWS AND CUTS. By evaluations in Lean's kernel on written data: no maker's term
is evaluated here. Five definitions; statements with their proofs.

Limits.
  * THE LAW's FIRST PREMISE hE (the book's entries at these places are the stated runs) IS NOT
    SHOWN HERE, NOR IN ANY FILE: so nothing here says that one of the three tests accepts.
  * THAT THESE FIFTY ARE THE LOOKUPS' OWN SITES (lookSites, Honest/K3/Lot.lean) AT ANY PUBLIC PART
    IS NO THEOREM. The figures v, d and first were printed by Lean's evaluator off lookSites at what
    ProofFile.pubPlain returns at the library's stored full-size files (VerifierAndGoals.storedPublicFiles) and laid into this
    file by a program; THE EVALUATOR IS TRUSTED FOR NOTHING. What Lean's kernel holds of them:
    k3Cuts_written (v and d against the book's cuts: each stage's number of rounds) and, of owner
    and base, k3Rows_written. OF first NOTHING IS HELD HERE: it is held only by hE.
  * k3Face's three functions are stand-ins: the tests read five numbers of a face alone
    (tests_face_congr). The rounds in front of a place (At.base) are written 0: no test reads them.
  * WP's own limit stands: its values were printed off the same files. The full size alone.
  * Numbers and addresses on public data: nothing on soundness, completeness or hiding.

  k3Face v d      a face with shifted, mu = 5, 32 planes, one part of v levels, a table of d levels
  k3SitesW        **the fifty, in the order of the places**: the place; v and d; the lookup's first
                  scalar in the segment's count; the link's mask row's owner; where that row's
                  entries begin among the owner's coins
  k3Places_nodup  no place stands twice. k3Places_bent
  k3NoRow_written   the first chain's 78 written rows (rawRowsFirstW,
                  AtFullSide/K14/RawBookRowsWritten.lean) have no row at one of the places.
                  k3NoRow_bent
  k3Inside_written   every stated run lies inside its owner's written count. k3Inside_bent
  k3CutsIs, k3Cuts_written, k3CutsAt   at each place the written cut (cutsOf_written,
                  Honest/BookWritten/Cuts.lean) is the stages' numbers of rounds; so cutsAt accepts
                  at every book with the maker's cuts. k3Cuts_bent
  k3RowsIs, k3RowsIs_written, k3Rows_written   owner and base are those of the link's mask row as
                  ownerOf returns it (rawRows_written, AtFullSide/K14/RawFactsWritten.lean).
                  k3Rows_bent

THE LINES NAMED …_bent ARE NEGATIVE TESTS ON PUBLIC WRITTEN NUMBERS: each shows that its evaluation
can come out false; each docstring says what is bent.
OPTIONS ARE RAISED in front of the evaluations: maxRecDepth to 1000000 (no lower number was tried).
What is assumed. Nothing.
-/
import AtFullSide.K14.K3FitsOfStated
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.BookWritten.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- A face with the five numbers that a proof file's lookup of a shape with v key levels and d table
levels has (faceOf, Johnson/Desc/First/Look/K3LookupGeneral.lean). Its three functions are stand-ins. -/
def k3Face (v d : Nat) : LFace :=
  { shifted := true, mu := 5, planes := 32, parts := [v], d := d
    orders := fun _ _ => [], padding := [], leaf := fun _ _ _ => OnBytes.zeroE }

/-- **The fifty places of the kind K3, written.** -/
def k3SitesW : List K3At := [
  ⟨⟨⟨1, some 0, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩⟩,
  ⟨⟨⟨1, some 0, 7, .K3⟩, k3Face 27 11, 0⟩, 2696, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩⟩,
  ⟨⟨⟨1, some 1, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 1, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 1, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 2, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 2, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 2, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 3, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 3, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 4, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 4, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 4, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 5, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 5, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 5, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 6, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 6, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 7, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 7, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 7, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 8, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 8, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 8, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 9, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 9, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 10, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 10, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 10, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 11, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 11, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 11, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 12, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 12, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 13, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 13, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 13, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 14, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 14, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 14, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 15, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 15, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 16, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 16, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 16, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 17, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 17, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 17, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 18, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 18, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 19, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 19, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 19, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 20, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 20, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 20, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 21, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 21, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 22, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 22, 7, .K3⟩, k3Face 27 11, 0⟩, 2695, ⟨⟨1, some 22, 1, .K2⟩, 0⟩, ⟨23436, 439⟩⟩,
  ⟨⟨⟨1, some 23, 2, .K3⟩, k3Face 29 18, 0⟩, 0, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 23, 7, .K3⟩, k3Face 26 11, 0⟩, 2884, ⟨⟨1, some 23, 1, .K2⟩, 0⟩, ⟨11832, 439⟩⟩,
  ⟨⟨⟨1, some 24, 3, .K3⟩, k3Face 31 19, 0⟩, 0, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩⟩,
  ⟨⟨⟨1, some 24, 8, .K3⟩, k3Face 27 11, 0⟩, 2168, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩⟩]

theorem k3SitesW_length : k3SitesW.length = 50 := rfl

/-! ## 1 No place twice -/

set_option maxRecDepth 1000000 in
/-- No place stands twice. -/
theorem k3Places_nodup : (k3SitesW.map (·.at_.place)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: the first member is laid in front once more: its place stands twice. -/
theorem k3Places_bent : ¬ ((k3SitesW.take 1 ++ k3SitesW).map (·.at_.place)).Nodup := by
  decide +kernel

/-! ## 2 No row at a place -/

set_option maxRecDepth 1000000 in
/-- The first chain's written rows have no row at one of the fifty places. -/
theorem k3NoRow_written : noRowAt rawRowsFirstW k3SitesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: a row with one coin is laid in front, at part 0 of the first of the fifty places. -/
theorem k3NoRow_bent :
    noRowAt ((⟨⟨1, some 0, 2, .K3⟩, 0⟩, ⟨0, 1⟩) :: rawRowsFirstW) k3SitesW = false := by
  decide +kernel

/-! ## 3 Inside the owners' counts -/

set_option maxRecDepth 1000000 in
/-- Every stated run lies inside its owner's written count. -/
theorem k3Inside_written : insideAll (dueAt rawRowsFirstW) (k3Stated k3SitesW) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: the table without its first row, link 0's sender's: that owner's count is then 0. -/
theorem k3Inside_bent : insideAll (dueAt (rawRowsFirstW.drop 1)) (k3Stated k3SitesW) = false := by
  decide +kernel

/-! ## 4 The cuts -/

/-- At each member's place the written cut is the stages' numbers of rounds: a test with code. -/
def k3CutsIs (S : List K3At) : Bool :=
  S.all fun s => (cutsFirstW ++ cutsSharedW ++ cutsSecondW).lookup s.at_.place ==
    some ((stages s.at_.face).map (Stage.rounds s.at_.face))

set_option maxRecDepth 1000000 in
/-- The test accepts the fifty. -/
theorem k3Cuts_written : k3CutsIs k3SitesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: at the first place the face has 31 key levels for 30. -/
theorem k3Cuts_bent :
    k3CutsIs (⟨⟨⟨1, some 0, 2, .K3⟩, k3Face 31 19, 0⟩, 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩⟩ ::
      k3SitesW.drop 1) = false := by decide +kernel

/-- **At every book with the maker's cuts at WP the law's premise on the cuts holds.** -/
theorem k3CutsAt {B : ProverCoinCounts} (h : B.cuts = cutsOf WP) : cutsAt B k3SitesW = true := by
  unfold cutsAt
  rw [h, cutsOf_written]
  exact k3Cuts_written

/-! ## 5 Owner and base -/

/-- Each member's owner and base are those of its link's written mask row: a test with code. -/
def k3RowsIs (S : List K3At) : Bool :=
  S.all fun s => rawRowsW.any fun x =>
    s.at_.place.link == some x.1 && x.2.owner == s.o && x.2.base == s.base

set_option maxRecDepth 1000000 in
/-- The test accepts the fifty. -/
theorem k3RowsIs_written : k3RowsIs k3SitesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: at the first place the base's second number is 1 for 0. -/
theorem k3Rows_bent :
    k3RowsIs (⟨⟨⟨1, some 0, 2, .K3⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 1⟩⟩ ::
      k3SitesW.drop 1) = false := by decide +kernel

/-- **Owner and base are the link's mask row's, as the frame's ownerOf returns it at WP and the
written sendings.** -/
theorem k3Rows_written : ∀ s ∈ k3SitesW, ∃ (l : Nat) (r : MsgAt), s.at_.place.link = some l ∧
    ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
      s!"link {l}, moment 0" isMaskRowMsg = some r ∧ r.owner = s.o ∧ r.base = s.base := by
  intro s hs
  obtain ⟨x, hx, h⟩ := List.any_eq_true.1 (List.all_eq_true.1 k3RowsIs_written s hs)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨x.1, x.2, h.1.1, rawRows_written x hx, h.1.2, h.2⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.k3SitesW_length
#print axioms AtFullSide.K14.k3Places_nodup
#print axioms AtFullSide.K14.k3Places_bent
#print axioms AtFullSide.K14.k3NoRow_written
#print axioms AtFullSide.K14.k3NoRow_bent
#print axioms AtFullSide.K14.k3Inside_written
#print axioms AtFullSide.K14.k3Inside_bent
#print axioms AtFullSide.K14.k3Cuts_written
#print axioms AtFullSide.K14.k3Cuts_bent
#print axioms AtFullSide.K14.k3CutsAt
#print axioms AtFullSide.K14.k3RowsIs_written
#print axioms AtFullSide.K14.k3Rows_bent
#print axioms AtFullSide.K14.k3Rows_written
