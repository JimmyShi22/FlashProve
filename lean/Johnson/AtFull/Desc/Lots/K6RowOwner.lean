-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K6RowOwner.lean: THE ROW OF K6's LOT FROM SIX PREMISES, AND THE LAST FIELD
FACT BENEATH IT: in the goals' scope the table arrayOf of the head's built segment books link 22 as
the owner of that segment's one foreign array. A joining: calls alone; nothing is evaluated.
WHAT IT DOES NOT SHOW, FIRST. THAT ANY FILES MEET THE SIX: NOT PROVED IN THIS FILE; WHETHER A
THEOREM ELSEWHERE SHOWS IT WAS NOT EXAMINED FOR THIS FILE. At the full-size example: the scope and
the reader's return are theorems of the library; the plain public part's return and the blank
letters' return are not proved in this file (Lean's evaluator returned them; whether a theorem
elsewhere shows them was not examined for this file). **hc AND he (the table of steps and the
entries ARE the written ones) ARE ALL THAT IS "AT THE RELEASE'S FILES" HERE; THIS FILE SHOWS
NEITHER.** hc speaks of the constant Johnson.AtFull.Cut.cutWritten
(Johnson/AtFull/Cut/CutWrittenLit.lean). Both are said to follow from laws in other files, which
were not read for this file, under the plain public part's return and one further condition that is
itself not shown: laws that conclude just this constant, and the entries. NO EXAMPLE OF THE HEAD IS
SHOWN IN THIS FILE; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth. At the second hash function
OnBytes.secondHashFunction alone. The letter lay is tied to P's own field lay by nothing. Nothing on soundness.
THE GROUND. k6_row_written, on which all stands, lies over the files that K6RowScope.lean's head
names.
Main names (namespace Johnson.AtFull.Lots).
  stream_tree: in the goals' scope, at what the library's publicOf returns: entry 0 of the map's
      list FT in the head's plan is the array of the head's eighth matrix (the stream), and that
      matrix's label names link 22 as the owner.
  head_owner: the premise hO of k6_row_scope (K6RowScope.lean).
  k6_row_scope6: THE END: THE ROW FROM SIX PREMISES: the goals' scope · the goals' reader's return ·
      the plain public part's return · the blank letters' return · the written table of steps · the
      written entries.
  esWritten_is: a tie: the written entries here are the first part of P5T.esFull
      (Johnson/P5T/PlanSeatsFull.lean): by rfl.

THE MATHEMATICS IS THAT OF names_tie_head_stream
(Johnson/Desc/AtSeats/NamesTieHeadStream.lean): the built segment 24 lists (22, "M7") at the eighth
matrix's array. **stream_tree RETYPES STEPS OF A PROOF IN THAT FILE** (names_at_head_stream, its
lines 109 to 136): the two facts stand there as steps and in no lemma; they are had here by the same
calls (planH2_names · shapeF_names' third arm · matsH_stream · Meaning.owner_label · ix_of_core).
Beside it:
Meaning.K2.built_arr (Johnson/IMR/ArraysOpen.lean; THAT FILE HOLDS LAWS AT AN OPENING FURTHER DOWN:
NONE IS
CALLED), ground_publicK, ground_tails; ProofFile.Law.blankBy_W.

-/
import Johnson.AtFull.Desc.Lots.K6RowScope
import Johnson.Desc.AtSeats.NamesTieHeadStream
import Johnson.IMR.ArraysOpen
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Lots

open OnBytes OnBytes.Model
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.K4Sent (esWritten)
open VerifiableInference.Desc.K1.HeadNames (planH2_names matsH_stream names_tie_head_stream)
open OnBytes.Road.K4.Names (shapeF_names)
open _root_.Meaning (labAt ownerK ownerA nameOf matsAt ownerOf)
open ProofFile.Sk (lotSk)

/-- **The stream's array and its owner, off the head's plan.** -/
theorem stream_tree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (h : Verify.publicOf P.pol P.KL lay = .ok X) :
    X.H.tl.ix.FT[0]? = some (X.H.tl.gtTree.getD 7 0) ∧ ownerK (labAt X 24 7) = 22 := by
  have C := OnBytes.Road.Hd.core_of_scope hS hR h
  have Bc := (OnBytes.Road.Hd.eleven_of_core h C (OnBytes.Road.Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head).NHf
  obtain ⟨_, i7, _⟩ := _root_.Meaning.ix_of_core h C
  obtain ⟨H0, h0, eH⟩ := Fo.Pub.public_H h
  have etl : X.H.tl = H0.tl := by rw [eH]
  obtain ⟨sid, f, tl0, hsh, same⟩ := planH2_names h0
  have hμm : 7 < (matsAt X 24).size := by
    rw [_root_.Meaning.size_head h C]
    omega
  have ol := _root_.Meaning.owner_label h C (by omega : 24 < 25) hμm
  have oo : ownerOf X 24 7 = (22, 7) := by
    unfold _root_.Meaning.ownerOf
    rw [if_pos rfl, hN, if_pos rfl, i7]
  rw [oo] at ol
  obtain ⟨-, -, S3⟩ := shapeF_names hsh (μ := 7)
    (by rw [VerifiableInference.Desc.K1.HeadNames.matsH_size _ _ _ _ _ hN]; omega)
  rw [← same.ix, ← same.gtTree] at S3
  obtain ⟨k1, kf⟩ := matsH_stream X.hS X.HLy (Verify.borderOf X.layers.y) (1 + X.layers.y.NGr) sid
    hN
  obtain ⟨f1, _⟩ := S3 k1 0 kf
  exact ⟨by rw [etl]; exact f1, congrArg Prod.fst ol⟩

/-- **The head's built segment books link 22 as the owner of its one foreign array.** -/
theorem head_owner {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    ∀ X t, G.built[24]? = some X → X.tl.ix.FT.toList = [t] →
      ∃ nm, X.arrayOf[t]? = some (22, nm) := by
  intro X t hX hFT
  have hW := IM.ground_publicK hZ hG
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  obtain ⟨f1, eK⟩ := stream_tree hS hR hW
  obtain ⟨-, X', hX', eT, -⟩ := IM.ground_tails hS hR hZ hG
  obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
  have e0 : X.tl.ix.FT[0]? = some t := by
    rw [← Array.getElem?_toList, hFT]
    rfl
  have et : t = G.W.H.tl.gtTree.getD 7 0 := by
    rw [eT, f1] at e0
    exact (Option.some.inj e0).symm
  have tie := names_tie_head_stream hS hR hZ
  rw [← eW, eK] at tie
  refine ⟨nameOf (ownerA (labAt G.W 24 7)), ?_⟩
  rw [_root_.Meaning.K2.built_arr hG hX, et]
  exact tie

/-- **THE ROW FROM SIX PREMISES.** -/
theorem k6_row_scope6 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) : lotSk G (P4.k6Lot Z) = k6LotW :=
  k6_row_scope hS hR hZ hG hc he (head_owner hS hR hZ hG)

/-- A tie: the written entries are the first part of P5T.esFull. -/
theorem esWritten_is : esWritten = P5T.esFull.1 := rfl

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.stream_tree
#print axioms Johnson.AtFull.Lots.head_owner
#print axioms Johnson.AtFull.Lots.k6_row_scope6
#print axioms Johnson.AtFull.Lots.esWritten_is
