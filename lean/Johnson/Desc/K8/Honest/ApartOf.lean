-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ApartOf.lean: THE SMALLNESS TEST: THE NUMBERS OF ITS ARRAYS (THE DIGITS', THE
PLANES', THE SYMBOLS', THE TWO VECTORS OF READS') ARE APART AT THE RECORD OF EVERY SMALLNESS TEST IN
WHAT Verify.publicOf RETURNS; SO `planesLaid` (Johnson/Desc/K8/Honest/PlanesFew.lean) SAYS YES
THERE. A definition with code, statements and proofs. On the routines that make a plan alone: no
state, no prover. Lemmas; none of the library's goals.

  **`apartB tl`**   with code: ZZ is not BZ; neither vector's array is ZZ or BZ; no matrix's array
      is BZ, ZZ or a vector's
  `planesLaid_of_apart`   it gives `planesLaid`
  `blocks_pos`, `blocks_from`   piecesF's return has a block
  `first_piece`   where `piecesLaid` says yes and there is a block, the first call has a piece in
      array ZZ, virtual row 0
  **`apart_of`**   from the library's two sentences on a plan's record and ledger
      (LinkJoin.TwoStatic, Fo.CoefOK), `piecesLaid` and a block
  **`public_apart`**   at all records of the three kinds of plans in what Verify.publicOf returns
By: LinkJoin.public_G_two, public_A_two, public_H_two
(Johnson/Desc/First/Link/Law/StaticOfMade.lean) · Fo.ZPlan.public_G_zMine, public_A_zMine,
public_H_zMine (OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean) · Fo.coefOK_of_test (FoTailPlanes.lean) ·
`public_tests` (Johnson/Desc/K8/Honest/PublicOfPieces.lean).
Limits. Nothing on the shapes, on the matrices' sizes, on two matrices' arrays, on the ledger's
rows. Nothing on a record that a later routine of a run has turned.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PublicOfPieces
import Johnson.Desc.K8.Honest.PlanesFew
import Johnson.Desc.First.Link.Law.StaticOfMade
import OnBytes.Tie.Pv.Lookup.Ends.FoZPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open Fo (SameP)
open Fo.ZPlan (FromPieces)

/-- The arrays' numbers are apart. -/
def apartB (tl : HTailF2) : Bool :=
  tl.ix.ZZ != tl.ix.BZ &&
    ([0, 2].all fun n => (tl.ix.U.getD n none).getD 0 != tl.ix.ZZ &&
      (tl.ix.U.getD n none).getD 0 != tl.ix.BZ) &&
    (List.range tl.NM).all fun mu =>
      tl.gtTree.getD mu 0 != tl.ix.BZ && tl.gtTree.getD mu 0 != tl.ix.ZZ &&
        (tl.ix.U.getD 0 none).getD 0 != tl.gtTree.getD mu 0 &&
        (tl.ix.U.getD 2 none).getD 0 != tl.gtTree.getD mu 0

/-- What the test says, clause by clause. -/
theorem apartB_iff (tl : HTailF2) : apartB tl = true ↔
    tl.ix.ZZ ≠ tl.ix.BZ ∧
      ((tl.ix.U.getD 0 none).getD 0 ≠ tl.ix.ZZ ∧ (tl.ix.U.getD 0 none).getD 0 ≠ tl.ix.BZ) ∧
      ((tl.ix.U.getD 2 none).getD 0 ≠ tl.ix.ZZ ∧ (tl.ix.U.getD 2 none).getD 0 ≠ tl.ix.BZ) ∧
      ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.BZ ∧ tl.gtTree.getD mu 0 ≠ tl.ix.ZZ ∧
        (tl.ix.U.getD 0 none).getD 0 ≠ tl.gtTree.getD mu 0 ∧
        (tl.ix.U.getD 2 none).getD 0 ≠ tl.gtTree.getD mu 0 := by
  unfold apartB
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_assoc]

theorem planesLaid_of_apart (tl : HTailF2) (h : apartB tl = true) : planesLaid tl = true := by
  obtain ⟨h1, ⟨-, h2⟩, ⟨-, h3⟩, h4⟩ := (apartB_iff tl).1 h
  unfold planesLaid
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨h1, fun mu hmu => (h4 mu hmu).1⟩, h2⟩, h3⟩

/-- piecesF's return has a block. -/
theorem blocks_pos {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) : 0 < tl.zzBlocks := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨hb, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  show 0 < bz.size
  rcases Nat.eq_zero_or_pos bz.size with h0 | h0
  · exact absurd (by simp [Array.isEmpty, h0]) hb
  · exact h0

theorem blocks_from {tl : HTailF2} (h : FromPieces tl) : 0 < tl.zzBlocks := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  unfold HTailF2.zzBlocks
  rw [h2.same.blocks]
  exact blocks_pos h1

/-- The first call's first piece. -/
theorem first_piece (tl : HTailF2) (hL : piecesLaid tl = true) (hb : 0 < tl.zzBlocks) :
    ∃ p ∈ tl.z1.pieces.toList, p.tree = tl.ix.ZZ ∧ p.row = 0 := by
  unfold piecesLaid at hL
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hL
  have hm : (tl.ix.ZZ, 0, 0, tl.mz) ∈ tl.z1.pieces.toList.map pieceKey := by
    rw [hL.1]
    exact List.mem_map.2 ⟨0, List.mem_range.2 hb, rfl⟩
  obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
  unfold pieceKey at e
  simp only [Prod.mk.injEq] at e
  exact ⟨p, hp, e.1, e.2.1⟩

/-- **The arrays' numbers are apart, from the library's two sentences.** -/
theorem apart_of (tl : HTailF2) (F : Fork) (T : LinkJoin.TwoStatic tl F) (C : Fo.CoefOK tl F)
    (hL : piecesLaid tl = true) (hb : 0 < tl.zzBlocks) : apartB tl = true := by
  obtain ⟨p, hp, pt, pr⟩ := first_piece tl hL hb
  have hall : ((0, p) : Nat × OnBytes.Model.Piece) ∈ Fo.allPieces tl :=
    List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  obtain ⟨-, -, -, c4, c5⟩ := C.piece _ hall
  obtain ⟨-, -, -, a1, a2, a3, -⟩ := T.1 { tree := 0 }
  obtain ⟨-, -, -, b1, b2, b3, -⟩ := T.1 { tree := 2 }
  refine (apartB_iff tl).2 ⟨fun e => c4 (by rw [← e]; exact pt.symm), ⟨Ne.symm a1, Ne.symm a2⟩,
    ⟨Ne.symm b1, Ne.symm b2⟩, fun mu hmu => ⟨C.mats mu hmu, fun e => ?_,
      Ne.symm (a3 mu hmu), Ne.symm (b3 mu hmu)⟩⟩
  exact c5 mu hmu ⟨e.trans pt.symm, pr.symm⟩

/-- **At the record of every smallness test in what publicOf returns.** -/
theorem public_apart {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → apartB hp.tl = true) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → apartB a.seam.tl = true) ∧
    apartB X.H.tl = true :=
  ⟨fun g hp hg => apart_of hp.tl hp.Fp (LinkJoin.public_G_two h g hp hg)
      (Fo.coefOK_of_test (Fo.ZPlan.public_G_zMine h g hp hg).t9)
      ((public_tests h).1 g hp hg).1 (blocks_from (Fo.ZPlan.public_G_from h g hp hg)),
    fun g a hg => apart_of a.seam.tl a.seam.Fp (LinkJoin.public_A_two h g a hg)
      (Fo.coefOK_of_test (Fo.ZPlan.public_A_zMine h g a hg).t9)
      ((public_tests h).2.1 g a hg).1 (blocks_from (Fo.ZPlan.public_A_from h g a hg)),
    apart_of X.H.tl X.H.Fp (LinkJoin.public_H_two h)
      (Fo.coefOK_of_test (Fo.ZPlan.public_H_zMine h).t9)
      (public_tests h).2.2.1 (blocks_from (Fo.ZPlan.public_H_from h))⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.apartB_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.planesLaid_of_apart
#print axioms VerifiableInference.Desc.First.K8.Honest.blocks_pos
#print axioms VerifiableInference.Desc.First.K8.Honest.apart_of
#print axioms VerifiableInference.Desc.First.K8.Honest.public_apart
