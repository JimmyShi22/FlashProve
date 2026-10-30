-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PublicOfPieces.lean: THE SMALLNESS TEST: THREE TESTS ON PUBLIC NUMBERS
(`piecesLaid`, Johnson/Desc/K8/Honest/PiecesLaid.lean; `piecesFit`, GoodOf.lean; `keyFitB`, here)
SAY YES AT EVERY RECORD THAT COMES FROM THE VERIFIER's OWN ROUTINE piecesF
(OnBytes/Model/Tail.lean), SO AT THE RECORD OF EVERY SMALLNESS TEST IN WHAT Verify.publicOf RETURNS.
A definition with code, statements and proofs. On the routines that make a plan alone: no state, no
prover. Lemmas; none of the library's goals.

  `placeZ_key4`, **`laid_of_piecesF`**   placeZ keeps each piece's array, virtual row, first column
      and number of columns, and the order; so piecesF's return passes `piecesLaid`
  `fit_call`, **`fit_of_piecesF`**   and `piecesFit`
  **`keyFitB tl`**   with code: the key side has a level; its last level's order names each bit just
      once; there are two calls at least; each of the two calls' numbers of coordinates fits the
      shape's
  `orderOk_forest`, **`keyFit_of_piecesF`**   the last key level's order is in order where the trees
      are deep enough; piecesF's return passes `keyFitB`
  `laid_same`, `fit_same`, `keyFit_same`   the three read the ten fields of Fo.SameP alone
  **`public_from`**   the three at every record with Fo.ZPlan.FromPieces
  **`public_tests`**   the three at all records of the three kinds of plans in what Verify.publicOf
      returns
By: Fo.PiecesF.piecesF_tail_lay_cut, piecesF_tail_lay_place, piecesF_tail_lay_n
(OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailLay.lean) · Fo.ZPlan.public_G_from, public_A_from,
public_H_from (FoZPlaced1.lean) · piecesF_shapeZ, ShapeZ.ok (FoShapeZ.lean) · zRec_pieces
(FoZRec.lean) · Cb.Fo.ok_parts (OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean) · E3.lastList_perm
(Cb/Pv/Lookup/Order/E3Ord.lean).
Limits. Nothing on a record that a later routine of a run has turned.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PiecesLaid
import Johnson.Desc.K8.Honest.GoodOf
import Johnson.Desc.First.Look.K3Lookup
import Johnson.Desc.First.ProdV.Level
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailLay
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ
import OnBytes.Tie.Pv.Lookup.Ends.FoZRec
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Port.E3OrdPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open Fo (SameP)
open Fo.ZPlan (FromPieces)

/-- placeZ keeps each piece's key, and the order. -/
theorem placeZ_key4 (pieces : Array OnBytes.Model.Piece) (name : String) (k lid : Nat) :
    (placeZ pieces name k lid).pieces.toList.map pieceKey = pieces.toList.map pieceKey := by
  obtain ⟨o, ho, -, -⟩ := Fo.PiecesF.piecesF_tail_lay_place pieces name k lid
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList, ho i,
    Option.map_map]
  rfl

/-- **piecesF's return passes `piecesLaid`.** -/
theorem laid_of_piecesF {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) : piecesLaid tl = true := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  unfold piecesLaid
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · show (placeZ _ _ _ _).pieces.toList.map pieceKey = _
    rw [placeZ_key4, Array.toList_map, Array.toList_range, List.map_map]
    rfl
  · show (placeZ _ _ _ _).pieces.toList.map pieceKey = _
    rw [placeZ_key4, Array.toList_map, Array.toList_range, List.map_map]
    rfl

/-- One call's pieces fit the call. -/
theorem fit_call (pieces : Array OnBytes.Model.Piece) (name : String) (k lid : Nat)
    (hn : (placeZ pieces name k lid).call.n ≤ 63) (p : OnBytes.Model.Piece)
    (hp : p ∈ (placeZ pieces name k lid).pieces.toList) :
    p.b ≤ (placeZ pieces name k lid).call.n ∧ (placeZ pieces name k lid).call.n - p.b ≤ 63 ∧
      p.off / 2 ^ p.b < 2 ^ ((placeZ pieces name k lid).call.n - p.b) ∧
      (placeZ pieces name k lid).call.n - p.b + p.a + clog2 p.CP ≤
        (placeZ pieces name k lid).call.n ∧ p.Cp ≤ 2 ^ clog2 p.CP := by
  obtain ⟨o, ho, hb, -⟩ := Fo.PiecesF.piecesF_tail_lay_place pieces name k lid
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.1 hp
  have e : (placeZ pieces name k lid).pieces[i]? = some p := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hpi]
  rw [ho i] at e
  obtain ⟨p0, h0, rfl⟩ := Option.map_eq_some_iff.1 e
  have hbd := hb i p0 h0
  generalize (placeZ pieces name k lid).call.n = n at hn hbd ⊢
  have hc : clog2 (2 ^ clog2 p0.Cp) = clog2 p0.Cp := Slice.ceilLog2_two_pow _
  show clog2 p0.Rp + clog2 p0.Cp ≤ n ∧ n - (clog2 p0.Rp + clog2 p0.Cp) ≤ 63 ∧
    o i / 2 ^ (clog2 p0.Rp + clog2 p0.Cp) < 2 ^ (n - (clog2 p0.Rp + clog2 p0.Cp)) ∧
    n - (clog2 p0.Rp + clog2 p0.Cp) + clog2 p0.Rp + clog2 (2 ^ clog2 p0.Cp) ≤ n ∧
    p0.Cp ≤ 2 ^ clog2 (2 ^ clog2 p0.Cp)
  have hCp : p0.Cp ≤ 2 ^ clog2 p0.Cp := Ends.le_two_pow_ceilLog2 p0.Cp
  rw [hc]
  generalize clog2 p0.Rp = a at hbd ⊢
  generalize clog2 p0.Cp = w at hbd hCp ⊢
  have h1 : a + w ≤ n :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (le_trans (Nat.le_add_left _ _) hbd)
  have hpos : 0 < 2 ^ (a + w) := Nat.two_pow_pos _
  refine ⟨h1, by omega, ?_, by omega, hCp⟩
  rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, Nat.sub_add_cancel h1]
  omega

theorem pair_mem (tl : HTailF2) (x : Nat × OnBytes.Model.Piece) (h : x ∈ joinPairs tl) :
    x.2 ∈ (tl.zOf x.1).pieces.toList := by
  unfold joinPairs at h
  obtain ⟨q, -, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact hp

theorem zOf_placeZ {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) (q : Nat) :
    ∃ pieces name k lid, tl.zOf q = placeZ pieces name k lid := by
  obtain ⟨bz, f9, pub, -, e1, e2, -⟩ := Fo.PiecesF.piecesF_tail_lay_cut h
  unfold HTailF2.zOf
  split
  · exact ⟨_, _, _, _, e1⟩
  · exact ⟨_, _, _, _, e2⟩

/-- **piecesF's return passes `piecesFit`.** -/
theorem fit_of_piecesF {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) : piecesFit tl = true := by
  have h63 := (Fo.ZPlan.zRec_pieces h).t8
  unfold piecesFit
  rw [List.all_eq_true]
  intro x hx
  have hp := pair_mem tl x hx
  have hn := h63 x.1 (pair_lt tl x hx)
  obtain ⟨pieces, name, k, lid, e⟩ := zOf_placeZ h x.1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [e] at hp hn ⊢
  obtain ⟨c1, c2, c3, c4, c5⟩ := fit_call pieces name k lid hn x.2 hp
  exact ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩

/-- On public numbers: the key side's shape fits what `digitsLive` is read off. -/
def keyFitB (tl : HTailF2) : Bool :=
  decide (0 < tl.f9.v) &&
    ProdV.orderOk (tl.f9.v - 1) (K3.keyOrders tl.f9 (tl.f9.v - 1)) && decide (2 ≤ tl.f9.NC) &&
    [0, 1].all fun q => decide (tl.f9.iota.getD q 0 ≤ tl.f9.rK) &&
      decide (tl.f9.iota.getD q 0 + tl.f9.dT = (tl.zOf q).call.n)

/-- The last key level's order names each bit just once. -/
theorem orderOk_forest (m rK : Nat) (h : rK + 9 ≤ m) :
    ProdV.orderOk m (Forest.orderForestRange m rK) = true := by
  have hp : (Forest.orderForestRange m rK).Perm (List.range m) := by
    rw [← E3.lastList_eq_port]
    exact E3.lastList_perm h
  unfold ProdV.orderOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range]
  refine ⟨⟨by rw [hp.length_eq, List.length_range],
    fun b hb => List.mem_range.1 (hp.mem_iff.1 hb)⟩, fun b hb => ?_⟩
  rw [hp.count_eq]
  exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hb)

/-- **piecesF's return passes `keyFitB`.** -/
theorem keyFit_of_piecesF {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) : keyFitB tl = true := by
  obtain ⟨bz, f9, pub, -, -, -, hs, ef, -, -⟩ := Fo.PiecesF.piecesF_tail_lay_cut h
  obtain ⟨hNC, hn⟩ := Fo.PiecesF.piecesF_tail_lay_n hs ef
  have hok : FoNums.ok tl.f9 = true := (Fo.ZPlan.piecesF_shapeZ h).ok
  obtain ⟨⟨a1, -, -, a4, -, -, -⟩, -, c, -⟩ := Cb.Fo.ok_parts hok
  have hv : tl.f9.v = tl.f9.dT + tl.f9.rK := rfl
  have hq : ∀ q, q < 2 → tl.f9.iota.getD q 0 ≤ tl.f9.rK ∧
      tl.f9.iota.getD q 0 + tl.f9.dT = (tl.zOf q).call.n := by
    intro q hq
    obtain ⟨-, -, c3, c4⟩ := c q (by omega)
    have c3' : (tl.zOf q).call.n = tl.f9.iota.getD q 0 + tl.f9.dT := (hn q hq).symm.trans c3
    refine ⟨?_, c3'.symm⟩
    have hpos := Nat.two_pow_pos (tl.f9.iota.getD q 0)
    have hb1 : tl.f9.first.getD q 0 + (2 ^ tl.f9.iota.getD q 0 - 1) < tl.f9.NT :=
      (c4 (2 ^ tl.f9.iota.getD q 0 - 1) (Nat.sub_lt hpos Nat.one_pos)).1
    have hle : 2 ^ tl.f9.iota.getD q 0 ≤ 2 ^ tl.f9.rK := by omega
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hle
  have ho : ProdV.orderOk (tl.f9.v - 1) (K3.keyOrders tl.f9 (tl.f9.v - 1)) = true := by
    unfold K3.keyOrders
    rw [if_pos (by omega)]
    exact orderOk_forest _ _ (by omega)
  unfold keyFitB
  rw [ho, decide_eq_true (by omega : 0 < tl.f9.v), decide_eq_true (by omega : 2 ≤ tl.f9.NC),
    Bool.and_self, Bool.and_self, Bool.true_and, List.all_eq_true]
  intro q hq'
  have hq2 : q < 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    omega
  obtain ⟨x1, x2⟩ := hq q hq2
  rw [decide_eq_true x1, decide_eq_true x2]
  rfl

theorem laid_same {a b : HTailF2} (k : SameP a b) : piecesLaid b = piecesLaid a := by
  unfold piecesLaid HTailF2.zzBlocks
  rw [k.same.z1, k.same.z2, k.same.ix, k.same.blocks, k.mz]

theorem fit_same {a b : HTailF2} (k : SameP a b) : piecesFit b = piecesFit a := by
  unfold piecesFit joinPairs HTailF2.zOf
  rw [k.same.z1, k.same.z2]

theorem keyFit_same {a b : HTailF2} (k : SameP a b) : keyFitB b = keyFitB a := by
  unfold keyFitB HTailF2.zOf
  rw [k.f9, k.same.z1, k.same.z2]

/-- **The three tests at every record that comes from piecesF.** -/
theorem public_from {tl : HTailF2} (h : FromPieces tl) :
    piecesLaid tl = true ∧ piecesFit tl = true ∧ keyFitB tl = true := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  exact ⟨by rw [laid_same h2]; exact laid_of_piecesF h1,
    by rw [fit_same h2]; exact fit_of_piecesF h1,
    by rw [keyFit_same h2]; exact keyFit_of_piecesF h1⟩

/-- **At the record of every smallness test in what publicOf returns.** -/
theorem public_tests {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp →
      piecesLaid hp.tl = true ∧ piecesFit hp.tl = true ∧ keyFitB hp.tl = true) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
      piecesLaid a.seam.tl = true ∧ piecesFit a.seam.tl = true ∧ keyFitB a.seam.tl = true) ∧
    (piecesLaid X.H.tl = true ∧ piecesFit X.H.tl = true ∧ keyFitB X.H.tl = true) :=
  ⟨fun g hp hg => public_from (Fo.ZPlan.public_G_from h g hp hg),
    fun g a hg => public_from (Fo.ZPlan.public_A_from h g a hg),
    public_from (Fo.ZPlan.public_H_from h)⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.laid_of_piecesF
#print axioms VerifiableInference.Desc.First.K8.Honest.fit_of_piecesF
#print axioms VerifiableInference.Desc.First.K8.Honest.orderOk_forest
#print axioms VerifiableInference.Desc.First.K8.Honest.keyFit_of_piecesF
#print axioms VerifiableInference.Desc.First.K8.Honest.public_from
#print axioms VerifiableInference.Desc.First.K8.Honest.public_tests
