-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeDigitsPlan.lean: the public test `BzAt.why` (Johnson/HonestTrace/BZVals.lean) on the
data of the array "BZ" of a segment: what its clauses read of the smallness test's lookup holds at whatever the verifier's
maker `HTailF2.piecesF` returns at 128 combinations and at least one column.

  `shape_cK`        the shape's field cK is the logarithm of its number of calls
  `PiecesFit f`     the lookup's numbers that `BzAt.why` compares: two calls, tables of 2^10 and 2^8 rows, padding row 0, the
                    identity tables, fewer than 32 places, and the library's test `FoNums.ok`
  `pieces_fit`      so it is at what `piecesF` returns
  `fit_of_from`     and at a record that agrees with such a return on the fields that the tests read
  `why_none`        `BzAt.why` says nothing against a segment's data, from these and six public equations

Limits. From a return of the maker alone. At 128 combinations alone. On public numbers: no state, no prover.
-/
import Johnson.Desc.K8.Honest.HeldAtPieces
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ
import OnBytes.Tie.Pv.Lookup.Ends.FoZTests0
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailLay
import Johnson.HonestTrace.BZVals

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.HonestTrace (BzAt)
open VerifiableInference.Desc.First.K8.Honest (allRows pieces_cut blocks_128 placed_facts lowPiece highPiece range_one_map
  shape_two)
open ProofFile.Honest.K8 (parOfTail)

/-- The shape's field cK is the logarithm of its number of calls. -/
theorem shape_cK {calls : Array Call} {lid : Nat} {fo : Forest.Shape} (h : Forest.shape calls lid = .ok fo) :
    fo.cK = clog2 calls.size := by
  unfold Forest.shape at h
  obtain ⟨u, hfor, h⟩ := OnBytes.Ends.ok_of_bind h
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨r, -, h⟩ := OnBytes.Ends.ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := OnBytes.Ends.ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

/-- **The lookup's numbers that the test on public data compares.** -/
structure PiecesFit (f : Forest.Shape) : Prop where
  ok : FoNums.ok f = true
  two : f.calls.size = 2
  cK : f.cK = 1
  k0 : FoNums.kOf f 0 = 10
  k1 : FoNums.kOf f 1 = 8
  kT : f.kT = 10
  t0 : FoNums.t0Of f 0 = 0
  t1 : FoNums.t0Of f 1 = 0
  tab : ((List.range 2).all fun c =>
    (List.range (2 ^ FoNums.kOf f c)).all fun t => FoNums.tauN f c t == t) = true
  n32 : ((List.range 2).all fun c => decide (FoNums.nOf f c < 32)) = true

set_option maxRecDepth 100000 in
/-- The first numbers are their own words. -/
theorem small_ids : ((List.range (2 ^ 10)).all fun t => t.toUInt64.toNat == t) = true := by decide +kernel

/-- **At what `piecesF` returns, at 128 combinations and a column.** -/
theorem pieces_fit {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) (ht : tl0.tau = 128) (hm : 0 < tl0.mz) :
    PiecesFit tl.f9 := by
  obtain ⟨bz, f9, pub, hb, eB, eL, e1, e2, hs, e9⟩ := pieces_cut h
  rw [ht, blocks_128] at hb
  obtain rfl : #[(0, 128)] = bz := Except.ok.inj hb
  have e1' : tl.z1 = placeZ #[lowPiece tl0] "R10z" t2D0 tl0.lidb := by
    rw [e1]
    show placeZ ((Array.range 1).map _) _ _ _ = _
    rw [range_one_map]
    rfl
  have e2' : tl.z2 = placeZ #[highPiece tl0] "R8d" t2D1 tl0.lidb := by
    rw [e2]
    show placeZ ((Array.range 1).map _) _ _ _ = _
    rw [range_one_map]
    rfl
  obtain ⟨a1, -, -, -⟩ := placed_facts (lowPiece tl0) "R10z" t2D0 tl0.lidb rfl rfl hm
  obtain ⟨b1, -, -, -⟩ := placed_facts (highPiece tl0) "R8d" t2D1 tl0.lidb rfl rfl hm
  rw [← e1'] at a1
  rw [← e2'] at b1
  have hn : tl.z2.call.n = tl.z1.call.n := b1.trans a1.symm
  obtain ⟨d, k, -, r, -, -, v⟩ := shape_two hs hn
  have k1 : tl.z1.call.k = 10 := by
    rw [e1']
    rfl
  have k2 : tl.z2.call.k = 8 := by
    rw [e2']
    exact t2D1_eq
  have u1 : tl.z1.call.t0 = 0 := by
    rw [e1']
    rfl
  have u2 : tl.z2.call.t0 = 0 := by
    rw [e2']
    rfl
  have w1 : tl.z1.call.tau = none := by
    rw [e1']
    rfl
  have w2 : tl.z2.call.tau = none := by
    rw [e2']
    rfl
  have c1 : tl.f9.calls = #[tl.z1.call, tl.z2.call] := by
    rw [e9]
    exact (Cb.Fo.shape_more hs).1
  have kT : tl.f9.kT = 10 := by
    rw [e9]
    show f9.kT = 10
    rw [k, k1, k2]
    rfl
  have cK : tl.f9.cK = 1 := by
    rw [e9]
    show f9.cK = 1
    rw [shape_cK hs]
    rfl
  have q0 : FoNums.kOf tl.f9 0 = 10 := by
    show ((tl.f9.calls[0]?).map (·.k)).getD 0 = 10
    rw [c1]
    exact k1
  have q1 : FoNums.kOf tl.f9 1 = 8 := by
    show ((tl.f9.calls[1]?).map (·.k)).getD 0 = 8
    rw [c1]
    exact k2
  have hlow : tl.z1.call.n + 1 < 32 := by omega
  refine ⟨(Fo.ZPlan.piecesF_shapeZ h).ok, ?_, cK, q0, q1, kT, ?_, ?_, ?_, ?_⟩
  · rw [c1]
    rfl
  · show ((tl.f9.calls[0]?).map (·.t0)).getD 0 = 0
    rw [c1]
    exact u1
  · show ((tl.f9.calls[1]?).map (·.t0)).getD 0 = 0
    rw [c1]
    exact u2
  · have all2 : ∀ c, c < 2 → ∀ t, t < 2 ^ 10 → FoNums.tauN tl.f9 c t = t := by
      intro c hc t ht'
      have eid : t.toUInt64.toNat = t := eq_of_beq (List.all_eq_true.1 small_ids t (List.mem_range.2 ht'))
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · show ((tl.f9.calls.getD 0 {}).tauAt t).toNat = t
        rw [c1]
        show (tl.z1.call.tauAt t).toNat = t
        unfold Call.tauAt
        rw [w1]
        exact eid
      · show ((tl.f9.calls.getD 1 {}).tauAt t).toNat = t
        rw [c1]
        show (tl.z2.call.tauAt t).toNat = t
        unfold Call.tauAt
        rw [w2]
        exact eid
    refine List.all_eq_true.2 fun c hc => List.all_eq_true.2 fun t ht' => ?_
    have hc' := List.mem_range.1 hc
    have ht2 : t < 2 ^ 10 := by
      have := List.mem_range.1 ht'
      obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
      · rw [q0] at this
        exact this
      · rw [q1] at this
        omega
    rw [all2 c hc' t ht2]
    exact beq_self_eq_true t
  · refine List.all_eq_true.2 fun c hc => decide_eq_true ?_
    have hc' := List.mem_range.1 hc
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · show ((tl.f9.calls[0]?).map (·.n)).getD 0 < 32
      rw [c1]
      show tl.z1.call.n < 32
      omega
    · show ((tl.f9.calls[1]?).map (·.n)).getD 0 < 32
      rw [c1]
      show tl.z2.call.n < 32
      omega

/-- At a record that agrees with a return of `piecesF` on the fields that the tests read. -/
theorem fit_of_from {tl : HTailF2} (hF : Fo.ZPlan.FromPieces tl) (ht : tl.tau = 128) (hm : 0 < tl.mz) :
    PiecesFit tl.f9 := by
  obtain ⟨tl0, tlp, hp, k⟩ := hF
  obtain ⟨-, -, -, -, -, -, -, -, k1, k2⟩ := Fo.PiecesF.piecesF_tail_lay_cut hp
  rw [k.f9]
  exact pieces_fit hp (by rw [← k1, ← k.tau]; exact ht) (by rw [← k2, ← k.mz]; exact hm)

/-- **The test on public data says nothing against a segment's data.** -/
theorem why_none {b : BzAt} {front rows columns : Nat} (F : PiecesFit b.tl.f9) (hT : DgP.tailTest b.tl = true)
    (c1 : b.rng + 1 = front) (c2 : b.declared = b.wanted) (c3 : b.mats.length = b.tl.mats.size)
    (c4 : b.tl.mz = allRows (parOfTail b.tl)) (c5 : rows = 32) (c6 : columns = b.tl.bzColumns) :
    b.why front rows columns = none := by
  have n1 : (b.rng + 1 != front) = false := by simp [c1]
  have n2 : (b.declared != b.wanted) = false := by simp [c2]
  have n3 : (b.mats.length != b.tl.mats.size) = false := by simp [c3]
  have n4 : (b.tl.mz != allRows (parOfTail b.tl)) = false := by simp [← c4]
  have n5 : (!(FoNums.ok b.tl.f9 && OnBytes.DgP.tailTest b.tl)) = false := by rw [F.ok, hT]; rfl
  have n6 : (!(b.tl.f9.calls.size == 2 && 2 ^ b.tl.f9.cK == 2)) = false := by rw [F.two, F.cK]; rfl
  have n7 : (!(FoNums.kOf b.tl.f9 0 == 10 && FoNums.kOf b.tl.f9 1 == 8 && b.tl.f9.kT == 10)) = false := by
    rw [F.k0, F.k1, F.kT]; rfl
  have n8 : (!(FoNums.t0Of b.tl.f9 0 == 0 && FoNums.t0Of b.tl.f9 1 == 0)) = false := by rw [F.t0, F.t1]; rfl
  have n9 : (!((List.range 2).all fun c =>
      (List.range (2 ^ FoNums.kOf b.tl.f9 c)).all fun t => FoNums.tauN b.tl.f9 c t == t)) = false := by
    rw [F.tab]; rfl
  have n10 : (!((List.range 2).all fun c => decide (FoNums.nOf b.tl.f9 c < 32))) = false := by rw [F.n32]; rfl
  have n11 : (!(rows == 32 && columns == b.tl.bzColumns)) = false := by rw [c5, c6]; simp
  unfold BzAt.why
  simp only [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, Bool.false_eq_true, if_false]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.shape_cK
#print axioms ProofFile.Honest.K10.PiecesFit
#print axioms ProofFile.Honest.K10.small_ids
#print axioms ProofFile.Honest.K10.pieces_fit
#print axioms ProofFile.Honest.K10.fit_of_from
#print axioms ProofFile.Honest.K10.why_none
