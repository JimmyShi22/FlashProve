-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeldAtPieces.lean: THE SMALLNESS TEST: THE PUBLIC TEST `heldPubB`
(Johnson/Desc/K8/Honest/HeldPublic.lean: the verifier's own tests forestHeld and callHeld at a
made-up heard structure) SAYS YES AT WHATEVER THE LAST STEP OF THE VERIFIER's OWN MAKER OF THE
TEST's DATA RETURNS (`HTailF2.piecesF`, OnBytes/Model/Tail.lean), AT 128 COMBINATIONS AND AT LEAST
ONE COLUMN OF DIGITS. Clause by clause off the texts of piecesF, placeZ and Forest.shape. Lemmas on
the verifier's own text; none of the library's goals.

  `falling_one` one number has one order
  `placeZ_one` placeZ at one piece: the piece as it is laid, and the call's number of bits of keys
  `blocks_128` at 128 rows there is one block: t2BL 128 = .ok #[(0, 128)]
  `pieces_cut` what piecesF returns: the blocks, the bound on a tree's bits, the two calls, the
                   shape
  `clog2_128`, `range_one_map` helpers
  `placed_facts` what placeZ makes of one piece of 128 rows from row 0 on, with a column: the call's
                   bits are max 10 (7 + clog2 Cp); one piece; it is well placed (the library's
                   `PieceFits`); the bits are the second computation's
  `lowPiece`, `highPiece` the one piece of each call, as piecesF hands it to placeZ there
  **`heldPub_pieces`** tl0.piecesF = .ok tl · tl0.tau = 128 · 0 < tl0.mz ⊢ heldPubB tl = true
WHENCE THE TWO BOUNDS THAT NO LINE OF piecesF TESTS (a call has at most 2 ^ 44 keys; a piece at most
2 ^ 40 rows): piecesF calls Forest.shape, which refuses (forest-keys) unless dT + rK < 32: so a call
has fewer than 2 ^ 31 keys; the piece has 2 ^ 7 rows.
By: `shape_two` (Johnson/Desc/K8/Honest/ShapeAtTwo.lean) · the library's `forestHeld_iff`,
`callHeld_iff` (Johnson/Desc/First/TailClaims/AgainMeans.lean), `forestHeld_eq`, `callHeld_eq`
(AgainAgrees.lean) · `piecesF_tail_cnt_placeZ`, `piecesF_tail_cnt_order`
(OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailCnt.lean) · `le_two_pow_ceilLog2`
(OnBytes/Slice/ProgCodes.lean).
WRITTEN A FURTHER TIME: `pieces_cut` is the library's `piecesF_tail_lay_cut`
(Ends/PiecesFTailLay.lean) with two clauses more (the blocks; the bound) and two fewer.
Limits. AT 128 COMBINATIONS ALONE: one block, one piece a call; where there are two blocks nothing
is said. WITH NO COLUMN THE TEST SAYS NO (callHeld asks that a piece has one): whether piecesF
returns there is not looked at. From a return of the routine alone: nothing says that it returns.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ShapeAtTwo
import Johnson.Desc.K8.Honest.HeldPublic
import Johnson.Desc.First.TailClaims.AgainMeans
import Johnson.Desc.First.TailClaims.AgainAgrees
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open _root_.Fo.PiecesF (piecesF_tail_cnt_placeZ piecesF_tail_cnt_order piecesF_tail_cnt_laid
  piecesF_tail_cnt_sized piecesF_tail_cnt_size1 piecesF_tail_cnt_clog2)

/-- One number has one order. -/
theorem falling_one (key : Nat → Nat) : byFallingKey 1 key = [0] := by
  have p := piecesF_tail_cnt_order key 1
  have e : List.range 1 = [0] := rfl
  rw [e] at p
  exact List.perm_singleton.1 p

/-- **placeZ at one piece.** -/
theorem placeZ_one (p : Piece) (name : String) (k lid : Nat) :
    (placeZ #[p] name k lid).pieces =
        #[{ p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp,
                   off := 0 }] ∧
      (placeZ #[p] name k lid).call.n = max 10 (clog2 p.Rp + clog2 p.Cp) := by
  obtain ⟨e1, e2⟩ := piecesF_tail_cnt_placeZ #[p] name k lid
  have hs : (piecesF_tail_cnt_sized #[p]).size = 1 := by simp [piecesF_tail_cnt_sized]
  rw [hs, falling_one] at e1 e2
  constructor
  · rw [e1]
    simp [piecesF_tail_cnt_laid, piecesF_tail_cnt_sized, piecesF_tail_cnt_size1]
  · rw [e2]
    simp [piecesF_tail_cnt_laid, piecesF_tail_cnt_sized, piecesF_tail_cnt_size1,
      piecesF_tail_cnt_clog2]

/-- At 128 rows there is one block. -/
theorem blocks_128 : t2BL 128 = .ok #[(0, 128)] := by
  have l : Nat.log2 128 = 7 := by
    have := Nat.log2_two_pow (n := 7)
    simpa using this
  simp [t2BL, t2BLLoop, l]

/-- What piecesF returns, with the blocks and the bound on a tree's bits. -/
theorem pieces_cut {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    ∃ bz f9 pub, t2BL tl0.tau = .ok bz ∧ tl.blocks = bz ∧ tl.lidb = tl0.lidb ∧
      tl.z1 = placeZ ((Array.range bz.size).map fun i =>
        ({ tree := tl0.ix.ZZ, row := i, r0 := (bz.getD i (0, 0)).1, Rp := (bz.getD i (0, 0)).2,
           c0 := 0, Cp := tl0.mz } : Piece)) "R10z" t2D0 tl0.lidb ∧
      tl.z2 = placeZ ((Array.range bz.size).map fun i =>
        ({ tree := tl0.ix.ZZ, row := bz.size + i, r0 := (bz.getD i (0, 0)).1,
           Rp := (bz.getD i (0, 0)).2, c0 := tl0.mz, Cp := tl0.mz } : Piece)) "R8d" t2D1
          tl0.lidb ∧
      Forest.shape #[tl.z1.call, tl.z2.call] tl0.lidb = .ok f9 ∧
      tl.f9 = { f9 with pub := pub } := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hb, h⟩ := OnBytes.Ends.ok_of_bind h
  obtain ⟨_, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨_, h⟩ := OnBytes.Ends.ok_of_jp h
  obtain ⟨f9, hs, h⟩ := OnBytes.Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := OnBytes.Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := OnBytes.Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨bz, f9, pub, hb, rfl, rfl, rfl, rfl, hs, rfl⟩

/-- 128 rows have seven bits. -/
theorem clog2_128 : clog2 128 = 7 := by
  have := piecesF_tail_cnt_clog2 7
  simpa using this

/-- **What placeZ makes of one piece of 128 rows from row 0 on, with a column.** -/
theorem placed_facts (p : Piece) (name : String) (k lid : Nat) (hR : p.Rp = 128) (h0 : p.r0 = 0)
    (hC : 0 < p.Cp) :
    (placeZ #[p] name k lid).call.n = max 10 (7 + clog2 p.Cp) ∧
      (placeZ #[p] name k lid).pieces.size = 1 ∧
      (∀ x ∈ (placeZ #[p] name k lid).pieces,
        TailClaims.PieceFits (placeZ #[p] name k lid).call.n x) ∧
      (placeZ #[p] name k lid).call.n =
        max 10 (clog2 ((placeZ #[p] name k lid).pieces.foldl (fun s x => s + 2 ^ x.b) 0)) := by
  obtain ⟨q, n⟩ := placeZ_one p name k lid
  rw [hR, clog2_128] at q n
  refine ⟨n, by rw [q]; rfl, ?_, ?_⟩
  · intro x hx
    rw [q] at hx
    obtain rfl : x = _ := by simpa using hx
    rw [n]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨clog2 p.Cp, rfl⟩, ?_, ?_, ?_, ?_⟩
    · show (128 : Nat) ≠ 0
      omega
    · show p.Cp ≠ 0
      omega
    · show 7 ≤ 40
      omega
    · show 2 ^ 7 = 128
      rfl
    · show p.r0 % 128 = 0
      rw [h0]
    · show p.Cp ≤ 2 ^ clog2 p.Cp
      exact OnBytes.Slice.le_two_pow_ceilLog2 p.Cp
    · show 7 + clog2 p.Cp = 7 + clog2 (2 ^ clog2 p.Cp)
      rw [piecesF_tail_cnt_clog2]
    · show 7 + clog2 p.Cp ≤ max 10 (7 + clog2 p.Cp)
      omega
    · show 0 % 2 ^ (7 + clog2 p.Cp) = 0
      exact Nat.zero_mod _
    · show 0 + 2 ^ (7 + clog2 p.Cp) ≤ 2 ^ max 10 (7 + clog2 p.Cp)
      rw [Nat.zero_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
  · rw [n, q]
    simp [piecesF_tail_cnt_clog2]

/-- A table over the one number below 1. -/
theorem range_one_map {α : Type} (f : Nat → α) : (Array.range 1).map f = #[f 0] := by
  apply Array.ext'
  simp [List.range_succ]

/-- The one piece of the call of the low digits, as piecesF hands it to placeZ at 128 rows. -/
def lowPiece (tl0 : HTailF2) : Piece :=
  { tree := tl0.ix.ZZ, row := 0, r0 := 0, Rp := 128, c0 := 0, Cp := tl0.mz }

/-- That of the high digits. -/
def highPiece (tl0 : HTailF2) : Piece :=
  { tree := tl0.ix.ZZ, row := 1, r0 := 0, Rp := 128, c0 := tl0.mz, Cp := tl0.mz }

/-- **THE PUBLIC TEST SAYS YES AT WHAT piecesF RETURNS, at 128 combinations and a column.** -/
theorem heldPub_pieces {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) (ht : tl0.tau = 128)
    (hm : 0 < tl0.mz) : heldPubB tl = true := by
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
  obtain ⟨a1, a2, a3, a4⟩ := placed_facts (lowPiece tl0) "R10z" t2D0 tl0.lidb rfl rfl hm
  obtain ⟨b1, b2, b3, b4⟩ := placed_facts (highPiece tl0) "R8d" t2D1 tl0.lidb rfl rfl hm
  rw [← e1'] at a1 a2 a3 a4
  rw [← e2'] at b1 b2 b3 b4
  have hn : tl.z2.call.n = tl.z1.call.n := b1.trans a1.symm
  obtain ⟨d, k, t, r, i, f, v⟩ := shape_two hs hn
  rw [← eL] at d t r i f
  have k1 : tl.z1.call.k = 10 := by
    rw [e1']
    rfl
  have k2 : tl.z2.call.k = 8 := by
    rw [e2']
    exact t2D1_eq
  have hB : tl.zzBlocks = 1 := by
    unfold HTailF2.zzBlocks
    rw [eB]
    rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := model_sizes tl
  have n44 : tl.z1.call.n ≤ 44 := by
    rw [d, r] at v
    omega
  have n10 : 10 ≤ tl.z1.call.n := by
    rw [a1]
    omega
  unfold heldPubB
  rw [Bool.and_eq_true]
  constructor
  · rw [← TailClaims.forestHeld_eq]
    refine (TailClaims.forestHeld_iff tl _).2 ?_
    dsimp only
    rw [e9]
    refine ⟨hn, d, ?_, t, r, i, f, m1, m2, m3⟩
    show f9.kT = 10
    rw [k, k1, k2]
    rfl
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [← TailClaims.callHeld_eq]
    constructor
    · refine (TailClaims.callHeld_iff tl _ _ 0).2 ?_
      dsimp only
      rw [show tl.zOf 0 = tl.z1 from rfl]
      refine ⟨by rw [e1']; rfl, by rw [e1']; rfl, k1, by rw [e1']; rfl, by rw [e1']; rfl,
        a2.trans hB.symm, n10, n44, m4, a3, Or.inl (by rw [hB]; omega), a4, ?_⟩
      rw [eL, e1']
      rfl
    · refine (TailClaims.callHeld_iff tl _ _ 1).2 ?_
      dsimp only
      rw [show tl.zOf 1 = tl.z2 from rfl]
      refine ⟨by rw [e2']; rfl, by rw [e2']; rfl, k2, by rw [e2']; rfl, by rw [e2']; rfl,
        b2.trans hB.symm, by rw [hn]; exact n10, by rw [hn]; exact n44, m5, b3,
        Or.inl (by rw [hB]; omega), b4, ?_⟩
      rw [eL, e2']
      rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.falling_one
#print axioms VerifiableInference.Desc.First.K8.Honest.placeZ_one
#print axioms VerifiableInference.Desc.First.K8.Honest.blocks_128
#print axioms VerifiableInference.Desc.First.K8.Honest.pieces_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.clog2_128
#print axioms VerifiableInference.Desc.First.K8.Honest.placed_facts
#print axioms VerifiableInference.Desc.First.K8.Honest.range_one_map
#print axioms VerifiableInference.Desc.First.K8.Honest.heldPub_pieces
