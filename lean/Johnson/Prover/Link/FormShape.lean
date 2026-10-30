-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormShape.lean: THE FORM's HALF: AT A GROUP IN ORDER, THE LAYOUT THAT THE
STATEMENT GIVES IT PASSES THE FOLD's TEST ON THE SHAPE (Own.foldShapeFits,
Johnson/Desc/Own/Fold.lean), at a stage whose numbers are the layout's and the group's.

Main names.
  layBlocks_size      the placing of blocks returns as many places as it is handed sizes.
  has_iff, rowBits_at what Statement.has and Statement.rowBits say at a message that is there.
  memberFit_of_group  each member of the layout fits (Own.MemberFit,
  Johnson/Desc/Own/FoldMean.lean). shapeFits_of_group  THE STATEMENT.

What it asks. The group is there and in order (GroupOk, Johnson/Desc/Means/Says.lean) · the layout
is the statement's · the stage's k, h are the layout's and its two codes' numbers the group's · the
two codes are there · four tests on numbers (1 ≤ k · h ≤ k · the mask code is not longer than the
main code · 2 k + 1 - h ≤ the mask code's message) · SOME MEMBER HAS A MAIN ROW AND IS NOT KEPT.

Limits. All these are premises. No value that is sent or drawn is read.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Own.FoldMean
import Johnson.Desc.Means.Layout
import OnBytes.Iop.Prox

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc

theorem layBlocks_size (sizes : Array (Option Nat)) : (layBlocks sizes).1.size = sizes.size := by
  have e : layBlocks sizes = layAll sizes (List.range sizes.size) (topSize sizes)
      (Array.replicate sizes.size none, 0) := layBlocks_eq sizes
  have inv := LayInv.outer (List.range sizes.size) (topSize sizes) _
    (LayInv.start (sizes := sizes) (topSize sizes))
  rw [← e] at inv
  exact inv.size

theorem sizesOf_size (S : Statement) (G : Group) (part : Part) :
    (sizesOf S G part).size = G.members.size := by
  unfold sizesOf
  rw [Array.size_map, Array.size_range]

theorem has_iff {S : Statement} {o : Nat} {x : Oracle} (hx : S.oracles[o]? = some x) (part : Part) :
    S.has o part = true ↔ 0 < x.shape.rows part := by
  unfold Statement.has
  rw [hx]
  exact decide_eq_true_iff

theorem rowBits_at {S : Statement} {o : Nat} {x : Oracle} (hx : S.oracles[o]? = some x)
    (part : Part) : S.rowBits o part = ceilLog2 (x.shape.rows part) := by
  unfold Statement.rowBits
  rw [hx]

/-- One table's clause of a member's fit. tot: the rows that the blocks take. -/
theorem block_fits {S : Statement} {G : Group} {i : Nat} {x : Oracle} (part : Part)
    (hi : i < G.members.size) (hx : S.oracles[G.members.getD i noId]? = some x) (K : Nat)
    (hK : (layBlocks (sizesOf S G part)).2 ≤ 2 ^ K) :
    (∀ f, (layBlocks (sizesOf S G part)).1.getD i none = some f →
      (0 < x.shape.rows part ∧ (part = .main → G.kept.getD i false = false)) ∧
        f + x.shape.rows part ≤ 2 ^ K) ∧
    ((layBlocks (sizesOf S G part)).1.getD i none = none →
      ¬ (0 < x.shape.rows part ∧ (part = .main → G.kept.getD i false = false))) := by
  constructor
  · intro f hf
    obtain ⟨a, ha, _, hle⟩ := (layBlocks_right (sizesOf S G part)).1 i f hf
    obtain ⟨_, h1, h2, rfl⟩ := sizesOf_some ha
    refine ⟨⟨(has_iff hx part).1 h1, h2⟩, ?_⟩
    rw [rowBits_at hx part] at hle
    have := Slice.le_two_pow_ceilLog2 (x.shape.rows part)
    omega
  · intro hn hc
    obtain ⟨f, hf⟩ := (layBlocks_right (sizesOf S G part)).2.2 i _
      (sizesOf_of hi ((has_iff hx part).2 hc.1) hc.2)
    rw [hn] at hf
    cases hf

/-- **Each member of the layout fits.** -/
theorem memberFit_of_group {S : Statement} {G : Group} (hOk : GroupOk S G) (c : IoppStage)
    (ck : c.k = (layoutOf S G).k) (ch : c.h = (layoutOf S G).h) (c1 : G.code = c.code)
    (c2 : G.maskCode = c.maskCode) (i : Nat) (hi : i < G.members.size) :
    Own.MemberFit S (ioppFoldShape c (layoutOf S G)) i := by
  have hmem : G.members.getD i noId ∈ G.members.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
  obtain ⟨x, hx⟩ : ∃ x, S.oracles[G.members.getD i noId]? = some x :=
    ⟨_, Array.getElem?_eq_getElem (hOk.there _ hmem)⟩
  have kM : (layBlocks (sizesOf S G .main)).2 ≤ 2 ^ c.k := by
    rw [ck]
    refine Nat.le_trans (Slice.le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) ?_)
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have kZ : (layBlocks (sizesOf S G .mask)).2 ≤ 2 ^ c.h := by
    rw [ch]
    exact Slice.le_two_pow_ceilLog2 _
  obtain ⟨m1, m2⟩ := block_fits .main hi hx c.k kM
  obtain ⟨z1, z2⟩ := block_fits .mask hi hx c.h kZ
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · show x.shape.mainRows = 0 ∨ x.shape.code = c.code
    rw [← c1]
    exact hOk.mainCode _ hmem x hx
  · show x.shape.maskRows = 0 ∨ x.shape.maskCode = c.maskCode
    rw [← c2]
    exact hOk.maskCode _ hmem x hx
  · show match (layBlocks (sizesOf S G .main)).1.getD i none with
      | some f => (0 < x.shape.mainRows ∧ G.kept.getD i false = false) ∧
          f + x.shape.mainRows ≤ 2 ^ c.k
      | none => ¬ (0 < x.shape.mainRows ∧ G.kept.getD i false = false)
    cases h : (layBlocks (sizesOf S G .main)).1.getD i none with
    | some f => exact ⟨⟨(m1 f h).1.1, (m1 f h).1.2 rfl⟩, (m1 f h).2⟩
    | none => exact fun hc => m2 h ⟨hc.1, fun _ => hc.2⟩
  · show match (layBlocks (sizesOf S G .mask)).1.getD i none with
      | some f => 0 < x.shape.maskRows ∧ f + x.shape.maskRows ≤ 2 ^ c.h
      | none => x.shape.maskRows = 0
    cases h : (layBlocks (sizesOf S G .mask)).1.getD i none with
    | some f => exact ⟨(z1 f h).1.1, (z1 f h).2⟩
    | none =>
      exact Nat.eq_zero_of_not_pos fun hc => z2 h ⟨hc, fun e => by cases e⟩

/-- **THE LAYOUT PASSES THE FOLD's TEST ON THE SHAPE.** -/
theorem shapeFits_of_group {S : Statement} {G : Group} {g : Nat} {L : GroupLayout}
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G) (c : IoppStage)
    (ck : c.k = L.k) (ch : c.h = L.h) (c1 : G.code = c.code) (c2 : G.maskCode = c.maskCode)
    (cd zk : Code) (hb : S.codes.base[c.code]? = some cd) (hm : S.codes.mask[c.maskCode]? = some zk)
    (n1 : 1 ≤ c.k) (n2 : c.h ≤ c.k) (n3 : zk.logN ≤ cd.logN) (n4 : 2 * c.k + 1 - c.h ≤ zk.ell)
    (hmain : ∃ i < G.members.size, ∃ x, S.oracles[G.members.getD i noId]? = some x ∧
      0 < x.shape.mainRows ∧ G.kept.getD i false = false) :
    Own.foldShapeFits S (ioppFoldShape c L) = true := by
  obtain rfl : L = layoutOf S G := Option.some.inj (hL.symm.trans (layout_eq S g G hG))
  rw [Own.foldShapeFits_iff]
  refine ⟨cd, zk, hb, hm, n1, n2, n3, n4, hOk.marks, ?_, ?_, ?_, hmain⟩
  · show (layBlocks (sizesOf S G .main)).1.size = G.members.size
    rw [layBlocks_size, sizesOf_size]
  · show (layBlocks (sizesOf S G .mask)).1.size = G.members.size
    rw [layBlocks_size, sizesOf_size]
  · exact fun i hi => memberFit_of_group hOk c ck ch c1 c2 i hi

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.layBlocks_size
#print axioms Johnson.Prover.Link.sizesOf_size
#print axioms Johnson.Prover.Link.has_iff
#print axioms Johnson.Prover.Link.rowBits_at
#print axioms Johnson.Prover.Link.block_fits
#print axioms Johnson.Prover.Link.memberFit_of_group
#print axioms Johnson.Prover.Link.shapeFits_of_group
