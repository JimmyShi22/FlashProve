-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkBat.lean: a run of the program's batching block, taken apart.

The program is the Lean verifier in OnBytes/; run, view, context and dry run are the words of
OnBytes/Iop/Ground.lean. The block (OnBytes/Iop/Bat.lean: `batVerify`) begins the proximity test on
a group, closes one round, in which the verifier draws one element, and combines the group's rows
under the powers of that element. This file says what a run of the block on a view has done
(`batVerify_inv`): which round of the view it has taken, which rows it has combined and in which
order, and what it leaves.

Main definition: `BatRan`. Main theorem: `batVerify_inv`.
Not claimed. What the combination of rows computes (`Bat.combine`) is not looked into here. Nothing
on the dry run. Nothing on soundness.
-/
import OnBytes.Iop.Bat
import OnBytes.Slice.BlkBegin

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The batching -/

/-- What a run of the batching on group g, on a view, has done. G, L: the group and its layout
before the run; x: the element that the round drew; row: the row that the block returns. -/
structure BatRan (g : Nat) (c c' : Ctx) (G : Group) (L : GroupLayout) (x : E) (row : GroupRow) :
    Prop where
  group : c.st.groups[g]? = some G
  fresh : G.inRun = false
  layout : c.st.layout g = some L
  /-- the row is the combination of the rows in the fixed order -/
  row : Bat.combine (begun c.st g G) g ⟨L, runRows c.st G⟩ x = some row
  st : c'.st = begun c.st g G
  book : c'.book = c.book
  failed : c'.failed = c.failed
  dry : c'.ch.dry = false
  opened : c'.ch.opened = c.ch.opened
  roots : c'.ch.roots = c.ch.roots
  firstTree : c'.ch.firstTree = c.ch.firstTree
  samples : c'.ch.samples = c.ch.samples

/-- A run of the batching on a view, taken apart. The block has taken one round of the view, in
which nothing was sent and one element was drawn; the plan's entry of that round has the name of the
batching and counts the rows that were combined. -/
theorem batVerify_inv (g : Nat) (row : GroupRow) (lay : GroupLayout) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (batVerify g).Yields c (row, lay) c') :
    ∃ G x e es r rest, BatRan g c c' G lay x row ∧
      c.ch.entries = e :: es ∧ e.name = "BAT" ∧ e.rows = (runRows c.st G).size ∧
      c.ch.pending = r :: rest ∧ r.vals = [] ∧ r.drawn.elems = [x.triple] ∧
      c'.ch.pending = rest ∧ c'.ch.entries = es ∧ c'.ch.settled = true := by
  unfold batVerify at h
  obtain ⟨input, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨G, L, hG, hf, _, hL, ei, e1⟩ := beginRun_inv _ _ _ _ h1
  obtain ⟨x, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨d, h2', hx⟩ := Blk.closeOne_inv _ _ _ _ _ _ h2
  have hd1 : c1.ch.dry = false := by rw [e1]; exact hd
  obtain ⟨e, es, r, rest, k1, k2, _, k4, k5, ed, _, _, _, k9, k10, k11, k12, k13, k14, k15, k16,
    k17, k18, k19⟩ :=
    Blk.close_inv _ _ _ _ _ _ hd1 h2'
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨e', q1, q2, e3⟩ := requireRows_inv _ _ _ k15 h3
  obtain ⟨S, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨eS, e4⟩ := (Blk.yields_statement _ _ _).1 h4
  have hd4 : c4.ch.dry = false := by rw [e4, e3]; exact k15
  obtain ⟨row', c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨hrow, e5⟩ := (Blk.yields_getOnView _ _ _ _ _ hd4).1 h5
  obtain ⟨hp, e6⟩ := (Blk.yields_pure _ _ _ _).1 a5
  obtain ⟨er, el⟩ := Prod.mk.inj hp
  have ee : e' = e := Option.some.inj (q1.symm.trans k11)
  -- the context at the end: that after the closed round, with the question on rows asked
  have ec : c' = { c2 with ch := { c2.ch with askedRows := true } } := by rw [e6, e5, e4, e3]
  have es1 : c1.st = begun c.st g G := by rw [e1]
  have eS' : S = begun c.st g G := by rw [eS, e3]; exact k12.trans es1
  rw [ei] at el q2 hrow
  rw [ee] at q2
  rw [eS', ← er] at hrow
  rw [e1] at k1 k4 k13 k14 k16 k17 k18 k19
  rw [ed] at hx
  rw [el]
  refine ⟨G, x, e, es, r, rest, ⟨hG, hf, hL, hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, k1, k2, q2, k4,
    k5, hx, ?_, ?_, ?_⟩
  · rw [ec]; exact k12.trans es1
  · rw [ec]; exact k13
  · rw [ec]; exact k14
  · rw [ec]; exact k15
  · rw [ec]; exact k16
  · rw [ec]; exact k17
  · rw [ec]; exact k18
  · rw [ec]; exact k19
  · rw [ec]; exact k9
  · rw [ec]; exact k10
  · rw [ec]
    show Chan.settled { c2.ch with askedRows := true } = true
    unfold Chan.settled
    simp [k11]

end OnBytes.Slice

#print axioms OnBytes.Slice.batVerify_inv
