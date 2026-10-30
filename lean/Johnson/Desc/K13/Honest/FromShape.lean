--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/FromShape.lean: which of the conditions on the state behind W's sending
(`SentAtM4`, Johnson/Desc/K13/Honest/RowsAccept.lean) follow from the test on the public shape,
which the batching's joined sub-protocol has asked in front. Statements with their proofs.

The test (`linFits`, Johnson/Desc/Own/Lin.lean; the library's `linOk`) asks, among other things,
that W has main rows over the large field, that its mask rows, if it has any, are under the own
group's mask code, and that 2^kCol entries have room in W's main table in front of its pad.
Main names:
  `shape_room`, `shape_small`: W's vector fits its table; the table has at most 63 index bits.
  `shape_rows`: each of the first 2^kCol entries lies in a real row of W's table.
  `w_ready`: a message of W's shape whose OOD sample is answered can join the own group; it has a
    main table, with the layout's number of index bits.
  `split_ready`: a message of the split's shape whose OOD sample is answered can join the own group,
    where the shape asks for a split.
  `sentAtM4_of_shape`: **the conditions, from the test on the shape and what is left**: the numbers
    handed on; the test on the own group's codes; W's message (its shape, its mark `sampled`, its
    pad's places); the split's message, where there is one (its shape, its mark, that it is no other
    member); the messages and places of the claim's mask entries; the length of the claim's point.

What is not claimed. That the test passes at any shape. BOTH HALVES OF THE PREMISE ON W's PAD (each
of its places in the main table lies within the table, and holds an entry with a number from 2^kCol
on) ARE PREMISES HERE. The test on the own group's codes is taken whole, though two of its three
clauses follow from the test on the shape. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.PadFree
import Johnson.Desc.K13.Law.M3Fits
import Johnson.Desc.Own.LinAgree
import Johnson.Desc.Own.RoomPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Own (linFits)
open VerifiableInference.Desc.K13.Law

/-- W's vector fits its table. -/
theorem shape_room {codes : Codes} {Sh : LinShape} (h : linFits codes Sh = true) :
    Sh.kCol ≤ (linLayW codes Sh).bits :=
  fits_of_linOk (by rw [← VerifiableInference.Desc.Own.linFits_eq]; exact h)

/-- W's table has at most 63 index bits. -/
theorem shape_small {codes : Codes} {Sh : LinShape} (h : linFits codes Sh = true) :
    (linLayW codes Sh).bits ≤ 63 :=
  le_trans ((VerifiableInference.Desc.Own.roomCan_iff _ _ _).1
    (VerifiableInference.Desc.Own.w_has_room codes Sh h).1).2.1 (by norm_num)

/-- Each of the first 2^kCol entries lies in a real row of W's table. -/
theorem shape_rows {codes : Codes} {Sh : LinShape} (h : linFits codes Sh = true) :
    ∀ e < 2 ^ Sh.kCol,
      (linLayW codes Sh).index e % 2 ^ (linLayW codes Sh).rowBits < Sh.w.mainRows := by
  obtain ⟨_, _, _, _, _, _, _, hr⟩ := (VerifiableInference.Desc.Own.linFits_iff codes Sh).1 h
  exact fun e he => VerifiableInference.Desc.Own.room_rows codes Sh.w Sh.wRowsHigh (2 ^ Sh.kCol)
    Nat.one_le_two_pow hr e he

/-- **A message of W's shape whose OOD sample is answered**: it can join the own group; it has a
main table, with the layout's number of index bits. -/
theorem w_ready {St : Statement} {Sh : LinShape} {w : ℕ} {x : OnBytes.Oracle}
    (h : linFits St.codes Sh = true) (hx : St.oracles[w]? = some x) (hs : x.shape = Sh.w)
    (hsam : x.sampled = true) :
    CanJoin St Sh.w.code Sh.ownMaskCode w ∧ St.has w .main = true ∧
      St.tableBits w .main = (linLayW St.codes Sh).bits := by
  obtain ⟨hS, _⟩ := (VerifiableInference.Desc.Own.linFits_iff St.codes Sh).1 h
  obtain ⟨_, _, _, _, _, _, _, hW, _, hWm, _⟩ := hS
  have hne : Sh.w.mainRows ≠ 0 := hW.2.1
  refine ⟨⟨x, hx, hsam, Or.inr (by rw [hs]), by rw [hs]; exact hWm⟩, ?_, ?_⟩
  · have hpos : 0 < x.shape.rows .main := by
      rw [hs]
      exact Nat.pos_of_ne_zero hne
    unfold Statement.has
    rw [hx]
    exact decide_eq_true hpos
  · simp only [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, hs,
      OracleShape.rows]
    rw [if_neg (by simpa using hne)]
    rfl

/-- A message of the split's shape whose OOD sample is answered can join the own group, where the
shape asks for a split. -/
theorem split_ready {St : Statement} {Sh : LinShape} {sp : ℕ} {x : OnBytes.Oracle}
    (h : linFits St.codes Sh = true) (hn : Sh.ownSplitNeeded = true)
    (hx : St.oracles[sp]? = some x) (hs : x.shape = Sh.ownSplit) (hsam : x.sampled = true) :
    CanJoin St Sh.w.code Sh.ownMaskCode sp := by
  obtain ⟨hS, _⟩ := (VerifiableInference.Desc.Own.linFits_iff St.codes Sh).1 h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsp⟩ := hS
  rcases hsp with hsp | hsp
  · rw [hn] at hsp
    cases hsp
  · exact ⟨x, hx, hsam, Or.inl (by rw [hs]; exact hsp.1), Or.inr (by rw [hs]; exact hsp.2.2.2)⟩

/-- **The conditions on the state behind W's sending, from the test on the shape and what is
left.** x: W's message. -/
theorem sentAtM4_of_shape {Sh : LinShape} {row : TensorRow} {ids : Array ℕ} {St : Statement}
    {w : ℕ} {x : OnBytes.Oracle} (h : linFits St.codes Sh = true)
    (hx : St.oracles[w]? = some x) (hs : x.shape = Sh.w) (hsam : x.sampled = true)
    (hpadW : ∀ q ∈ x.pad, q.1 = .main → q.2 < 2 ^ (linLayW St.codes Sh).bits ∧
      2 ^ Sh.kCol ≤ (linLayW St.codes Sh).entryAt q.2)
    (first : ids[0]? = some w)
    (split : Sh.ownSplitNeeded = true → ∃ (sp : ℕ) (y : OnBytes.Oracle), ids[1]? = some sp ∧
      St.oracles[sp]? = some y ∧ y.shape = Sh.ownSplit ∧ y.sampled = true ∧ sp ≠ w ∧
      ∀ t ∈ row.masks, t.1.oracle ≠ sp)
    (codes : Ground.groupOk St.codes Sh.w.code Sh.ownMaskCode = true)
    (masks : ∀ t ∈ row.masks, CanJoin St Sh.w.code Sh.ownMaskCode t.1.oracle ∧ t.1.oracle ≠ w)
    (point : row.psi.length = Sh.kCol)
    (within : ∀ t ∈ row.masks, St.has t.1.oracle .mask = true ∧
      t.1.index < 2 ^ St.tableBits t.1.oracle .mask)
    (hoff : ∀ t ∈ row.masks, ∀ y : OnBytes.Oracle, St.oracles[t.1.oracle]? = some y →
      (OnBytes.Part.mask, t.1.index) ∉ y.pad) :
    SentAtM4 Sh row ids St w := by
  obtain ⟨hj, ht, hb⟩ := w_ready h hx hs hsam
  have hsplit : Sh.ownSplitNeeded = true → ∃ sp, ids[1]? = some sp ∧
      CanJoin St Sh.w.code Sh.ownMaskCode sp ∧ sp ≠ w ∧ ∀ t ∈ row.masks, t.1.oracle ≠ sp := by
    intro hn
    obtain ⟨sp, y, h1, hy, hys, hym, h3, h4⟩ := split hn
    exact ⟨sp, h1, split_ready h hn hy hys hym, h3, h4⟩
  refine ⟨first, hsplit, codes, masks, hj, point, shape_room h, shape_small h, ht, hb, within,
    sentAtM4_pad (by rw [point]; exact shape_room h) (fun y hy q hq hm => ?_) hoff⟩
  rw [hx] at hy
  obtain rfl := Option.some.inj hy
  rw [point]
  exact hpadW q hq hm

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.shape_room
#print axioms VerifiableInference.Desc.K13.Honest.shape_small
#print axioms VerifiableInference.Desc.K13.Honest.shape_rows
#print axioms VerifiableInference.Desc.K13.Honest.w_ready
#print axioms VerifiableInference.Desc.K13.Honest.split_ready
#print axioms VerifiableInference.Desc.K13.Honest.sentAtM4_of_shape
