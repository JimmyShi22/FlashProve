-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyFrames.lean: the table of joints of the key file: what only rides past a block (Piece.Frames, Johnson/Desc/Sound/Spine.lean, paid by sort of item): an item that a block neither closes nor opens must hold in front if it holds behind. Here: for every sort of item that
KeyMeaning.meaning₁ fills, from named facts on the readers at the state in front (s) and behind (s'): the block has not turned what the item reads.
  SameStmt X s s'    the statement's tables' sizes; each oracle message's «sampled» and its sample rows
  rides_srow · rides_rows · rides_kclaims · rides_grows · rides_pile · rides_unmarked · rides_inRange   proved, each from just the facts that its item reads
  SamePins F G …     the reading's two letters agree at the two records: the samples; the stored table's record · rides_pin · rides_pinT   proved
What it pays, once the facts are shown of a block (equations on its state: other files' to show): the claim's half («what is open behind is true ⟹ what is open in front is true») of the nine empty rows of the first chain (a lookup's «laid» · caller · «behind the
batching» · «cleared»; the seal); and at every other row the same for the items that are open and not named in it. The promise's half (the promise in front and the block's yes give the promise behind) is not here.
Not here: forms | worth (open at one border alone: nothing rides past them) · the promise's half · that any block has the facts.
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

section
variable {P S Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- The block has not turned the statement's tables' sizes, nor an oracle message's «sampled» or its sample rows. -/
structure SameStmt (s s' : S) : Prop where
  tables : SameTables (X.st s') (X.st s)
  oracle : ∀ (o : Nat) (x' : OnBytes.Oracle), (X.st s').oracles[o]? = some x' → ∃ x : OnBytes.Oracle, (X.st s).oracles[o]? = some x ∧ x.sampled = x'.sampled ∧ x.sampleRows = x'.sampleRows

local notation "Mg" => meaning₁ K R X near forms worth other

theorem rides_unmarked (p : P) (s s' : S) (h : X.marked s = X.marked s') (hu : (Mg).unmarked (p, s')) : (Mg).unmarked (p, s) :=
  h.trans hu

/-- inRange reads the witness alone. -/
theorem rides_inRange (l : Nat) (w : Wit Cells Unit M) (hu : (Mg).inRange l w) : (Mg).inRange l w := hu

theorem rides_srow (k : Nat) (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (H : SameStmt X s s') (hu : (Mg).srow k (p, s') y w) : (Mg).srow k (p, s) y w := by
  obtain ⟨o, x', ho, hx', h1, h2, h3⟩ := hu
  obtain ⟨x, hx, e1, e2⟩ := H.oracle o x' hx'
  exact ⟨o, x, ho, hx, e1.trans h1, e2 ▸ h2, fun r hr => (rowHolds_congr _ H.tables _ r).1 (h3 r (e2 ▸ hr))⟩

theorem rides_rows (l : Nat) (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (H : SameStmt X s s') (hr : X.rowsAt s l = X.rowsAt s' l)
    (hu : (Mg).rows l (p, s') y w) : (Mg).rows l (p, s) y w := by
  obtain ⟨rs, h1, h2, h3⟩ := hu
  exact ⟨rs, hr.trans h1, h2, fun r hr' => (rowHolds_congr _ H.tables _ r).1 (h3 r hr')⟩

theorem rides_kclaims (l : Nat) (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (hk : X.keysAt s l = X.keysAt s' l)
    (hu : (Mg).kclaims l (p, s') y w) : (Mg).kclaims l (p, s) y w := by
  obtain ⟨L, ks, h1, h2, h3, h4⟩ := hu
  exact ⟨L, ks, h1, hk.trans h2, h3, h4⟩

theorem rides_pile (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (hp : X.pile s = X.pile s') (hu : (Mg).pile (p, s') y w) : (Mg).pile (p, s) y w := by
  obtain ⟨x, h1, h2⟩ := hu
  exact ⟨x, hp.trans h1, h2⟩

theorem rides_grows (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M) (H : SameStmt X s s') (hg : X.grpB s = X.grpB s')
    (hG : ∀ (g : Nat) (G' : OnBytes.Group), (X.st s').groups[g]? = some G' → ∃ G : OnBytes.Group, (X.st s).groups[g]? = some G ∧ G.rows = G'.rows)
    (hu : (Mg).grows (p, s') y w) : (Mg).grows (p, s) y w := by
  obtain ⟨g, G', o, x', h1, h2, h3, h4, h5, h6, h7⟩ := hu
  obtain ⟨G, hG1, hG2⟩ := hG g G' h2
  obtain ⟨x, hx, _, e2⟩ := H.oracle o x' h4
  exact ⟨g, G, o, x, hg.trans h1, hG1, h3, hx, hG2 ▸ h5, fun r hr => (rowHolds_congr _ H.tables _ r).1 (h6 r (hG2 ▸ hr)),
    fun r hr => (rowHolds_congr _ H.tables _ r).1 (h7 r (e2 ▸ hr))⟩

end

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)

/-- The reading's two letters that read the chain's record agree at the two records. -/
structure SamePins (a a' : P × S) : Prop where
  smp : ∀ j t, G.smp a j t = G.smp a' j t
  recOf : G.recOf a = G.recOf a'

theorem rides_pin (j t : Nat) (a a' : P × S) (y : Strs) (w : Wit Cells Unit M) (H : SamePins G a a') (hu : PIN F G j t a' y w) : PIN F G j t a y w := by
  obtain ⟨o, z, h1, h2, h3⟩ := hu
  exact ⟨o, z, h1, (H.smp j t).trans h2, h3⟩

/-- The stored table's pin fixes the cells. -/
theorem pinT_one (a : P × S) (y : Strs) (w w' : Wit Cells Unit M) (h : PINW G a y w) (h' : PINW G a y w') : w.cells = w'.cells := by
  obtain ⟨r, h1, h2⟩ := h
  obtain ⟨r', h1', h2'⟩ := h'
  have e : r' = r := Option.some.inj (h1'.symm.trans h1)
  subst e
  exact Option.some.inj (h2.symm.trans h2')

/-- A pin reads the witness through msgOf at its seat alone. -/
theorem pin_of_msgOf (j t : Nat) (a : P × S) (y : Strs) (w w' : Wit Cells Unit M) (e : msgOf G w' j t = msgOf G w j t) (h : PIN F G j t a y w) : PIN F G j t a y w' := by
  obtain ⟨o, z, h1, h2, h3⟩ := h
  exact ⟨o, z, h1, h2, e.symm ▸ h3⟩

/-- The stored table's pin reads the witness's cells alone. -/
theorem pinT_of_cells (a : P × S) (y : Strs) (w w' : Wit Cells Unit M) (e : w'.cells = w.cells) (h : PINW G a y w) : PINW G a y w' := by
  obtain ⟨r, h1, h2⟩ := h
  exact ⟨r, h1, e.symm ▸ h2⟩

theorem rides_pinT (a a' : P × S) (y : Strs) (w : Wit Cells Unit M) (H : SamePins G a a') (hu : PINW G a' y w) : PINW G a y w := by
  obtain ⟨r, h1, h2⟩ := hu
  exact ⟨r, H.recOf.trans h1, h2⟩

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.rides_srow
#print axioms VerifiableInference.Desc.Key.rides_rows
#print axioms VerifiableInference.Desc.Key.rides_kclaims
#print axioms VerifiableInference.Desc.Key.rides_pile
#print axioms VerifiableInference.Desc.Key.rides_grows
#print axioms VerifiableInference.Desc.Key.rides_pin
#print axioms VerifiableInference.Desc.Key.rides_pinT
