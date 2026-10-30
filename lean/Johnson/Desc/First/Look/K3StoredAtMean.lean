-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3StoredAtMean.lean: the kind "lookup" (K3), the lookup on the calls at a
layers' link and at the head's: THE FIELDS OF `LayAtTable`, `HeadAtTable`, `LayMean` AND `HeadMean`
THAT SPEAK OF THE STORED TABLE, PAID AT THE CONDUIT (Johnson/Desc/First/Look/K3StoredThree.lean), at
EVERY meaning Mg whose "decodes" and whose pin of the stored table are made of one decoder decT that
does not read the first chain's verifier's state.

Main name:
  `StoredPaid`: the eight: tabIn, pinWIn, pinWOut (the tables' three fields, to the letter, at
    every value z of the public part); hstrW, hsmpW (in the stronger form "at all states"), a
    sample is there; the message reads the witness's cells alone; wOf of the message is the cell.
  `stored_paid`: they hold, at the letters `k3StoredAt rad arr seat`, smpW := `Stored.smpWc`,
    strW := `Stored.strWc decT s₀`.

WHAT BINDS THE CELLS TO THE COMMITTED TABLE IS NOT HERE: it is the table's own item pinW
(decT y.cell a = some w.cells), which stands in the row's context in front and behind and is made
and closed by other kinds' rows at the real decoder. The conduit hands it to the library's dress
and back, both ways: see K3StoredThree.lean's head.

Limits: hd, hp (the meaning's two fields are decT's) and hS (decT does not read the first chain's
state) are premises. At `mgAll` hd and hp hold by unfolding (`mgAll_decodes`, `mgAll_pinW`); at the
seated term's decoder hS holds by unfolding (Johnson/P5J/LettersAt.lean: `noRec_decT`): what it
reads beside the strings it reads off the public part (by its authors' word: the key's
out-of-domain (OOD) sample on the committed table, which our files call the record; its text is
not opened here). Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker Run
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Wit)

section
variable {P Tok : Type} {rows cols : ℕ} {Fr : Frame}
  (Mg : Meaning P (Wit (Stored.CellsW rows cols) Tok MsgT))
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × Desc.First.S → Option (Stored.CellsW rows cols))
  (s₀ : Desc.First.S)

/-- **What the calls' laws ask on the stored table, at the conduit.** -/
structure StoredPaid : Prop where
  tabIn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Mg.decodes (z, a.1) (strsOf Fr a.2) →
    ∃ σW, Stored.smpWc (rows := rows) (cols := cols) a.1 = some σW ∧
      ¬ (Stored.oWc rows cols).Clash (Stored.strWc decT s₀ z a.2) σW.1
  pinWIn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str) w, Mg.pinW (z, a.1) (strsOf Fr a.2) w →
    ∃ σW, Stored.smpWc (rows := rows) (cols := cols) a.1 = some σW ∧
      (Stored.oWc rows cols).dec (Stored.strWc decT s₀ z a.2) σW = some (Stored.msgWc w)
  pinWOut : ∀ (z : P) (a : Desc.First.S × Fr.E.Str) w,
    (∃ σW, Stored.smpWc (rows := rows) (cols := cols) a.1 = some σW ∧
      (Stored.oWc rows cols).dec (Stored.strWc decT s₀ z a.2) σW = some (Stored.msgWc w)) →
    Mg.pinW (z, a.1) (strsOf Fr a.2) w
  hstrW : ∀ (C : Run.PQ.CK) (base : ℕ) (ds : List RDT) (z : P) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)),
    Stored.strWc decT s₀ z (behind C Fr base ds y τ) = Stored.strWc decT s₀ z y
  hsmpW : ∀ s s' : Desc.First.S,
    Stored.smpWc (rows := rows) (cols := cols) s' = Stored.smpWc (rows := rows) (cols := cols) s
  smpW0 : Nonempty (Stored.oWc rows cols).Smp
  cellsOnly : ∀ w w' : Wit (Stored.CellsW rows cols) Tok MsgT, w.cells = w'.cells →
    Stored.msgWc w = Stored.msgWc w'
  isCell : ∀ (w : Wit (Stored.CellsW rows cols) Tok MsgT) (y c : ℕ) (hy : y < rows)
    (hc : c < cols), Stored.wOfC (Stored.msgWc w) y c = w.cells ⟨y, hy⟩ ⟨c, hc⟩

variable {Mg decT}

/-- **They hold.** -/
theorem stored_paid (hd : Mg.decodes = decodesOf decT) (hp : Mg.pinW = pinWOf decT)
    (hS : Stored.NoRec decT) : StoredPaid (Fr := Fr) Mg decT s₀ where
  tabIn := fun z a h => Stored.tabIn_c s₀ z a (hd ▸ h)
  pinWIn := fun z a w h => Stored.pinWIn_c hS s₀ z a w (hp ▸ h)
  pinWOut := fun z a w h => hp ▸ Stored.pinWOut_c hS s₀ z a w h
  hstrW := fun C base ds z y τ => Stored.hstrW_c C s₀ z base ds y τ
  hsmpW := fun _ _ => rfl
  smpW0 := ⟨((), fun s => s.elim)⟩
  cellsOnly := Stored.msgW_cells
  isCell := Stored.wOf_msgW

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.stored_paid
