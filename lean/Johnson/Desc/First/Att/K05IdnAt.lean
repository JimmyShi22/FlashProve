-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05IdnAt.lean: kind K5: THE KIND's OWN TWO FAMILIES OF IDENTITIES (at1: the bits of the index of a row's largest score are bits; at2: the row's largest score is the score at that index), FROM THE CELLS OFF THE MESSAGES, OVER THE
EXTENSION FIELD, TO THE CASTS OF THE INTEGER CELLS, OVER THE BASE FIELD: under the named reading CellsAre (Johnson/Desc/First/Look/K3CallerAttMeans.lean: the cells off the tuple of messages are the casts of the integers Z). The like of that file's att_attRidden
(at3), for at1 and at2. The conclusion is the integer model's AttOwn1 S Z ∧ AttOwn2 S Z (Johnson/Goal/Meaning/Row.lean), written out: that file is not imported.
Main name: own12_of_cells.
For whom: whoever pays the clause "idn" of K5FillIns at a meaning whose part .idn at an attention segment is that pair.
IS IT EMPTY HERE? An implication; CellsAre is shown of nothing here (attCells_cast, in the file named, pays it where the committed symbols are the packing of small integers).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Road.L5 (Zs dimOf cellsA)
open Inst.Model.AttSeg (Raw Idn idnVal castT)
open VerifiableInference.Desc.First.Look (Sent attSg attCells CellsAre)

/-- One identity: from the extension field to the base field, at the casts of integers. -/
theorem idn_down (S : Attention.Shape) (Z : Zs) (j : Idn)
    (h : idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.E) j = 0) :
    idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) j = 0 := by
  rw [Inst.Model.AttSeg.idn_cast] at h ⊢
  exact (CharP.intCast_eq_zero_iff Cb.Gl.F Cb.Gl.p _).2 ((CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).1 h)

/-- **The kind's two families, at the integers.** -/
theorem own12_of_cells {x : VerifiableInference.Desc.First.Look.Place} {S : Attention.Shape} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {m : (attSg x D rad).Msg} {Z : Zs} (hZ : CellsAre x S tl D rad m Z)
    (h1 : ∀ j b g i, (Idn.at1 j b g i).Valid (dimOf S) → idnVal (dimOf S) (attCells x S tl D rad m) (.at1 j b g i) = 0)
    (h2 : ∀ b g i, (Idn.at2 b g i).Valid (dimOf S) → idnVal (dimOf S) (attCells x S tl D rad m) (.at2 b g i) = 0) :
    (∀ k b g' n, (Idn.at1 k b g' n).Valid (dimOf S) →
        idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Idn.at2 b g' n).Valid (dimOf S) →
        idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) (.at2 b g' n) = 0 := by
  unfold CellsAre at hZ
  rw [hZ] at h1 h2
  exact ⟨fun k b g' n hv => idn_down S Z _ (h1 k b g' n hv), fun b g' n hv => idn_down S Z _ (h2 b g' n hv)⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.idn_down
#print axioms VerifiableInference.Desc.First.Att.P.own12_of_cells
