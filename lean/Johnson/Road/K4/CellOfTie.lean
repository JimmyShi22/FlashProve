-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CellOfTie.lean: "THE COMMITTED CELL OF THE READS IS ITS STATED FUNCTION", AT A
LAYERS' SEGMENT, OUT OF THE APPROXIMATE RANGE PROOF's TIE. The exchange of the table of joints'
items "forms" and "formsT" across a segment's second sending (formsTQ_of_formsQ,
Johnson/Desc/Sound/FormsT.lean) asks one thing of weight (its premise hcell): at each cell that a
form names, the data read behind the sending are the stated data in front. At the array of the
reads, at a letter St with StatedAt (Johnson/Road/K4/FillStated.lean), the stated data are
entryTrue: the owning table's sum over the matrices M. The tie (TieOf,
Johnson/Desc/First/K8/LawItems.lean), third clause, says of a table of cells A: entry pos of row 0
of the reads is that sum over THE small integers behind the committed symbols (cellA,
Johnson/Meaning/PlanesTieK8Cells.lean: tie_named).

  `gl_is`: the reading in entryTrue is the library's Reading.gl.
  `saysOf_cellA`: the tie's third clause, in the words of saysOf.
  `entryTrue_of_tie`: at an owned place of row 0: entryTrue is the tie's cell.
  `cell_of_tie`: THE EQUATION OF hcell at one entry.
The argument is from a text on paper (not in this library); typed here. No table need
lie apart from another: the tie speaks of every table of the list that has the place, so whichever
owner entryTrue has chosen, its sum is the one cell. The number of columns K3 drops out at row 0.
Limits. PREMISES of cell_of_tie, none paid here: X: StatedAt in front of the sending · T: the tie at
the approximate range proof's structure tl' behind it, at the table of cells A · hfun: the closed
structure's list of tables is what K4 has heard (o.funs) · htab: StatedAt's tl (meant: the public
parameters') and the closed structure number the places alike · hu3: the closed structure's number
of the reads is K4's · hA: BELOW n A's row 0 of the reads is the data's cell behind the sending ·
hM: INSIDE THE RANGES the matrices M are cellA at A · the entry has row 0, a place below n (hi) and
an owner among o.funs (hown: for the entries that K4's two runs name: back_owned and its kin,
Johnson/Road/K4/OwnedForms.lean, under premises on what the lookup has heard: not called here):
WITHOUT AN OWNER THE STATED CELL IS 0 AND THE EQUATION WOULD ASK THAT THE COMMITTED CELL IS 0. No
chance stands in it. The entries of other arrays are not treated. Met through Lean at no member.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED: K4's row spends formsT; this serves the
row of the second sending. Nothing on soundness.


-/
import Johnson.Road.K4.FillStated
import Johnson.Road.K4.EntryCells
import Johnson.Meaning.PlanesTieK8Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8 (TieOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ Stated)
open Meaning.Reads (cellA cellZ tie_named)

/-- The reading in entryTrue is the library's. -/
theorem gl_is : OnBytes.Desc.First.P1.gl = Reading.gl := rfl

/-- The tie's third clause, in the words of saysOf. -/
theorem saysOf_cellA {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (T : TieOf tl A) {Fn : HFun}
    (hF : Fn ∈ tl.funs) {c sg pos : ℕ} (hp : tl.tabAt Fn c sg = some pos) :
    A (u3Of tl) 0 pos = saysOf Reading.gl (cellA tl A) Fn c sg := by
  obtain ⟨n, hn, e⟩ := Array.mem_iff_getElem.mp hF
  have hn' : tl.funs[n]? = some Fn := by rw [Array.getElem?_eq_getElem hn, e]
  exact (tie_named T).2.2 n Fn hn' c sg pos hp

/-- At an owned place of row 0 entryTrue is the tie's cell. -/
theorem entryTrue_of_tie {tl tl' : HTailF2} {o : Own} {A : ℕ → ℕ → ℕ → Cb.Gl.E} {M : Mats Cb.Gl.E}
    (T : TieOf tl' A) (hfun : tl'.funs = o.funs)
    (htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) (hM : InRange tl' M (cellA tl' A))
    {i : ℕ} (hown : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some i) :
    entryTrue tl o M o.v.iU3 0 i = A (u3Of tl') 0 i := by
  classical
  have hx : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧
      tl.tabAt x.1 x.2.1 x.2.2 = some (0 * o.v.K3 + i) := by
    rw [Nat.zero_mul, Nat.zero_add]
    exact hown
  show (if o.v.iU3 = o.v.iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧
        tl.tabAt x.1 x.2.1 x.2.2 = some (0 * o.v.K3 + i)
     then saysOf OnBytes.Desc.First.P1.gl M h.choose.1 h.choose.2.1 h.choose.2.2 else 0)
    else 0) = _
  rw [if_pos rfl, dif_pos hx]
  obtain ⟨h1, h2⟩ := hx.choose_spec
  have h3 : tl'.tabAt hx.choose.1 hx.choose.2.1 hx.choose.2.2 = some i := by
    rw [← htab]
    exact h2.trans (congrArg some (by rw [Nat.zero_mul, Nat.zero_add]))
  have h4 : hx.choose.1 ∈ tl'.funs := by
    rw [hfun]
    exact h1
  rw [saysOf_cellA T h4 h3, gl_is]
  exact saysOf_cells Reading.gl hM h3

/-- **THE EQUATION OF hcell AT ONE ENTRY OF THE READS**, under X T hfun htab hu3 hA hM hi hown. -/
theorem cell_of_tie {St : Stated} {Mq : S → Bound GQ → Mats GQ} {s : S} {tl : HTailF2} {o : Own}
    {c : ℕ × String} {n : ℕ} {D D' : Bound GQ} {tl' : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (X : StatedAt St Mq s tl o c n D) (T : TieOf tl' A) (hfun : tl'.funs = o.funs)
    (htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) (hu3 : u3Of tl' = o.v.iU3)
    (hA : ∀ i, i < n → A o.v.iU3 0 i = D'.cell c.1 c.2 0 i)
    (hM : InRange tl' (Mq s D) (cellA tl' A))
    {i : ℕ} (hi : i < n)
    (hown : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some i) :
    D'.cell c.1 c.2 0 i = (St.at1 s D).cell c.1 c.2 0 i := by
  rw [X.cell i hi, entryTrue_of_tie T hfun htab hM hown, hu3, hA i hi]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gl_is
#print axioms OnBytes.Road.K4.saysOf_cellA
#print axioms OnBytes.Road.K4.entryTrue_of_tie
#print axioms OnBytes.Road.K4.cell_of_tie
