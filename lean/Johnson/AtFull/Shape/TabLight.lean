-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TabLight.lean: THE TABLE OF STEPS ON SHAPES (`TabL.cells`, TabLetters.lean)
WITH THE LIGHT STEPS LAID IN AT TWO KINDS OF CELLS OF THE LINKS 0 TO 23: `cellsH hint L`; AND THE
TIE: `cellsH_eq`: THE LIGHT CELLS ARE THE TABLE's, AT EVERY HINT, UNDER ONE PREMISE, WHICH
`hpad_of_public` PAYS AT WHAT publicOfO RETURNS. Four definitions, four theorems. General in the
letters L; nothing is evaluated.

Purpose. Lean's kernel bears the table's own steps at a link's closing and at an attention link's
batching only at a high price or not at all (timed trials; not shown here). Second texts that are
equal to them stand in files of their own. Here they are laid into the table once, for all links, so
that a closed fact on a run over the light cells speaks of the run over the table's.

The two kinds of cells (n = 14 l + j + 1, l < 24: these are the numbers 1 to 336; the code says it
from the other side: at n = 0 and from 337 on the cell is the table's).
* j = 11, the closing: `closeGFH.1 (hint l) Q` (CloseHint.lean) for closeGF Q. hint l: the runs of
  the list that the closing of link l leaves sorted: a letter; no premise hangs on it.
* j = 8 at an odd l, an attention link's batching: `batchGSL.1` (batchGS with the adding by
  AddLight.lean's addListL: made here, by Lean) over `gAtt A lm`: the rows' steps of
  RowsAttLight.lean's made rows, and eqRunGO (K8AllOr.lean) at "K8.equations". The plan A is
  L.XG.A[l / 2]: the attention links are the odd ones, and link 2 g + 1 has the plan of group g: as
  in the table's own cell.

Every other cell, and every cell's test on values, is the table's. Where a cell's numbers are
lacking, the light cell is the table's cell.

Main names.
* `batchGSL`: a pair: the made function and its tie. `gAtt`, **`gAtt_eq`** (under the padding key's
  test at the plan).
* `cellsH`, `shapeH hint L`: the frame's letters over the light cells. **`cellsH_eq`**, `shapeH_eq`.
* **`hpad_of_public`**: publicOfO OnBytes.secondHashFunction pol KL lay = .ok X and X.A[g]? = some A ⊢
  P.padKeyOk (P.parCOf A).geo = true: by `H2K5.Row.padKeyOk_ofPlan`
  (Johnson/Desc/First/Att/Row/K5PadKeyOk.lean), `K5Law.public_ofPlan` (Att/Claims/OfPlan.lean) and
  `publicOfO_older` (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).

Limits. EQUATIONS OF TERMS; ONE UNDER A PREMISE. batchGSL's second text can be read nowhere here:
`#print` shows it. The layers' links' batchings, the head's link and the five members behind are the
table's own: nothing is lightened there. hpad is asked at every g; the cells spend it at g = l / 2
for odd l < 24 alone (hpad_of_public pays all). shapeH_eq has no caller: JoinPieces.lean draws the
same from cellsH_eq and runFrom_congr. What any cell costs is not said. Nothing says that a step
returns. At the format's second hash function (hpad_of_public). Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.LettersRun
import Johnson.AtFull.Shape.RowsAttLight
import Johnson.AtFull.Shape.K8AllOr
import Johnson.AtFull.Shape.CloseHint
import Johnson.Desc.First.Batch.Shape.AddLight
import Johnson.Desc.First.Att.Row.K5PadKeyOk
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K9 (testsWhere)
open VerifiableInference.Desc.K9.Shape
open ProofFile.Honest.K10.YesFree
open IM (subAt)

/-- batchGS with the adding's second text (AddLight.lean: addListS_eq). The first field is made by
Lean: the closing rfl fills it. The second field is the tie. -/
def batchGSL : { f : Nat → VerifiableInference.Desc.K9.SegSort →
      (Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)) →
      List (Nat × String) → ChainSh → Except String ChainSh //
    ∀ rows k g order a, batchGS rows k g order a = f rows k g order a } :=
  ⟨_, fun rows k g order a => by
    delta batchGS batchG addsG laidG
    simp -zeta only [addListS_eq]
    rfl⟩

/-- The steps of an attention link's ten rows: the made rows', and eqRunGO at "K8.equations". -/
def gAtt (A : Attention.Plan) (lm : Nat) (o : Nat × String) :
    Nat → ChainSh → Except String (List ClaimSh × ChainSh) :=
  if o == (4, "K8.equations") then VerifiableInference.Desc.First.K8.Honest.eqRunGO
  else (tabOf (rowsAttL.1 A lm) o).g

/-- **They are the table's rows' steps**, where the padding key's test accepts. -/
theorem gAtt_eq (A : Attention.Plan) (lm : Nat) (h : P.padKeyOk (P.parCOf A).geo = true) :
    gAtt A lm = fun o => (tabOf (rowsAtt A lm) o).g := by
  funext o
  unfold gAtt
  rw [← rowsAttL.2 A lm h]
  by_cases e : o = (4, "K8.equations")
  · subst e
    rw [if_pos (by decide)]
    funext n a
    exact (VerifiableInference.Desc.First.K8.Honest.eqRunG_eqO n a).symm
  · rw [if_neg (by simpa using e)]

/-- **THE TABLE's CELLS WITH THE LIGHT STEPS**: at the links 0 to 23: at a link's closing closeGFH
at the link's hint; at an attention link's batching batchGSL over gAtt; every other cell, and every
test on values, is the table's. -/
def cellsH (hint : Nat → List (Nat × Nat)) (L : TabLetters) (n : Nat) : Cell :=
  if n = 0 ∨ 337 ≤ n then TabL.cells L n
  else
    let l := (n - 1) / 14
    let j := (n - 1) % 14
    if j = 11 then
      match L.close l with
      | some Q => (optE (closeGFH.1 (hint l) Q), (TabL.cells L n).2)
      | none => TabL.cells L n
    else if j = 8 ∧ l % 2 = 1 then
      match L.k9 l, testsWhere L.XZ l 0, L.XG.A[l / 2]?,
          VerifiableInference.Desc.First.Look.placeAt L.XG l false with
      | some p, some w, some A, some q =>
        (liftQ (batchGSL.1 p.rows w.1 (gAtt A q.lm)
          (VerifiableInference.Desc.First.orderOf (subAt l))), (TabL.cells L n).2)
      | _, _, _, _ => TabL.cells L n
    else TabL.cells L n

/-- The frame's letters over the light cells. -/
abbrev shapeH (hint : Nat → List (Nat × Nat)) (L : TabLetters) : ProofFile.Honest.Shape S :=
  firstZA (fun n => (cellsH hint L n).1) fun n => (cellsH hint L n).2

/-- **THE TIE: THE LIGHT CELLS ARE THE TABLE's**, at every hint, where the padding key's test
accepts at each attention plan. -/
theorem cellsH_eq (hint : Nat → List (Nat × Nat)) (L : TabLetters)
    (hpad : ∀ (g : Nat) (A : Attention.Plan), L.XG.A[g]? = some A →
      P.padKeyOk (P.parCOf A).geo = true) (n : Nat) :
    cellsH hint L n = TabL.cells L n := by
  unfold cellsH
  by_cases h0 : n = 0 ∨ 337 ≤ n
  · rw [if_pos h0]
  rw [if_neg h0]
  obtain ⟨l, j, hl, hj, rfl⟩ : ∃ l j, l < 24 ∧ j < 14 ∧ n = 14 * l + j + 1 :=
    ⟨(n - 1) / 14, (n - 1) % 14, by omega, by omega, by omega⟩
  have el : (14 * l + j + 1 - 1) / 14 = l := by omega
  have ej : (14 * l + j + 1 - 1) % 14 = j := by omega
  have ec : TabL.cells L (14 * l + j + 1) = (TabL.linkRow L l).at j := table_link _ _ _ _ l j hl hj
  simp only [el, ej]
  by_cases h11 : j = 11
  · subst h11
    have e11 : (TabL.linkRow L l).at 11 = TabL.close L l := rfl
    rw [if_pos rfl, ec, e11]
    unfold TabL.close
    cases hQ : L.close l with
    | none => rfl
    | some Q =>
      have e : closeGFH.1 (hint l) Q = closeGF Q := funext fun x => (closeGFH.2 (hint l) Q x).symm
      simp only [e]
  rw [if_neg h11]
  by_cases h8 : j = 8 ∧ l % 2 = 1
  · obtain ⟨rfl, ho⟩ := h8
    have e8 : (TabL.linkRow L l).at 8 = TabL.batch L l := rfl
    rw [if_pos ⟨rfl, ho⟩, ec, e8]
    unfold TabL.batch
    cases h1 : L.k9 l with
    | none => rfl
    | some p =>
      cases h2 : testsWhere L.XZ l 0 with
      | none => rfl
      | some w =>
        have n24 : (l == 24) = false := by simpa using (by omega : l ≠ 24)
        have nev : (l % 2 == 0) = false := by simpa using (by omega : l % 2 ≠ 0)
        cases h3 : L.XG.A[l / 2]? with
        | none => simp [n24, nev]
        | some A =>
          cases h4 : VerifiableInference.Desc.First.Look.placeAt L.XG l false with
          | none => simp [n24, nev]
          | some q =>
            have e : batchGSL.1 p.rows w.1 (gAtt A q.lm)
                (VerifiableInference.Desc.First.orderOf (subAt l)) =
                batchGS p.rows w.1 (fun o => (tabOf (rowsAtt A q.lm) o).g)
                  (VerifiableInference.Desc.First.orderOf (subAt l)) := by
              rw [gAtt_eq A q.lm (hpad _ A h3)]
              exact funext fun a => (batchGSL.2 _ _ _ _ a).symm
            simp only [n24, nev, e]
            rfl
  · rw [if_neg h8]

/-- **So the frame's letters over the light cells are those over the table's second text.** -/
theorem shapeH_eq (hint : Nat → List (Nat × Nat)) (L : TabLetters)
    (hpad : ∀ (g : Nat) (A : Attention.Plan), L.XG.A[g]? = some A →
      P.padKeyOk (P.parCOf A).geo = true) :
    shapeH hint L = shapeL L := by
  have e : cellsH hint L = TabL.cells L := funext (cellsH_eq hint L hpad)
  unfold shapeH shapeL
  rw [e]

/-- **WHO PAYS THE PREMISE**: at a public record that publicOfO returns at the format's second
hash function, the padding key's test accepts at every attention plan. Three laws of the library; no
evaluation. -/
theorem hpad_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (hX : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL lay = .ok X) (g : Nat)
    (A : Attention.Plan) (hA : X.A[g]? = some A) : P.padKeyOk (P.parCOf A).geo = true :=
  H2K5.Row.padKeyOk_ofPlan (K5Law.public_ofPlan
    ((VerifiableInference.PlanWritten.publicOfO_older pol KL lay).symm.trans hX) g A hA)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.batchGSL
#print axioms Johnson.AtFull.Shape.gAtt
#print axioms Johnson.AtFull.Shape.gAtt_eq
#print axioms Johnson.AtFull.Shape.cellsH
#print axioms Johnson.AtFull.Shape.shapeH
#print axioms Johnson.AtFull.Shape.cellsH_eq
#print axioms Johnson.AtFull.Shape.shapeH_eq
#print axioms Johnson.AtFull.Shape.hpad_of_public
