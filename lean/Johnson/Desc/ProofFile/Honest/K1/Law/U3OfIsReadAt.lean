-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/U3OfIsReadAt.lean: ON THE ROAD TO THE
ITEM "tie m" AT AN ATTENTION's SEGMENT: THE BRIDGE BETWEEN TWO SPELLINGS OF ONE READING. Two
statements and their proofs. No definition. No premise.

  elemsOf_is_partLength   a table's number of entries: attention's elemsOf at the sizes of mats is
                          the smallness test's partLength at parOfMats mats, at funBack F
  u3Of_is_readAt          u3Of (sizesOf mats) (fun a r c => ofInt (cell a r c)) funs n = readAt
                          (parOfMats mats) (funs.map funBack).toList cell n, at all mats, cells,
                          tables and n

WHY. The filler's maker at an attention's segment lays u3Of (Johnson/Desc/K5/Honest/U3.lean) at the
tables that tablesP returns (attention's house's attVals_vec,
Johnson/Desc/ProofFile/Honest/K5/Law/AttValsVec.lean); our form of the second family of "tie m",
TieReadsS, and the public form VecPlanS speak by readAt (Johnson/Desc/K8/Honest/Arrays.lean) at all
25 segments. Attention's house, […], […]: "WE HAVE IT NOT, AND WE LEAVE IT TO


THE TWO TEXTS: both take the first table with start ≤ n < start + (columns times blocks), one in an
array, the other in a list; both read block (n - start) % blocks and column (n - start) / blocks;
both fold addE over range len of weight times the cell's image; both answer 0 where no table holds
n.

Limits. THE CELLS ARE BOUND AND READ ON BOTH SIDES, AT ALL CELLS: an identity of two texts of one
function. Nothing is said of a seat, a message, a Script, a state, or of what is committed or sent.
It stands over files that are in no seal (U3Rows.lean, Reads.lean). Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K5.Honest.Law.U3Law
import Johnson.Desc.K8.Honest.Arrays
import Johnson.Desc.First.Att.TabsBack
import Johnson.HonestTrace.U3Rows
import Johnson.HonestTrace.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Att (funBack)
open VerifiableInference.Desc.First.K8.Honest (CellsAt partLength readOf readAt)
open OnBytes.HonestTrace (parOfMats parFits_parOfMats)
open OnBytes.HonestTrace.U3 (sizesOf)
open H2K5.Honest (u3Of entryOf blocksOf)

/-- A table's number of entries, by attention's spelling and by the smallness test's. -/
theorem elemsOf_is_partLength (mats : Array TMat) (F : First.Att.P.Fun1) :
    H2K5.Honest.elemsOf (sizesOf mats) F = partLength (parOfMats mats) (funBack F) := by
  have hsz : (sizesOf mats).getD F.mat (0, 0) = ((mats.getD F.mat {}).m, (mats.getD F.mat {}).k) :=
    H2K5.Honest.U3Law.matsOf_getD mats F.mat
  unfold H2K5.Honest.elemsOf blocksOf partLength
  rw [hsz, (parFits_parOfMats mats).ks, (parFits_parOfMats mats).ms]
  rfl

/-- **ATTENTION's OWN READING OF AN ENTRY OF THE VECTOR OF READS IS THE SMALLNESS TEST's readAt**:
two spellings of one sum: the first table in whose stretch n lies; the same block and column; the
sum over the block's rows of weight times cell. AT ALL CELLS: an identity of two texts of one
function of the cells. No premise. -/
theorem u3Of_is_readAt (mats : Array TMat) (cell : CellsAt) (funs : Array First.Att.P.Fun1)
    (n : ℕ) :
    u3Of (sizesOf mats) (fun a r c => ofInt (cell a r c)) funs n =
      readAt (parOfMats mats) (funs.map funBack).toList cell n := by
  have hp : ((fun f : HFun => decide (f.start ≤ n) &&
        decide (n < f.start + partLength (parOfMats mats) f)) ∘ funBack) =
      fun F : First.Att.P.Fun1 => decide (F.start ≤ n) &&
        decide (n < F.start + H2K5.Honest.elemsOf (sizesOf mats) F) := by
    funext F
    show (decide (F.start ≤ n) && decide (n < F.start + partLength (parOfMats mats) (funBack F))) =
      _
    rw [elemsOf_is_partLength]
  have hfind : (funs.map funBack).toList.find? (fun f : HFun => decide (f.start ≤ n) &&
        decide (n < f.start + partLength (parOfMats mats) f)) =
      (funs.find? fun F : First.Att.P.Fun1 => decide (F.start ≤ n) &&
        decide (n < F.start + H2K5.Honest.elemsOf (sizesOf mats) F)).map funBack := by
    rw [Array.toList_map, List.find?_map, Array.find?_toList, hp]
  unfold u3Of readAt
  rw [hfind]
  cases funs.find? (fun F : First.Att.P.Fun1 => decide (F.start ≤ n) &&
      decide (n < F.start + H2K5.Honest.elemsOf (sizesOf mats) F)) with
  | none => rfl
  | some F =>
    have hsz : (sizesOf mats).getD F.mat (0, 0) =
        ((mats.getD F.mat {}).m, (mats.getD F.mat {}).k) :=
      H2K5.Honest.U3Law.matsOf_getD mats F.mat
    have hnb : blocksOf (sizesOf mats) F = (parOfMats mats).ms.getD (funBack F).mat 0 /
        (funBack F).len := by
      unfold blocksOf
      rw [hsz, (parFits_parOfMats mats).ms]
      rfl
    show entryOf (sizesOf mats) (fun a r c => ofInt (cell a r c)) F (n - F.start) =
      readOf (funBack F) cell
        ((n - (funBack F).start) / ((parOfMats mats).ms.getD (funBack F).mat 0 / (funBack F).len))
        ((n - (funBack F).start) % ((parOfMats mats).ms.getD (funBack F).mat 0 / (funBack F).len))
    rw [← hnb]
    rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.elemsOf_is_partLength
#print axioms ProofFile.Honest.K1.u3Of_is_readAt
