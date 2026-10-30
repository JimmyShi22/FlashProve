-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/EndSays.lean: K10's LAW's END, IN THE WORDS OF THE TABLE's ITEM "row":
from "each row's vector on the group's cube, against the decoded group's message, gives the row's
target" to "each row says its claim of the words" (`OnBytes.Means.Says`). A definition, statements
and proofs.

Why. K10's law (`k10_block_self` and its like, beside this file) ends in: for every row of `runRows
st G`: the sum over the fold's input code of `rowVec N (begun st g G) lay row j` times the message's
entry is the row's target. The table's item "row" says (FillRow.lean, beside this file): the row
says its claim of the witness's words: a sum over the members' own tables. This file shows that the
first gives the second.
  `tabK N v`: a vector on the fold's input code as a group's three tables (`Means.Tables`): main and
    mask by `tabBack` (Johnson/Desc/K12/Law/RInSays.lean); the kept part of a
    message o at an index i: the sum of v's entries at the slots and places that N names so, at the
    corner 0.
  `sum_cin`: the sum over the fold's input code in its three parts.
  `rowVec_groupValue`: the row's vector against v IS `groupValue` of the row, laid alone by the
    program's `addToGroupRow` (x := 1, on the empty group's row), on `tabK N v`: by the three
    laws of the laying (`addToGroupRow_main`, `_mask`, `_kept`) and `sum_table`
    (Johnson/Desc/K12/Law/ClaimSays.lean).
  `says_of_rowVec`: with `rowMeans_on` (Johnson/Desc/Means/Bridge.lean): if v's tables hold the
    words m on the members' blocks (`LaidOn`), the row says its claim of m.
  `allSay_of_rowVec`: at a statement in order, over the beginning of the test (`says_extends`,
    `extends_begun`): `AllSay rdE st (runRows st G).toList m`: the premise of FillRow.lean's
    `rowSays_of_taken` and of `Holds.of_begun` (Johnson/Desc/Means/Holds.lean).
Limits. (1) `LaidOn (begun st g G) lay m (tabK N v)` IS A PREMISE, AND IT IS THE WHOLE TIE BETWEEN
THE TYPED MESSAGE AND THE WORDS: that the decoded group's message, arranged on the cube, holds at
each member's block that member's own table as the table's one reader reads it off the witness.
Shown of no v and no m here. For words read back off v itself it would hold by make and say nothing
of a witness. (2) The layout's four numbers are the stage's (hk, hh, hl, hz): premises, ON THE BEGUN
STATEMENT's LAYOUT lay. They are not the promise's two equations: these (`K10OnS`) are on the k and
h of THE FRAME's record of the group. What stands between the two is the closing's own test "K10.kh"
(the layout's k and h are the plan's): read, not laid in here. hl and hz say that the two codes'
message lengths are powers of two with the layout's exponents. (3) hN: the slots' names lie within
the statement's tables: a premise on the letter N. (4) The law itself is not called here: no theorem
joins its end to h. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BatTie
import Johnson.Desc.K12.Law.RInSays
import Johnson.Desc.Means.Bridge
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means Cb Johnson.Top.H
open H2K.ClaimSays (sum_table tabBack tabBack_at)

variable {S : Sig GE} {R : RowsK S} (N : SlotNames R)

/-- A vector on the fold's input code, as a group's tables: the cube's part without a slot as the
main table, the mask part as the mask table (the entry at the index J is the vector's at row
J % 2^k, place J / 2^k); the kept part of an oracle message o at the index i: the sum of the
vector's entries at the slots and places that bear these two names, at the corner 0. -/
noncomputable def tabK (v : R.Sh.Cin.J → GE) : Tables GE where
  main := tabBack (R.s.h + R.s.g) R.s.C.l fun x => v (.inl (x.1, (none, x.2)))
  mask := tabBack R.s.h R.s.Z.l fun x => v (.inr x)
  kept := fun o i => ∑ q : R.Kp, ∑ x : R.s.cM.J,
    if N.orc q = o ∧ N.idx q x = i then v (.inl (fun _ => false, (some q, x))) else 0

/-- The sum over the fold's input code, in its three parts. -/
theorem sum_cin (f : R.Sh.Cin.J → GE) :
    ∑ j, f j = (∑ x : (Fin (R.s.h + R.s.g) → Bool) × Fin R.s.C.l, f (.inl (x.1, (none, x.2)))) +
      (∑ b : Fin (R.s.h + R.s.g) → Bool, ∑ q : R.Kp, ∑ x : R.s.cM.J, f (.inl (b, (some q, x)))) +
      ∑ x : (Fin R.s.h → Bool) × Fin R.s.Z.l, f (.inr x) := by
  have h1 : ∑ j, f j = (∑ x : (Fin (R.s.h + R.s.g) → Bool) × (Option R.Kp × R.s.cM.J), f (.inl x)) +
      ∑ x : (Fin R.s.h → Bool) × Fin R.s.Z.l, f (.inr x) := Fintype.sum_sum_type f
  rw [h1]
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  rfl

/-- **A row's vector against a vector on the fold's input code IS the row, laid alone, on that
vector's tables.** T: the statement; L: a layout with the stage's four numbers; Rr: the row laid
alone (x := 1, on the empty group's row). The names of the slots are within the statement's tables.
-/
theorem rowVec_groupValue (T : Statement) (L : GroupLayout) (g : ℕ) (row : OnBytes.Row)
    (Rr : GroupRow) (hlay : addToGroupRow T L row oneE { group := g } = some Rr)
    (hM : MainBlocksOk T L) (hZ : MaskBlocksOk T L) (hf : RowFits T row) (hm : MaskFits T L row)
    (hk : L.k = R.s.h + R.s.g) (hh : L.h = R.s.h) (hl : 2 ^ L.logEll = R.s.C.l)
    (hz : 2 ^ L.logEllZk = R.s.Z.l)
    (hN : ∀ q x, N.orc q < T.oracles.size ∧ N.idx q x < tableSize T (N.orc q) .main)
    (v : R.Sh.Cin.J → GE) :
    ∑ j, rowVec N T L row j * v j = groupValue rdE T L Rr (tabK N v) := by
  have e1 : ∀ J, rdE.val (Rr.c.entry J) = row.mainSum rdE T L oneE J := by
    intro J
    rw [addToGroupRow_main rdE T L hM row hf oneE _ Rr hlay J]
    show rdE.val (({} : Form).entry J) + _ = _
    rw [Form.entry_empty, zero_add]
  have e2 : ∀ J, J < 2 ^ (L.h + L.logEllZk) →
      rdE.val (Rr.d.getD J zeroE) = row.maskSum rdE T L oneE J := by
    intro J hJ
    rw [(addToGroupRow_mask rdE T L hZ row hf hm oneE _ Rr (Or.inl rfl) hlay J hJ).2]
    show rdE.val ((#[] : Array E).getD J zeroE) + _ = _
    simp [rdE.zero]
  have e3 : ∀ o i, keptSum rdE o i Rr.kept.toList =
      keptWeight (K := GE) L o * rdE.val (row.coefficient o .main i) := by
    intro o i
    rw [addToGroupRow_kept rdE T L row hf oneE _ Rr hlay o i, rdE.one, mul_one]
    show keptSum rdE o i ([] : List KeptForm) + _ = _
    simp [keptSum]
  -- the main table
  have hA : (∑ x : (Fin (R.s.h + R.s.g) → Bool) × Fin R.s.C.l,
      rowVec N T L row (.inl (x.1, (none, x.2))) * v (.inl (x.1, (none, x.2)))) =
      ∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)), rdE.val (Rr.c.entry J) * (tabK N v).main J := by
    rw [hk, sum_table _ _ _ hl]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [e1]
    show _ = _ * tabBack (R.s.h + R.s.g) R.s.C.l (fun x => v (.inl (x.1, (none, x.2)))) _
    rw [tabBack_at]
    rfl
  -- the mask table
  have hC : (∑ x : (Fin R.s.h → Bool) × Fin R.s.Z.l, rowVec N T L row (.inr x) * v (.inr x)) =
      ∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        rdE.val (Rr.d.getD J zeroE) * (tabK N v).mask J := by
    have hC' : (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        rdE.val (Rr.d.getD J zeroE) * (tabK N v).mask J) =
        ∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
          row.maskSum rdE T L oneE J * (tabK N v).mask J :=
      Finset.sum_congr rfl fun J hJ => by rw [e2 J (Finset.mem_range.1 hJ)]
    rw [hC', hh, sum_table _ _ _ hz]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = _ * tabBack R.s.h R.s.Z.l (fun x => v (.inr x)) _
    rw [tabBack_at]
    rfl
  -- the kept tables
  have hB : (∑ b : Fin (R.s.h + R.s.g) → Bool, ∑ q : R.Kp, ∑ x : R.s.cM.J,
      rowVec N T L row (.inl (b, (some q, x))) * v (.inl (b, (some q, x)))) =
      ∑ o ∈ Finset.range T.oracles.size, ∑ i ∈ Finset.range (tableSize T o .main),
        keptSum rdE o i Rr.kept.toList * (tabK N v).kept o i := by
    have l1 : (∑ b : Fin (R.s.h + R.s.g) → Bool, ∑ q : R.Kp, ∑ x : R.s.cM.J,
        rowVec N T L row (.inl (b, (some q, x))) * v (.inl (b, (some q, x)))) =
        ∑ q : R.Kp, ∑ x : R.s.cM.J,
          keptWeight (K := GE) L (N.orc q) *
            rdE.val (row.coefficient (N.orc q) .main (N.idx q x)) *
            v (.inl (fun _ => false, (some q, x))) := by
      rw [Finset.sum_eq_single (fun _ => false)]
      · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => ?_
        show (if (fun _ => false : Fin (R.s.h + R.s.g) → Bool) = fun _ => false then _ else 0) * _
          = _
        rw [if_pos rfl]
        rfl
      · intro b _ hb
        refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun x _ => ?_
        show (if b = fun _ => false then _ else 0) * _ = _
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [l1]
    have r1 : ∀ o i, keptSum rdE o i Rr.kept.toList * (tabK N v).kept o i =
        ∑ q : R.Kp, ∑ x : R.s.cM.J, if N.orc q = o ∧ N.idx q x = i then
          keptWeight (K := GE) L (N.orc q) *
            rdE.val (row.coefficient (N.orc q) .main (N.idx q x)) *
            v (.inl (fun _ => false, (some q, x))) else 0 := by
      intro o i
      rw [e3]
      show _ * (∑ q : R.Kp, ∑ x : R.s.cM.J, if N.orc q = o ∧ N.idx q x = i then
        v (.inl (fun _ => false, (some q, x))) else 0) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases c : N.orc q = o ∧ N.idx q x = i
      · rw [if_pos c, if_pos c, c.1, c.2]
      · rw [if_neg c, if_neg c, mul_zero]
    simp only [r1]
    -- the sums over o and i go inside, and pick the slot's own names
    have swap : ∀ (I : Finset ℕ) (Jn : ℕ → Finset ℕ) (Fn : ℕ → ℕ → R.Kp → R.s.cM.J → GE),
        (∑ o ∈ I, ∑ i ∈ Jn o, ∑ q : R.Kp, ∑ x : R.s.cM.J, Fn o i q x) =
        ∑ q : R.Kp, ∑ x : R.s.cM.J, ∑ o ∈ I, ∑ i ∈ Jn o, Fn o i q x := by
      intro I Jn Fn
      have s1 : ∀ o, (∑ i ∈ Jn o, ∑ q : R.Kp, ∑ x : R.s.cM.J, Fn o i q x) =
          ∑ q : R.Kp, ∑ x : R.s.cM.J, ∑ i ∈ Jn o, Fn o i q x := by
        intro o
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
      simp only [s1]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    rw [swap]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨h1, h2⟩ := hN q x
    symm
    rw [Finset.sum_eq_single (N.orc q)]
    · rw [Finset.sum_eq_single (N.idx q x)]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro i _ hi
        rw [if_neg fun c => hi c.2.symm]
      · intro h
        exact absurd (Finset.mem_range.2 h2) h
    · intro o _ ho
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg fun c => ho c.1.symm]
    · intro h
      exact absurd (Finset.mem_range.2 h1) h
  rw [sum_cin, hA, hB, hC]
  unfold groupValue
  ring

/-- **From the law's sum to "the row says"**: at a statement T whose group g is G, with the layout L
that T gives it, a row that has passed the tests, a layout with the stage's four numbers, names
within the tables: if the row's vector against v is the row's target, and v's tables hold the words
m on the members' blocks, the row says its claim of m. -/
theorem says_of_rowVec (T : Statement) (g : ℕ) (G : Group) (L : GroupLayout) (row : OnBytes.Row)
    (hG : T.groups[g]? = some G) (hL : T.layout g = some L) (hOk : GroupOk T G)
    (hr : RowIn T G row)
    (hk : L.k = R.s.h + R.s.g) (hh : L.h = R.s.h) (hl : 2 ^ L.logEll = R.s.C.l)
    (hz : 2 ^ L.logEllZk = R.s.Z.l)
    (hN : ∀ q x, N.orc q < T.oracles.size ∧ N.idx q x < tableSize T (N.orc q) .main)
    (v : R.Sh.Cin.J → GE) (m : Words GE) (hT : LaidOn T L m (tabK N v))
    (h : ∑ j, rowVec N T L row j * v j = readE row.target) : Says rdE T row m := by
  have F := layFacts hG hL hOk
  obtain ⟨Rr, hlay, -, e⟩ := rowMeans_on rdE T g G L row hG hL hOk hr
  refine (e m (tabK N v) hT).1 ?_
  unfold GroupSays
  rw [← rowVec_groupValue N T L g row Rr hlay F.mainOk F.maskOk hr.fits (hr.maskFits F) hk hh hl hz
    hN v, h, addToGroupRow_target rdE T L row oneE _ Rr hlay, rdE.one, mul_one]
  show readE row.target = rdE.val zeroE + rdE.val row.target
  rw [rdE.zero, zero_add]
  rfl

/-- **K10's LAW's END, IN THE TABLE's WORDS.** st: the statement in front of the closing, in order;
G: its group g; lay: the layout of the begun statement. If every row that the test takes in has, on
the cube, its target against v (what the law's end says, at v := the decoded group's message), and
v's tables hold the words m on the members' blocks: ALL ROWS THAT THE TEST TAKES IN SAY THEIR CLAIMS
OF m, AT THE STATEMENT IN FRONT. -/
theorem allSay_of_rowVec (st : Statement) (hI : InOrder st) (g : ℕ) (G : Group)
    (hG : st.groups[g]? = some G) (lay : GroupLayout) (hL : (begun st g G).layout g = some lay)
    (hk : lay.k = R.s.h + R.s.g) (hh : lay.h = R.s.h) (hl : 2 ^ lay.logEll = R.s.C.l)
    (hz : 2 ^ lay.logEllZk = R.s.Z.l)
    (hN : ∀ q x, N.orc q < (begun st g G).oracles.size ∧
      N.idx q x < tableSize (begun st g G) (N.orc q) .main)
    (v : R.Sh.Cin.J → GE) (m : Words GE) (hT : LaidOn (begun st g G) lay m (tabK N v))
    (h : ∀ (i : ℕ) (hi : i < (runRows st G).toList.length),
      ∑ j, rowVec N (begun st g G) lay (runRows st G).toList[i] j * v j =
        readE (runRows st G).toList[i].target) :
    AllSay rdE st (runRows st G).toList m := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  have hG' : (begun st g G).groups[g]? = some { code := G.code, maskCode := G.maskCode
                                                members := G.members, kept := G.kept
                                                inRun := true } := by
    rw [begun_groups, Array.getElem?_modify, if_pos rfl, hG]
    rfl
  have hOk := (hI.begun g G hG).groups g _ hG'
  have hin := hI.runRows g G hG _ hrow
  have hin' := RowIn.extends (G := G) (G' := { code := G.code, maskCode := G.maskCode
                                               members := G.members, kept := G.kept
                                               inRun := true })
    (extends_begun st g G) (fun _ h => h) hin
  exact (says_extends rdE (extends_begun st g G) hin m).1
    (says_of_rowVec N _ g _ lay _ hG' hL hOk hin' hk hh hl hz hN v m hT (h i hi))

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.sum_cin
#print axioms VerifiableInference.Desc.First.Close.rowVec_groupValue
#print axioms VerifiableInference.Desc.First.Close.says_of_rowVec
#print axioms VerifiableInference.Desc.First.Close.allSay_of_rowVec
