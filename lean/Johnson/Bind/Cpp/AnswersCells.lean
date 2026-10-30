-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AnswersCells.lean: general in the sizes: the sample map's values on the messages
that hold a matrix of cells (`cellWords`, Johnson/Flat/CodingCells.lean), spelled, are the
out-of-domain (OOD) answers of the committer that runs (Johnson/Bind/Twin.lean), at a table whose
plain entries are these words before the pads and whose pads are read as the pads. Statements and
proofs, by `Bind.Twin.answers_spelled` (Johnson/Bind/TwinAnswers.lean). No hash function is named.
Limits. Values in a field. No binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no correctness of extraction and no index privacy is
stated here. Nothing on any program.

-/
import Johnson.Flat.CodingCells
import Johnson.Bind.TwinAnswers
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open OnBytes.Flat OnBytes.Slice Cb Cb.Ood VerifiableInference

/-- Before the cut an entry does not read the pads. -/
theorem entry_before_cut (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (M : Cells (S.toDecR Z cut) N) (η η' : PadsOf S cut) (b e : ℕ) (he : e < cut) :
    cellEntry S Z cut N M η b e = cellEntry S Z cut N M η' b e := by
  unfold cellEntry cellEntryAt
  rw [if_pos he, if_pos he]

/-- From the cut on an entry is a pad's word. -/
theorem entry_at_pad (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (b k : ℕ) (hb : b < 2 ^ S.P.v)
    (hk : k < S.P.T.l - cut) :
    cellEntry S Z cut N M η b (cut + k) = OnBytes.Slice.ofF (η ⟨b, hb⟩ ⟨k, hk⟩) := by
  have h1 : ¬ cut + k < cut := by omega
  have h2 : b < 2 ^ S.P.v ∧ cut + k - cut < S.P.T.l - cut := ⟨hb, by omega⟩
  unfold cellEntry cellEntryAt
  rw [if_neg h1, dif_pos h2]
  congr 2
  exact Fin.ext (by show cut + k - cut = k; omega)

/-- **General in the sizes.** -/
theorem answers_cells (S : Sz) (cut lg s sigma : ℕ) (N : MatrixNums)
    (hcut : cut = S.P.T.l - 3 * s) (h : 3 * s ≤ S.P.T.l)
    (M : Cells (S.toDecR (recZ S.P.T.l lg s) cut) N) (η : PadsOf S cut) (T : Bind.Twin.Table)
    (hT1 : ∀ b e, e < cut →
      T.entry b e = cellEntry S (recZ S.P.T.l lg s) cut N M (fun _ _ => 0) b e)
    (hT2 : ∀ b k (hb : b < 2 ^ S.P.v) (hk : k < S.P.T.l - cut),
      toF (T.pad b k) = η ⟨b, hb⟩ ⟨k, hk⟩)
    (sd : (recZ S.P.T.l lg s).D) :
    (OnBytes.K.IdTable.spellAns S.P.v s
        ((S.toDecR (recZ S.P.T.l lg s) cut).ix.ZR.val sd
          (honestMsgs S (cellWords S (recZ S.P.T.l lg s) cut N M η)))).map OnBytes.E.triple =
      Bind.Twin.answers ⟨S.P.T.a, S.P.T.l, S.P.T.r, S.P.v, s, sigma⟩ T
        ((OnBytes.K.IdTable.spellSeedL lg s sd).map fun y =>
          (y.1.map OnBytes.E.triple, y.2.triple)) := by
  subst hcut
  exact Bind.Twin.answers_spelled ⟨S.P.T.a, S.P.T.l, S.P.T.r, S.P.v, s, sigma⟩ T lg h sd
    (honestMsgs S (cellWords S (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) N M η))
    (fun b j hb => by
      show algebraMap GF GE (toF ((cellWords S (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) N M η
        (Sz.rowNo (vtx S.P.v b))).getD j.val 0)) = _
      rw [OnBytes.Slice.ProxRun.rowNo_vtx S.P.v b hb,
        cellWords_getD S _ _ N M η b j.val (Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)),
        entry_before_cut S _ _ N M η (fun _ _ => 0) b j.val j.isLt, ← hT1 b j.val j.isLt])
    (fun b a t hb => by
      have ha := a.isLt
      have ht := t.isLt
      have hk : 3 * a.val + t.val < S.P.T.l - (S.P.T.l - 3 * s) := by
        show 3 * a.val + t.val < S.P.T.l - (S.P.T.l - 3 * s)
        have ha' : a.val < s := ha
        omega
      have hl : S.P.T.l - 3 * s + 3 * a.val + t.val < S.P.T.l := by
        have ha' : a.val < s := ha
        omega
      show algebraMap GF GE (toF ((cellWords S (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) N M η
        (Sz.rowNo (vtx S.P.v b))).getD (S.P.T.l - 3 * s + 3 * a.val + t.val) 0)) = _
      rw [OnBytes.Slice.ProxRun.rowNo_vtx S.P.v b hb, cellWords_getD S _ _ N M η b _ hl,
        Nat.add_assoc,
        entry_at_pad S _ _ N M η b _ hb hk, toF_ofF, ← hT2 b _ hb hk])

end Bind.Cpp


#print axioms Bind.Cpp.entry_before_cut
#print axioms Bind.Cpp.entry_at_pad
#print axioms Bind.Cpp.answers_cells
