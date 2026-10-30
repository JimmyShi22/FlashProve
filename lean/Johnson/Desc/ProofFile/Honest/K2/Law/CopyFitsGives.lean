-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyFitsGives.lean: the kind "the code switch" (K2): THE TEST
ON A KEPT COPY GIVES THE PREMISES: where `copyFitsAt id` (Honest/K2/Law/CopyFitsWritten.lean)
accepts, nine public premises of `msgOff_copy_is_senders` (Honest/K2/Law/MsgOffCopy.lean) hold, each
spelt as that law asks it; and by the closed fact it accepts at every kept copy of every written
pair. PUBLIC DATA ALONE. Two statements with their proofs; no definition.

  `copyFits_at`      at a pair of the list, at a kept copy of it: the test accepts
  `copyFits_gives`   where the test accepts: hn₀ · hs · hsk · hell · hm · hpad · hdeg · ha' · hSent

By: `copyFits_written` (CopyFitsWritten.lean): the first · the test's own text, clause by clause:
the second. WHY: the four controls of that file reject at two clauses alone; here each of the nine
clauses is spent for the premise that it is meant for: were one misspelt, this proof would not
close.

Limits. n and the list of kept shapes are written out, where `msgOff_copy_is_senders` has letters
pinned by hnn and hk: a caller lays them in by rfl. THE TEST's LAST TWO CLAUSES ARE NOT SPENT: the
length of what lies between the two links (of hS), the codes' lengths (of hc): hS and hc themselves
are not had here; nor hSz, hw, hn, hl, hi. At the written lists: not carried to the head's own. The
two copies at link 1 stand at no pair. Nothing on the book, the data, the challenges or a run.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyFitsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- **At every kept copy of every written pair the test accepts.** -/
theorem copyFits_at {x : SwitchPlace × SwitchPlace × SegmentPub} (hx : x ∈ copyPairs) {i : Nat}
    (hi : i < x.2.1.sizes.kept.length) : copyFitsAt id x.1 x.2.1 x.2.2 i = true :=
  List.all_eq_true.1 (List.all_eq_true.1 copyFits_written.2.2 x hx) i (List.mem_range.2 hi)

/-- **Where the test accepts, nine premises hold**, each in the form in which
`msgOff_copy_is_senders` asks it. -/
theorem copyFits_gives {p₀ p : SwitchPlace} {S : SegmentPub} {i : Nat}
    (h : copyFitsAt id p₀ p S i = true) :
    (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i) <
        (switchSent p₀.sizes p₀.others).size - 1 ∧
      ((switchSent p₀.sizes p₀.others).getD
        (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i) default).shape =
        ((switchSent p.sizes p.others).getD (1 + i) default).shape ∧
      (((membersOfSeg S true).filter (·.kept)).map (·.shape)).getD i {} =
        ((switchSent p.sizes p.others).getD (1 + i) default).shape ∧
      (S.sizes.codes.base.getD S.sizes.code default).ell = (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell ∧
      0 < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows ∧
      (K1.stepsOf p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape
        none).pad ≤ (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell ∧
      ((VerifiableInference.Desc.K2.Honest.shapeOf (membersOfSeg S true)
          (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)).mainDeg == 3) =
        (((switchSent p₀.sizes p₀.others).getD
          (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)
          default).shape.mainDeg == 3) ∧
      i < (((membersOfSeg S true).filter (·.kept)).map (·.shape)).length ∧
      S.sent.headD #[] = switchSent p₀.sizes p₀.others := by
  unfold copyFitsAt at h
  simp only [id, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, -⟩, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copyFits_at
#print axioms ProofFile.Honest.K2.Law.copyFits_gives
