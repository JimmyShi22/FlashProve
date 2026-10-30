-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskAllCopy.lean: behind a yes of the one term of Johnson/RunOne/AskAll.lean
(verifyAllAskSmall), what its part "join 2" has tested: the parsed leaf file's own copy of the first
table is the table in the parsed key file. A proof.

No soundness: a test. This module states laws on the term verifyAllAskSmall, which has the value of
verifyAllAskRun (verifyAllAskRun_eq, AskAllLaws.lean), the form whose tests the runs of lean/Ask/
make one by one (tellAll); that a run's answer is that value is in part by a reading of two texts
(that file's head). It states nothing on soundness.

Main name.
  verifyAllAskSmall_join2: if verifyAllAskSmall H U G = true, then rdKeyHead returns a pair K of the
    parsed key file, rdLeaf returns a value L of the parsed leaf file, and K.1 = L.root0 and
    K.2 = L.answers0.

Limits. No check judges at that copy: see the head of AskAll.lean. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskAllLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.All
open OnBytes OnBytes.Maker
open OnBytes.ShellOf.EntryParsed (rdLeaf rdKeyHead)

/-- **What "join 2" has tested, behind a yes.** -/
theorem verifyAllAskSmall_join2 (H : ByteArray → ByteArray) (U : User) (G : Given)
    (h : verifyAllAskSmall H U G = true) :
    ∃ K L, rdKeyHead G.key = some K ∧ rdLeaf G.leaf = some L ∧ K.1 = L.root0 ∧
      K.2 = L.answers0 := by
  unfold verifyAllAskSmall testsWith at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, _, h6, _⟩ := h
  cases hK : rdKeyHead G.key with
  | none =>
    rw [hK] at h6
    exact (Bool.false_ne_true h6).elim
  | some K =>
    cases hL : rdLeaf G.leaf with
    | none =>
      rw [hK, hL] at h6
      exact (Bool.false_ne_true h6).elim
    | some L =>
      rw [hK, hL] at h6
      have e6 : (decide (K.1 = L.root0) && decide (K.2 = L.answers0)) = true := h6
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at e6
      exact ⟨K, L, rfl, rfl, e6.1, e6.2⟩

end Johnson.RunOne.Ask.All

#print axioms Johnson.RunOne.Ask.All.verifyAllAskSmall_join2
