-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormLawI.lean: THE PUBLIC ITEMS THAT ARE TIED TO THE OPEN
ITEMS HOLD TOO. The library's promise tests the Bool of every public item of TWO lists: those that
are open at the border by the table of public items, and those that are tied to the items open
there (`pubOfItems`: for one, `formsIn m k r` beside `forms m k r`). `thr_pub`
(Honest/Thread/FormLaw.lean) hands out the first list; here the second: found by the authors of the
rule's lemmas, at the library's `formsIn_of_promise`. General in the first chain's letters.
`thr_pub`'s own proof, at the list's other half.

  `thr_pubI`

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S onAt openSets pubSets pubHeld pubOfItems start)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **EVERY PUBLIC ITEM THAT IS TIED TO AN ITEM OPEN AT THE BORDER HOLDS OF THE STATE**, wherever
the thread holds. -/
theorem thr_pubI (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E)
    {q : VerifiableInference.Desc.First.Pub}
    (hq : q ∈ pubOfItems (((openSets L.links L.ps (start L.links))[b]?).getD [])) :
    L.mgP.pub q (L.pubOf m.st.input.x, s) = true := by
  unfold Thr at hT
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT
  have hf' : s.failed.isNone = true := hf
  have hP' : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hP
  obtain ⟨-, hP2⟩ := hP'
  rcases hP2 with hm | ⟨hB, -⟩
  · exfalso
    have hm' : s.failed ≠ none := hm
    cases hs : s.failed with
    | none => exact hm' hs
    | some e =>
      rw [hs] at hf'
      cases hf'
  · simp only [Bool.and_eq_true] at hB
    obtain ⟨⟨-, hpub⟩, -⟩ := hB
    unfold pubHeld at hpub
    exact List.all_eq_true.1 hpub q (List.mem_append_right _ hq)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.thr_pubI
