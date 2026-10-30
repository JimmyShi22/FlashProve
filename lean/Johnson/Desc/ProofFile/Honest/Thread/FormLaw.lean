-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormLaw.lean: what the first chain's invariant gives of the
table's public items. The first chain's `Thread` (Honest/Thread/First.lean) has as its public form
the library's promise at the border (`onAt`, Johnson/Desc/First/Borders.lean) and "no mark". The
promise asks, of a verifier's state without a mark, every public item that is open at the border
(`pubHeld`). So at every state at which the invariant holds, each public item that is open there has
its Bool true of the verifier's state. A kind's author who needs a flag or a size of the state
before a sub-protocol looks first whether a public item that is open there says it: then no clause
of `rides` and no hypothesis is needed. One lemma, general in the first chain's parameters.

  `thr_pub`   the lemma

Limits.
  * Which public items are open at a border is the table's matter (`pubSets`): an evaluation at
    written lists.
  * What an item's Bool is depends on the parameter `pub` of the `Meaning`.
  * It is none of the library's goals.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S onAt openSets pubSets pubHeld start)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **Every public item that is open at the border holds of the state**, wherever the invariant
holds. -/
theorem thr_pub (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E)
    {q : VerifiableInference.Desc.First.Pub}
    (hq : q ∈ ((pubSets L.mgP.more L.links L.ps)[b]?).getD []) :
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
    exact List.all_eq_true.1 hpub q (List.mem_append_left _ hq)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.thr_pub
