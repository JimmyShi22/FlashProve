-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormLawP.lean: WHAT THE FIRST CHAIN's THREAD GIVES OF THE
STATE FOR NOTHING, SECOND PIECE: WHAT EACH OPEN PUBLIC ITEM SAYS BESIDE ITS Bool. `thr_pub`
(Honest/Thread/FormLaw.lean) hands out the Bools of the public items that are open at a border. The
library's promise (`onAt`, Johnson/Desc/First/Borders.lean) has a last clause: for each open public
item the sentence `Meaning.pubP`. Here that clause, by the same proof. Part 4's find: in front of
the head's own rounds the item "left" says there, as an equation, where the ledger's next free slot
stands. A file of its own, so that FormLaw.lean keeps its bytes. General in the first chain's
letters.

  `thr_pubP`

Limits. Which items are open at a border, and what an item's sentence says at a filling, are other
files'. Part 4 types a lemma that hands out all the promise's clauses at once (for Honest/Small/):
when it lies this one is a corollary of it. None is one of the library's goals. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (S onAt openSets pubSets start)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **WHAT EACH PUBLIC ITEM THAT IS OPEN AT THE BORDER SAYS BESIDE ITS Bool HOLDS OF THE STATE**,
wherever the thread holds. -/
theorem thr_pubP (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E)
    {q : VerifiableInference.Desc.First.Pub}
    (hq : q ∈ ((pubSets L.mgP.more L.links L.ps)[b]?).getD []) :
    L.mgP.pubP q (L.pubOf m.st.input.x, s) := by
  unfold Thr at hT
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT
  have hf' : s.failed.isNone = true := hf
  have hP' : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hP
  obtain ⟨-, hP2⟩ := hP'
  rcases hP2 with hm | ⟨-, -, -, hpp⟩
  · exfalso
    have hm' : s.failed ≠ none := hm
    cases hs : s.failed with
    | none => exact hm' hs
    | some e =>
      rw [hs] at hf'
      cases hf'
  · exact hpp q hq

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.thr_pubP
