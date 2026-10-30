-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingExchange.lean: the first chain's closing proximity test
owes no item behind it: its row closes four and opens none. So `ExchangeS` (Thread/PaysS.lean) holds
there, at every `Said`.

  `owes_placeL`      the forward row at the test's place owes nothing
  `exchangeS_at_L`   `ExchangeS` at a border whose place is the test's

By what. The table's row (`backRow`, Johnson/Desc/First/Borders.lean; `rowAt`,
Honest/Thread/FirstRows.lean).

Limits. It says nothing of the four items that the row closes, nor of the items that ride past:
those are `RidesPastS`. Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `exchangeS_at_L` bears this label; the rule is at its home, the head
of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `ThrS` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc.First (ModelPart)
open ProofFile.Honest.K12.AtProof (placeL)

theorem owes_placeL (links : List ModelPart) : (FirstRows.rowAt links placeL).owes = [] := rfl

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **The test owes nothing behind it.** -/
theorem exchangeS_at_L (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : ℕ}
    (hp : L.ps[b]? = some placeL) : ExchangeS L.thread Said b := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  have e : (L.thread.row b).owes = [] := by
    show (FirstRows.rows L.links L.ps b).owes = []
    unfold FirstRows.rows
    rw [hp]
    exact owes_placeL L.links
  rw [e] at hi
  cases hi

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.owes_placeL
#print axioms ProofFile.Honest.K12.exchangeS_at_L
