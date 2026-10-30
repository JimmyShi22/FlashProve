-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/LedgerMade.lean: WHO MAKES THE TABLE's OWN TWO PUBLIC ITEMS `ledger m` AND
`freeAbove m`: the step that opens a link. Their tests with code (`ledgerB`, `freeAboveB`,
Johnson/Desc/First/FillKeeper.lean) say yes at every state of the verifier whose ledger is the one
from which a sub-proof starts (`emptySlots F n`, Johnson/Desc/First/Walk/FirstQuiet.lean): n slots,
none of them filled. Statements and proofs.

  `ledgerB_empty`, `freeAboveB_empty`: at `t.fork? = some (emptySlots F n)`, whatever F is: so at
    `startFork X n` too, and at the head's link's own term.
  `ledger_opened_lay` | `_layZero` | `_att`, `freeAbove_opened_lay` | `_layZero` | `_att`: behind
    `openLay`, `openLayZero`, `openAtt` (Johnson/Desc/First/Walk/Frame.lean, LinkZero.lean), at the
    step's own number of slots P.ns: by `openLay_ok` and its like.
  **`ledger_made`**, **`freeAbove_made`**: in the form in which the composed public tests ask them:
    `pubAll D base (.ledger m) (z, t) = true`; `pubAll D base (.freeAbove m) (z, t) = true` UNDER
    ONE NAMED PREMISE ON THE PLAN: hn : D.nsOf m = some n.
  `freeAboveB_other`: A NEGATIVE FACT: at another number of slots the test says no.

OBJECT: two tests with code. USER: Johnson/P1K2R/MadeLedger.lean; meant: the premise hMade at the 24
places of kind K2 that open a link. LETTERS: t, F, n, D, base, m, z: free.

Limits. That the state behind a place of kind K2 has such a ledger is the opening step's law: called
here for three steps; for the head's link it is a premise (`placeH2_fork`). hn is a
fact on the plan: not shown here. Nothing on who keeps the two items further on. Nothing on
soundness.
-/
import Johnson.Desc.First.PubAllAt
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LayPar AttPar openLay openLayZero openAtt startFork emptySlots)
open Johnson.Desc.First.Walk.Law (openLay_ok openLayZero_ok openAtt_ok)

/-- At the ledger from which a sub-proof starts the three arrays have as many entries as slots. -/
theorem ledgerB_empty {t : S} {F : Fork} {n : Nat} (h : t.fork? = some (emptySlots F n)) :
    ledgerB t = true := by
  unfold ledgerB
  rw [h]
  simp [emptySlots]

/-- There every slot from the next free number on is free, and it has n slots. -/
theorem freeAboveB_empty {t : S} {F : Fork} {n : Nat} (h : t.fork? = some (emptySlots F n)) :
    freeAboveB n t = true := by
  unfold freeAboveB
  rw [h]
  simp only [Option.any_some, emptySlots, Bool.and_eq_true, List.all_eq_true, beq_self_eq_true,
    and_true]
  intro j hj
  have hlt : F.next + j < n := by
    have := List.mem_range.1 hj
    omega
  simp [Array.getD_eq_getD_getElem?, hlt]

/-- At another number of slots the test says no. -/
theorem freeAboveB_other {t : S} {F : Fork} {n k : Nat} (h : t.fork? = some (emptySlots F n))
    (hk : n ≠ k) : freeAboveB k t = false := by
  unfold freeAboveB
  rw [h]
  simp [emptySlots, hk]

theorem ledger_opened_lay {P : LayPar} {s t : S} (h : openLay P s = .ok t) : ledgerB t = true :=
  ledgerB_empty (openLay_ok h).2.2.2.2.2.2.1

theorem freeAbove_opened_lay {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    freeAboveB P.ns t = true := freeAboveB_empty (openLay_ok h).2.2.2.2.2.2.1

theorem ledger_opened_layZero {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : ledgerB t = true :=
  ledgerB_empty (openLayZero_ok h).2.2.2.2.2.2.1

theorem freeAbove_opened_layZero {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : freeAboveB P.ns t = true :=
  freeAboveB_empty (openLayZero_ok h).2.2.2.2.2.2.1

theorem ledger_opened_att {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : ledgerB t = true :=
  ledgerB_empty (openAtt_ok h).2.2.2.2.2.1

theorem freeAbove_opened_att {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    freeAboveB P.ns t = true := freeAboveB_empty (openAtt_ok h).2.2.2.2.2.1

section
variable {P : Type} (D : PubData) (base : Pub → P × S → Bool)

/-- **`ledger m` is made.** -/
theorem ledger_made (m : Nat) (z : P) {t : S} {F : Fork} {n : Nat}
    (h : t.fork? = some (emptySlots F n)) : pubAll D base (.ledger m) (z, t) = true := by
  rw [pubAll_ledger]
  exact ledgerB_empty h

/-- **`freeAbove m` is made**, where the plan's number of slots of segment m is the ledger's. -/
theorem freeAbove_made (m : Nat) (z : P) {t : S} {F : Fork} {n : Nat}
    (h : t.fork? = some (emptySlots F n)) (hn : D.nsOf m = some n) :
    pubAll D base (.freeAbove m) (z, t) = true := by
  rw [pubAll_freeAbove, hn]
  exact freeAboveB_empty h

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.ledgerB_empty
#print axioms VerifiableInference.Desc.First.freeAboveB_empty
#print axioms VerifiableInference.Desc.First.freeAboveB_other
#print axioms VerifiableInference.Desc.First.ledger_opened_lay
#print axioms VerifiableInference.Desc.First.freeAbove_opened_lay
#print axioms VerifiableInference.Desc.First.ledger_opened_layZero
#print axioms VerifiableInference.Desc.First.freeAbove_opened_layZero
#print axioms VerifiableInference.Desc.First.ledger_opened_att
#print axioms VerifiableInference.Desc.First.freeAbove_opened_att
#print axioms VerifiableInference.Desc.First.ledger_made
#print axioms VerifiableInference.Desc.First.freeAbove_made
