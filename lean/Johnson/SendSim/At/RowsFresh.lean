-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/RowsFresh.lean: under the four public premises of rowsExact, if the book's
entries that concern one address p are within the sender's number of coins and p is clear
(SpenderClear), the coins of the honest sender that p spends are uniform and independent of what the
sender discloses together with the coins known at p. It claims no property of the protocol: not
hiding, not zero knowledge. The proof of Spec.rowsFresh.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves.
  rowsFresh   For all P, first, ride, data, challenges, queried positions, every book and order, the
              owner's address o and one address p, under six public premises. (1) The job fits its
              place (sendFits). (2) The challenge consists of exactly the seeds (seedsFit). (3) No
              seed's factor is 0 in the field. (4) The queried positions are within the bound
              (budAt). (5) The entries by which p spends and the known entries are within the
              sender's number of coins (WithinAt). (6) p is clear (SpenderClear;
              Johnson/SendSim/At/Fresh.lean, "clear"). Then, over the sender's uniform coins, the
              tuple (the runs that p spends, shownR, the known runs) has the distribution in which
              the runs that p spends are replaced by fresh uniform values, independent of the rest.

Limits.
  - None of the six premises is proved here for the release's files or at any book. That a book of
    the release is clear in the strict form (`SpenderClear`, `BookClear`) is proved in no file of
    this folder. Where each premise is proved: the table of premises in Johnson/SendSim/Defs.lean.
  - It speaks of one owner's runs at one spender. Of the runs of two owners together it says nothing
    (Johnson/SendSim/At/Fresh.lean, "Two owners").
  - It speaks of what the sender itself discloses and of the known runs, and of nothing that a later
    part makes of the spent coins.
  - A table of more than one row that is sent along is excluded by a clause of SpenderClear. The
    wider form admits it: rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean).
  - The limits of the folder, in short (in full: Johnson/SendSim/Defs.lean). The theorem is about
    sub-protocols of the kind K1 alone; K2 and K12 send tables too. The honest sender is a
    definition in Lean, connected with no program. Nothing is hashed, and challenges and queried
    positions are fixed in advance. The data are a free variable, connected with the weights by no
    theorem. The premises are public. Each statement is of one execution: one proof of one request.
    It is not one of the release's goal statements.

How it fits. The statement is in Johnson/SendSim/At/CutTie.lean. The proof is one line from four
theorems: rowsFresh_of_core (Johnson/SendSim/At/JoinRows.lean), the model's sendFresh
(Johnson/SendSim/CoreProofs.lean), readUnif (Johnson/SendSim/At/ReadUnif.lean) and spentUnif
(Johnson/SendSim/At/SpentUnif.lean). Johnson/SendSim/At/FreshAtMember.lean carries it to every
Seated side.
-/
import Johnson.SendSim.CoreProofs
import Johnson.SendSim.At.ReadUnif
import Johnson.SendSim.At.SpentUnif
import Johnson.SendSim.At.JoinRows

set_option autoImplicit false

namespace OnBytes.SendSim.At

/-- Under the six premises of Spec.rowsFresh, over the honest sender's uniform coins, the runs that
the address p spends are uniform and independent of what the sender discloses together with the
runs known at p. -/
theorem rowsFresh : Spec.rowsFresh := rowsFresh_of_core sendFresh readUnif spentUnif

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rowsFresh
