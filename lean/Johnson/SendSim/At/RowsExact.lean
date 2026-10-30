-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/RowsExact.lean: under four public premises on the job, the challenge and the
queried positions, what the honest sender discloses in its two rounds has the same distribution for
any two data. It claims no property of the protocol: not hiding, not zero knowledge. The proof of
Spec.rowsExact.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves.
  rowsExact   For all public parameters P, first and ride, all challenges and all queried positions:
              if the job fits its place (sendFits), the challenge consists of exactly the seeds
              (seedsFit), no seed's factor is 0 in the field, and for each oracle message in a tree
              the queried positions are within the bound (budAt), then the distribution of shownR,
              over the sender's uniform coins, is the same for any two data. shownR is the columns
              of the sender's trees at the queried positions, and its answers; that the sender at a
              Seated side discloses it is showsAt (Johnson/SendSim/At/Shows.lean).

Limits.
  - None of the four premises is proved here for the release's files. Where each is proved: the
    table of premises in Johnson/SendSim/Defs.lean.
  - It speaks of what the sender itself discloses and of nothing after it: of no coin that a later
    part is given. For that see rowsFresh (Johnson/SendSim/At/RowsFresh.lean).
  - exact is never to be quoted without fresh (Johnson/SendSim/At/ExactAt.lean says why).
  - The limits of the folder, in short (in full: Johnson/SendSim/Defs.lean). The theorem is about
    sub-protocols of the kind K1 alone; K2 and K12 send tables too. The honest sender is a
    definition in Lean, connected with no program. Nothing is hashed, and challenges and queried
    positions are fixed in advance. The data are a free variable, connected with the weights by no
    theorem. The premises are public. Each statement is of one execution: one proof of one request.
    It is not one of the release's goal statements.

How it fits. The statement is in Johnson/SendSim/At/Sim.lean. The proof is one line from three
theorems: rowsExact_of_core (Johnson/SendSim/At/JoinRows.lean), the model's sendExact
(Johnson/SendSim/CoreProofs.lean) and readUnif (Johnson/SendSim/At/ReadUnif.lean).
Johnson/SendSim/At/ExactAt.lean carries it to every Seated side.
-/
import Johnson.SendSim.CoreProofs
import Johnson.SendSim.At.ReadUnif
import Johnson.SendSim.At.JoinRows

set_option autoImplicit false

namespace OnBytes.SendSim.At

/-- Under the four premises of Spec.rowsExact, the distribution of what the honest sender discloses,
over uniform coins, is the same for any two data. -/
theorem rowsExact : Spec.rowsExact := rowsExact_of_core sendExact readUnif

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rowsExact
