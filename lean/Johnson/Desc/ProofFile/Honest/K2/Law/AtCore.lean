-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtCore.lean: the kind "the code switch" (K2): BOTH LAWS ON THE
SENDER (`SendSameLaw`, Honest/K2/Exact.lean; `SendFreshLaw`, Honest/K2/Fresh.lean) AT THE CORE's OWN
SENDER (`coreSender`, Honest/K2/Sending.lean), OVER ANOTHER WRITER's TWO THEOREMS ON THE SHARED
SENDING's ROWS (`rowsExact`, Johnson/SendSim/At/RowsExact.lean; `rowsFresh`,
Johnson/SendSim/At/RowsFresh.lean). Statements with their proofs, each one term; no definition.

  `sendSameLaw_core`   the first law, at every sending in which every message with a main row is
                 sampled, at the shared sending's own table for a fresh mask
  `rowsFreshAt_of_book`   the named premise of Honest/K2/Law/FreshFromRows.lean, paid at a book's
                 two lists at one spender, under that writer's two premises on the book
                 (`WithinAt`, `SpenderClear`, Johnson/SendSim/At/Fresh.lean)
  `sendFreshLaw_core`   so the second law at these two lists
  `sendFreshLaw_core_all`   and at every spender, under that writer's premise on the book at this
                 owner (`BookClear`)

Limits. THESE FOUR ARE AS GOOD AS THE TWO THEOREMS THAT THEY CALL. The premises that are left are
public: `NoWord`, the table, and for the second law the two on the book (at every spender: the one,
`BookClear`, which holds both): that this kind's own test on the two lists (`bookFits`) gives them
is not shown in this file: Honest/K2/Law/BookFromFits.lean shows it (`within_of_bookFits`,
`clear_of_bookFits`). Inside the laws their own hypotheses stand as they were. Nothing here says
what either law would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshFromRows
import Johnson.SendSim.At.RowsExact
import Johnson.SendSim.At.RowsFresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes.SendSim.At (WithinAt SpenderClear BookClear)

/-- **The first law on the sender, at the core's own sender.** -/
theorem sendSameLaw_core {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)} (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j) :
    SendSameLaw (coreSender table) codes sent fresh :=
  sendSameLaw_of_rowsExact OnBytes.SendSim.At.rowsExact hw htab

/-- The named premise on the rows, at a book's two lists at one spender. -/
theorem rowsFreshAt_of_book {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option K1.Ride}
    {Bk : ProverCoinCounts} {ord : List VerifiableInference.Desc.Place} {o p : Addr}
    (hW : WithinAt P ride Bk ord o p) (hC : SpenderClear P ride Bk ord o p) :
    RowsFreshAt P ride (Bk.spentBy o p) (Bk.knownBy ord o p) :=
  fun first data ds asks h1 h2 h3 h4 =>
    OnBytes.SendSim.At.rowsFresh P first ride data ds asks Bk ord o p h1 h2 h3 h4 hW hC

/-- **The second law on the sender, at the core's own sender**, at a book's two lists at one
spender. -/
theorem sendFreshLaw_core {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)} {Bk : ProverCoinCounts}
    {ord : List VerifiableInference.Desc.Place} {o p : Addr} (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (hW : WithinAt (sendingPar codes sent) (rideOf sent fresh) Bk ord o p)
    (hC : SpenderClear (sendingPar codes sent) (rideOf sent fresh) Bk ord o p) :
    SendFreshLaw (coreSender table) codes sent fresh (Bk.spentBy o p) (Bk.knownBy ord o p) :=
  sendFreshLaw_of_rowsAt (rowsFreshAt_of_book hW hC) hw htab

/-- The same at every spender. -/
theorem sendFreshLaw_core_all {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)} {Bk : ProverCoinCounts}
    {ord : List VerifiableInference.Desc.Place} {o : Addr} (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (hB : BookClear (sendingPar codes sent) (rideOf sent fresh) Bk ord o) (q : Addr) :
    SendFreshLaw (coreSender table) codes sent fresh (Bk.spentBy o q) (Bk.knownBy ord o q) :=
  sendFreshLaw_core hw htab (OnBytes.SendSim.At.withinAt_of_takes hB.1 ord q) (hB.2 q)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.sendSameLaw_core
#print axioms ProofFile.Honest.K2.rowsFreshAt_of_book
#print axioms ProofFile.Honest.K2.sendFreshLaw_core
#print axioms ProofFile.Honest.K2.sendFreshLaw_core_all
