-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Lays.lean: THE CLAUSE OF THE THREAD's RIDER THAT THE MEMBER
"the output head's own rounds" (K6) LAYS: behind its accepted step the chain stands in the head's
link, and what the head's rounds have heard is laid: the debt `LaysAt` (Honest/Thread/Riders.lean)
at `riderHead lo hi fun a => a.x.isSome = true`. GENERAL IN THE THREAD. CONDITIONAL.

  `k6_lays`   CONDITIONAL: whatever stands at the number b of the thread's flat list has the form in
              which the description seats the member (`K6MemberIs`,
              Johnson/Desc/Kinds/Law/K6WayUp.lean)

What is called: `k6_keeps_of_member_step` (Johnson/Desc/K6/Honest/Law/KeepsMember.lean) and
`K6Keeps.heard` (Honest/Law/Keeps.lean). Of the debt's premises the step's yes alone is spent.

Of the five facts on the head's own part at which that file's head means `riderHead` (opened; what
the head's rounds heard is laid; the tables are laid; the claim is laid; the ledger has its sizes)
THIS MEMBER LAYS THE SECOND ALONE: the four others are other members'.

Limits. The premise on the flat list is shown at no thread here. lo and hi are free letters: nothing
holds lo against b + 1. No step's yes is shown. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.K6.Honest.Law.KeepsMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs)
open VerifiableInference.Desc.Kinds.Head.Honest (k6_keeps_of_member_step K6Keeps.heard)

/-- **THE MEMBER LAYS "WHAT THE HEAD's ROUNDS HAVE HEARD IS LAID".** CONDITIONAL: the premise on the
thread's flat list. -/
theorem k6_lays {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk S Claim V W X Pb) {b lo hi : Nat}
    {Wp : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
    (hM : ∀ blk, T.bs[b]? = some blk → K6MemberIs Wp l same a blk) :
    LaysAt T b (riderHead lo hi fun o => o.x.isSome = true) := by
  intro blk hblk k s m E ds y cols s' _ _ hS
  exact (k6_keeps_of_member_step (hM blk hblk) hS.2).heard

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_lays
