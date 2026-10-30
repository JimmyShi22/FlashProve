-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Sits.lean: A DEFINITION OF A HYPOTHESIS. No statement.

What is here. WHAT IT MEANS THAT THE MEMBER OF A CHAIN's `Thread` (Honest/Thread/Thr.lean) AT K4's
PLACE STEPS AS K4's SUB-PROTOCOL DECIDES. K4 is the sub-protocol of the feed-forward layers' own
rounds. It is a hypothesis of the statements of this folder on the state behind the member. General
in T's parameters but the verifier's state and the claims.

  `K4Sits T b p`   where the member number b of T's flat list steps from s to s' on the rounds rs,
      the sub-protocol at the first chain's state and the parameters p (`blockAtS p`,
      Johnson/Desc/First/K4/AtS.lean) decides from s to s' ON THESE ROUNDS WITHOUT THE SEALED DIGEST
      (`noDigest`: so a step shows them to its decision: `Block.step`, Johnson/Desc/Block.lean), at
      some groups of columns.

Not shown here. A HYPOTHESIS's FORM: nothing here shows that it holds at a description of the
protocol. Who is meant to prove it: whoever ties T's flat list to the description: the member is
the sub-protocol, wrapped (a guard in front, a test on the mark, the claims' type); at the full
size the library's `k04_sits_desc` (Johnson/Road/K4/K04Sits.lean) says what the wrapped decision
and step are; `k4Sits_of_laid` (Law/SitsAt.lean) has it at a member
that is seated alone. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies
behind these is not counted. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.First.K4.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par blockAtS)
open VerifiableInference.Desc (Claim First.S noDigest)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **Where the member's own step accepts, the kind's sub-protocol accepts**, on the same rounds
without the sealed digest. A hypothesis's form. Nothing is claimed by the definition. -/
def K4Sits (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ s rs cols s' n, blk.step T.ft s rs cols = .ok (s', n) →
    ∃ gs, (blockAtS p).decide s (rs.map noDigest) gs = .ok s'

end ProofFile.Honest.K4
#print axioms ProofFile.Honest.K4.K4Sits
