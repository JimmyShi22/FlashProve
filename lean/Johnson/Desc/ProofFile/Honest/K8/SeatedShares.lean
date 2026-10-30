-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedShares.lean: THE SMALLNESS TEST AT ITS OWN MEMBER: ITS TWO
SHARES OF THE EXCHANGE, EACH IN THE FORM OF A SHARE (`ExchangeAt`,
Johnson/Desc/ProofFile/Honest/Thread/Shares.lean): at the item of the forms of the run "small", and
at the item of the digits' lookup. Two corollaries of `small_exchange`
(Johnson/Desc/ProofFile/Honest/K8/SeatedLaws.lean), general in the thread; none of the library's
goals.

  `small_share`   K8Seated → K8Items → ExchangeAt T b iS
  `digits_share`   K8Seated → K8Items → ExchangeAt T b iD
The records' limits stand: what they name as premises is not shown at any thread.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedLaws
import Johnson.Desc.ProofFile.Honest.Thread.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par)

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- **The share at the forms of the run "small".** -/
theorem small_share {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    {A : T.Wt → TableE} {iS iD : T.ι} (h : K8Seated T b blk cells P)
    (hI : K8Items T b cells P A iS iD) : ExchangeAt T b iS := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' j hj
  rw [h.here] at hblk'
  cases hblk'
  obtain rfl := List.mem_singleton.1 hj
  exact small_exchange _ _ _ _ _ _ _ T b blk cells P A j iD h hI k s m E ds y cols s' hT hd hS ds' j
    (List.mem_cons_self ..)

/-- **The share at the digits' lookup.** -/
theorem digits_share {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    {A : T.Wt → TableE} {iS iD : T.ι} (h : K8Seated T b blk cells P)
    (hI : K8Items T b cells P A iS iD) : ExchangeAt T b iD := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' j hj
  rw [h.here] at hblk'
  cases hblk'
  obtain rfl := List.mem_singleton.1 hj
  exact small_exchange _ _ _ _ _ _ _ T b blk cells P A iS j h hI k s m E ds y cols s' hT hd hS ds' j
    (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.small_share
#print axioms ProofFile.Honest.K8.digits_share
