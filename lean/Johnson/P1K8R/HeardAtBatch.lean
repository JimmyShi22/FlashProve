-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/HeardAtBatch.lean: AT THE 24 SEGMENTS IN FRONT OF THE HEAD's, AT STATES THAT THE FIRST
CHAIN's OWN BLOCKS REACH: IN FRONT OF THE BATCHING THE DIGITS' LOOKUP HAS HEARD SOMETHING AND ITS
ROWS NAME NO ENTRY, AND A LEDGER IS OPEN WITH ITS SIZES; BEHIND THE LOOKUP ON THE CALLS THE LIKE OF
WHAT THAT LOOKUP HAS HEARD. UNDER THE SCOPE, THE FILES READ, IM.Open AND THE DESCRIPTION's TEST ON
ITS PLAN. Lemmas; none of the library's goals. No prover stands in them; nothing on completeness,
soundness or hiding.

  **`digitsRows_at_batch`**, `callsRows_behind`, `sized_at_batch`   OnPublicFiles.rowsBare_reached, at
      both seats, and OnPublicFiles.sized_upTo (Johnson/Desc/First/Look/K03RowsBare.lean), carried from
      the fold over the blocks to "reached" by reach_fold (Johnson/Top/H0/Walk/Reach.lean), at the
      borders' numbers 14 l + 9 and 14 l + 4, in the state's own readers
The like elsewhere: OnPublicFiles.reached_rowsBare (Johnson/Desc/First/Look/K03ReachedAt.lean): at the
attention segments, at the states that the wrapped blocks reach. At the head's segment: P4.bare_341
(Johnson/P4R/BareAt341.lean).
Limits. The head's segment is not spoken of. Five blocks stand between 14 l + 4 and the batching:
that what was heard stays is not said here. Nothing on the two other forms that a lookup hears
(cEnd, the leaves' start). Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At a state reached in front of the batching of one of the 24 segments in front of the head's:
the digits' lookup has heard something, and its rows name no entry.** That lookup is the last block
in front of the batching. -/
theorem digitsRows_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ g, s.tl?.bind (·.heard) = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have e : 14 * l + 2 + IM.k3Ix l true + 1 = 14 * l + 9 := by
    show 14 * l + 2 + ((if true = true then 6 else 1) + (if l = 24 then 1 else 0)) + 1 = _
    rw [if_pos rfl, if_neg (by omega)]
  exact OnPublicFiles.rowsBare_reached hS hR O hOk l hl true (by rw [e]; exact f)

/-- **At a state reached behind the lookup on the calls, at these 24 segments: it has heard
something, and its rows name no entry.** Five blocks stand between that border and the batching. -/
theorem callsRows_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 4) (z, s)) :
    ∃ g, s.lookHeard? = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have e : 14 * l + 2 + IM.k3Ix l false + 1 = 14 * l + 4 := by
    show 14 * l + 2 + ((if false = true then 6 else 1) + (if l = 24 then 1 else 0)) + 1 = _
    rw [if_neg (by decide), if_neg (by omega)]
  exact OnPublicFiles.rowsBare_reached hS hR O hOk l hl false (by rw [e]; exact f)

/-- **At a state reached in front of the batching of one of these 24 segments a ledger is open, with
its sizes.** -/
theorem sized_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ G, s.fork? = some G ∧ PscRun.Sized G := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  exact OnPublicFiles.sized_upTo hS hR O hOk l hl 6 (by omega) f

end

end P1K8

#print axioms P1K8.digitsRows_at_batch
#print axioms P1K8.callsRows_behind
#print axioms P1K8.sized_at_batch
