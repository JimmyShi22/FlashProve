-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/F9AtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING, THE DATA's FIELD f9 (the public numbers of the lookup on the
digits) IS THAT OF THE PUBLIC PART's BUILT SEGMENT. One lemma; none of the library's goals. No
prover stands in it; nothing on completeness, soundness or hiding. A joining: calls of the library's
lemmas.

  **`f9_at_batch`**   in the goals' scope, under an opening of the description, at l < 25; K := 14 l
      + 9, or 347 at the head's segment: at every (z, s) reached at K, every X with
      Z.p.built.links[l]? = some X and every data tl of s: tl.f9 = X.tl.f9
By: LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) · planned_gD,
of_readTl (OkAtBatch.lean) · gD_parts (OkDigAt.lean) · K9Asks.built_tl (K9RowsAskLaw.lean) ·
P1K8T.built_at (Johnson/P1K8R/Tied.lean).
Limits. The full size's 25 segments. The first chain. Nothing on what the field holds.

-/
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.P1K8R.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The data's f9 in front of a batching is the public part's.** -/
theorem f9_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {X : LinkH} (hX : Z.p.built.links[l]? = some X) {tl : HTailF2} (ht : s.tl? = some tl) :
    tl.f9 = X.tl.f9 := by
  obtain ⟨Xl, e3⟩ := P1K8T.built_at hS hR O (by omega : l ≤ 24)
  obtain ⟨X', x1, x2⟩ := K9Asks.built_tl O.blank e3
  obtain rfl : X' = X := Option.some.inj (x1.symm.trans hX)
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  rw [← x2]
  exact (LinkJoin.gD_parts (LinkJoin.of_readTl
    (LinkJoin.planned_at_batch LinkJoin.planned_gD hS hR O hx e3 (z, s) h') tl ht)).1

end P1K8

#print axioms P1K8.f9_at_batch
