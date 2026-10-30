-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontNumbers.lean: THE SMALLNESS TEST: THE TWO NUMBERS OF WHICH THE
FIRST FALL's STATED SHARE IS MADE (`k8FrontFall link o columns tau`,
Johnson/Desc/ProofFile/Honest/K8/Falls.lean), AS THEY ARE DEFINED AT A SEGMENT OF THE FULL SIZE
(`k8ColsAt`, `k8TauAt`: Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean), ARE THE NUMBERS AT WHICH
THE COUNTED SENTENCE SPEAKS: at every state that the first chain's own blocks reach in front of the
segment's batching, in the goals' scope, the state's own data have just these columns and
combinations. Lemmas; none of the library's goals. The two definitions stand in the file of
definitions: code in one file, laws in another. One definition is left here: `numbersView` picks
three fields out, for the law on planned fields.

  `k8ColsAt_cols` the sum that is written out in k8ColsAt is `cols`
                   (Johnson/Desc/ProofFile/Honest/K8/FrontCount.lean), by rfl
  `k8TauAt_par` k8TauAt is the field tau of the lot's own numbers (ProofFile.k8Par,
                   Johnson/Desc/ProofFile/Lot/K8.lean), by rfl
  `numbersView`, `planned_numbers` the three fields NM · mats · tau; they are planned fields
  **`frontNumbers_at_batch`** cols tl = k8ColsAt Bs.G₀ l · tl.tau = k8TauAt Bs.G₀ l
  **`liveOf_at_batch`** so, where every column of the drawn matrix is live: `liveOf (k8ColsAt Bs.G₀
                   l) (k8TauAt Bs.G₀ l) s` (Johnson/P1K8R/FrontFallHeld.lean): the set of states on
                   which `front_fall_heldOn` and `front_fall_heldOn_blocks` hold the record's stated
                   share
Limits. "Every column is live" IS A PREMISE (its failing is a mark with a place and a stated number
of its own: Johnson/P1K8R/DeadMark.lean). That k8ColsAt is the sum of the list ks of the lot's own
numbers wants NM = mats.size at the built segment's data: that is `made_count`
(Johnson/Desc/K8/Honest/HeldOutright.lean) at `made_at_built`
(Johnson/P1K8R/SecondLaidAtBatch.lean); the join is not typed here. IN SCOPE ALONE: the full size's
25 segments; under an opening of the description; the first chain; the family of states from the
description's own first state. Nothing says that any state is reached. Which of the files that this
head names are rows of the library is for the library's own list to say: it is not said here. No
prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.P1K8R.FrontFallHeld
import Johnson.P1K8R.StaticAtBatch
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.ProofFile.Honest.K8.FallNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The sum that is written out in `k8ColsAt` is `cols`. -/
theorem k8ColsAt_cols (G : ProofFile.Ground) (l : Nat) :
    k8ColsAt G l = ((G.built[l]?).map fun X => cols X.tl).getD 0 := rfl

/-- It is the field tau of the lot's own numbers. -/
theorem k8TauAt_par (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    k8TauAt G l = ((G.built[l]?).map fun X => (ProofFile.k8Par Z G X l).tau).getD 0 := rfl

/-- The three fields that the two numbers read. -/
def numbersView (tl : HTailF2) := (tl.NM, tl.mats, tl.tau)

/-- They are planned fields. -/
theorem planned_numbers : LinkJoin.Planned numbersView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The state's own data have just these numbers.** -/
theorem frontNumbers_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) :
    cols tl = k8ColsAt Bs.G₀ l ∧ tl.tau = k8TauAt Bs.G₀ l := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_numbers hS hR O hx e3 (z, s) h') tl ht
  simp only [numbersView, Prod.mk.injEq] at g
  obtain ⟨g1, g2, g3⟩ := g
  unfold k8ColsAt k8TauAt
  rw [e3]
  refine ⟨?_, g3⟩
  show cols tl = cols Xl.tl
  unfold cols
  rw [g1, g2]

/-- **So the counted sentence's set of states.** -/
theorem liveOf_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) (hv : allLive tl = true) :
    _root_.P1K8.liveOf (k8ColsAt Bs.G₀ l) (k8TauAt Bs.G₀ l) s :=
  ⟨tl, ht, hv, (frontNumbers_at_batch hS hR O hl e3 h ht).1,
    (frontNumbers_at_batch hS hR O hl e3 h ht).2⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8ColsAt_cols
#print axioms ProofFile.Honest.K8.k8TauAt_par
#print axioms ProofFile.Honest.K8.numbersView
#print axioms ProofFile.Honest.K8.planned_numbers
#print axioms ProofFile.Honest.K8.frontNumbers_at_batch
#print axioms ProofFile.Honest.K8.liveOf_at_batch
