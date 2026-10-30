-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FrontSharper.lean: THE SMALLNESS TEST: `FrontLeftOver`
(Johnson/Desc/K8/Honest/AllFrontAtBatch.lean: what was left of `AllFront`'s seventeen at a state
that the first chain's own blocks reach in front of a segment's batching: eight sentences, one of
them of four fields) FROM LESS: the bound on the matrices' rows and the two public fields of BitsPub
are shown there; at the 24 segments in front of the head's the two forms too. So `AllFront` there
from SIX SENTENCES AT THESE 24, EIGHT AT THE HEAD's. And one fact beside: the lengths of the vectors
in the state's data are the built segment's. An assembly; none of the library's goals.

  `FrontLeftSix tl F g`   WHAT IS LEFT: the two points zb0 and zb1 that the digits' lookup has heard
                   have 5 + (kT + cK) coordinates each · the digits' array has the name "ZZ" · the
                   verifier's three tests at the data in front (forestHeld · both callHeld ·
                   pointsHeld)
  `leftOver_of_six`   at a reached state: FrontLeftSix tl G g · the two forms name no entry ⊢
                   FrontLeftOver tl G g
  **`allFront_of_six`**   at the 24 segments in front of the head's: what the lookup heard is
                   there; and FrontLeftSix tl G g at it ⊢ there are nbW, Wn with AllFront tl G g nbW
                   Wn
  `lengthsView`, `planned_lengths`, **`lengths_at_batch`**   tl.nUF = Xl.tl.nUF at a reached
                   state: where the link's lengths are the built segment's, the second of the two
                   facts of `FrontLeftN` (Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean)
By: `cells_at_batch` (Johnson/P1K8R/CellsAtBatch.lean) · `bitsPub_of_sizes`
(Johnson/Desc/K8/Honest/BitsPubAtBatch.lean) · `forms_at_batch`, `allFront_at_batch`
(AllFrontAtBatch.lean) · LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
Limits. AN IMPLICATION STILL: `FrontLeftSix` IS PAID BY NOBODY HERE; three of the six are the
verifier's own tests. At the head's segment the two forms stay premises. IN SCOPE ALONE: the full
size's 25 segments; under an opening of the description and its test on its plan; the first chain;
the family of states from the description's own first state. Nothing says that any state is reached.
`lengths_at_batch` says nothing on a link's own lengths. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.AllFrontAtBatch
import Johnson.Desc.K8.Honest.BitsPubAtBatch
import Johnson.P1K8R.CellsAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What is left. -/
structure FrontLeftSix (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Prop where
  zb0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK)
  zb1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK)
  name : (F.trees.getD tl.ix.ZZ {}).name = "ZZ"
  forest : tl.forestHeld g = true
  calls : [0, 1].all (tl.callHeld g tl.zzBlocks) = true
  points : tl.pointsHeld g = true

/-- The lengths of the vectors, as the data hold them. -/
def lengthsView (tl : HTailF2) := tl.nUF

/-- It is a planned field. -/
theorem planned_lengths : LinkJoin.Planned lengthsView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At a reached state: from the six and the two forms. -/
theorem leftOver_of_six (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) {g : Forest.Heard}
    (L : FrontLeftSix tl G g) (h1 : g.cEnd.ents.isEmpty = true)
    (h2 : g.leaves.start.ents.isEmpty = true) : FrontLeftOver tl G g :=
  ⟨_root_.P1K8.cells_at_batch hS hR O hl e3 h ht, h1, h2,
    bitsPub_of_sizes hS hR O hl e3 h ht L.zb0 L.zb1, L.name, L.forest, L.calls, L.points⟩

/-- **AT THE 24 SEGMENTS IN FRONT OF THE HEAD's.** -/
theorem allFront_of_six (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ g, tl.heard = some g ∧ (FrontLeftSix tl G g →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  obtain ⟨g, hg, h1, h2⟩ := forms_at_batch hS hR O hOk hl h ht
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact h
  exact ⟨g, hg, fun L => allFront_at_batch hS hR O hOk (by omega) e3 h' ht hG
    (leftOver_of_six hS hR O (by omega) e3 h' ht L h1 h2)⟩

/-- **The lengths of the vectors are the built segment's.** -/
theorem lengths_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : tl.nUF = Xl.tl.nUF := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  exact LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_lengths hS hR O hx e3 (z, s) h') tl ht

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planned_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.leftOver_of_six
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_six
#print axioms VerifiableInference.Desc.First.K8.Honest.lengths_at_batch
