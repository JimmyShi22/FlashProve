-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeldInScope.lean: THE SMALLNESS TEST: THE PUBLIC TEST `heldPubB`
(Johnson/Desc/K8/Honest/HeldPublic.lean) IS NO PREMISE ANY MORE: IN THE GOALS' SCOPE IT SAYS YES AT
THE BUILT SEGMENT's DATA WHEREVER THE FIRST CHAIN's OWN BLOCKS REACH A STATE IN FRONT OF THAT
SEGMENT's BATCHING. SO `AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean) AT EVERY SUCH STATE OF
THE 24 SEGMENTS IN FRONT OF THE HEAD's FROM TWO SENTENCES: the words of one coordinate of the
digits' lookup's key point lie below the prime · the digits' array has the name "ZZ". Lemmas; none
of the library's goals.

  **`heldPub_of_made`** `Made tlc` (Johnson/P1K8R/MadeAtPlans.lean: but for two lists, what
                   addTreesF returned on what shapeF returned) · tlc.tau = 128 · 0 < tlc.mz ⊢
                   heldPubB tlc = true
  `column_at_batch` at a reached state the digits' array has a column
  `columnsView`, `planned_columns` the field mz; it is a planned field
  **`heldPub_at_batch`** at all 25 segments: a state reached in front of the batching shows data ⊢
                   heldPubB Xl.tl = true
  **`allFront_of_two`** l < 24: what the lookup heard is there; and the two sentences at it ⊢ there
                   are nbW, Wn with AllFront tl G g nbW Wn
By: `heldPub_pieces` (Johnson/Desc/K8/Honest/HeldAtPieces.lean) · the library's `shapeF_pieces`
(Fo.ZPlan), `addTreesF_fits` (OnBytes/Tie/Pv/Tail/EndSame.lean), `piecesF_tail_lay_cut`,
IM.k8_tau_128 (Johnson/K8Q14R/TauAt.lean) · `made_at_built` (Johnson/P1K8R/SecondLaidAtBatch.lean) ·
`apart_at_batch`, `sizes_at_batch`, `matrix_there`, `mz_pos` (Johnson/P1K8R/) · `allFront_of_below`
(Johnson/Desc/K8/Honest/WeightsAtReach.lean).
Limits. AN IMPLICATION STILL: THE TWO SENTENCES ARE PAID BY NOBODY HERE: the first can fail at the
family of states at which these theorems stand (Johnson/Desc/K8/Honest/WeightsAtReach.lean says
why); the second is shown at the built segment's planned ledger alone. THE TEST IS SHOWN WHERE A
STATE IS REACHED, NOT OUTRIGHT: that the digits' array has a column is read off the draw's block's
yes and its test on the plan. NOTHING AT THE HEAD's SEGMENT in the last. IN SCOPE ALONE: the full
size's 25 segments; under an opening of the description and its test on its plan; the first chain;
the family of states from the description's own first state. Nothing says that any state is reached.
No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeldAtPieces
import Johnson.Desc.K8.Honest.WeightsAtReach
import Johnson.P1K8R.SecondLaidAtBatch
import Johnson.P1K8R.WantAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.P1K8 (Made)

/-- **The public test says yes at every record that is made as the three plans make it**, at 128
combinations and a column. -/
theorem heldPub_of_made {tlc : HTailF2} (M : Made tlc) (ht : tlc.tau = 128) (hm : 0 < tlc.mz) :
    heldPubB tlc = true := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  obtain ⟨tl1, h1⟩ := _root_.Fo.ZPlan.shapeF_pieces hs
  obtain ⟨-, -, hE⟩ := OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine ha
  obtain ⟨-, -, -, -, -, -, -, -, k1, k2⟩ := _root_.Fo.PiecesF.piecesF_tail_lay_cut h1
  have a : heldFields tl' = heldFields tl := by
    rw [hE]
    rfl
  have b0 : heldFields ({ tlc with plFor := tl'.plFor, plOwn := tl'.plOwn } : HTailF2) =
      heldFields tl' := congrArg heldFields hr
  have b : heldFields tlc = heldFields tl' := b0
  have t1 : tl'.tau = tl.tau := by rw [hE]
  have t2 : tlc.tau = tl'.tau := congrArg (·.tau) hr
  have z1 : tl'.mz = tl.mz := by rw [hE]
  have z2 : tlc.mz = tl'.mz := congrArg (·.mz) hr
  rw [pub_heldFields tlc, b, a, ← pub_heldFields tl]
  refine heldPub_pieces h1 ?_ ?_
  · rw [← k1, ← t1, ← t2]
    exact ht
  · rw [← k2, ← z1, ← z2]
    exact hm

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At a reached state the digits' array has a column. -/
theorem column_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : 0 < tl.mz := by
  obtain ⟨t3, a3, -, hC⟩ := _root_.P1K8.apart_at_batch hS hR O hl h
  rw [Option.some.inj (a3.symm.trans ht)] at hC
  obtain ⟨t4, a4, hZ⟩ := _root_.P1K8.sizes_at_batch hS hR O hl h
  rw [Option.some.inj (a4.symm.trans ht)] at hZ
  obtain ⟨t5, a5, hN⟩ := _root_.P1K8.matrix_there hS hR O hOk hl h
  rw [Option.some.inj (a5.symm.trans ht)] at hN
  exact _root_.P1K8.mz_pos hN hC hZ

/-- The number of columns of the digits' array. -/
def columnsView (tl : HTailF2) := tl.mz

/-- It is a planned field. -/
theorem planned_columns : LinkJoin.Planned columnsView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- **THE PUBLIC TEST SAYS YES AT THE BUILT SEGMENT's DATA, wherever a state is reached in front of
the segment's batching.** -/
theorem heldPub_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : heldPubB Xl.tl = true := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : tl.mz = Xl.tl.mz := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_columns hS hR O hx e3 (z, s) h') tl ht
  refine heldPub_of_made (_root_.P1K8.made_at_built hS hR O hl e3)
    (IM.k8_tau_128 hS hR O (by omega) e3) ?_
  rw [← v]
  exact column_at_batch hS hR O hOk hl h ht

/-- **SO `AllFront` AT THE 24 SEGMENTS IN FRONT OF THE HEAD's FROM TWO SENTENCES.** -/
theorem allFront_of_two (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ g, tl.heard = some g ∧ (OnBytes.okE (g.zy.getD 0 zeroE) = true →
      (G.trees.getD tl.ix.ZZ {}).name = "ZZ" →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact h
  exact allFront_of_below hS hR O hOk hl e3 h ht hG
    (heldPub_at_batch hS hR O hOk (by omega) e3 h' ht)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.heldPub_of_made
#print axioms VerifiableInference.Desc.First.K8.Honest.column_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.planned_columns
#print axioms VerifiableInference.Desc.First.K8.Honest.heldPub_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_two
