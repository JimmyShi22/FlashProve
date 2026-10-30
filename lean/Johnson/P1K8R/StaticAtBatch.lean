-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/StaticAtBatch.lean: THE STATIC CLAUSES (LinkJoin.StaticOk,
Johnson/Desc/First/Link/Law/OkJoin.lean), BARE, AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING: FROM THE SAME CLAUSES OF THE BUILT SEGMENT. UNDER THE SCOPE,
THE FILES READ AND IM.Open. Lemmas; none of the library's goals. No prover stands in them; nothing
on completeness, soundness or hiding. Why. LinkJoin.ok_at_batch
(Johnson/Desc/First/Link/Law/OkAtBatch.lean) has them there in another dress: at the blanked data,
at the part that the batching's lens finds, under the premise that it finds one, and at the states
that the wrapped blocks reach.

  `looks_at_batch`   the open ledger's arrays have the looks of the built segment's planned arrays.
      ITS LINES ARE THOSE OF LinkJoin.looks_at_open, link_at_batch AND THE END OF part_at_batch
      (Johnson/Desc/First/Link/Law/AtBatchOpen.lean), which stand at the states that the wrapped
      blocks reach and, the last, at the lens's part
  **`static_at_batch`**   the sentence of the title
  `three_of_static`   what the clauses hand: the number of blocks that the expected pieces are cut
      by; Fo.CoefOK; the third array of reads is apart (LinkJoin.ApartAt)
By: LinkJoin.static_congr (OkJoin.lean) · LinkJoin.planned_at_batch (PlannedAtDraw.lean) at
planned_g9, of_readTl (OkAtBatch.lean) · Meaning.K2.open_fold (Johnson/IMR/OpenWalk.lean) at
LinkJoin.seatKeeps_looks, okHead_at, start_none (Johnson/LPFK9R/LooksSeat.lean), looksInv_none
(LooksWalk.lean) · Meaning.K2.group_all (Johnson/IMR/GroupHead.lean) · Meaning.Carry.front_len
(Johnson/IMR/RootsWhole.lean) · LinkJoin.shOf_at (AtBatchOpen.lean) · reach_fold
(Johnson/Top/H0/Walk/Reach.lean).
Limits. THE CLAUSES OF THE BUILT SEGMENT ARE A PREMISE, and so is that the built list has a segment
at l. P5J.AtMg.staticOk_ground (Johnson/P5T/StaticWholeAtMg.lean) and K9Asks.static_of_seg
(Johnson/Desc/First/Link/Law/K9AsksLaw.lean) end in the first: not called here. Nothing on whether
any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.AtBatchOpen
import Johnson.Desc.First.Link.Law.PlannedAtDraw
import Johnson.Desc.First.Link.Law.OkJoin
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.LPFK9R.LooksSeat
import Johnson.IMR.GroupHead
import Johnson.IMR.OpenWalk
import Johnson.IMR.RootsWhole
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At a state reached in front of a segment's batching the open ledger's arrays have the looks of
the built segment's planned arrays.** The like of LinkJoin.part_at_batch
(Johnson/Desc/First/Link/Law/AtBatchOpen.lean), at the state's own ledger: that the batching's lens
finds its part there is not asked. -/
theorem looks_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {G : Fork} (hG : s.fork? = some G) :
    G.trees.toList.map LinkJoin.look = Xl.Fp.trees.toList.map LinkJoin.look := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have hk' : 14 * l + (if l = 24 then 11 else 9) ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    split_ifs <;> omega
  obtain ⟨L, h1, h2, -⟩ := Meaning.K2.group_all hS hR O hl
    (k := 14 * l + (if l = 24 then 11 else 9)) (by split_ifs <;> omega) (by split_ifs <;> omega) f
  have hlk : LinkJoin.LooksAre (LinkJoin.shOfBuilt Z.p.built.links L.link) G :=
    Meaning.K2.open_fold (LinkJoin.seatKeeps_looks Z.p.built.links) O rfl
      (fun l Q hQ => LinkJoin.okHead_at O.blank hQ) hk' f
      (LinkJoin.looksInv_none _ (LinkJoin.start_none O.pub z)) G L hG h1
  rw [h2] at hlk
  exact hlk.trans (LinkJoin.shOf_at O.blank e3)

/-- **THE STATIC CLAUSES (LinkJoin.StaticOk, Johnson/Desc/First/Link/Law/OkJoin.lean), BARE, AT A
STATE REACHED IN FRONT OF A SEGMENT's BATCHING: FROM THE SAME CLAUSES OF THE BUILT SEGMENT.** -/
theorem static_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (H : LinkJoin.StaticOk Xl.tl Xl.Fp) : LinkJoin.StaticOk tl G := by
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
    (LinkJoin.planned_at_batch LinkJoin.planned_g9 hS hR O hx e3 (z, s) h') tl ht
  exact LinkJoin.static_congr g (looks_at_batch hS hR O hl e3 h hG) H

/-- **What that hands of the premises on the state in front**: the number of blocks that the
expected pieces are cut by; what the declared weights' laws ask; and that the third array of reads
is apart from the digits', the planes', the symbols' and the pieces'. -/
theorem three_of_static {tl : HTailF2} {G : Fork} (H : LinkJoin.StaticOk tl G) :
    (∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks) ∧ Fo.CoefOK tl G ∧
      LinkJoin.ApartAt tl ((tl.ix.U.getD 2 none).getD 0) := by
  refine ⟨fun nbW W hw => ?_, H.coef, H.apart { tree := 2 } (Or.inr rfl)⟩
  have k := H.blocks
  rw [hw] at k
  exact Option.some.inj k

end

end P1K8

#print axioms P1K8.looks_at_batch
#print axioms P1K8.static_at_batch
#print axioms P1K8.three_of_static
