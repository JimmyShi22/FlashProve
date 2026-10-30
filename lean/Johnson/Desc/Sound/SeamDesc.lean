-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeamDesc.lean: three of the binders on the description that the seam's core at the
shared chain's two proximity tests has (`tupleNine_rec`, `tupleTen_rec`, Johnson/Desc/Sound/
SeamRec.lean: hG, hlo, hd), GENERAL IN THE DESCRIPTION: from its tests on the plan and its data.
Statements and proofs. No new mathematics: counting.

  `told_count`: in a list of blocks that are shaped (`Block.shaped`) the oracle messages that are told
    are as many as the roots that the blocks' rounds declare.
  `oracles_retype`: a chain without links tells, behind `Chain.retype`, the oracle messages that it
    told before: (hG) wherever a description's shared chain is such a chain retyped.
  `counts_of_planOk`: at a description G that passes `planOk`, with data D: the first chain tells
    D.t₁ oracle messages and the shared chain D.t₂: (hlo) at t₁ := D.t₁.
  `depth_of_planOk`: (hd) at the frame of D over the list of all trees: one call of
    `depth_at_desc` (Johnson/Desc/K12/Coin/FramesTie.lean).
Limits. Nothing here names a description. That the seated description's shared chain IS
`(K14.chainOf …).retype` holds by its text; it is stated where that text can be imported. No
soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.K12.Coin.FramesTie
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Johnson.G.OfPlan (rootsOf)

/-- One block's rounds and what it tells, list by list. -/
theorem told_rounds : ∀ (rs : List Fmt.DeclaredRound) (os : List (List Oracle)),
    os.length = rs.length → (∀ x ∈ rs.zip os, x.2.length = x.1.entry.roots) →
    (os.flatMap id).length = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | r :: rs, o :: os, h, hz => by
    have h1 := hz (r, o) (by simp)
    have ih := told_rounds rs os (by simpa using h) fun x hx => hz x (by simp [hx])
    simp only [List.flatMap_cons, id, List.length_append, List.map_cons, List.sum_cons]
    rw [ih]
    exact congrArg (· + _) h1

/-- **As many oracle messages are told as roots are declared.** -/
theorem told_count {S Cl : Type} : ∀ l : List (Block S Cl), (∀ b ∈ l, b.shaped = true) →
    (oraclesOf l).length = rootsOf (l.flatMap (·.rounds))
  | [], _ => rfl
  | b :: l, h => by
    have hb := h b (by simp)
    simp only [Block.shaped, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hb
    have h1 := told_rounds b.rounds b.oracles hb.1 fun x hx => (hb.2 x hx).1
    have ih := told_count l fun c hc => h c (by simp [hc])
    unfold oraclesOf rootsOf at *
    simp only [List.flatMap_cons, List.length_append, List.map_append, List.sum_append]
    rw [ih, h1]

/-- **A chain without links tells the same behind `Chain.retype`.** -/
theorem oracles_retype {S Cl Cl' : Type} (c : Chain S Cl) (hl : c.links = []) :
    oraclesOf (c.retype (Cl' := Cl')).blocksInOrder = oraclesOf c.blocksInOrder := by
  rw [Chain.flat_eq, Chain.flat_eq]
  simp [oraclesOf, Chain.retype, hl, Block.retype, Block.asBare, List.flatMap_map,
    List.flatMap_append]

section
variable {Xi : Type} (G : FileDescription Xi) (file : String) (D : WholeD)

/-- **The two counts.** -/
theorem counts_of_planOk (hp : G.planOk = true) (h : G.data file = .ok D) :
    (oraclesOf G.first.blocksInOrder).length = D.t₁ ∧ (oraclesOf G.shared.blocksInOrder).length = D.t₂ := by
  obtain ⟨_, e1, e2⟩ := opensShaped G file D h
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hp
  have b1 : blocksOk G.first.blocksInOrder = true := hp.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  have b2 : blocksOk G.shared.blocksInOrder = true := hp.1.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at b1 b2
  exact ⟨(told_count _ fun b hb => (b1 b hb).2).trans e1.symm,
    (told_count _ fun b hb => (b2 b hb).2).trans e2.symm⟩

/-- **The frame lists no tree deeper than it is told.** -/
theorem depth_of_planOk (hp : G.planOk = true) (h : G.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) :
    ∀ j o, G.oracleAt j = some o → ∀ e ∈ (frameAt D (allOf D) key ft).all, e.no = j →
      e.a ≤ o.logLength := by
  intro j o ho
  obtain ⟨c1, c2⟩ := counts_of_planOk G file D hp h
  have hs : G.sentFit = true := by
    simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hp
    exact hp.1.2
  exact K12.Coin.depth_at_desc G file D h hs c1 c2 key ft j o ho

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.told_count
#print axioms Desc.K14.Law.Fence.oracles_retype
#print axioms Desc.K14.Law.Fence.counts_of_planOk
#print axioms Desc.K14.Law.Fence.depth_of_planOk
