-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/RowsAtScope.lean: the round that names the next token (kind K7) at
the description's own member: in scope, the block at the place of the last link has the kind's one
round and no oracle message. So the premise of `reply_hand` (Honest/K7/Rows.lean) on the block holds
at the chain c of `IM.Open`.

  `reply_block_at_scope`   the statement `ReplyBlockAtScope` at c.blocksInOrder and link 24
  `reply_seated_at_scope`   the same as `reply_hand` takes it

At the chain c of `IM.Open`: that the description's first chain is c is not carried here. That the
ground's last link is number 24 is not carried here either: `replySLot` reads it off the ground.
-/
import Johnson.Desc.ProofFile.Honest.K7.Rows
import Johnson.IMR.FirstSeats
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The description's own member at the place.** -/
theorem reply_block_at_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ReplyBlockAtScope c.blocksInOrder 24 := by
  intro b' hf
  obtain ⟨Lk, b, e1, e2, hJ, -⟩ := IM.k7_sits hS hR O
  have hn : (c.blocksInOrder.map (·.place)).Nodup := by
    rw [IM.places_scope hS hR O]
    exact IM.places_nodup
  obtain ⟨fr, f, -, -, e⟩ := hJ
  have hp : b.place = ⟨1, some 24, 1, .K7⟩ := by
    rw [e]
    rfl
  have hfind := find_at c.blocksInOrder _ b hn (IM.hear_at_flat e1 e2)
  rw [hp] at hfind
  have hb : b' = b := Option.some.inj (hf.symm.trans hfind)
  rw [hb]
  constructor
  · rw [e]
    rfl
  · rw [e]
    rfl

/-- **As `reply_hand` takes it.** -/
theorem reply_seated_at_scope {W₀ Rc Tr X : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (h : Side.seated c.blocksInOrder (⟨1, some 24, 1, .K7⟩ : Place) (replyRow 24 1) fs = some σ) :
    σ.block.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ σ.block.oracles = [[]] := by
  obtain ⟨b, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  exact reply_block_at_scope hS hR O b hf

end

end ProofFile.Honest

#print axioms ProofFile.Honest.reply_block_at_scope
#print axioms ProofFile.Honest.reply_seated_at_scope
