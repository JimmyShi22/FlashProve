-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/InScope.lean: IN THE GOALS' SCOPE, AT THE PROOF FILE's OWN
DESCRIPTION: WHAT THE LIBRARY ALREADY GIVES OF THE PREMISES THAT THIS FOLDER's LAWS ON THE NEXT
TOKEN's MEMBER TAKE: entry 338 of the first chain's flat list. Statements with their proofs: each a
few calls of sealed theorems (`IM.hearer_at`, Johnson/IMR/TokAtReach.lean; `IM.k7_sits`,
`IM.Joined.rounds`, Johnson/IMR/FirstSeats.lean; `IM.ground_gets`, Johnson/IMR/PureJoin.lean). It
imports, through Johnson/IMR/TokAtReach.lean, a module under lean/Johnson/Goal/; no definition
stands here.

  `k7Block_lot`     the library's `IM.k7Block G₀.W 24` is the lot's own sub-protocol (`h1Own G₀`)
  `joined_oracles`  the joined form's oracle messages are the lot's sub-protocol's
  `k7Made_inScope`  **THE RECORD `K7Made` (Honest/K7/Lays.lean) IS PAID AT ENTRY 338**, with: the
      member's place, rounds and oracle messages; and: the frame's «opened» of that segment hands
      the state on
  `k7_opens_of`     so `K7Ready.opens` (Honest/K7/Accepts.lean) holds at such a frame
  `k7Place_hears`   the place is the one that may write the reply

WHAT IS NOT PAID HERE. `K7Stands`' ties to a thread's letters (that its list of members is this flat
list; which half its fold finds at the place; that the member sends no tree) · `K7Ready`' four other
fields · `K7Ties` · `K7Turns`.

Limits. Under the library's «in scope», «the files are read» and its record `IM.Open` of the
description's making, at the format's second hash function. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K7.Accepts
import Johnson.IMR.TokAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place FileDescription Chain)
open VerifiableInference.Desc.First (S hearsReply)
open Johnson.Desc.First.Walk.Seat (LinkFrame)
open ProofFile (Cl)

theorem k7Place_hears : hearsReply IM.k7Place = true := rfl

/-- The joined form's oracle messages are the lot's sub-protocol's. -/
theorem joined_oracles {Z : Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (h : IM.Joined Z l b b' a) : b.oracles = b'.oracles := by
  obtain ⟨fs, f, -, -, e⟩ := h
  rw [e]
  show b'.oracles ++ [] = b'.oracles
  rw [List.append_nil]

/-- Where «opened» hands the state on: the frame's half of the yes. -/
theorem k7_opens_of {f : LinkFrame} (hid : f.opened = fun s => .ok s) (tl : OnBytes.Model.HTailF2)
    (V : Nat) (s mid : S) (h : H1Keeps tl V s mid) :
    ∃ s', f.opened mid = .ok s' ∧ s'.failed = none ∧ sameReply mid s' = true := by
  refine ⟨mid, by rw [hid], h.1, ?_⟩
  show (mid.out.reply == mid.out.reply) = true
  exact beq_self_eq_true _

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription Inst} {Z : Pub}
  {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

theorem k7Block_lot (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    IM.k7Block Bs.G₀.W 24 ∈ h1Own Bs.G₀ := by
  obtain ⟨sz, -⟩ := IM.ground_gets hS hR O.pub O.blank
  unfold h1Own P4.k7Core
  rw [sz]
  exact List.mem_singleton.2 rfl

/-- **THE RECORD IS PAID AT ENTRY 338.** -/
theorem k7Made_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ blk fs f, c.blocksInOrder[338]? = some blk ∧
      K7Made Z Bs.G₀ 24 blk (IM.k7Block Bs.G₀.W 24) IM.k7Place fs f ∧
      blk.place = IM.k7Place ∧ blk.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧
      blk.oracles = [[]] ∧ f.opened = fun s => .ok s := by
  obtain ⟨blk, e, J⟩ := IM.hearer_at hS hR O
  obtain ⟨-, -, -, -, -, hid⟩ := IM.k7_sits hS hR O
  have hl := k7Block_lot hS hR O
  obtain ⟨er, eo⟩ := h1_shape hl
  obtain ⟨fs, f, hfs, hf, -⟩ := id J
  exact ⟨blk, fs, f, e, ⟨hl, J, hfs, hf⟩, IM.joined_place J, J.rounds.trans er,
    (joined_oracles J).trans eo, hid fs f hfs hf⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.k7Place_hears
#print axioms ProofFile.Honest.joined_oracles
#print axioms ProofFile.Honest.k7_opens_of
#print axioms ProofFile.Honest.k7Block_lot
#print axioms ProofFile.Honest.k7Made_inScope
