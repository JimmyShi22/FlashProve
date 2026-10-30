-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtBook.lean: the round that names the next token (kind K7) at the
book and the ground that the maker of the proof file's description returns. Where `onlineProverFromPublicFiles`
(Honest/AtPure.lean) returns, in scope, the lot `replySLot` has one row, at link 24, and the premise of
`reply_hand` (Honest/K7/Rows.lean) on the book holds: no entry of the book that `onlineProverFromPublicFiles` returns spends
a coin of the part. The premise on the block holds by Honest/K7/RowsAtScope.lean. So the hypothesis
`hand₁` of the rule `file_owed_rows` holds at that row, at every filling. The rule's other hypotheses
on the row are not treated here.

  `reply_no_seed`   the kind's one round is no round "SEND seed"
  `reply_spent_of_open`   no entry of a whole book spends a coin of the part
  `reply_hand_of_open`   the hypothesis `hand₁` at the row, at the chain c of `IM.Open`
  `reply_at_return`   the same where `onlineProverFromPublicFiles` returns, with the row read off the lot

`Good` here is as in Honest/K7/Rows.lean: fits, exact and fresh, with the fields plays and acc met for
nothing. The row's On and bud ask nothing. That the description passes `placesOk` is a premise. Nothing
here says that `onlineProverFromPublicFiles` returns, and nothing is said of a request on which the model has no value.
This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.RowsAtScope
import Johnson.Desc.ProofFile.Honest.BookOwners
import Johnson.Desc.ProofFile.Honest.AtPureBook
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)

/-- The kind's one round is no round "SEND seed". -/
theorem reply_no_seed :
    ∀ r ∈ VerifiableInference.Desc.Kinds.Reply.rounds, r.entry.name ≠ "SEND seed" := by
  intro r hr
  have hr' : r ∈ ([{ entry := { name := "REPLY", msg := 24 } }] : List Fmt.DeclaredRound) := hr
  rw [List.mem_singleton] at hr'
  rw [hr']
  show "REPLY" ≠ "SEND seed"
  decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
  {Bk : ProverCoinCounts}

/-- **No entry of a whole book spends a coin of the part**, in scope, at the chain c of `IM.Open`. -/
theorem reply_spent_of_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hp : F.placesOk = true) (q : Addr) :
    Bk.spentBy ⟨⟨1, some 24, 1, .K7⟩, 0⟩ q = [] := by
  obtain ⟨Lk, b, e1, e2, hJ, -⟩ := IM.k7_sits hS hR O
  obtain ⟨fr, f, -, -, e⟩ := hJ
  have hpl : b.place = ⟨1, some 24, 1, .K7⟩ := by
    rw [e]
    rfl
  have hr : b.rounds = VerifiableInference.Desc.Kinds.Reply.rounds := by
    rw [e]
    rfl
  have hm : b ∈ c.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat e1 e2)
  obtain rfl := O.desc
  have h := bookWhole_spent_nil hw hp (b := b) hm (by rw [hr]; exact reply_no_seed) 0 q
  rwa [hpl] at h

/-- **The hypothesis `hand₁` of `file_owed_rows` at the row**, in scope, at that chain. -/
theorem reply_hand_of_open {W₀ Rc Tr X : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hp : F.placesOk = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall S))
    (T : Local W₀ Rc Inst Tr →
      Thread Bk S ProofFile.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (Sd : Local W₀ Rc Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) :
    ∀ σ, ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).side c.blocksInOrder fs = some σ →
      ∃ A' B', Good pre Face.own σ Bk ord chain firstTree A' B'
        ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).On
        ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).bud :=
  reply_hand pre ord chain firstTree c.blocksInOrder fs 24 1 T Sd
    (fun σ h => reply_seated_at_scope hS hR O fs σ h)
    (reply_spent_of_open hS hR O hw hp)

end

/-- **WHERE `onlineProverFromPublicFiles` RETURNS, in scope, at every filling**: the lot's one row stands at link 24, and
the hypothesis `hand₁` of `file_owed_rows` holds at it, at the returned book. -/
theorem reply_at_return {W₀ Rc Tr X₀ X : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
    {lay : ByteArray} {Fl : OnlineProverParts W₀ Rc Tr X₀ X} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol lay P.KL Fl = .ok R) (hp : R.F.placesOk = true) :
    (replySLot (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X)).rows R.Z R.G =
        [replyUnlettered 24 1] ∧
      ∃ Bs base c Sh Se, IM.Open OnBytes.secondHashFunction P.pol lay P.KL R.F R.Z Bs base c Sh Se ∧
        ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place) (chain firstTree : Nat)
          (fs : List (Fall S))
          (T : Local W₀ Rc Inst Tr →
            Thread R.B S ProofFile.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
          (Sd : Local W₀ Rc Inst Tr → Nat → Coins R.B → Mid (Local W₀ Rc Inst Tr) X → Prop),
          ∀ σ, ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).side c.blocksInOrder fs = some σ →
            ∃ A' B', Good pre Face.own σ R.B ord chain firstTree A' B'
              ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).On
              ((replyUnlettered 24 1).lay T Sd c.blocksInOrder).bud := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok h
  have hsz : R.G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  obtain ⟨-, -, -, -, p0, p1, p2, -, hB⟩ := atPure_book h
  obtain ⟨Bs, base, c, Sh, Se, O⟩ := atPure_open (X := X) h
  refine ⟨?_, Bs, base, c, Sh, Se, O, ?_⟩
  · show [replyUnlettered (R.G.built.size - 1) 1] = _
    rw [hsz]
  · intro pre ord chain firstTree fs T Sd
    exact reply_hand_of_open hS hR O hB hp pre ord chain firstTree fs T Sd

end ProofFile.Honest

#print axioms ProofFile.Honest.reply_no_seed
#print axioms ProofFile.Honest.reply_spent_of_open
#print axioms ProofFile.Honest.reply_hand_of_open
#print axioms ProofFile.Honest.reply_at_return
