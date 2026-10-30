-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtValues.lean: the test on values of the round that names the next
token (kind K7), member 338 of the first chain: the table's test there is `replyV`
(Johnson/AtFull/Shape/ReplyFrame.lean), one round, a reply read in it, and a token. The honest half
sends the asked token, so the test says yes wherever the asked token is a token of the vocabulary.

  `tab_vals_338`   the table's test at the member is `replyV`
  `reply_words`   `replyV` says yes at the honest round, at every challenge that the round can draw
  `reply_values`   the field `ValuesJ` at the member, at every J, every letter Said and every fall

The thread is a letter, at the seat `K7Stands`. The one premise on the input: at every input that the
thread's test on inputs lets through, the asked token is a token of the vocabulary. No fall is read, so
the fall may be any. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtSeat
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.AtFull.Shape.TableFramesV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.Reply (readReply isToken)
open Johnson.AtFull.Shape
open ProofFile (Cl)

/-- **The table's test at the member.** -/
theorem tab_vals_338 (Zp : ProofFile.Pub) (G : ProofFile.Ground) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    Tab.vals Zp G 338 s rs gs = replyV G.W.hS.V rs := by
  have hc : Tab.cells Zp G 338 = (Tab.headRow Zp G).at 1 := cells_head Zp G 1 (by omega) rfl
  rw [cell_v hc]
  rfl

/-- **The test says yes at the honest round.** -/
theorem reply_words {x : Inst} {d : Fmt.Drawn} {V : Nat}
    (hd : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds [d] = true)
    (ht : isToken V x.asked = true) :
    replyV V [noDigest ⟨[.e (OnBytes.Slice.ofE (replyOf x))], d⟩] = true := by
  have h0 : drawFit { entry := { name := "REPLY", msg := 24 } } d = true := by
    simpa [VerifiableInference.Desc.Kinds.Reply.rounds, drawsFit] using hd
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h0
  have e1 : d.elems = [] := List.eq_nil_of_length_eq_zero h1
  have e2 : d.poss = [] := List.eq_nil_of_length_eq_zero h2
  have e3 : d.trits = [] := List.eq_nil_of_length_eq_zero h3
  have hr : readReply (noDigest ⟨[.e (OnBytes.Slice.ofE (replyOf x))], d⟩) =
      some (OnBytes.E.ofTriple (OnBytes.Slice.ofE (replyOf x))) := by
    unfold readReply noDigest
    simp [e1, e2, e3]
  show (match readReply (noDigest ⟨[.e (OnBytes.Slice.ofE (replyOf x))], d⟩) with
    | some y => isToken V y
    | none => false) = true
  rw [hr]
  show isToken V (OnBytes.E.ofTriple (OnBytes.Slice.ofE (replyOf x))) = true
  rw [asked_code]
  exact ht

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}
  {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {l V : Nat}
  {blk : Block S Cl}

/-- **The field `ValuesJ` at the member**, at the seat, at every J and every fall. -/
theorem reply_values (Zp : ProofFile.Pub) (G : ProofFile.Ground) (K : K7Stands T 338 l V blk)
    (hv : ∀ w, T.valid w → isToken G.W.hS.V w.x.asked = true)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) (J : Nat → S → Prop)
    (g : Nat → ShA → Except String ShA)
    (fall : Nat → S → List Fmt.Drawn → Option String) :
    ValuesJ T Said J (firstZA g (Tab.vals Zp G)) fall 338 := by
  intro blk' hblk k s m E ds y cols hA _ hd _ _ hM
  obtain rfl : blk = blk' := Option.some.inj (K.member.symm.trans hblk)
  obtain ⟨d, rfl, ey⟩ := k7_played K hd hM
  have hval : T.valid m.st.input := hA.1.2.2.2.2.2.2
  show Tab.vals Zp G 338 s ((roundsOf y.1).map noDigest) (blk.shown T.ft (roundsOf y.1) cols) = true
  rw [tab_vals_338, ey]
  exact reply_words (K.rounds ▸ hd) (hv _ hval)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.tab_vals_338
#print axioms ProofFile.Honest.reply_words
#print axioms ProofFile.Honest.reply_values
