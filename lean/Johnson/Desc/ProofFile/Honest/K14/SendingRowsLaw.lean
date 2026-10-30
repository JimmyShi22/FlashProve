-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingRowsLaw.lean: kind K14: THE STATEMENT OF
Honest/K14/SendingRowsStated.lean AS A THEOREM: what the frame's rule for rows (file_owed_rows,
Honest/Thread/Rows.lean) asks of the two sendings' rows, at the own members of the proof file's IOP
as written in Lean (below: the description): under the library's head. A JOIN: no new law.

  seated_any      where Side.seated returns a side, the list has a member at the place
  send_side_fits  a side of one part of two moves, at a sub-protocol of two rounds and two lists of
                  oracle messages, whose simulator names the part's address, passes Side.fits
  rowsServe_of    **RowsServe** at a list off which Side.seated returns, at both sendings' places,
                  a side with the declared rounds and SendDeclared; at shapes that fit
  sendingRowsAtHead   **the statement**

What is joined. The member, the place, the declared rounds and SendDeclared: seated_declares_head
(Honest/K14/SendingsSeated.lean). The shapes: sendings_at_head (Honest/K14/SendingsAtHead.lean).
exact: exactAtU, exactAtOmega (Honest/K14/ExactSend.lean). fresh: maskOwnerLaw'
(Honest/K14/MaskSend.lean); sp_owner_law' (Honest/K14/FreshOwnerLaw.lean), with spBud_of_budAt
(Honest/K14/BudSends.lean): the row's one bound serves both fields.
WHAT IS LEFT. All that is left beside the laws that are joined: their files' heads say it. fresh is
concluded WHERE THE TWO OWNERS' TESTS ON THE BOOK ACCEPT: that any book of a description passes them
is not shown in this file (under premises: Honest/K14/BookAtU.lean, Honest/K14/BookAtOmega.lean) ·
that the row's sentence at entry holds where a run stands, and that a run's positions are within the
row's bound, is not shown here, and is to be had at the same On and bud (the first, out of the
frame's sentence on where a run stands, which nothing shows to hold along a run:
Honest/K14/OnSending.lean; of the second, the count at the positions that the frame lays at one
request's challenges, not at a run's: Honest/K14/BudRows.lean) · the list is the shared rounds' own
flat list carried to a type of claims: that it is a description's field shared, blocksInOrder, is one
equation more (rowsServe_at_shared, Honest/K14/RowsAtShared.lean) · that a filling of the frame lays
its sides for these two rows off that list is not shown · at the row of o_omega the clauses of the
owner's test that read no book are not shown met here: were they not, the test would accept at no
book, and the clause fresh of BOTH rows, as stated here, would be empty (the law at "send o_u"
itself, maskOwnerLaw', asks its own test alone) · one request. This file states no goal of the
release. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingRowsStated
import Johnson.Desc.ProofFile.Honest.K14.ExactSend
import Johnson.Desc.ProofFile.Honest.K14.MaskSend
import Johnson.Desc.ProofFile.Honest.K14.FreshOwnerLaw
import Johnson.Desc.ProofFile.Honest.K14.BudSends
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (P14 St chainOf)
open ProofFile.Honest.Small (ExactMember FreshMember)

variable {S Cl V W X Pb W₀ Rc Ky : Type}

/-- Where Side.seated returns a side, the list has a member at the place. -/
theorem seated_any {xs : List (Block S Cl)} {a : Place} {row : List (Part V W X × Sim Pb)}
    {fs : List (Fall S)} {σ : Side S Cl V W X Pb} (h : Side.seated xs a row fs = some σ) :
    xs.any (fun b => b.place == a) = true := by
  unfold Side.seated at h
  obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 h
  have hp : (b.place == a) = true :=
    List.find?_some (p := fun b : Block S Cl => b.place == a) hb
  exact List.any_eq_true.2 ⟨b, List.mem_of_find?_eq_some hb, hp⟩

/-- A side of one part of two moves passes the frame's test on sides. -/
theorem send_side_fits (σ : Side S Cl V W X Pb) (p : Part V W X) (sim : Sim Pb)
    (hrow : σ.row = [(p, sim)]) (haddr : sim.addr = ⟨σ.block.place, 0⟩)
    (hmv : p.moves.length = 2) (hr2 : σ.block.rounds.length = 2)
    (ho2 : σ.block.oracles.length = 2) : σ.fits = true := by
  unfold Side.fits Side.half Placed.rounds
  rw [hrow]
  simp [haddr, hmv, hr2, ho2]

/-- **What the frame's rule for rows asks of the two sendings' rows**, at a list off which
Side.seated returns, at both sendings' places, a side with the declared rounds and SendDeclared. -/
theorem rowsServe_of (xs : List (Block St Cl)) (P : P14) (hfit : sendingsFit P = true)
    (hdecl : ∀ (row : List (Part Empty (Common W₀ Rc Ky) X × Sim Ky)) (fs : List (Fall St)),
      (∃ σ : Side St Cl Empty (Common W₀ Rc Ky) X Ky,
          Side.seated xs (sendPlace 2) row fs = some σ ∧ σ.row = row ∧
          σ.block.place = sendPlace 2 ∧
          σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobU ⟨P, 0⟩).Q ∧
          SendDeclared σ.block (jobU ⟨P, 0⟩)) ∧
        ∃ σ : Side St Cl Empty (Common W₀ Rc Ky) X Ky,
          Side.seated xs (sendPlace 5) row fs = some σ ∧ σ.row = row ∧
          σ.block.place = sendPlace 5 ∧
          σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega ⟨P, 0⟩).Q ∧
          SendDeclared σ.block (jobOmega ⟨P, 0⟩))
    (weights : W₀ → Weights) (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts)
    (ord : List Place) :
    RowsServe (X := X) (Ky := Ky) xs ⟨P, 0⟩ weights rand fs Bk ord := by
  intro r hr
  unfold sendingRows at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨⟨σ₀, hσ₀, hrow, hpl, hrd, hdc⟩, -⟩ := hdecl
      [(liftSend (fun c => ⟨rowsOf P.S (weights c.w₀) (rand c.rc)⟩) (sendingPart (jobU ⟨P, 0⟩)),
        sendingSim (jobU ⟨P, 0⟩) ⟨sendPlace 2, 0⟩)] fs
    refine ⟨seated_any hσ₀, fun σ hσ => ?_⟩
    obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
    have hrow' : σ₀.row = [(liftSend (fun c => ⟨rowsOf P.S (weights c.w₀) (rand c.rc)⟩)
        (sendingPart (jobU ⟨P, 0⟩)), sendingSim (jobU ⟨P, 0⟩) ⟨σ₀.block.place, 0⟩)] := by
      rw [hpl]
      exact hrow
    obtain ⟨d₀, d₁, os, -, ho, -⟩ := hdc.rounds
    refine ⟨send_side_fits σ₀ _ _ hrow' rfl rfl (by rw [hrd]; rfl) (by rw [ho]; rfl),
      exactAtU St Cl X Ky W₀ Rc Ky ⟨P, 0⟩ hfit _ .shared σ₀ hrow' hrd hdc 1 0 _
        (fun _ _ _ _ h => h) _ (fun _ _ h => h), fun okU _ => ?_⟩
    obtain ⟨hf, hg⟩ := OwnerTest.ok_clear okU
    exact maskOwnerLaw' ⟨P, 0⟩ Bk ord ⟨sendPlace 2, 0⟩ (beq_self_eq_true _) hf hg St Cl X Ky W₀ Rc
      Ky _ _ .shared σ₀ hrow hrd hdc (by rw [hpl]) _ (fun _ _ h => h)
  · obtain ⟨-, σ₀, hσ₀, hrow, hpl, hrd, hdc⟩ := hdecl
      [(liftSend (fun c => ⟨rowsOf P.S (weights c.w₀) (rand c.rc)⟩)
          (sendingPart (jobOmega ⟨P, 0⟩)),
        sendingSim (jobOmega ⟨P, 0⟩) ⟨sendPlace 5, 0⟩)] fs
    refine ⟨seated_any hσ₀, fun σ hσ => ?_⟩
    obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
    have hrow' : σ₀.row = [(liftSend (fun c => ⟨rowsOf P.S (weights c.w₀) (rand c.rc)⟩)
        (sendingPart (jobOmega ⟨P, 0⟩)), sendingSim (jobOmega ⟨P, 0⟩) ⟨σ₀.block.place, 0⟩)] := by
      rw [hpl]
      exact hrow
    obtain ⟨d₀, d₁, os, -, ho, -⟩ := hdc.rounds
    refine ⟨send_side_fits σ₀ _ _ hrow' rfl rfl (by rw [hrd]; rfl) (by rw [ho]; rfl),
      exactAtOmega St Cl X Ky W₀ Rc Ky ⟨P, 0⟩ hfit _ .shared σ₀ hrow' hrd hdc 1 0 _
        (fun _ _ _ _ h => h) _ (fun _ _ h => h), fun _ okO => ?_⟩
    obtain ⟨hf, hg⟩ := OwnerTest.ok_clear okO
    obtain ⟨-, -, hsp, H, -, -⟩ := fits_gives (A := ⟨P, 0⟩) (n := spEntries ⟨P, 0⟩) hf
    exact sp_owner_law' ⟨P, 0⟩ Bk ord ⟨sendPlace 5, 0⟩ (beq_self_eq_true _) hf hg St Cl X Ky W₀ Rc
      Ky _ _ .shared σ₀ hrow hrd hdc (by rw [hpl]) _
      (fun _ asks h => spBud_of_budAt ⟨P, 0⟩ _ hsp H asks h)

/-- **SendingRowsAtHead.** The statement, with what is left beside it:
Honest/K14/SendingRowsStated.lean. -/
theorem sendingRowsAtHead : SendingRowsAtHead := by
  intro Z D r Zp Np cF x₀ o h Cl X W₀ Rc Ky weights rand fs Bk ord
  exact rowsServe_of _ (qAt Zp Np) (sendings_at_head h).1
    (fun row fs => seated_declares_head h 0 row fs) weights rand fs Bk ord

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.seated_any
#print axioms ProofFile.Honest.K14.send_side_fits
#print axioms ProofFile.Honest.K14.rowsServe_of
#print axioms ProofFile.Honest.K14.sendingRowsAtHead
