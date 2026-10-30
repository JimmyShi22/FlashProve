-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExactAtHead.lean: the kind "the code switch" (K2): under the
library's head and the opening, at each place of the kind, at the letters at which the kind's lot of
rows lays its row: all eight premises ExactAsks (Honest/K2/Exact.lean), and so the statement's end
ExactOf. Statements with their proofs, calls; no definition.

  exactAsks_at_head   the eight premises, and that the side fits its block
  exactOf_at_head     the end: the sentence of the field exact of Good at the seated side

By: k2_member_at_head, k2_block_at_head, four_public_at_head, fits_at_head, seeds_at_place,
placeOneRow_yes, oneRowW, numbers_at_place, rounds_at_place (as in FreshSixAtHead.lean) · send_open
(SendOpen.lean) · closing_at_head (ClosingAtHead.lean) · returnsLaw (SegmentAlike.lean) · switchExact
(ExactProof.lean).

Limits. The head and the opening are hypotheses here; where the public files pass they are met
(P5J.head_exists_at_name, and the field laid.opened of the head). The end is an equation of two laws
over the part's own coins, at every state: what it is worth hangs on the bound switchBud, a premise
inside it. The sender is the core's and the closing the lot's own; D, readers and fs are free.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshSixAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SendOpen
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.ExactProof
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain Place Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Xi Tr X : Type}

/-- **All eight premises at a place of the kind**, at the letters of the kind's lot of rows; and the
side fits its block. -/
theorem exactAsks_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      ExactAsks (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p
        (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link))
        (roundsAt Zp Bs.G₀ p.place) cF.blocksInOrder fs σ ∧ σ.fits = true := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  obtain ⟨blk, member, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp, n, nm, st, before, after, hP, hn, -, ⟨-, hr, ho⟩, -, -⟩ :=
    k2_block_at_head h O hp member
  have hR := rounds_at_place hP hp hn nm st
  obtain ⟨nm', st', hq⟩ := numbers_at_place hP hp hn
  obtain ⟨-, -, s1, s2⟩ := four_public_at_head h O hp hP hn p.place nm' st'
  have hfind : cF.blocksInOrder.find? (fun b => b.place == p.place) = some blk := by
    rw [find_at_findIdx]
    have e := K1.borderNo_written h p.place
    unfold borderNo at e
    rw [e]
    exact member
  have hseat : Side.seated cF.blocksInOrder p.place (switchRow (X := X) (coreSender freshTable) D readers
               (lotClosing Zp Bs.G₀) p
               (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link))
               (roundsAt Zp Bs.G₀ p.place)) fs =
      some ({ block := blk
              row := switchRow (X := X) (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p
                (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link))
                (roundsAt Zp Bs.G₀ p.place)
              fall := fallOf fs p.place } :
        Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) := by
    unfold Side.seated
    rw [hfind]
    rfl
  refine ⟨_, ?_, switchRow_fits _ _ _ _ _ _ _ _ fs _ hseat ?_ ?_⟩
  · exact
      { seated := hseat
        blocks := by
          show blk.rounds.zip blk.oracles = _
          rw [hr, ho, hR]
        two := by
          rw [hR]
          rfl
        fits := fits_at_head h.toAtMg O p hp
        seeds := seeds_at_place Zp Bs.G₀ p.place hq s1 s2
        returns := fun w heard ca =>
          returnsLaw D readers Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p
            (closing_at_head h.toAtMg O p hp) w heard ca
        oneRow := placeOneRow_yes (List.all_eq_true.1 oneRowW.1 p hpW)
        send := send_open O p hp }
  · show blk.rounds.length = 2
    rw [hr]
    rfl
  · show blk.oracles.length = 2
    rw [ho]
    rfl

/-- **The statement's end at a place of the kind**, at the side that Side.seated lays there. An
equation of two laws over the part's own coins. -/
theorem exactOf_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (fs : List (Fall TS)) (chain firstTree : Nat) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      Side.seated cF.blocksInOrder p.place (switchRow (coreSender freshTable) D readers
                 (lotClosing Zp Bs.G₀) p
                 (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link))
                 (roundsAt Zp Bs.G₀ p.place)) fs = some σ ∧ σ.fits = true ∧
      ExactOf σ chain firstTree (switchBud p) := by
  obtain ⟨σ, A, hf⟩ := exactAsks_at_head (X := X) h O hp D readers fs
  exact ⟨σ, A.seated, hf, Law.switchExact _ _ _ _ _ _ _ _ _ σ chain firstTree A⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.exactAsks_at_head
#print axioms ProofFile.Honest.K2.Law.exactOf_at_head
