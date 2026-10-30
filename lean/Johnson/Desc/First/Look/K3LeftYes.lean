-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LeftYes.lean: the lookup on a link's CALLS, at any closed caller: WHAT A
YES OF THE BLOCK's PIECE LEAVES, WITH THE PROVED BLOCK's OUT-STATEMENT BY NAME; and the sharp
promise laid BESIDE an end theorem that lies. K3YesNamesOut and K3CallsKeepLeft
(Johnson/Desc/First/Look/K3LeftRuleStatement.lean), proved under ONE NAMED PREMISE, LkPadCEnd
(Johnson/Top/H/K3LeftProof.lean: the form left for the join names no entry of a virtual row, and its
slots are filled and below the number of slots). Theorems with their proofs.

Main names:
  `k3YesNamesOut_of`, `k3CallsKeepLeft_of`: the two statements.
  `k3_left_beside_of`: any GoodIn of the piece whose condition in front is COn gives GoodIn with the
    condition "COn, and Q of the ledger in front" and the promise "the old promise, and K3LeftAt at
    Q": NO RELATION AND NO THEOREM THAT LIES TURNS.

Limits. Ties: no error term. Q is a letter.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LeftRule
import Johnson.Top.H.K3LeftProof
import Johnson.Top.H.K3PieceHears
import Johnson.Top.H.K3DecideMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **ONE THEOREM AT A YES OF THE BLOCK, general in the caller.** -/
theorem k3YesNamesOut_of (hC : Fo.Tp.LkPadCEnd) : K3YesNamesOut := by
  rintro Cl W Fr r set x mk pl st y₀ sm wd claim piece laid before guests b hyes p hb hback hsh
    hmk hbc hM hA a τ a' ⟨Fk, hFk, hSz⟩ ho
  obtain ⟨-, -, hw, cols, hdec⟩ := piece_hears_below p b hb hback a τ a' ho
  have hdec' := hyes _ _ _ _ hdec
  obtain ⟨F, F', g, hF, hF', hg, hL⟩ := k3LeavesAtCalls_of hC Cl claim piece laid before _ guests
    r.c.h hsh Cb.Gl.E Reading.gl x.lm a.1 a'.1 _ cols hw hdec'
  obtain rfl : Fk = F := Option.some.inj (hFk.symm.trans hF)
  have hnx : Fk.next = x.F.next :=
    decide_first _ piece laid before _ guests a.1 a'.1 _ cols Fk hFk hdec'
  have hL' := hL hSz
  rw [viewRounds_noDigest] at hL'
  exact ⟨Fk, F', g, hFk, hnx, hF', hg, hL',
    lookKindR_view [r] r (_root_.Fo.Pay.shapeOf_ok (shape_some _ _ hsh)) x.lm x.F.next mk pl hmk hbc
      p.ds hM hA
      (cRd r st y₀ sm wd a) τ⟩

/-- **So the piece keeps the sharp promise.** -/
theorem k3CallsKeepLeft_of (hC : Fo.Tp.LkPadCEnd) : K3CallsKeepLeft := by
  rintro Cl W Fr h set x claim piece laid before guests b hyes p hb hback hsh Q a τ a'
    ⟨Fk, hFk, hSz, hQ⟩ ho
  obtain ⟨-, -, hw, cols, hdec⟩ := piece_hears_below p b hb hback a τ a' ho
  have hdec' := hyes _ _ _ _ hdec
  obtain ⟨F, F', g, hF, hF', hg, hL⟩ := k3LeavesAtCalls_of hC Cl claim piece laid before _ guests
    h hsh Cb.Gl.E Reading.gl x.lm a.1 a'.1 _ cols hw hdec'
  obtain rfl : Fk = F := Option.some.inj (hFk.symm.trans hF)
  have hnx : Fk.next = x.F.next :=
    decide_first _ piece laid before _ guests a.1 a'.1 _ cols Fk hFk hdec'
  exact ⟨Fk, F', g, _, hQ, hnx, hL hSz, hg, hF'⟩

/-- **The sharp promise, laid beside an end theorem that lies.** -/
theorem k3_left_beside_of (hC : Fo.Tp.LkPadCEnd) {Cl W : Type} {Fr : Frame} {h : Forest.Shape}
    {set : Params.Setting} {x : Desc.First.Look.Place} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hb : p.b = below b) (hback : p.back = [])
    (hsh : (Desc.First.Look.P.ofPlace set false x).shape = some h)
    (Cond on' : Desc.First.S × Fr.E.Str → Prop) (R R' : Desc.First.S × Fr.E.Str → W → Prop)
    (hG : p.GoodIn (COn (Desc.K3.seatCalls claim).fork Cond) on' R R') (Q : Fork → Prop) :
    p.GoodIn
      (fun a => COn (Desc.K3.seatCalls claim).fork Cond a ∧
        ∀ F, (Desc.K3.seatCalls claim).fork a.1 = some F → Q F)
      (fun c => on' c ∧ K3LeftAt (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard h
        x.lm x.F.next Q c.1) R R' :=
  goodInPromise _ _ _ _ p _ _ _ _ _ (fun a ha => hG a ha.1) fun a τ c ha hc => by
    obtain ⟨⟨-, Fk, hFk, hSz⟩, hQ⟩ := ha
    exact k3CallsKeepLeft_of hC Cl W Fr h set x claim piece laid before guests b hyes p hb hback
      hsh Q a τ c ⟨Fk, hFk, hSz, hQ Fk hFk⟩ hc

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3YesNamesOut_of
#print axioms VerifiableInference.OnPublicFiles.k3CallsKeepLeft_of
#print axioms VerifiableInference.OnPublicFiles.k3_left_beside_of
