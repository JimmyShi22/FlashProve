-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LeftAll.lean: the lookup on a link's CALLS, at any closed caller: WHAT A
YES OF THE BLOCK's PIECE LEAVES, WITH NO PREMISE LEFT: the three theorems of
Johnson/Desc/First/Look/K3LeftYes.lean at the theorem lkPadCEnd (Johnson/Top/H/K3CEnd.lean).

Main names: `k3YesNamesOut` · `k3CallsKeepLeft` · `k3_left_beside`.

Limits. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LeftYes
import Johnson.Top.H.K3CEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **ONE THEOREM AT A YES OF THE BLOCK, general in the caller.** -/
theorem k3YesNamesOut : K3YesNamesOut := k3YesNamesOut_of Fo.Tp.lkPadCEnd

/-- **The piece keeps the sharp promise.** -/
theorem k3CallsKeepLeft : K3CallsKeepLeft := k3CallsKeepLeft_of Fo.Tp.lkPadCEnd

/-- **The sharp promise, laid beside an end theorem that lies.** -/
theorem k3_left_beside {Cl W : Type} {Fr : Frame} {h : Forest.Shape}
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
  k3_left_beside_of Fo.Tp.lkPadCEnd claim piece laid before guests b hyes p hb hback hsh Cond on' R
    R' hG Q

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3YesNamesOut
#print axioms VerifiableInference.OnPublicFiles.k3CallsKeepLeft
#print axioms VerifiableInference.OnPublicFiles.k3_left_beside
