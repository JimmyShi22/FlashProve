-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3RidesCalls.lean: the kind "lookup" (K3) AT THE TABLE OF JOINTS: SameOut
(by SameBut.sameOut, Johnson/Desc/First/Look/K3Rides.lean) AT THE VALUE OF K3.theStated, at
a link's lookup on the calls: a yes of the seated piece turns the open link's own part of the
carried record and nothing else. One theorem: by k3_calls_stated_yes (K3CallsStatedYes.lean) and
k3_calls_sameBut (K3CallsTurns.lean). A tie: no error term. NO RESULT ON THE PROTOCOL.

OBJECT: the piece ⟨below B', q.base, q.ds, q.back, the identity, q.err⟩, B' any block that narrows
  the value Bst of K3.theStated at the address and whose yes bears no mark.
USER: nobody yet.
LETTERS: claim, readers, X, codes, shape, a, Bst, i, x, q free.
Compiled with the whole library.



Limits. h, hOk, the address's two equations, the place's and hback are premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Rides
import Johnson.Desc.First.Look.K3CallsStatedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cl P W : Type} {Fr : Frame}

/-- **At a link's lookup on the calls a yes of the seated piece is SameOut.** -/
theorem calls_seated_sameOut (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (Bst : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (i : ℕ) (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    {x : Desc.First.Look.Place}
    (e : placeAt X i false = some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl W) (hback : q.back = []) :
    ∀ B', SeatOf Bst B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl W).ior.red.out u τ = some v →
      Desc.First.SameOut u.1 v.1 := by
  intro B' hS u τ v hv
  obtain ⟨laid, sent, rs, cols, -, hd⟩ :=
    k3_calls_stated_yes claim readers codes shape a Bst B' h hOk hS.1
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl W) rfl hl hpc e hback u v τ hv
  exact (k3_calls_sameBut claim a.piece laid sent _ [] u.1 v.1 rs cols hd).sameOut

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.calls_seated_sameOut
