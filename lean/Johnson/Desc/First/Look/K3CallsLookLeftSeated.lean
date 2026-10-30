-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
k3_lay_lookLeft_seated: no place of a stored set is shown at which all
premises hold together.
Johnson/Desc/First/Look/K3CallsLookLeftSeated.lean: the lookup on a layers' link's CALLS: THE
MAKER's LEMMA OF THE PUBLIC ITEM (some m, "K4.lookLeft") AT THE SEATED PIECE: where a piece that
holds "below B'", B' any sub-protocol that narrows the value of K3.theStated at the address,
accepts, the test lookLeftB (Johnson/Desc/First/FillBare.lean) is true at the verifier's state that
it puts out. One theorem and a small one. A tie of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a, and any B' that narrows it.
USER: K03LeftQ.lean, K03ReachedAt.lean (planOk_room). k3_lay_lookLeft_seated: nobody yet (the clause
  of the promise behind the lookup on the calls at a layers' link).
LETTERS: a with a.link = some i, a.piece = K3.pieceAt X i false; x: any place whose parameters are
  placeAt X i false's value; W free.
Compiled with the whole library.


Main names:
  `planOk_room`: the kind's test on the public parameters says that the link has room for the
    lookup's scalars from the first slot on.
  `k3_lay_lookLeft_seated`: by k3_calls_stated_yes (K3CallsStatedYes.lean), stated_planOk
    (K3PlanOfOk.lean) and k3_calls_lookLeft (K3CallsLookLeft.lean).

WHAT IS LEFT, AND WHOSE IT IS. h, hOk, hN, hp, hback, hl, hpc, e: the seat's. hF, hQ: the promise in
front (the ledger's items). hlay: the promise's stand at a layers' link.

Limits. At a layers' link alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsLookLeft
import Johnson.Desc.First.Look.K3CallsStatedYes
import Johnson.Desc.First.Look.K3PlanOfOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.FillBare (lookLeftB)

/-- The kind's test on the public parameters: room for the lookup's scalars. -/
theorem planOk_room {S Cl : Type} {p : Desc.First.Look.P} {laid : Array Nat}
    {guests : List (Desc.First.Look.Guest S Cl)} (h : p.planOk laid guests = true) :
    ∃ hs, p.shape = some hs ∧ p.first + Forest.elems hs ≤ p.ns := by
  unfold Desc.First.Look.P.planOk at h
  cases e : p.shape with
  | none =>
    rw [e] at h
    cases h
  | some hs =>
    rw [e] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨hs, rfl, h.1.1.2⟩

section
variable {Cl W : Type} {Fr : Frame} {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **WHERE THE SEATED PIECE ACCEPTS, "K4.lookLeft" IS MADE.** -/
theorem k3_lay_lookLeft_seated (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (p : Piece (ckP .two) Fr Desc.First.S Cl W) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP) (hback : p.back = [])
    (s c : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
    (hc : p.ior.red.out s τ = some c) {F : Fork} (hF : s.1.fork? = some F)
    (hQ : LeftQ (theP).ns F) (hlay : ∃ a', s.1.here = .lay a') : lookLeftB c.1 = true := by
  obtain ⟨laid, sent, rs, cols, hw, hd⟩ :=
    k3_calls_stated_yes claim readers codes shape a B B' h hOk hN p hp hl hpc e hback s c τ hc
  obtain ⟨j, d, p', laid', hj, hpj, hP, hk⟩ :=
    Desc.K3.stated_planOk claim readers X codes shape a B h hOk
  obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
  have ed : d = false := (Desc.K3.pieceAt_inj X i (hpc.symm.trans hpj)).symm
  subst ed
  have eP : p' = theP := Option.some.inj (hP.symm.trans e)
  subst eP
  obtain ⟨hs, e1, e2⟩ := planOk_room hk
  exact k3_calls_lookLeft claim a.piece laid sent theP [] s.1 c.1 rs cols e1 hw hd hF hQ e2 hlay

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_lookLeft_seated
