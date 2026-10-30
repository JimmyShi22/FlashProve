-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsIdnFirst.lean: OF THE LINE idn OF `K4Lines`
(Johnson/Road/K4/CloseAtTable.lean) IN THE FIRST GROUP, AT THE FILLED PINNED PART, THE HALF ON THE
17 IDENTITIES: the road's sentence `Idn`, at the first group's value, gives the clause `NormField`
(Johnson/Road/Rows/LayerTop.lean) at "what the prover hides". The twin of
Johnson/Road/K4/K4PinsIdn.lean's `mats_raw`, `norm_of_idn` and of the first half of `idn_fields`, by
their proofs. `own_cast`, `raw_own`, `ownW` name no value: they are taken as they stand. `SeamFit`
AND WHAT HANGS ON IT ARE NOT CALLED: in the first group no stream comes in from a group in front. No
draw, no count.

  `mats_rawF`: under `Covers` the value's matrices are `PinPlan.raw`.
  `norm_of_idnF`: `NormField` at any integers whose casts are the value's matrices.
  `mats_mgF`: the value's matrices off the pinned part of a witness are the casts of "what the
    prover hides": the premise hM of `norm_of_idnF`, AND OF `emb_of_j11`
    (Johnson/Road/K4/K4IdnFirst.lean).
  `norm_fieldsF`: the two laid together.

Limits. K04_law IS NOT PROVED BY THIS. THE OTHER HALF IS NOT HERE: in the first group `EmbField` is
no empty clause (`emb_later` falls): it is to come from (J11), at the request's own tokens and the
committed matrix alone, NOT AT EVERY MATRIX AND EVERY REQUEST (K4IdnFirst.lean). All limits of
K4PinsIdn.lean stand but those on the seam. USER: `k4_own_allF` (K4PinsAllFirst.lean). The reference
sizes alone.
-/
import Johnson.Road.K4.K4PinsIdn
import Johnson.Road.K4.K4PinsMat
import Johnson.Road.K4.K4PinsPlanesFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Model.Verify (Public layerShape)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.Rows.Norms (castM NormField EmbField)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls cellJ szOf)
open VerifiableInference.Desc.Sound (Mem MsgT)
open Cb.Pv.Tail (Size cellValS)
open Inst.Model (Scl Mat)
open Inst.Model.FFSeg (Dim)

/-- Under `Covers` the value's matrices are `PinPlan.raw`: they are the seat's
(`PinPlan.seat_mats_raw`, K4PinsMat.lean). -/
theorem mats_rawF [Scl] {Cells : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public)
    (p : Par) (t : PinM Cells) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).mats t = A.raw tl t :=
  PinPlan.seat_mats_raw A n N tl y nM nR nC n0 ns nx v7 hC t

/-- **The road's sentence gives `NormField`**, at any integers whose casts are the value's matrices,
where the section's table of scales is X's, a group has four layers and the group is the
first. -/
theorem norm_of_idnF [scl : Scl] {M : Type} (U : RefSeat M VerifiableInference.Desc.First.S)
    (X : Public) (p : Par) (eg : p.g = 0) (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4)
    (t : M) (Mz : Mats ℤ) (hM : (U.atRecF X p).mats t = castM Mz)
    (hI : (U.atRecF X p).toLF.planF.toPlan4.Idn t) (Wi : Mat) (xx : Cm.Seg.XI) :
    NormField (layerShape X.P) X.layers.sc U.y p.g Mz Wi xx := by
  have hsc : scl = sclOf (layerShape X.P) X.layers.sc p.g 4 := by
    rw [hscl, ← hlam]
  rw [eg] at hsc ⊢
  intro k ν i hv
  obtain ⟨_, hν, hi⟩ := hv
  have h0 := hI (k, ⟨ν, hν⟩) i hi
  have hc : (U.atRecF X p).toLF.planF.toPlan4.cells t = _ :=
    (U.atRecF X p).cells_eqF t (fun _ _ _ hb => if_neg hb)
  rw [hc, hM] at h0
  subst hsc
  exact h0

/-- **The first group's value's matrices off the pinned part of a witness are the casts of "what the
prover hides"**: from `Covers`, `SitsIn`, "tl's size is s (2 p.g)", `SymsOne` at segment 2 p.g, and
"the group is the first": there `Meaning.mgOf` is the segment's own list, by its text: NO `SeamFit`
IS ASKED. -/
theorem mats_mgF [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (eg : p.g = 0)
    (hC : Covers tl nM nR nC) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)
    (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hσ : szOf tl = s (2 * p.g))
    (h1 : SymsOne A tl arr N (2 * p.g) (s (2 * p.g)) (seat (2 * p.g)))
    (w : Wit Cells Tok MsgT) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).mats (partOf A.D.codes arr ms N m w) =
      castM (Meaning.mgOf y (ownW arr ms N s seat A.D.codes w) p.g) := by
  have emg : Meaning.mgOf y (ownW arr ms N s seat A.D.codes w) p.g =
      ownW arr ms N s seat A.D.codes w (2 * p.g) := by
    funext a
    unfold Meaning.mgOf
    rw [if_neg (fun h => by have := h.2; omega)]
  rw [mats_rawF A n N tl y nM nR nC n0 ns nx v7 hC X p,
    raw_own A tl arr ms N m s seat (2 * p.g) hσ hs h1 w, emg]
  rfl

/-- **THE ROAD's SENTENCE ON THE 17 IDENTITIES GIVES `NormField` AT "WHAT THE PROVER HIDES"**, in
the first group: from "the section's table of scales is X's", a group has four layers, the
group is the first, and the premises of `mats_mgF`. -/
theorem norm_fieldsF [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (eg : p.g = 0)
    (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4)
    (hC : Covers tl nM nR nC) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)
    (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hσ : szOf tl = s (2 * p.g))
    (h1 : SymsOne A tl arr N (2 * p.g) (s (2 * p.g)) (seat (2 * p.g))) (w : Wit Cells Tok MsgT)
    (hI : ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toLF.planF.toPlan4.Idn
      (partOf A.D.codes arr ms N m w)) (Wi : Mat) (xx : Cm.Seg.XI) :
    NormField (layerShape X.P) X.layers.sc y p.g
      (Meaning.mgOf y (ownW arr ms N s seat A.D.codes w) p.g) Wi xx :=
  norm_of_idnF (A.seatN n N tl y nM nR nC n0 ns nx v7) X p eg hscl hlam _ _
    (mats_mgF A n N tl y nM nR nC n0 ns nx v7 X p eg hC arr ms m hs s seat hσ h1 w) hI Wi xx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mats_rawF
#print axioms OnBytes.Road.K4.norm_of_idnF
#print axioms OnBytes.Road.K4.mats_mgF
#print axioms OnBytes.Road.K4.norm_fieldsF
