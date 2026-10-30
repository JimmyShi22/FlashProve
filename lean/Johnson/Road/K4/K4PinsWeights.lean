-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsWeights.lean: THE GROUP's WEIGHTS THAT K4's VALUE AT THE REFERENCE SIZES READS
OFF THE PINNED PART (`Plan4.weights`, Johnson/Road/K4/ValueSays.lean, at `PinPlan.seat`,
Johnson/Road/K4/K4PinsRead.lean) ARE THE LAYERS' MATRICES OF WHICH THE KEYS OF THE LOOKUP's CALLER
ARE MADE (`layLay`'s term `layerR ppref kRef (wOfE μ) (4 * g + l)`,
Johnson/Desc/First/Look/K3CallerLay.lean), at nr := `hRef` rows and nc := 2 ^ `kRef` columns. Two
theorems, by unfolding. No draw, no count.

  `Plan4.Wn_msg`: the value's committed matrix off a tuple m: matAt m inside its rows and columns, 0
    outside.
  `weights_lay`: at the value `(A.seat …).atRec X p hg`, A := `planAt` with rc := `cutW enc wOf hRef
    (2 ^ kRef)`: `weights t l = layerR ppref kRef (wOfE (msgLay x tl D rad oW wOf hRef (2 ^ kRef)
    mm)) (4 * p.g + l)`, at a tuple t that holds cells C with `mm none = enc C`.

OBJECT: none of its own. USER: none yet; meant: whoever ties what K4's row concludes on the keys to
what the lookup's law takes. LETTERS, filled by nobody: those of Johnson/Road/K4/K4PinsW.lean, and
what `PinPlan.seat` hands through.

Limits. K04_law IS NOT PROVED BY THIS. Those of K4PinsW.lean: IT IS NOT SHOWN THAT THE REAL STORED
TABLE's DECODER IS AN `OMsg`'s. The premise on t is met at the pinned part of a witness the image
of whose cells under enc is mm none (`lay_part_W`). The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls laySg msgLay wOfE)
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (layerR)

/-- The value's committed matrix off a tuple: matAt inside its rows and columns, 0 outside. -/
theorem Plan4.Wn_msg {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4 E M X)
    (m : M) (r c : ℕ) :
    Q.Wn (Q.msg m) r c = if r < Q.hW ∧ c < 2 ^ Q.kW then Q.matAt m r c else 0 := by
  unfold Plan4.Wn
  by_cases h : r < Q.hW ∧ c < 2 ^ Q.kW
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]

variable [scl : Scl] (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)

/-- **The group's weights are the caller's layers' matrices**, at hRef rows and 2 ^ kRef columns, at
a tuple that holds cells whose image under enc is the caller's external member. -/
theorem weights_lay (N : Numbers) (tl' : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ)
    (X : Public) (p : Par) (hg : p.g < 12) (mm : (laySg x D rad oW).Msg) (t : PinM Cells)
    (C : Cells) (h : t.2 = some C) (h0 : mm none = enc C) (l : ℕ) :
    ((((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seat N tl' y nM nR nC n0 ns nx
        v7).atRec X p hg).plan.weights t) l =
      layerR ppref kRef (wOfE (msgLay x tl D rad oW wOf hRef (2 ^ kRef) mm)) (4 * p.g + l) := by
  have e : (((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seat N tl' y nM nR nC n0 ns
      nx v7).atRec X p hg).plan.Wn
        ((((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seat N tl' y nM nR nC n0 ns nx
          v7).atRec X p hg).plan.msg t) =
      wOfE (msgLay x tl D rad oW wOf hRef (2 ^ kRef) mm) := by
    rw [mat_lay x D rad seatT posI tl oW enc wOf hRef (2 ^ kRef) mm t C h h0]
    funext r c
    rw [Plan4.Wn_msg]
    show (if r < hRef ∧ c < 2 ^ kRef then
        (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).mat t r c else 0) = _
    by_cases hrc : r < hRef ∧ c < 2 ^ kRef
    · rw [if_pos hrc]
    · rw [if_neg hrc, PinPlan.mat_some _ h]
      show 0 = cutW enc wOf hRef (2 ^ kRef) C r c
      unfold cutW
      rw [if_neg hrc]
  unfold Plan4.weights
  rw [e, Nat.mul_comm 4 p.g]
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.Wn_msg
#print axioms OnBytes.Road.K4.weights_lay
