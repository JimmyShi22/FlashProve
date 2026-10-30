-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLay.lean: THE MATRICES AND THE MASK ROW THAT K4's VALUE READS OFF THE PINNED
PART (`PinPlan.raw`, `PinPlan.mask`, Johnson/Road/K4/K4PinsRead.lean) ARE THOSE THAT THE CALLER OF
THE LOOKUP ON A LAYERS' LINK's CALLS READS OFF ITS TUPLE OF MESSAGES (`msgLay`, `matsOfE`,
Johnson/Desc/First/Look/K3CallerLay.lean), wherever the first chain's part of that tuple is the
tuple out of the pinned part. A definition and three theorems, by unfolding. No draw, no count.

  `planAt x D rad seatT rc posI`: the `PinPlan` whose link's number is the place x's.
  `raw_lay`: `matsOfE (msgLay x tl D rad oW wOf nr nc mm) = (planAt …).raw tl t`, if
    `ownPart mm = (planAt …).tuple t`.
  `mask_lay`: under the same premise, for j below x.ns: `msgLay … mm (lyMask x.ns tl nr nc j)` is
    `(planAt …).mask t j`.
  `lay_part`: under `SitsIn`: at a witness w, and a tuple mm whose first chain's part is w's own
    messages (`msgsOf`), both hold at t := the pinned part of w.

NEEDS, beside this folder's files: Johnson/Desc/First/Look/K3CallerLay.lean and
Johnson/Desc/First/Look/K3CallerAttMeans.lean.

OBJECT: none of its own. USER: none yet; meant: whoever ties what K4's row concludes (worth m 2) to
what the lookup's law takes. LETTERS, filled by nobody: the place x, tl, D, rad, the stored table's
oracle message oW and its reader wOf, nr, nc, the seats, rc, posI.

Limits. K04_law IS NOT PROVED BY THIS. THE WEIGHTS ARE NOT TIED HERE: the caller reads them off an
oracle message (wOf of the tuple's external member), K4's value off the witness's cells (rc): at one
reading of the two: Johnson/Road/K4/K4PinsW.lean, K4PinsWeights.lean. From x.ns on the caller reads
a mask entry as 0; `PinPlan.mask` reads on as far as the message's table goes. `SitsIn` has run
nowhere.
-/
import Johnson.Road.K4.K4PinsRead
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls cellJ szOf finOf_some laySg ownPart
  msgLay matsOfE lyCell lyMask)
open VerifiableInference.Desc.Sound (Mem MsgT msgsOf)

variable {Cells : Type} (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (rc : Cells → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ)

/-- The letters on the plan, at the place's own link. -/
def planAt : PinPlan Cells := ⟨D, rad, x.link, seatT, rc, posI⟩

variable (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)

/-- **The matrices are the caller's**, where the first chain's part of its tuple is the tuple out of
the pinned part. -/
theorem raw_lay (mm : (laySg x D rad oW).Msg) (t : PinM Cells)
    (h : ownPart mm = (planAt x D rad seatT rc posI).tuple t) :
    matsOfE (msgLay x tl D rad oW wOf nr nc mm) = (planAt x D rad seatT rc posI).raw tl t := by
  funext a r c
  unfold matsOfE lyCell PinPlan.raw
  rw [← h]
  cases cellJ (szOf tl) a r c <;> rfl

/-- **So is the mask row**, below the place's number of slots. -/
theorem mask_lay (mm : (laySg x D rad oW).Msg) (t : PinM Cells)
    (h : ownPart mm = (planAt x D rad seatT rc posI).tuple t) (j : ℕ) (hj : j < x.ns) :
    msgLay x tl D rad oW wOf nr nc mm (lyMask x.ns tl nr nc j) =
      (planAt x D rad seatT rc posI).mask t j := by
  unfold lyMask PinPlan.mask
  rw [← h, finOf_some hj]
  rfl

/-- **At a witness**: under `SitsIn`, at a tuple whose first chain's part is the witness's own
messages. -/
theorem lay_part {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (w : Wit Cells Tok MsgT)
    (mm : (laySg x D rad oW).Msg)
    (h : ownPart mm = msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) :
    matsOfE (msgLay x tl D rad oW wOf nr nc mm) =
        (planAt x D rad seatT rc posI).raw tl (partOf D.codes arr ms N m w) ∧
      ∀ j, j < x.ns → msgLay x tl D rad oW wOf nr nc mm (lyMask x.ns tl nr nc j) =
        (planAt x D rad seatT rc posI).mask (partOf D.codes arr ms N m w) j := by
  have e : ownPart mm =
      (planAt x D rad seatT rc posI).tuple (partOf D.codes arr ms N m w) :=
    h.trans ((planAt x D rad seatT rc posI).tuple_part arr ms N m hs w).symm
  exact ⟨raw_lay x D rad seatT rc posI tl oW wOf nr nc mm _ e,
    fun j hj => mask_lay x D rad seatT rc posI tl oW wOf nr nc mm _ e j hj⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.raw_lay
#print axioms OnBytes.Road.K4.mask_lay
#print axioms OnBytes.Road.K4.lay_part
