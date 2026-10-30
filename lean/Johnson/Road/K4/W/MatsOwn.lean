-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/MatsOwn.lean: CONDITIONAL.

What is here. THE MATRICES THAT THE CALLER OF THE LOOKUP ON A LAYERS' LINK's CALLS READS OFF A
WITNESS (`matsOfE` of `msgLay` over `layMs`, Johnson/Desc/First/Look/) ARE THE CASTS OF THE LIST OF
INTEGERS THAT THE LIBRARY's MEANING READS OFF THE SAME WITNESS FOR THE GROUP (`Meaning.mgOf` of the
segments' own lists `ownW`, Johnson/Road/K4/K4PinsIdn.lean): AT EVERY WITNESS, at every triple of
indices, from conditions on public letters alone. The library has the two halves at its own value's
matrices (`mats_mgF`, K4PinsIdnFirst.lean, in the first group; inside `idn_fields`, K4PinsIdn.lean,
in a later one); here they are joined at the caller's reading, in one statement for all groups. The
chain: the caller's matrices are the plan's raw ones at the pinned part of the witness (`raw_lay`,
K4PinsLay.lean, with `tupleOf_part`, K4PinsRead.lean); these are the casts of the segment's own list
(`raw_own`); in the first group the group's list is the segment's own by the text of `Meaning.mgOf`,
as in the library's proof of `mats_mgF`; in a later group by `mg_own` and `seam_of_fit`. It imports
nothing of the honest side; Johnson/Road/K4/W/TwoReaders.lean is imported for what it imports
(`layMs`, `raw_lay`): none of its own statements is called. Each proof is a chain of calls, but
`mg_first`, which unfolds.

  `own_part`   the first chain's part of the caller's tuple off a witness is the plan's tuple out
      of the witness's pinned part.
  `mg_first`, `mg_all`   the group's list is the segment's own.
  `mats_mg`   **the caller's matrices are the casts of the group's list.**

Not shown here. hs (`SitsIn`, Johnson/Road/K4/K4PinsRead.lean), hσ (the tail's size is the
segment's), h1 (`SymsOne`, K4PinsSym.lean) and, in a later group, hS (`SeamFit`, K4PinsIdn.lean):
CONDITIONS ON PUBLIC LETTERS: hypotheses here; Law/W/MatsAreHead.lean has the four together under
the library's hypothesis on the public files. WHAT IT SAYS: that two readers of one witness read one
thing. NOTHING ON WHAT A CELL IS WORTH: the equation holds whether or not the committed symbols
encode integers in range; nothing on an honest prover's cells, on weights, on tokens or on the mask
row. No test stands beside it. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 3 modules under Johnson/Goal/ and at 1 under Johnson/Bridge/; it saw 28 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 4 is not counted: the numbers are floors. They come with the
library's files that are called. THE STATEMENTS NAME `Meaning.mgOf`, a definition of a file under
Johnson/Goal/, and `mg_first` unfolds it, as the library's Johnson/Road/K4/K4PinsIdnFirst.lean does.
It imports nothing of the honest side (Johnson/Desc/ProofFile/Honest/). A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one.
-/
import Johnson.Road.K4.W.TwoReaders
import Johnson.Road.K4.K4PinsIdn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay)
open OnBytes.Road.K4 (SitsIn SymsOne SeamFit ownW partOf planAt raw_lay raw_own mg_own seam_of_fit
  tupleOf_part)
open OnBytes.Road.Rows.Norms (castM)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf ownPart msgLay matsOfE)
open VerifiableInference.Desc.Sound (Mem MsgT)
open VerifiableInference.OnPublicFiles (layMs)
open Cb.Pv.Tail (Size)

variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (rc : Cells → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)

/-- CONDITIONAL: on hs. The first chain's part of the caller's tuple off a witness is the plan's
tuple out of the witness's pinned part. -/
theorem own_part (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (w : Wit Cells Tok MsgT) :
    ownPart (layMs x D rad oW seatT arr msgW w) =
      (planAt x D rad seatT rc posI).tuple (partOf D.codes arr ms N m w) :=
  (tupleOf_part D.codes (sigListCalls D rad x.link) seatT arr ms N m hs w).symm

variable (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- CONDITIONAL: on hg. In the first group the group's list is the segment's own, by the text of
`Meaning.mgOf`. -/
theorem mg_first (cs : OnBytes.Codes) (y : Lay) (g : ℕ) (hg : g = 0) (w : Wit Cells Tok MsgT) :
    _root_.Meaning.mgOf y (ownW arr ms N s seat cs w) g = ownW arr ms N s seat cs w (2 * g) := by
  funext a
  unfold _root_.Meaning.mgOf
  rw [if_neg (fun h => by have := h.2; omega)]

/-- CONDITIONAL: on hS. **The group's list is the segment's own**, in every group. -/
theorem mg_all (cs : OnBytes.Codes) (y : Lay) (g : ℕ)
    (hS : 0 < g → SeamFit arr ms N s seat cs y g) (w : Wit Cells Tok MsgT) :
    _root_.Meaning.mgOf y (ownW arr ms N s seat cs w) g = ownW arr ms N s seat cs w (2 * g) := by
  rcases Nat.eq_zero_or_pos g with g0 | gp
  · exact mg_first arr ms N s seat cs y g g0 w
  · exact mg_own arr ms N s seat cs y g w (seam_of_fit arr ms N s seat cs y g (hS gp) w)

/-- CONDITIONAL: on hs, hσ, h1 and hS. **THE CALLER's MATRICES ARE THE CASTS OF THE GROUP's LIST**,
at every witness. g: the group; its segment is 2 g. m: the segment at which hs is asked; nothing
here ties it to 2 g. rc, posI: read by h1 alone. -/
theorem mats_mg (y : Lay) (g : ℕ) (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hσ : szOf tl = s (2 * g))
    (h1 : SymsOne (planAt x D rad seatT rc posI) tl arr N (2 * g) (s (2 * g)) (seat (2 * g)))
    (hS : 0 < g → SeamFit arr ms N s seat D.codes y g) (w : Wit Cells Tok MsgT) :
    matsOfE (msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)) =
      castM (_root_.Meaning.mgOf y (ownW arr ms N s seat D.codes w) g) := by
  rw [raw_lay x D rad seatT rc posI tl oW wOf nr nc _ _
      (own_part x D rad seatT rc posI oW arr ms N m msgW hs w),
    mg_all arr ms N s seat D.codes y g hS w]
  exact raw_own (planAt x D rad seatT rc posI) tl arr ms N m s seat (2 * g) hσ hs h1 w

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.own_part
#print axioms OnBytes.Road.K4.W.mg_first
#print axioms OnBytes.Road.K4.W.mg_all
#print axioms OnBytes.Road.K4.W.mats_mg
