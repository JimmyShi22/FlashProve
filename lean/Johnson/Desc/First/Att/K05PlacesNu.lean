-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05PlacesNu.lean: kind K5: TWO DICTIONARY LINES BETWEEN THE LOOKUPS' READING
OF THE PLACES AT AN ATTENTION LINK (attNu, Johnson/Desc/First/Look/K3AttGoodIn.lean)
AND THIS KIND's READINGS OF THE SAME TUPLE OF MESSAGES:
  `places_are_nu`: the planes' matrix of matsOfData (Johnson/Desc/First/Att/K05DataMats.lean) is
    attNu at the cells, AT EVERY r AND c, under AddrTie at the witness's messages attMs. THE
    STATEMENT AND THE PROOF COME FROM THE LOOKUP's SIDE (read in a text of ours, not in
    this repository): compiled here, as it stands above files of both kinds (the lookup's; K5's).
  `mask_is_nu`: the law's reading of the mask row, (attLin …).maskOf at attMs, is attNu at the masks
    BELOW THE PLACE's NUMBER OF SLOTS. (From there on attNu is 0, and the law's reading is whatever
    has a seat.)
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05DataMats
import Johnson.Desc.First.Look.K3AttGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT GQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu)

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Shape)
  (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- **The planes' matrix of the data is the lookup's places, at every row and column.** -/
theorem places_are_nu {arrayOf : Array (ℕ × String)} {Dt : Bound GQ} {fs : List Aff}
    (w : Wit Cells Tok MsgT) (T : AddrTie x tl D rad arrayOf (attMs x D rad seatT arr w) Dt fs)
    (r c : ℕ) :
    matsOfData tl arrayOf Dt (A.cf.NAs + 2) r c = attNu x A tl D rad seatT arr w (.cell r c) := by
  rw [← matsOfData_eq x tl D rad T]
  rfl

/-- **The law's reading of the mask row is the lookup's places at the masks.** -/
theorem mask_is_nu (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)
    (w : Wit Cells Tok MsgT) (j : ℕ) (hj : j < x.ns) :
    (attLin x A tl D rad Ex Wp α ns N).maskOf (attMs x D rad seatT arr w) j =
      attNu x A tl D rad seatT arr w (.mask j) := by
  have e : VerifiableInference.Desc.First.Look.enMask x.ns tl j = some (Sum.inl ⟨j, hj⟩) := by
    unfold VerifiableInference.Desc.First.Look.enMask
    rw [VerifiableInference.Desc.First.Look.finOf_some hj]
    rfl
  show _ = VerifiableInference.OnPublicFiles.attMu x tl D rad seatT arr w
    (VerifiableInference.Desc.First.Look.enMask x.ns tl j)
  rw [e]
  rfl

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.places_are_nu
#print axioms VerifiableInference.Desc.First.Att.P.mask_is_nu
