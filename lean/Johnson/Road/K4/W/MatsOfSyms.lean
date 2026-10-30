-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/MatsOfSyms.lean: CONDITIONAL.

Not shown here. THAT THE SYMBOLS WHICH ANY DATA HOLD ARE THE SYMBOLS WHICH THE LOOKUP's CALLER READS
OFF ANY MESSAGES: hSy, and hP in plain numbers, are hypotheses, and they are the content: at a run's
data and messages no example is known. hP CAN HOLD AS 0 = 0, AND CAN BE FALSE WHERE THE MESSAGES ARE
AS THEY SHOULD BE: both readers answer 0, without a word, where they find no seat for an array. THAT
`MatsAre` HOLDS OF ANY MESSAGES AND LIST: hA is a hypothesis. Both sides are read at ONE plan tl:
that the plan at which the data are read is the plan at which the lookup's caller stands is the
caller's to show. `cells_of_syms` stands AT THE FULL SIZE ALONE: the lookup's caller reads its cells
at the library's reference sizes `DF`; the others are general in the sizes. Nothing on soundness, on
completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).

The hypothesis hC of `k4_hot_mats` (Johnson/Desc/ProofFile/Honest/K4/Law/W/HotHead.lean: the cells
of the matrices that are unpacked from the data are the cells that the lookup's caller reads off the
messages) from an equation of committed symbols. The two matrices have one text: a cell inside the
plan's sizes is the one unpacking `cellValS` of the symbols, and 0 stands outside (`matsOfData`,
Johnson/Desc/Sound/DataMats.lean; `matsOfE`, `msgLay`, `lyCell`,
Johnson/Desc/First/Look/K3CallerLay.lean). So they are equal AT EVERY TRIPLE OF INDICES where the
symbols are. Statements with their proofs: unfolding.

  `mats_of_syms`   **`matsOfData tl names Dt = matsOfE (msgLay x tl Ds rad oW wOf nr nc m)`**, from
      hSy: the data's symbols are the symbols that the caller reads off its first chain's messages.
  `mats_of_are`   so `matsOfData tl names Dt = castM L` wherever the library's `MatsAre` holds of
      the caller's messages and a list L of integer matrices: no packing is asked of the data.
  `syms_of_plain`   hSy from one equation of field elements at each matrix a, row of symbols i and
      column c inside the sizes, IN PLAIN NUMBERS: both sides read the address
      `.cell (tl.gtTree.getD a 0) i c`.
  `cells_of_syms`   so hC, where the layout is the caller's.
-/
import Johnson.Desc.Sound.DataMats
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.Rows (Addr)
open Cb.Pv.Tail (cellValS)
open Inst.Model.All (DF)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ dataByAddr symOfData matsOfData)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls szOf cellJ symAt valAt laySg
  ownPart msgLay matsOfE lyCell LayPub layCells MatsAre)
open OnBytes.Road.Rows.Norms (castM)

variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (Ds : Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (m : (laySg x Ds rad oW).Msg) (names : Array (ℕ × String)) (Dt : Bound GQ)

/-- **The matrices off the data are the matrices that the lookup's caller reads, at every triple of
indices.** CONDITIONAL: on hSy. -/
theorem mats_of_syms
    (hSy : symOfData tl names Dt =
      symAt Ds.codes (sigListCalls Ds rad x.link) (seatCalls Ds x.link) tl (ownPart m)) :
    matsOfData tl names Dt = matsOfE (msgLay x tl Ds rad oW wOf nr nc m) := by
  funext a r c
  unfold matsOfData matsOfE lyCell
  cases cellJ (szOf tl) a r c with
  | none => rfl
  | some j => exact congrArg (fun y => cellValS y j) hSy

/-- **So the matrices off the data are the images of whatever list the caller's matrices are the
images of** (`MatsAre`, Johnson/Desc/First/Look/K3CallerLay.lean). CONDITIONAL: on hSy and hA. -/
theorem mats_of_are
    (hSy : symOfData tl names Dt =
      symAt Ds.codes (sigListCalls Ds rad x.link) (seatCalls Ds x.link) tl (ownPart m))
    {L : Mats ℤ} (hA : MatsAre x tl Ds rad oW wOf nr nc m L) :
    matsOfData tl names Dt = castM L :=
  (mats_of_syms x tl Ds rad oW wOf nr nc m names Dt hSy).trans hA

/-- **The equation of symbols, from plain numbers.** CONDITIONAL: on hP. -/
theorem syms_of_plain
    (hP : ∀ a, a < (szOf tl).NM → ∀ i, i < Alg.symRows ((szOf tl).m a) → ∀ c, c < (szOf tl).k a →
      dataByAddr names Dt (Addr.cell (tl.gtTree.getD a 0) i c) =
        (valAt Ds.codes (sigListCalls Ds rad x.link) (seatCalls Ds x.link) (ownPart m)
          (Addr.cell (tl.gtTree.getD a 0) i c)).getD 0) :
    symOfData tl names Dt =
      symAt Ds.codes (sigListCalls Ds rad x.link) (seatCalls Ds x.link) tl (ownPart m) := by
  funext μ i' c
  exact hP μ.val μ.isLt i'.val i'.isLt c.val c.isLt

/-- **The hypothesis hC of `k4_hot_mats`.** q: the caller's public values. CONDITIONAL: on hy and
hSy. -/
theorem cells_of_syms (q : LayPub) {y : Layer.Lay} (hy : y = q.y)
    (hSy : symOfData tl names Dt =
      symAt Ds.codes (sigListCalls Ds rad x.link) (seatCalls Ds x.link) tl (ownPart m)) :
    cellsOf DF (cellsAt y (matsOfData tl names Dt)) = layCells x q tl Ds rad oW wOf nr nc m := by
  subst hy
  rw [mats_of_syms x tl Ds rad oW wOf nr nc m names Dt hSy]
  rfl

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.mats_of_syms
#print axioms OnBytes.Road.K4.W.mats_of_are
#print axioms OnBytes.Road.K4.W.syms_of_plain
#print axioms OnBytes.Road.K4.W.cells_of_syms
