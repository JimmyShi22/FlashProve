-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HotOnCubes.lean: the kind "lookup" (K3): AT A LAYERS'
LINK: FROM THE LIBRARY'S SENTENCE ON THE SELECTORS OF THE INTEGER MATRICES (`HotField`,
Johnson/Road/Rows/LayerTop.lean) TO "EACH OF THE CALLER'S ARRAYS IS 0 AT EVERY VERTEX OF ITS CUBE"
(`OnCubes`, Cb/G6/Rider/Carrier.lean) at the lookup's caller with its rider (`layRider`,
Johnson/Desc/First/Look/K3CallerLay.lean). The converse of the core of the library's `lay_layHot`,
which goes from the lookup's relation to `HotField`. Over the library and one file of this tree.

  `hot_onCubes`         the theorem
  `worthRider_of_hot`   so: the lookup's item worth "rider" (`K3WorthRider`), at every state of the
                        verifier: `worthRider_of_onCubes` (ExchangeRider.lean) CALLED

By the library's `hot_source` (Cb/G6/Rider/Model/OneHot.lean), an equivalence. The identity on the
selectors reads neither the embedding nor the prompt (the library's `hotAt_idn`), and whether it is
asked does not hang on "the first group" (`Idn.Valid`, Inst/Model/FF/Trace.lean).

CONDITIONAL ON hM (`MatsAre`: the message's cells are the integer matrices', carried into the field)
and hHot (`HotField` of these matrices). No instance of these hypotheses is exhibited in this file.

Limits. That hM or hHot holds of any witness is not shown here. hM: the library shows `MatsAre`
where the committed symbols are the packing of small integers (`lay_mats_cast`,
Johnson/Desc/First/Look/K3CallerLay.lean). hHot: out of the item constr "rider", conditional:
`hot_of_constr` (ExchangeRiderLay.lean [not in this library]). The layers alone: attention's and the
head's families are not touched. Nothing on soundness, completeness or any other property of a
protocol.
-/
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRider

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes OnBytes.Model
open OnBytes.Road (Mats)
open OnBytes.Road.Rows.Norms (HotField)
open Inst.Model (Mat)
open Inst.Model.All (DF)
open Cb.Rider (OnCubes hot_source)
open VerifiableInference.OnPublicFiles (K3WorthRider)
open VerifiableInference.Desc.First.Look (Place LayPub Sent laySg layRider layCells MatsAre)

variable (x : Place) (p : LayPub) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → Nat → Nat → Cb.Gl.E) (nr nc : Nat) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- **FROM `HotField` OF THE INTEGER MATRICES TO `OnCubes` OF THE MESSAGE'S CELLS.** CONDITIONAL ON
hM and hHot. -/
theorem hot_onCubes (m : (laySg x D rad oW).Msg) (Mz : Mats ℤ)
    (hM : MatsAre x tl D rad oW wOf nr nc m Mz) (Wi : Mat) (xi : Cm.Seg.XI)
    (hHot : HotField p.h p.sc p.y p.g Mz Wi xi) :
    OnCubes (layRider x p tl D rad oW wOf nr nc Ex Wp).g
      (layRider x p tl D rad oW wOf nr nc Ex Wp).f () m :=
  (hot_source (scl := Road.sclOf p.h p.sc p.g 4) DF
    (fun (_ : Unit) m' => layCells x p tl D rad oW wOf nr nc m') () m).2
    fun _ _ _ l i hv => by
      have e := hHot l i hv
      unfold layCells
      rw [hM]
      exact e

/-- **SO: THE LOOKUP'S ITEM WORTH "rider"**, at every state of the verifier. CONDITIONAL ON hM and
hHot at the witness's messages. No instance of these hypotheses is exhibited in this file. -/
theorem worthRider_of_hot {S W : Type} (fork : S → Option Fork)
    (heard : S → Option OnBytes.Model.Forest.Heard) (lm first : Nat)
    (ms : W → (laySg x D rad oW).Msg) (s : S) (w : W) (Mz : Mats ℤ)
    (hM : MatsAre x tl D rad oW wOf nr nc (ms w) Mz) (Wi : Mat) (xi : Cm.Seg.XI)
    (hHot : HotField p.h p.sc p.y p.g Mz Wi xi) :
    K3WorthRider fork heard (layRider x p tl D rad oW wOf nr nc Ex Wp) lm first (fun _ => ()) ms s
      w :=
  worthRider_of_onCubes fork heard (layRider x p tl D rad oW wOf nr nc Ex Wp) lm first
    (fun _ => ()) ms s w (hot_onCubes x p tl D rad oW wOf nr nc Ex Wp (ms w) Mz hM Wi xi hHot)

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.hot_onCubes
#print axioms ProofFile.Honest.K3.Law.Exchange.worthRider_of_hot
