-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FitDCore.lean: fitAtD AND fitAtD_eq, OUT OF Johnson/PV/FitD.lean, TO THE LETTER, OVER
  FEWER IMPORTS: so that a native library can take them in without what Johnson/PV/FitD.lean
  imports through Johnson/PV/MvAt.lean.
THE TEST ON WHAT A CHAIN QUERY HOLDS (fitAt: OnBytes/Maker/Page/FitAt.lean:114) WITH THE PLAIN PART
  READ ALONG THE DATA (Lite.partAtD: Johnson/RunOne/OnceD.lean:40), FOR SPEED ALONE;
  fitAtD_eq: IT IS fitAt.


-/
import OnBytes.Maker.Page.FitAt
import Johnson.RunOne.OnceD

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- fitAt's text with partAtD in partAt's place. -/
def fitAtD (fF : List (Dig 256) → Option X → TF → Bool) (fJ : List (Dig 256) → TJ → Bool)
    (f3 : T3 → Bool) : FitJ L t where
  row := fun i rt z =>
    match Lite.partAtD C D tF tJ t3 rd z with
    | .row i' _ n => decide (i' = i) && decide (n < 2 ^ 64) && rootsFit D i rt
    | _ => false
  front := fun cms x z =>
    match Lite.partAtD C D tF tJ t3 rd z with
    | .front p => fF cms x p
    | _ => false
  join := fun cms z =>
    match Lite.partAtD C D tF tJ t3 rd z with
    | .join p => fJ cms p
    | _ => false
  seam := fun z =>
    match Lite.partAtD C D tF tJ t3 rd z with
    | .seam p => f3 p
    | _ => false
  slot := slotAt C D tF tJ t3 rd

/-- **It is fitAt.** -/
theorem fitAtD_eq (fF : List (Dig 256) → Option X → TF → Bool) (fJ : List (Dig 256) → TJ → Bool)
    (f3 : T3 → Bool) : fitAtD C D tF tJ t3 rd fF fJ f3 = fitAt C D tF tJ t3 rd fF fJ f3 := by
  have e : Lite.partAtD C D tF tJ t3 rd = partAt C D tF tJ t3 rd := funext (Lite.partAtD_eq C D tF
      tJ t3 rd)
  unfold fitAtD
  rw [e]
  rfl

end

end W4M

#print axioms W4M.fitAtD_eq
