-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/NormsTarget.lean: where the norms' stage of the layers' own rounds ends:
"every
identity of every norm holds at every position" (`D6.Bridge.Data.Holds`), at the data made of the
library's cells of a feed-forward segment, IS the premise hOwn of
Johnson/Road/Rows/LayerStart.lean's `layer_start_base`. Definition, statement and proof.

  `dataFF D t lNI`: the data of the norms' stage made of the sizes D and the cells t
    (Inst/Model/FF/Trace.lean): 2 ^ lT positions, d features, nNu norms with the parameters `npOf`,
    the limbs `bS`, the ledgers' bytes `led`. lNI, the number of coordinates of a point over the
    norms' numbers, is a letter: `Holds` does not read it.
  `holds_dJ`: `(dataFF D t lNI).Holds` just if every defect `dJ D t k nu i` is 0 for k below 17, nu
    below nNu, i below 2 ^ lT.

Both sides unfold to the same text. Nothing is said of a verifier.
-/
import OnBytes.Desc.First.NormBridge.BridgeCore
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open Inst.Model Inst.Model.FFSeg

variable [scl : Scl] {E : Type} [Field E]

/-- The data of the norms' stage, made of the library's cells. -/
def dataFF (D : Dim) (t : Cell → E) (lNI : ℕ) : D6.Bridge.Data E where
  lt := D.lT
  d := D.d
  NI := D.nNu
  lNI := lNI
  np := npOf D
  limb := fun i l j X => bS D t i l j X
  dig := fun i n X => led t i X n

/-- **The stage's end is the library's premise on the norms.** -/
theorem holds_dJ (D : Dim) (t : Cell → E) (lNI : ℕ) :
    (dataFF D t lNI).Holds ↔
      ∀ k ν, k < 17 → ν < D.nNu → ∀ i, i < 2 ^ D.lT → dJ D t k ν i = 0 :=
  ⟨fun h k ν hk hν i hi => h ν hν k hk i hi, fun h ν hν k hk i hi => h k ν hk hν i hi⟩

end OnBytes.Desc.First.K4
