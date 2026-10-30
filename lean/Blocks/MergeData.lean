-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/MergeData.lean: the data of Blocks/StageData.lean for the merges of claims.

These data (`Core.Data`) are numberings of the rounds and decision procedures (`Hon.Dec`) for the
withheld sets (`Hon.withheld`, Blocks/BlockHon.lean): `dataMergeC`, `dataMerge`, `dataRename`,
`dataPadsMerge`. The merges withhold nothing. Their rounds: independent coefficients; a masked
sumcheck with plain weights; masked scalars (renaming; the tensor claims' scalars have no round and
no data here). `merge` with its pad vector first sends one pad vector.
-/
import Blocks.MergeStage
import Blocks.StageData
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks.MG
open Iop

section
variable {E Y P Rw ι : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype Rw] [Fintype ι]
  [DecidableEq ι] (M : MG E Y P Rw ι) (J : Type) [Fintype J] [DecidableEq J] [FinEnum J] [IdxK J]
  [Fintype P] [DecidableEq P] [NeZero (2 : E)] (F : Type) [Field F] [Algebra F E] [FinEnum E]

def numMergeC (l : List ι) : SNum (M.mergeC J l).shape (M.encMergeC J F l) :=
  SNum.app (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (d := (REnc.none E F Empty (J → E), PUnit.unit)) (RNum.none F Empty (J → E), ())
    (SNum.app (s := (M.start J).shape) (d := PUnit.unit) ()
      (SNum.app (s := ((M.sc J).sc l).shape) (t := (M.finish J).shape) (d := SC.encSc (M.sc J) F l)
        (d' := PUnit.unit) (SC.numSc (M.sc J) l) ()))

def decMergeC (l : List ι) : (M.honMergeC J l).Dec :=
  Hon.Dec.seq (Hon.Dec.sample _ _)
    (Hon.Dec.seq (Hon.Dec.pure _ _ _) (Hon.Dec.seq ((M.prover J).decSc l []) (Hon.Dec.pure _ _ _)))

variable {F}

/-- the merge of column claims -/
def dataMergeC (l : List ι) (ra : Reads F E ⟨J → M.CClaim, Y, St0 E Rw ι J⟩) :
    (M.coMergeC J l).Data (M.trackMergeC J l ra) :=
  ⟨M.numMergeC J F l, M.decMergeC J l⟩

/-- `merge`, after its pad vector -/
def dataMerge (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y, StI E Rw ι J⟩) :
    (M.coMerge J l).Data (M.trackMerge J l ra) where
  num := SNum.app (s := (M.asC J).shape) (d := PUnit.unit) () (M.numMergeC J F l)
  dec := Hon.Dec.seq (Hon.Dec.pure _ _ _) (M.decMergeC J l)

/-- renaming -/
def dataRename (p : P) (ra : Reads F E ⟨M.Idx, Y, St2 E Rw ι⟩) :
    (M.coRename p).Data (M.trackRename p ra) :=
  ⟨(RNum.none F Unit Unit, ()), (show (M.honRename p).Dec from Hon.Dec.oneEmpty _ _)⟩

end

section
variable {F : Type} [Field F] {E Y₀ P Rw ι : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] [Fintype Rw] [Fintype ι] [DecidableEq ι] (C : Code.Enc F) [Nonempty (Fin C.n)]
  (M : MG E (Y₀ × (Fin C.msg → E)) P Rw ι) (J : Type) [Fintype J] [DecidableEq J] [FinEnum J]
  [IdxK J] [Fintype P] [DecidableEq P] [NeZero (2 : E)] [FinEnum E]

/-- `merge` with its pad vector: the pad vector, then the merge -/
def dataPadsMerge
    (q : ℕ) (pl : Fin C.msg → P) (l : List ι) (ra : Reads F E ⟨J → M.Idx, Y₀, StI E Rw ι J⟩) :
    (M.coPadsMerge J pl l).Data (M.trackPadsMerge C J q pl l ra) :=
  (Core.Data.pads C q pl ra).seq (M.dataMerge J l (Stage.readsPads C.msg ra))

end

end Blocks.MG
