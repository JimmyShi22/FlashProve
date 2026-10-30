-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngFront.lean: the lookup argument and the closing block send no vector.

 * `all_trackLookup`: the lookup argument (Blocks/LookupStage.lean) sends no vector.
 * `all_closing`: the closing block (Blocks/ClosingStage.lean) sends no vector.
Both are stated as `t.All Q` for every property Q.

Notation: a vector: `REnc` (Blocks/BlockFront.lean): how the oracle part of one round of a block is
sent: as the vectors a : A; the vector a has `rows a` rows of `(code a).msg` entries;
`Q C rows mrow role q`: a property of a vector's code, number of rows, number of row variables, role
and number of positions read (`EncData.All`, Blocks/StageSide.lean); `t.All Q`: every vector that
the protocol sends has the property Q.

Terms: lean/GLOSSARY.md.
-/
import Blocks.StageSide
import Blocks.ClosingStage
import Blocks.LookupStage
import Blocks.RngForest
import Blocks.RngForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Rng

open Iop Prob
open scoped ENNReal

section NoVector

variable {F : Type} [Field F] {E Y Pd N : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
  [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N)
  {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

theorem all_encPl (K : PL E Y Pd N (LkX N E)) : EncData.All Q K.pl.shape (Lk.encPl F K) :=
  EncData.All.app (s := K.init.shape) trivial
    (EncData.All.app (s := (K.sc.sc K.ord).shape) (t := K.fin.shape)
      (SC.all_encSc K.sc _) ⟨fun e => e.elim, trivial⟩)

theorem all_encKey : ∀ n l : ℕ, EncData.All Q (L.stKey n l).B.shape (L.encKey F n l)
  | 0, _ => trivial
  | n + 1, l =>
    EncData.All.app (s := (L.stK l).B.shape) (all_encPl (L.plK l)) (all_encKey n (l + 1))

theorem all_encTab : ∀ n l : ℕ, EncData.All Q (L.stTab n l).B.shape (L.encTab F n l)
  | 0, _ => trivial
  | n + 1, l =>
    EncData.All.app (s := (L.stT l).B.shape) (all_encPl (L.plT l)) (all_encTab n (l + 1))

theorem all_enc14 : EncData.All Q L.st14.B.shape (L.enc14 F) :=
  EncData.All.app (s := L.stAl.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.stZY.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := (L.stKey L.par.D 0).B.shape) (all_encKey L _ _) <|
  EncData.All.app (s := L.stKe.B.shape) trivial <|
  EncData.All.app (s := L.stT0.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := (L.stTab L.par.r 0).B.shape) (all_encTab L _ _) <|
  EncData.All.app (s := L.stL.B.shape) (all_encPl L.plL) <|
  EncData.All.app (s := L.stB0.B.shape)
    (t := L.stB.B.shape) ⟨fun e => e.elim, trivial⟩ (all_encPl L.plB)

theorem all_enc6 : EncData.All Q L.st6.B.shape (L.enc6 F) :=
  EncData.All.app (s := L.stUV.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.stXi.B.shape) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.stRs.B.shape) (t := L.stRec.B.shape) (SC.all_encSc L.scR _) trivial

/-- The lookup argument sends no vector. -/
theorem all_trackLookup (ra : Reads F E L.sL) : (L.trackLookup F ra).All Q :=
  EncData.All.app (s := L.st14.B.shape) (all_enc14 L)
    (EncData.All.app (s := L.st5.B.shape) (t := L.st6.B.shape)
      ⟨fun e => e.elim, trivial⟩ (all_enc6 L))

/-- The closing block sends no vector. -/
theorem all_closing {nO nR : ℕ} (nL : ℕ) (pl : Closing.Places N (Fin nR) nO)
    (pp : Closing.Places Pd (Fin nR) nO) :
    (Closing.track (E := E) nL pl pp F).All Q :=
  EncData.All.app (s := [])
    (t := [Closing.rAux E (Fin nR)] ++ [Closing.rOpen E (Fin nL) (Fin nR) nO])
    (d := PUnit.unit) trivial
    (EncData.All.app (s := [Closing.rAux E (Fin nR)]) (t := [Closing.rOpen E (Fin nL) (Fin nR) nO])
      (d := (REnc.none E F (Fin nR × Bool) E, PUnit.unit))
      (d' := (REnc.none E F (Fin nO) (Fin nL ⊕ Fin nO ⊕ Fin nR → E), PUnit.unit))
      ⟨fun e : Empty => e.elim, trivial⟩ ⟨fun e : Empty => e.elim, trivial⟩)

end NoVector

end Blocks.Rng
