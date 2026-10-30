-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsLayersAt.lean

The law of a group of layers (lawG, Johnson/HonestTrace/CountsLayers.lean) with its premise on the
keys in the words of Johnson/Road/Lane5ForInG.lean: ForInG, at the field Cb.Gl.E and at cells that
are read from integer matrices (cellMW).

Main theorems:
* "inTable_of_forInG": ForInG P g Mz Wi gives lawG's premise "for every call c below NC, every place
  below 2^(n_c) of G.kvG P g cell c holds the value of a row below 2^(k_c) of tabOf", at cell :=
  cellMW Mz Wi. The two unfold to one term, so the proof is the hypothesis itself.
* "lawG_forInG": if Layer.layout h pc returns P.y, Switches h holds, ForInG P g Mz Wi holds and
  LaidB P g (cellMW Mz Wi) holds, then for all θ and al Cb.Lkp.MidP holds of G.keyG, G.tabG,
  FoNums.pads and G.bitsG, with keys and bits both read at cellMW Mz Wi.

Limits. LaidB asks that the cells of matrix number G.iB P.y, at the rows below 2^lmb and the columns
below NC 2^(kT + 5 - lmb), are the planes bG of these very cells. The head of
Johnson/Road/Lane5TopLTrue.lean says of its matrices zTrue that the matrix b is 0 in them; under the
premises of sum_bG (Johnson/HonestTrace/CountsLayers.lean) matrices of that kind meet LaidB only if
all 2^v keys are padding keys. No theorem of this file makes matrices that meet ForInG and LaidB
together. Under six premises on public numbers, keysSkipB
(Johnson/HonestTrace/CountsLayersSkip.lean) with withBG_laid and inTable_withBG (CountsLayers.lean)
gives that withBG P g cell meets LaidB and keeps the premise on the keys, for every reading cell;
that withBG of cellMW Mz Wi is cellMW of matrices is not shown in this file.

Not claimed: that a prover's committed cells are such matrices; that a verifier accepts anything;
that the premises hold of any parameter file or request.

-/
import Johnson.HonestTrace.CountsLayers
import Johnson.Road.Lane5ForInG

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (layout)
open OnBytes.Road (Switches Mats)
open OnBytes.Road.Alg (ForInG cellMW)

/-- ForInG P g Mz Wi gives the premise of lawG on the keys, at the cells cellMW Mz Wi over
Cb.Gl.E. -/
theorem inTable_of_forInG {P : Layer.Pub} {g : ℕ} {Mz : Mats ℤ} {Wi : Inst.Model.Mat}
    (H : ForInG P g Mz Wi) :
    ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g (cellMW Mz Wi) c) (tabOf Cb.Gl.E P.y.fo c) := H

/-- If Layer.layout h pc returns P.y, Switches h, ForInG P g Mz Wi and LaidB P g (cellMW Mz Wi)
hold, then for all θ and al: Cb.Lkp.MidP holds of the joint key vector, the joint table, the public
padding and the planes' bits, with keys and bits both read at cellMW Mz Wi. -/
theorem lawG_forInG {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (Mz : Mats ℤ) (Wi : Inst.Model.Mat)
    (H : ForInG P g Mz Wi) (hb : LaidB P g (cellMW Mz Wi)) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP P.y.fo.v P.y.fo.d 5 32 (G.keyG P g (cellMW Mz Wi) θ) (G.tabG P θ)
      (FoNums.pads P.y.fo) (fun u j => G.bitsG P.y (cellMW Mz Wi) (u * 32 + j)) al :=
  lawG P hy S g _ (inTable_of_forInG H) hb θ al

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.inTable_of_forInG
#print axioms OnBytes.HonestTrace.lawG_forInG
