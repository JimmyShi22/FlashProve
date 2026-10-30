-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgramK.lean: the program with scales for each layer, at P's own scales in all layers,
one set of tables and `P.nf`, is the program with one set of scales. Theorems only; to audit the
relation `RinfPP` (Inst/Model/Scales.lean), nothing of this file need be read.

The last section of Inst/Model/Program.lean defines the integer program with the scales and the
tables of each layer and a separate final normalisation (`XK`, `RunsK`, `IsOutputK`, `ModelIsK`,
`RinfK`). Here the comparison with the program above it:
    `Params.at_scale`    P with its own scales in the place of its scales is P, by unfolding
    `XK_const`           with P's own scales and one set of tables in all layers the stream is `X`:
                         an induction over the blocks passed
    `RinfK_const`        and with `P.nf` the relation is `Rinf`
They are in a separate file so that Program.lean holds definitions (and one small lemma) only.
Notation (Inst/Model/Program.lean): `P : Params`: the parameters of the program: the sizes of the
model, and one set of scales for all layers; `tb : Tables`: the five table functions that the
program reads; `i : Weights`: an index: the weight tensors, as integers; `nf : NormPar`: the final
normalisation; `Rinf`: R_inf := {(i, x, ⊥) : WF(i), Model_i(prompt) = y}; `RinfK`: R_inf with
scales for each layer and the final normalisation nf.
-/
import Inst.Model.Program

set_option autoImplicit false

namespace Inst.Model

theorem Params.at_scale (P : Params) : P.at P.scale = P := rfl

/-- With P's own scales and one set of tables in all layers, the stream `XK` is the stream `X`. -/
theorem XK_const (P : Params) (tb : Tables) (i : Weights) (prompt : Fin P.T → Fin P.V) :
    XK P (fun _ => P.scale) (fun _ => tb) i prompt = X P tb i prompt := by
  funext l
  induction l with
  | zero => rfl
  | succ l ih =>
    show (if l % 2 = 0 then
          Att.x' P tb (i.layer (l / 2)) (l / 2) (XK P (fun _ => P.scale) (fun _ => tb) i prompt l)
        else
          FF.x'' P tb (i.layer (l / 2)) (l / 2)
            (XK P (fun _ => P.scale) (fun _ => tb) i prompt l)) = _
    rw [ih]
    rfl

theorem RinfK_const (P : Params) (tb : Tables) :
    RinfK P (fun _ => P.scale) P.nf (fun _ => tb) = Rinf P tb := by
  funext i x
  unfold RinfK Rinf ModelIsK ModelIs RunsK Runs IsOutputK IsOutput lgK lg nrmK nrm
  rw [XK_const]
  rfl

end Inst.Model
