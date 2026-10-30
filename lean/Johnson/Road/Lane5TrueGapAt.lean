-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5TrueGapAt.lean

A request that is true under its policy at the table of scales of the verifier's own record, with
counted positions and logits that are not all equal; and attention's seam at it.

Johnson/Road/Lane5AttSeamTrueAt.lean shows a statement "for every request that is true under its
policy" at the record X that publicOf returns, and Johnson/Road/Lane5TopLTrue.lean at letters.
Johnson/Road/Lane5AttSeamTrueAt.lean puts in the requests at all weights 0 ("seam_zero_all_file").
Here one more request is put in, at weights that are not all 0, at X's own table.

Main theorems, under publicOf's line, "Hd.PublicAt X.P" and "the scale file's words are scalesKF":
* "true_real_gap_file": the request "xOne" is true under the policy C = 2304, theta = 259, cap = 0
  at the index "Policy.PosGuards.idx0", at the table "scalesOf (layerShape X.P) X.layers.sc (Hd.npOf
  X.hS)". By "Policy.PosGuards.real_gap" (Policy/Rel/PosGuards.lean) and "scales_at_ref"
  (Johnson/Road/Lane5ScalesRef.lean).
* "seam_real_gap_file": so, with the test "attUsualK X", "AttR0" and "InTables" hold at the plan of
  every group g below 12, at the list read off that request's honest trace.

Limits. All 48 layers of that index are zero. The head of Policy/Rel/PosGuards.lean says of its
weights "wts σ τ": "token t is embedded in channel σ t, channel j votes for token τ j, all layers
are zero"; "The weights are made up, at the reference scales alone"; "the logits at a position
depend on that position's token alone". The index "idx0" is "wts" at σ and τ constantly 0. So
attention's cells in that trace come from layers whose weights are 0: no case is shown in this file
in which a layer's weights are not 0 (one with values and an output projection in layer 0:
Johnson/Road/Lane5TrueLayerAt.lean). The request has 1,023 counted positions ("nb_one",
Inst/Model/ProgramRGuards.lean); by the same head it "misses at position 0 alone". At "idx0" every
token has the same embedding row; by the same head "the logits are the same at every position". The
list of attention holds the arrays q, k, v, o and attention's own cells; these come from the layers'
weights, which are 0 as in "seam_zero_all_file". That this list differs from the list at all weights
0 is not shown. What is new in this request (logits that are not all equal, one miss) lies in the
head, which "AttR0" and "InTables" do not read.
The other limits of Johnson/Road/Lane5AttSeamTrueAt.lean hold here too: all but its sentences that
no request at weights not all 0 is named and that "scales_at_ref" is not put in.

Not claimed: that a prover's committed cells are this list; that an honest prover's proof is
accepted (completeness of the protocol). It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5AttSeamTrueAt
import Johnson.Road.Lane5ScalesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Verify (publicOf layerShape)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **A true request at the table of the verifier's own record.** -/
theorem true_real_gap_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS))
      ⟨2304, 259, 0⟩ Policy.PosGuards.idx0 ProgramRGuards.xOne := by
  rw [scales_at_ref h A hW]
  exact Policy.PosGuards.real_gap.1

/-- **Attention's seam at that request, at the record's own plan.** -/
theorem seam_real_gap_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (U : attUsualK X = true) (hW : Model.fileWords KL = scalesKF.toArray) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      AttR0 Ag.S (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) ⟨2304, 259, 0⟩)
        Policy.PosGuards.idx0 ProgramRGuards.xOne))) ∧
      (callsA Ag.S Ag.fs (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) ⟨2304, 259, 0⟩)
        Policy.PosGuards.idx0 ProgramRGuards.xOne)))).InTables :=
  seam_of_true_file h A U hW (po := ⟨2304, 259, 0⟩) ⟨by norm_num, by norm_num, by norm_num⟩ hg
    Policy.PosGuards.idx0 ProgramRGuards.xOne (true_real_gap_file h A hW)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.true_real_gap_file
#print axioms OnBytes.Road.L5.seam_real_gap_file
