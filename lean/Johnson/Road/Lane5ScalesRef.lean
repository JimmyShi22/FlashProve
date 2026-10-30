-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5ScalesRef.lean

The table of scales at the record X that the verifier's publicOf returns is the library's reference
table "Cm.sRef", if "Hd.PublicAt X.P" holds (a list of numbers of the parameter file) and the scale
file's words are "scalesKF". So the bundle "OrdsL" holds at that record at a request with counted
positions and at weights that are not all 0; all 48 layers of those weights are 0.

Johnson/Road/FormsKeysLawP.lean shows that this table is lawful. Its proofs go through an equation
between tables and then keep "Lawful" alone. Here the equation is kept, by the same three steps, and
closed with "scales_ref" (Johnson/Road/FormsKeysLaw.lean).

Main theorems:
* "scalesOf_ref_at": at every shape with the two constants 53687, at the record "scKF" of scale
  words and the final norm "nfKF": the table is "Cm.sRef".
* "scalesOf_ref_reader": the same at what the verifier's reader of a scale file returns on the words
  "scalesKF", at profile 4 and 48 layers.
* "scales_at_ref": the same at the record X of publicOf, under "Hd.PublicAt X.P".
* "ordsL_real_gap_file": so "OrdsL" holds at X's own shapes, at the policy C = 2304, theta = 259,
  cap = 0, the index "Policy.PosGuards.idx0" and the request "xOne" ("ordsL_real_gap",
  Johnson/Road/Lane5TopLTrueAt.lean), at the named matrices "zTrue" and "zaTrue".

Limits. By the head of Policy/Rel/PosGuards.lean the weights of that index are made up and all 48
layers are zero, so the logits at a position depend on that position's token alone: no case is shown
in this file in which a layer's weights are not 0 (one with values and an output projection in layer
0: Johnson/Road/Lane5TrueLayerAt.lean). The request has 1,023 counted positions ("nb_one",
Inst/Model/ProgramRGuards.lean). That publicOf returns and "Hd.PublicAt" holds of any parameter file
is a run's matter (Johnson/Road/Lane5PublicRun.lean), and so is that a scale file has the words
"scalesKF" (Johnson/Road/FormsKeysRunK.lean): no theorem. The runs are made with no layout file; the
theorems stand for every lay. The library's model has no cell for a lookup's counts. So in "zTrue"
the matrix b of a group of layers and in "zaTrue" the matrix bA of attention are 0, which no honest
prover of the protocol would commit to. The statements do not read them.

Not claimed: that a prover's committed cells are these matrices; that an honest prover's proof is
accepted (completeness of the protocol). It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5TopPub
import Johnson.Road.Lane5TopLTrueAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Verify (publicOf layerShape)

/-- At every shape with the two constants 53687, at the record scKF of scale words and the final
norm nfKF, the table is the reference table. -/
theorem scalesOf_ref_at {h : Model.Layer.Shape} {sc : Model.Layer.Scales} {nf : NormPar}
    (he1 : h.eps1 = 53687) (he2 : h.eps2 = 53687) (hsc : sc = scKF) (hnf : nf = nfKF) :
    scalesOf h sc nf = Cm.sRef := by
  subst hsc hnf
  have e : scalesOf h scKF nfKF = scalesOf hKF scKF nfKF := by
    show (⟨(fileOf h scKF).words, nfKF⟩ : Cm.Scales) = ⟨(fileOf hKF scKF).words, nfKF⟩
    rw [fileOf_eps (h' := hKF) scKF he1 he2]
  rw [e]
  exact scales_ref

/-- The same at what the verifier's reader of a scale file returns on the words scalesKF, at
profile 4 and 48 layers. -/
theorem scalesOf_ref_reader {h : Model.Layer.Shape} {W : Array ℕ} {sc : Model.Layer.Scales}
    {nf : NormPar} (hr : Model.Layer.scalesOf h W = .ok sc) (hW : W = scalesKF.toArray)
    (hp4 : h.p4 = true) (hL : h.L = 48) (he1 : h.eps1 = 53687) (he2 : h.eps2 = 53687)
    (hnf : nf = nfKF) : scalesOf h sc nf = Cm.sRef := by
  have e : sc = scKF := by
    rw [reader_record hr, hW, hL, if_pos hp4]
    rfl
  exact scalesOf_ref_at he1 he2 e hnf

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **The table of scales at the verifier's record is the reference table.** -/
theorem scales_at_ref (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS) = Cm.sRef := by
  have hs := Hd.scales_of_public h
  rw [shape_of_public h] at hs
  exact scalesOf_ref_reader hs hW (Hd.p4_of_at A) (A.num 2) (A.num 41) (A.num 42)
    (npOf_public h A)

/-- **At the verifier's own shapes: weights that are not all 0, and 1,023 counted positions.** -/
theorem ordsL_real_gap_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) ⟨2304, 259, 0⟩ (Hd.shapeA X)
      Policy.PosGuards.idx0.mat ProgramRGuards.xOne
      (zTrue (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) ⟨2304, 259, 0⟩
        Policy.PosGuards.idx0 ProgramRGuards.xOne)
      (zaTrue (Hd.shapeA X) (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS))
        ⟨2304, 259, 0⟩ Policy.PosGuards.idx0 ProgramRGuards.xOne) :=
  have B := Hd.public_of_publicOf h A
  ordsL_real_gap B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (att_of_at' h A hg).1) (fun _ hg => (att_of_at' h A hg).2.2.2)
    (fun _ hg => (att_of_at' h A hg).2.1) (fun _ hg => (att_of_at' h A hg).2.2.1)
    (scales_at_ref h A hW)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.scalesOf_ref_at
#print axioms OnBytes.Road.L5.scalesOf_ref_reader
#print axioms OnBytes.Road.L5.scales_at_ref
#print axioms OnBytes.Road.L5.ordsL_real_gap_file
