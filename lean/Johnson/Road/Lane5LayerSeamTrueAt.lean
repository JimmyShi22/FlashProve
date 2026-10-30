-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5LayerSeamTrueAt.lean

At the record that the verifier's publicOf returns, the two premises with content of the seam before
the lookup of a group of layers hold together, at named matrices: for every request that is true
under its policy.

"linkOK_of_one" (Johnson/Road/Ends/AlgBridgeOne.lean) has two premises with content: "L5.LayerR0"
(the group's meaning without its lookup clause) and "ForInG" (every call's keys, at the key vectors
kvG of this library, lie in its table). That every true request's honest matrices meet both is
"layerSeam_of_true" (Johnson/Road/Lane5LayerSeamTrue.lean), under 25 public premises at letters.
Here 22 of the 25 are drawn from one record: those that a program can decide from the test
"recordOneB"; Sized2, twelve groups and FullH from "Hd.PublicAt" (Johnson/Road/HeadL5Pub.lean,
Johnson/Road/Lane5TopPub.lean); that the table is lawful (in "layerSeam_of_true_file": from the
scale words), the policy's bounds and g < 12 stay premises.

Main theorems. X is what publicOf has returned. The public premises are that line, "Hd.PublicAt X.P"
(the numbers of the parameter file are the reference's) and the test "recordOneB X g". The matrices
are written out in every statement: mzA X.layers.y (Hd.zOf T) g, T the matrices of the library's
honest trace with the ledger of (i, x) under the policy, with the weights' matrix i.mat. No
statement has a "there is".
* "layers_y": X.layers.y = X.y: the layout in the layers' public part, of which "recordOneB" and
  "ForInG" speak and at which all is stated here, is the layout X.y of the bundles (OrdsL … X.y …,
  Johnson/Road/Lane5TopPub.lean).
* "layerSeam_of_true_publicAt": at a lawful table "scalesOf (layerShape X.P) X.layers.sc nf" and a
  policy with "Policy.PolCond": for every index i and request x that is true under the policy, at
  group g below 12.
* "layerSeam_of_true_file": the same at nf := "Hd.npOf X.hS", where the table is lawful if the scale
  file's words are "scalesKF" ("lawful_of_at").
* "layerSeam_zero_all_file": so at all weights 0 and a policy with "Policy.PolCond", 257 ≤ theta and
  257 ≤ C: for every request that has its form, with y = 0 if e = 1,024, whatever its other tokens,
  at the matrices of its own honest trace ("Policy.TrueGuards.zero_all",
  Policy/Rel/TrueGuards.lean).
* "layerSeam_real_gap_file": and at the request "xOne" at the index "Policy.PosGuards.idx0" under
  the policy C = 2304, theta = 259, cap = 0 ("true_real_gap_file",
  Johnson/Road/Lane5TrueGapAt.lean).
* "linkOK_of_true_file": so at these matrices link 2 * g is in order, by "linkOK_of_one". The proof
  of "layerSeam_of_true" starts from this link's order at the honest trace: this theorem shows that
  the premises of "linkOK_of_one" can be met together; it is no new fact on the link.

Limits. No case is shown in this file in which a layer's weights are not 0 (one with values and an
output projection in layer 0: Johnson/Road/Lane5TrueLayerAt.lean): at "iZero" all weights are 0, and
all 48 layers of "idx0" are zero (the head of Policy/Rel/PosGuards.lean). The key vectors in
"ForInG" are kvG, a term of this library over the verifier's records; the verifier holds no key
vector. The library's model has no cell for a lookup's counts. So in these matrices the matrix b of
a group of layers is 0, which no honest prover of the protocol would commit to; the statements do
not read it. The numbering is that of these files' dictionary; no function of the verifier's makes
these matrices. LayerR0 and ForInG read no logit and no counted position. By a reading, what is new
against all weights 0: at g = 0 the identity on the embedding reads a row that is not 0, the same
row for every token; in every group the stream and the normalisations' cells are not 0. Every
product with a layer's weight has the weight 0. "recordOneB" is no test of the verifier: it asks the
reference's switches and sizes, the floor, the library's rotary words and eight tables, and that the
eight lines of calls name the library's families in order. A configuration that the verifier admits
may fail it, and then nothing is said. That publicOf returns, and that "Hd.PublicAt" and
"recordOneB" hold of any parameter file, is a run's matter (Johnson/Road/Lane5PublicRun.lean,
Johnson/Road/Ends/GuardRec.lean), and so is that a scale file has the words "scalesKF": no theorem.
No Lean code compares the text linesKF and the words scalesKF of Johnson/Road/FormsKeysRunK.lean
with files. The runs are made with no layout file; the theorems stand for every lay. The readings
nF, kN and tauF in "ForInG" are typed with the bodies that the lookup's readings have, by a reading;
nothing compiles the two together (Johnson/Road/Lane5ForInG.lean).

Not claimed: that a prover's committed cells are these matrices; that an honest prover's proof is
accepted (completeness of the protocol); anything on a proof or a verifier's verdict. It is a
statement on integers and tables alone.

-/
import Johnson.Road.Lane5LayerSeamTrue
import Johnson.Road.Ends.AlgBridgeOne
import Johnson.Road.Lane5TrueGapAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Verify (publicOf layerShape)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- The layout in the layers' public part is X.y: both are what the verifier's layout returns. -/
theorem layers_y (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) : X.layers.y = X.y :=
  Except.ok.inj ((Hd.publicH_of_public h).lay.symm.trans (Hd.public_of_publicOf h A).lay)

/-- **At the record's own layers: every true request's honest matrices meet both premises.** -/
theorem layerSeam_of_true_publicAt (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (nf : NormPar)
    (hs : (scalesOf (layerShape X.P) X.layers.sc nf).Lawful) {po : AcceptancePolicy}
    (hpol : Policy.PolCond po) (hg : g < 12) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc nf) po i x) :
    LayerR0 (layerShape X.P) X.layers.sc X.layers.y g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc nf) po)
          i x))) g) i.mat x ∧
    Alg.ForInG X.layers g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc nf) po)
          i x))) g) i.mat := by
  have B := Hd.public_of_publicOf h A
  unfold Alg.recordOneB at t
  rw [Bool.and_eq_true] at t
  obtain ⟨hy, rd, r, hrd, hl, hW, tb⟩ := Alg.returns_of_record h t.1
  unfold Alg.bridgeB at tb
  simp only [Bool.and_eq_true] at tb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, -⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩,
    b15⟩ := tb
  have hsc : Model.Layer.scalesHeld (layerShape X.P) X.layers.sc = .ok () := by
    cases e : Model.Layer.scalesHeld (layerShape X.P) X.layers.sc with
    | ok u => rfl
    | error m =>
      rw [e] at b2
      cases b2
  have hgL : ∀ l < All.DF.nl, g * X.layers.y.Lam + l < ppref.layers := fun l hl' => by
    simpa using List.all_eq_true.mp b10 l (List.mem_range.mpr hl')
  have hfl : ∀ cc : Fin 8, (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
      Nat.clog 2 (FFSeg.used All.DF cc) := fun cc => by
    simpa using List.all_eq_true.mp b14 cc (List.mem_finRange cc)
  have hw : ∀ cd ∈ X.layers.y.calls, ∃ wg, (Alg.envG X.layers g r.1).weighedOf cd = some wg :=
    fun cd hcd =>
      Option.isSome_iff_exists.mp (List.all_eq_true.mp b15 cd (Array.mem_toList_iff.mpr hcd))
  have hL : ∀ cc : Fin 8, ∃ c0 : Model.Call, X.layers.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (FFSeg.lut tbRef cc) ∧ c0.k = if cc = 3 then 8 else 16 := fun cc => by
    obtain ⟨c0, e0, L0⟩ := Alg.hL_of_tablesB t.2 cc
    exact ⟨c0, e0, L0, Nat.pow_right_injective (le_refl 2) (L0.rows.trans (Alg.rows_ref cc))⟩
  have h12 : X.layers.y.NGr = 12 := by
    rw [layers_y h A]
    exact B.groups
  exact layerSeam_of_true (P := X.layers) (hH := X.hS) hy (Alg.switches_of_B b1) hsc hrd hl
    (Alg.sized_of_B b4) B.sized2 b5 (by simpa using b6) (Alg.hmats_of_all b7) (by simpa using b8)
    (Alg.sizedW_of_B b9) hW hgL b11 (by simpa using b12) (Alg.lines_of_B b13) hfl hw hL h12 B.full
    hs hpol i x ht hg

/-- **The same where the scale file's words are those written out: the table is lawful.** -/
theorem layerSeam_of_true_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) {po : AcceptancePolicy}
    (hpol : Policy.PolCond po) (hg : g < 12) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po i x) :
    LayerR0 (layerShape X.P) X.layers.sc X.layers.y g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
          i x))) g) i.mat x ∧
    Alg.ForInG X.layers g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
          i x))) g) i.mat :=
  layerSeam_of_true_publicAt h A t (Hd.npOf X.hS) (lawful_of_at h A hW) hpol hg i x ht

/-- **At all weights 0: every request that has its form, with y = 0 if e = 1,024, at the matrices of
its own honest trace.** -/
theorem layerSeam_zero_all_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) {po : AcceptancePolicy}
    (hpol : Policy.PolCond po) (hθ : 257 ≤ po.theta) (hC : 257 ≤ po.C) (hg : g < 12)
    (x : Instance ppref) (h3 : Head3 x) (hy0 : x.e = ppref.T → x.y.val = 0) :
    LayerR0 (layerShape X.P) X.layers.sc X.layers.y g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
          (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x))) g)
      (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero).mat x ∧
    Alg.ForInG X.layers g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
          (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x))) g)
      (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero).mat :=
  layerSeam_of_true_file h A t hW hpol hg (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x
    (Policy.TrueGuards.zero_all (lawful_of_at h A hW) po hθ hC x h3 hy0)

/-- **At "xOne" and "idx0": the embedding is not 0; all layers' weights are 0.** -/
theorem layerSeam_real_gap_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) (hg : g < 12) :
    LayerR0 (layerShape X.P) X.layers.sc X.layers.y g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace
          (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) ⟨2304, 259, 0⟩)
          Policy.PosGuards.idx0 ProgramRGuards.xOne))) g)
      Policy.PosGuards.idx0.mat ProgramRGuards.xOne ∧
    Alg.ForInG X.layers g
      (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace
          (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) ⟨2304, 259, 0⟩)
          Policy.PosGuards.idx0 ProgramRGuards.xOne))) g)
      Policy.PosGuards.idx0.mat :=
  layerSeam_of_true_file h A t hW (po := ⟨2304, 259, 0⟩) ⟨by norm_num, by norm_num, by norm_num⟩ hg
    Policy.PosGuards.idx0 ProgramRGuards.xOne (true_real_gap_file h A hW)

/-- **So link 2 * g is in order at these matrices**: the premises of linkOK_of_one can be met
together; it is no new fact on the link. -/
theorem linkOK_of_true_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P) {g : ℕ}
    (t : Alg.recordOneB X g = true) (hW : Model.fileWords KL = scalesKF.toArray) {po : AcceptancePolicy}
    (hpol : Policy.PolCond po) (hg : g < 12) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po i x) :
    LinkOK Cm.Seg.Hd.main
      (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po) i.mat x (2 * g)
      (libMZ X.layers.y g
        (mzA X.layers.y (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
        (Cm.trace (Policy.ppOf (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
          i x))) g)) :=
  have B := Hd.public_of_publicOf h A
  have K := layerSeam_of_true_file h A t hW hpol hg i x ht
  Alg.linkOK_of_one h t B.sized2 B.p4 hg (Hd.npOf X.hS) po x K.1 K.2

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.layers_y
#print axioms OnBytes.Road.L5.layerSeam_of_true_publicAt
#print axioms OnBytes.Road.L5.layerSeam_of_true_file
#print axioms OnBytes.Road.L5.layerSeam_zero_all_file
#print axioms OnBytes.Road.L5.layerSeam_real_gap_file
#print axioms OnBytes.Road.L5.linkOK_of_true_file
