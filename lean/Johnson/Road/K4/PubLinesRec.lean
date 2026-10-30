-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PubLinesRec.lean: THE NINETEEN PUBLIC LINES `PubLines` (Johnson/Road/K4/PubAt.lean)
AND THE ROTARY TABLES' FIT, AT THE RECORD THAT THE VERIFIER's OWN `publicOf` RETURNS, FROM TWO
TESTS OF THE LIBRARY. Statements and proofs. Nothing new is argued: existing lemmas are gathered.

THE TWO TESTS are Boolean functions of the public record alone, both in the library: `recordB X g`
(Johnson/Road/Ends/AlgBridgeRec.lean; its heart `bridgeB`, Johnson/Road/Ends/AlgBridgeTest.lean) and
`tablesB` (Johnson/Road/Ends/AlgTabs.lean).

WHAT IS A THEOREM AND WHAT IS A RUN. THE STEP FROM "the tests say true" TO THE LINES IS A THEOREM
(here). THAT THE TESTS SAY TRUE ANYWHERE IS NO THEOREM. A run stands in the library:
Johnson/Road/Ends/GuardRec.lean evaluates, by Lean's interpreter when that file is compiled,
`publicOf` on the parameter text linesKF and the scale words scalesKF of
Johnson/Road/FormsKeysRunK.lean, with no layout file: it returns a record with 12 groups; `tablesB`
says true; `recordB` says true in each of the 12 groups, and false at the number 12. By that file's
own head no Lean code compares linesKF and scalesKF with files. Such a run can be used in no proof.

AT WHICH SIZES. The tests compare with the library's REFERENCE sizes and tables, and so do the lines
here: D := `Dim.ref`, tb := `tbRef`, lk := `kRef` = 18. By the heads
(Inst/Model/Program.lean, `ppref`; Inst/Model/FF/Index.lean): the sizes V, layers, d, nq, nkv, ch,
f, fe, nexp of `ppref` are those of the text model of Llama 4 Maverick (48 layers, d = 5120, 128
experts); the window T = 1024 is a choice of this project; the scales are one set of example scales;
`Dim.ref` has 2^10 positions and groups of 2^2 layers. A SMALLER SHAPE DOES NOT PASS THESE TESTS
(`sizedB` compares with `Dim.ref`): of a small example nothing is said here.

  `bridgeB_more`: four more parts of `bridgeB` (beside `bridgeB_parts`): g is a group;
    profile 4; the weights' shape has the reference sizes; `ropeOK`.
  `linesAre_of`: `LinesAre` from eight calls and their eight lines.
  `pub_tails`: the public record's tails are `tailsOf` of its layout.
  `pubLines_of_record`: all nineteen lines, at { X.layers with tokv := tk }, s := weightShape X.P
    X.y and tl := the group's plan's.
  `ropeFits_of_ropeOK`, `rope_of_record`: `RopeFits` in every layer of the group, at any environment
    that holds the record's layout, scales and group.

WHERE EACH LINE COMES FROM. From `publicOf`'s return alone: hy, hs, hrd, hmats, hs0, hsL, htm, hNM
(`Hd.publicH_of_public`, `Hd.scalesHeld_of_public`, `shape_of_public`, `Model.Fit.public_reads`,
`Hd.public_plans`, `plan_sizes`, `shape_of_layout`); hρ is `gl_numerals`. From `recordB`:
S, hg, Z, hN, hfl, Zw, hlw, h4. From `tablesB`: hpad. ONE LINE IS IN NEITHER TEST AND STAYS A
PREMISE: hcap: the library's number cap (a batch has at most 2^cap keys; 28 at `Dim.ref`) is the
shape's lidb (a tree of a lookup holds at most 2^lidb keys). By reading, it can be met at the run's
own text: linesKF holds the line "lidb 28" (Johnson/Road/FormsKeysRunK.lean); at the typed full-size
shape hKF it is `cap_ref`, and hfl `hfl_ref` (Johnson/Road/FormsKeysRef.lean):
what stays a run is that the record's shape is hKF at linesKF.

Limits. See above: no test is shown to be true. Nothing on soundness.
-/
import Johnson.Road.K4.PubAt
import Johnson.Road.Ends.AlgBridgeOne
import Johnson.Road.FormsKeysPlan
import Johnson.Road.FormsKeysLawP
import Johnson.Road.HeadL5Grp
import Johnson.Road.HeadDict
import Johnson.Road.K4.PlanSizes
import OnBytes.Model.Fit.LayerCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Model.Layer (Pub HPlan2 Lay TableAt Env ClaimEnv tailsOf)
open OnBytes.Road.Alg (bridgeB recordB tablesB ropeOK bridgeB_parts recordB_parts returns_of_record
  hL_of_tablesB sizedW_of_B)
open Inst.Model (Tables ppref tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim lut fams)

/-- Four more parts of the test. -/
theorem bridgeB_more {h : Layer.Shape} {P : Pub} {g : ℕ} {s : WsShape} {tab : List TableAt}
    (t : bridgeB h P g s tab = true) :
    g < P.y.NGr ∧ h.p4 = true ∧ SizedW s ppref ∧
      ropeOK P Dim.ref tbRef (g * P.y.Lam) = true := by
  unfold bridgeB at t
  simp only [Bool.and_eq_true] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, b3⟩, -⟩, b5⟩, -⟩, -⟩, -⟩, b9⟩, -⟩, b11⟩, -⟩, -⟩, -⟩, -⟩ := t
  exact ⟨by simpa using b3, b5, sizedW_of_B b9, b11⟩

/-- The eight lines, as one equation of lists. -/
theorem linesAre_of {y : Lay} (h8 : y.calls.size = 8)
    (hl : ∀ (cc : Fin 8) (cd : CallD), y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName) : LinesAre y := by
  unfold LinesAre
  apply List.ext_getElem
  · simp only [List.length_map, Array.length_toList, List.length_finRange]
    exact h8
  · intro i h1 h2
    have hi : i < 8 := by simpa using h2
    have hi' : i < y.calls.size := by rw [h8]; exact hi
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_finRange]
    exact hl ⟨i, hi⟩ (y.calls[i]'hi') (Array.getElem?_eq_getElem hi')

/-- The public record's tails are those of its layout. -/
theorem pub_tails {y : Lay} {sc : Layer.Scales} {rope : Array ℕ} {wsLay : WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub}
    (hP : Pub.of y sc rope wsLay V tokv set = .ok P) : P.tails = tailsOf y := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  rfl

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {g : ℕ}

/-- **The nineteen public lines at `publicOf`'s own record, from the two tests.** -/
theorem pubLines_of_record (h : publicOf pol KL lay = .ok X) (t : recordB X g = true)
    (tt : tablesB X.layers.y = true) {hp : HPlan2} (hG : X.G[g]? = some hp)
    (hcap : Dim.ref.cap = (layerShape X.P).lidb) (tk : Array Nat) :
    ∃ s0, PubLines { X.layers with tokv := tk } g (layerShape X.P) X.P.polCalls Dim.ref tbRef
      (weightShape X.P X.y) kRef s0 hp.tl := by
  obtain ⟨hy, rd, r, _, _, hW, tb⟩ := returns_of_record h t
  obtain ⟨S, Z, h8, hl, hfl⟩ := bridgeB_parts tb
  obtain ⟨hg, h4, Zw, _⟩ := bridgeB_more tb
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hPl⟩ := Hd.public_plans h
  obtain ⟨htm, hNM⟩ := plan_sizes hP hPl hG
  obtain ⟨s0, pub, hs0, _⟩ := shape_of_layout hy
  have ey : X.layers.y = X.y := rfl
  have hsc := Hd.scalesHeld_of_public h
  rw [shape_of_public h] at hsc
  have hL := hL_of_tablesB tt
  have hfo := (fo_of_layout hy).1
  refine ⟨s0,
    { hy := hy
      S := S
      hs := hsc
      hg := hg
      hrd := Model.Fit.public_reads h
      hmats := ?_
      hρ := gl_numerals
      Z := Z
      hc := hcap
      hN := linesAre_of h8 hl
      hfl := hfl
      hs0 := hs0
      Zw := Zw
      hsL := rfl
      hlw := hW
      h4 := h4
      htm := htm
      hNM := hNM
      hpad := ?_ }⟩
  · show ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR X.layers.y g
    rw [pub_tails hP]
    rfl
  · intro k
    obtain ⟨c0, e0, I⟩ := hL k
    rw [hfo] at e0
    have e1 : X.layers.y.cl.getD k.val {} = c0 := by
      rw [Array.getD_eq_getD_getElem?, e0]
      rfl
    show Reading.gl.val (ofF ((X.layers.y.cl.getD k.val {}).tauAt
      (X.layers.y.cl.getD k.val {}).t0)) = _
    rw [e1]
    exact I.pad_value gl_numerals

/-- `RopeFits` from the test on the rotary tables, at an environment that holds the record's layout,
scales and group. -/
theorem ropeFits_of_ropeOK {P : Pub} {D : Dim} {tb : Tables} {h : Layer.Shape}
    (hr : ropeOK P D tb (g * P.y.Lam) = true) (Z : Sized h D) (eh : P.y.h = h)
    (hLam : P.y.Lam = D.nl) {c : ClaimEnv} (vy : c.v.y = P.y) (vsc : c.v.sc = P.sc)
    (vg : c.v.g = g) (vr : c.rope = P.rope) {lam : ℕ} (hlam : lam < P.y.Lam) :
    RopeFits Reading.gl c D tb (g * P.y.Lam) lam := by
  have key : ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
      tb.C (g * P.y.Lam + lam) t i =
          Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) t i false ∧
        tb.S (g * P.y.Lam + lam) t i =
          Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) t i true := by
    intro t i ht hi
    have hi' : i < D.P.ch / 2 := by
      rw [Z.ch, ← eh, ← vy]
      exact hi
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hr lam
      (List.mem_range.mpr (hLam ▸ hlam))) t (List.mem_range.mpr ht)) i (List.mem_range.mpr hi')
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h1
  have el : c.v.lay lam = g * P.y.Lam + lam := by
    show c.v.g * c.v.y.Lam + lam = _
    rw [vg, vy]
  exact ⟨fun t i ht hi => by rw [gl_numerals.ofInt, vy, vsc, vr, el, (key t i ht hi).1],
    fun t i ht hi => by rw [gl_numerals.ofInt, vy, vsc, vr, el, (key t i ht hi).2]⟩

/-- **The rotary tables fit in every layer of the group, at `publicOf`'s own record.** -/
theorem rope_of_record (h : publicOf pol KL lay = .ok X) (t : recordB X g = true) {v : Env}
    (vy : v.y = X.layers.y) (vsc : v.sc = X.layers.sc) (vg : v.g = g) (rs rt : Array E)
    {lam : ℕ} (hlam : lam < X.layers.y.Lam) :
    RopeFits Reading.gl
      { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt } Dim.ref tbRef
      (g * X.layers.y.Lam) lam := by
  obtain ⟨hy, rd, r, _, _, _, tb⟩ := returns_of_record h t
  obtain ⟨_, Z, _⟩ := bridgeB_parts tb
  obtain ⟨_, _, _, hr⟩ := bridgeB_more tb
  have L := laySizes_of_layout hy
  exact ropeFits_of_ropeOK hr Z L.shape (L.Lam.trans (nl_tie Z).symm) vy vsc vg rfl hlam

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pubLines_of_record
#print axioms OnBytes.Road.K4.rope_of_record
