-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysRun.lean: a shape for which layout and the other functions that a layer
sub-proof's forms and panels depend on return, under the switches for which the library has keys: a
run on made-up numbers.

The theorems of Johnson/Road/FormsKeysLaid.lean begin "if layout returns a layout", and those on the
forms of the lookup's segments begin "if line returns a form". This file shows that these beginnings
can be met together. It writes out a small shape, five lines of calls and a file of scales, and
evaluates the verifier's own functions on them. A part of that is proved; the whole is run.

Two kinds of evidence.
A line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the compilation
fails if the value is not true. It is a run. It is no theorem: nothing that only a guard shows can
be used in a proof.
The theorems of the last section are theorems. They say that the first half of the layout
(layoutBase) returns a layout for this shape, that this layout has all that the record Admitted
gathers, and that the scales pass scalesOf and scalesHeld (publicR).

What is run and not proved: that the second half of the layout (layoutLook) returns, and so that
layout does; noWrap; points 4 to 11 below.

What is run, on the shape hR, the calls pcR and the words klR:
 1. layout returns a layout,
 2. scalesOf returns the scales; scalesHeld, noWrap and weightWidthsHeld pass,
 3. the eleven switches hold (a theorem: switchesR),
 4. the calls hold 34 segments, one under the name of each of the library's families,
 5. readsOf returns the tables of reads, and for each of the two groups layTables places the
    families of tables: 20 in each group (5 long ones of af, 1 of qa, 3 of the stream that comes in,
    1 of the stream that goes out; 2 short ones of ad, 4 of ar, 1 of qa; 3 of b), and one more in
    the first group, for the embedding,
 6. in each group line returns a form for every segment on every layer on which the segment exists,
    under the weights that the join makes (ewJ, whJ): 118 pairs of a segment and a layer, 25
    segments on 4 layers and 9 on 2,
 7. in each group weighedOf and joinPart return a value for every call,
 8. in each group panelsA and panelsT list 18 panels, which leave 32 weight claims; placePanels
    gives them 586 places, so the batched sumcheck has 10 rounds,
 9. in each group stackEnd returns, so stackEndOf has returned on every panel, and every form that a
    side of a panel names is there,
 10. wsLayOf and ropeOf return, and in each group weightClaims returns 32 claims, as many as the
    panels leave; in the first group claimE returns the embedding's claim,
 11. three controls: a shape whose hidden units are not twice an expert's, a list of calls that
    lacks a segment, and a file of scales with a norm's shift of 16 are refused.

This is not a shape that the verifier has admitted. The verifier reads a shape from a parameter
file and makes many more tests on it (publicOf in OnBytes/Model/VerifyPublic.lean). Of these the
following are not run here: the scan of the file and the tests before and behind the layout
(polScan, polBeforeLayout, polBehindLayout, polTablesAdmitted), planesHeld, tableHeld on the three
tables, hPar, the head's and attention's layouts (Head.vocabulary, Head.layout, Attention.config),
Pub.of, and the plans with their comparisons (plansG, attentionOwners, ownerOf, Head.planH2,
crossPlans).

What is made up. All numbers of hR, the names and the order in pcR, the words klR, the size of the
vocabulary and the number of column bits of the committed weights, the tokens, and every element of
the field that stands for a challenge, a point or a shown value (zkR, elemsR) are made up for this
file; none is taken from a parameter file, and no two of the points are tied to each other as a run
of the verifier would tie them. Each array of elements has the length that the verifier's caller
gives it (hearStack and hearOwn in OnBytes/Model/Layer.lean). The matrices' rows and columns are
those that the check of a layer sub-proof takes from the layout (tailsOf). Two fields of Env come
from a sub-proof's plan, which this file does not build: the number of the array of the reads (here
0) and the number of its columns (here 16).

What is not claimed. Nothing is said of any other shape. No proof is made or checked: no prover has
run, and the forms are built, not valued. The program does not import this file.

-/
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysJoin
import OnBytes.Model.Layer

set_option autoImplicit false

namespace OnBytes.Road

open OnBytes.Model (Seg CallD refuseIf TenAt WsShape WsLay wsLayOf)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads layout layoutBase scalesOf scalesHeld noWrap
  weightWidthsHeld readsOf tableAsks layTables tailsOf tensorsFill tensorRuns runsEnd PanelEnv
  ClaimEnv panelsA panelsT placePanels stackEnd ropeOf nEndT stubO)
open Inst.Model.FFSeg (Fam)

/-! ## The made-up numbers -/

/-- A small shape: 16 tokens, 8 layers in 2 groups of 4, width 8, two query heads and one key head
of width 4, 32 hidden units, 4 routed experts of 16 hidden units, blocks of 2 features. -/
def hR : Shape :=
  { prof := 4, lt := 4, L := 8, ll := 2, d := 8, H := 2, Gk := 1, dh := 4, f := 32, fe := 16,
    NE := 4, eps1 := 7, eps2 := 11, epsF := 13, cs := 12, theta0 := 10007, hq := 2, hv := 1,
    ho := 1, hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 5, nmin := 10, D := 32,
    tau := 128, lmaf := 7, NAf := 2, lmad := 6, NAd := 2, lmar := 6, lmb := 12, lmq := 6, lmx := 6,
    wb := Array.replicate 12 13, iota := #[3, 4, 1, 1, 0, 0, 0, 0], seed := 5, gcl := true,
    rcl := true, xl := 5, lidb := 22 }

/-- Five calls, one for each kind of table, with all 34 segments. -/
def pcR : List (List String) :=
  [["wide", "R16", "QK", "G", "N1", "XR", "U", "O", "LT", "UT", "N2", "QKH", "D", "LR", "N1H", "V",
    "DD", "N2H"],
   ["byte", "R8", "ROW", "GH", "SEL", "OH", "UH", "L3", "VH", "G0", "LH", "DH"],
   ["cut", "FC", "CQK", "CN1", "CLR", "CV", "CN2"],
   ["score", "FS", "CG", "MR"],
   ["gate", "FL", "F"]]

/-- The words of a file of scales: a record of 13 words for each of the 8 layers, then a record of 3
words for each of the 4 layers with routed experts. Some shifts are below 16 and some above. -/
def klR : Array Nat :=
  ((List.range 8).flatMap fun l =>
    [17 + l % 4, 20, 9 + l, 12 + l, 14 + l % 5, 11 + l % 7, 15 + l % 4, 26 + l % 4, 17 + l % 6,
     24 + l % 3, 18 + l % 4, 3, l % 2]).toArray ++
  ((List.range 4).flatMap fun i => [10 + i, 13 + i, 16 + i]).toArray

/-- A point for each call, of the length that the call's point has: the coordinates of the layer, of
the column and of the token. -/
def zkR (y : Lay) : Array (Array E) :=
  y.calls.mapIdx fun q cd =>
    (Array.range (y.h.ll + cd.lJ + y.h.lt)).map fun i => Model.ofNat (1000 * q + 7 * i + 3)

/-! ## What is evaluated -/

/-- The rows and columns of the matrices of group g, as the check of a layer sub-proof takes them
from the layout. -/
def matsR (y : Lay) (g : ℕ) : Array (ℕ × ℕ) := ((tailsOf y).getD g {}).mats.map fun M => (M.m, M.k)

/-- What the forms of group g read. Returns none if layTables places no tables. -/
def envR (y : Lay) (sc : Scales) (rd : Reads) (g : ℕ) : Option Env :=
  (layTables (matsR y g) (tableAsks y rd g) 0).map fun t =>
    { y, sc, g, iU3 := 0, K3 := 16, tab := t.1, zk := zkR y }

/-- The number of pairs of a segment and a layer on which it exists for which line returns a form
under the join's weights, and the number of all such pairs. -/
def linesR (v : Env) : ℕ × ℕ :=
  v.y.calls.toList.zipIdx.foldl (fun n x =>
    x.1.segs.foldl (fun n s =>
      (List.range v.y.Lam).foldl (fun n lam =>
        if s.moe && !v.isMoe lam then n
        else if (v.line s.name lam (ewJ v x.2 x.1 s) (whJ v x.2 x.1 s)).isSome then
          (n.1 + 1, n.2 + 1)
        else (n.1, n.2 + 1)) n) n) (0, 0)

/-- True if weighedOf and joinPart return a value for every call. -/
def joinsR (v : Env) : Bool :=
  v.y.calls.toList.zipIdx.all fun x =>
    match v.weighedOf x.1 with
    | some w => (v.joinPart (Model.ofNat 5) (Model.ofNat 9) x.2 x.1 w).isSome
    | none => false

/-- The library's families. -/
def famsR : List Fam :=
  [.G, .U, .UT, .QK, .N1, .N2, .O, .D, .V, .LR, .XR, .LT, .DD, .GH, .UH, .OH, .DH, .VH, .LH, .QKH,
   .N1H, .N2H, .ROW, .SEL, .L3, .G0, .CN1, .CN2, .CQK, .CV, .CLR, .F, .MR, .CG]

/-- For each group of layers: the number of families of tables, the two numbers of linesR, and
joinsR. Refuses where the verifier's functions refuse. -/
def runR : Except String (List (ℕ × (ℕ × ℕ) × Bool)) := do
  let y ← layout hR pcR
  let sc ← scalesOf hR klR
  let rd ← readsOf y
  (List.range y.NGr).mapM fun g =>
    match envR y sc rd g with
    | some v => pure (v.tab.length, linesR v, joinsR v)
    | none => throw "no tables"

/-- n elements of the field, made up from a number. -/
def elemsR (seed n : ℕ) : Array E := (Array.range n).map fun i => Model.ofNat (seed + 13 * i + 1)

/-- What the lists of panels read besides the tables: a weight for each call, the values that the
second token sumcheck shows, and a token point. -/
def panelEnvR (v : Env) : PanelEnv :=
  { v, e := elemsR 100 v.y.calls.size, shownT := elemsR 200 (nEndT v.y), zt := elemsR 300 v.y.h.lt,
    stubO := stubO v.y }

/-- The numbers on which the layout of the committed weights depends, with a vocabulary of 16. -/
def wsShapeR (y : Lay) : WsShape :=
  { D := y.h.D, L := y.h.L, d := y.h.d, dh := y.h.dh, dkv := y.dkv, dq := y.dq, f := y.h.f,
    fe := y.h.fe, NE := y.h.NE, V := 16 }

/-- The panels of a group, as the check of a layer sub-proof calls the functions: the number of
panels, of the weight claims that they leave, of their places and of the sumcheck's rounds, the bits
of the panel of the down product at the sumcheck's end, and the number of claims that weightClaims
returns. Returns none where one of the functions does. -/
def panelsR (v : Env) (rd : Reads) (wsLay : WsLay) (rope : Array ℕ) :
    Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := do
  let y := v.y
  let pe := panelEnvR v
  let TS ← rd.tscCalls.mapM y.callNo
  let pans ← panelsT pe TS (panelsA pe {})
  let (bl, places) := placePanels pans.bl
  let lamS := ceilLog2 places
  let rs := elemsR 400 lamS
  let fin ← stackEnd y bl rs lamS (elemsR 500 2) (elemsR 600 (1 + y.LamM)) (elemsR 700 pans.nextV)
    (Model.ofNat 801) (Model.ofNat 802)
  let ce : ClaimEnv := { v, wsLay, rope, rs, rt := elemsR 900 y.h.lt }
  let claims ← ce.weightClaims TS
  pure (bl.size, pans.nextV, places, lamS, fin.wD, claims.length)

/-- True if the embedding's claim is returned, at made-up points and tokens. -/
def claimER (v : Env) (wsLay : WsLay) (rope : Array ℕ) : Bool :=
  let y := v.y
  let ce : ClaimEnv := { v, wsLay, rope, rs := #[], rt := #[] }
  (ce.claimE (elemsR 1000 (y.ls + y.h.lt)) (elemsR 1100 (y.lPd - y.ls)) 16
    ((Array.range y.T).map fun t => (5 * t + 3) % 16)).isSome

/-- For each group of layers what panelsR returns. Refuses where the verifier's functions refuse. -/
def run2R : Except String (List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × Bool) := do
  let y ← layout hR pcR
  let sc ← scalesOf hR klR
  let rd ← readsOf y
  let wsLay ← wsLayOf (wsShapeR y) y.h.p3 6
  let rope ← ropeOf y.h
  let r ← (List.range y.NGr).mapM fun g =>
    match (envR y sc rd g).bind fun v => panelsR v rd wsLay rope with
    | some x => pure x
    | none => throw "a function of the panels returns none"
  let e := match envR y sc rd 0 with
    | some v => claimER v wsLay rope
    | none => false
  pure (r, e)

/-! ## The run -/

/- 1: the layout -/
#guard (layout hR pcR).isOk

/- 2: the scales -/
#guard (match scalesOf hR klR with
  | .ok sc => (scalesHeld hR sc).isOk && (noWrap hR sc (hR.H * hR.dh)).isOk
  | .error _ => false)
#guard (match layout hR pcR with
  | .ok y => (weightWidthsHeld hR y.kinds).isOk
  | .error _ => false)

/-- 3: the shape has the switches and digit forms for which the library has keys. -/
theorem switchesR : Switches hR :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- 4: 34 segments, one under each family's name -/
#guard (match layout hR pcR with
  | .ok y =>
    let names := (y.calls.toList.flatMap fun c : CallD => c.segs).map fun s : Seg => s.name
    names.length == 34 && famsR.length == 34 && famsR.all fun fam => names.contains (segName fam)
  | .error _ => false)

/- 5, 6, 7: the tables, the forms of the segments, the calls' factors, in the two groups -/
#guard (match runR with
  | .ok r => r == [(21, (118, 118), true), (20, (118, 118), true)]
  | .error _ => false)

/- 8, 9, 10: the panels, the end of the batched sumcheck, the weight claims, in the two groups -/
#guard (match run2R with
  | .ok r => r == ([(18, 32, 586, 10, 7, 32), (18, 32, 586, 10, 7, 32)], true)
  | .error _ => false)

/- 11: three controls -/
#guard !(layout { hR with f := 30 } pcR).isOk
#guard !(layout hR (pcR.dropLast ++ [["gate", "FL"]])).isOk && !(layout hR pcR.dropLast).isOk
#guard (match scalesOf hR (klR.set! 8 16) with
  | .ok sc => !(scalesHeld hR sc).isOk
  | .error _ => false)

/-! ## What is proved -/

/-- A computation that is marked as having returned has returned a value. -/
theorem ok_of_isOk {α : Type} {x : Except String α} (h : x.isOk = true) : ∃ y, x = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

/-- A test whose condition is false goes on. -/
theorem isOk_refuse {β : Type} {b : Bool} {n : String} {f : Unit → Except String β}
    (hb : b = false) (h : (f ()).isOk = true) : (refuseIf b n >>= f).isOk = true := by
  subst hb
  exact h

/-- A step that returns a value goes on from it. -/
theorem isOk_step {α β : Type} {x : Except String α} {a : α} {f : α → Except String β}
    (hx : x = .ok a) (h : (f a).isOk = true) : (x >>= f).isOk = true := by
  subst hx
  exact h

/-- The test that tensors fill a matrix passes if each tensor's features are a whole number of
blocks and the tensors' runs, which are in rising order already, follow each other without a gap. -/
theorem fill_ok (ten : List (String × TenAt)) (feat S2 : ℕ) (arr : String)
    (h1 : (ten.any fun t => t.2.J == 0 || t.2.J % S2 != 0) = false)
    (h2 : (tensorRuns ten).Pairwise fun a b => decide (a.1 ≤ b.1) = true)
    (h3 : runsEnd (tensorRuns ten) 0 = some feat) : tensorsFill ten feat S2 arr = .ok () := by
  have hs : (tensorRuns ten).mergeSort (fun a b => decide (a.1 ≤ b.1)) = tensorRuns ten :=
    List.mergeSort_of_pairwise h2
  have hb : (some feat != some feat) = false := by simp
  unfold tensorsFill
  rw [h1, hs]
  show (refuseIf false _ >>= fun _ => refuseIf (runsEnd (tensorRuns ten) 0 != some feat) _) = _
  rw [h3, hb]
  rfl

/-- The one tensor of a matrix of the residual stream fills it. -/
theorem fillStreamR : tensorsFill [("x", ⟨0, 5, 1, 8⟩)] 40 2 "stream" = .ok () :=
  fill_ok _ _ _ _ (by rfl) (by decide) (by rfl)

/-- The four tensors of the matrix qa fill it. -/
theorem fillQaR : tensorsFill [("q", ⟨0, 2, 4, 8⟩), ("kx", ⟨64, 2, 4, 4⟩), ("v", ⟨96, 2, 4, 4⟩),
    ("o", ⟨128, 2, 4, 8⟩)] 192 2 "qa" = .ok () :=
  fill_ok _ _ _ _ (by rfl) (by decide) (by rfl)

set_option maxRecDepth 100000 in
/-- The first half of the layout goes through all its tests on the shape hR and the calls pcR. One
line for each step of layoutBase, in its order. -/
theorem baseR_isOk : (layoutBase hR pcR).isOk = true := by
  unfold layoutBase
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_step (a := ()) (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_step (a := ()) fillStreamR ?_
  refine isOk_step (a := ()) fillQaR ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_step (a := ?taken) ?ht ?_
  case ht => rfl
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  refine isOk_refuse (by rfl) ?_
  rfl

/-- The first half of the layout returns a layout for the shape hR and the calls pcR. -/
theorem baseR : ∃ y, layoutBase hR pcR = .ok y := ok_of_isOk baseR_isOk

set_option maxRecDepth 100000 in
/-- The words klR are a file of scales for the shape hR, and they pass the tests on the scales. -/
theorem scalesR : ∃ sc, scalesOf hR klR = .ok sc ∧ scalesHeld hR sc = .ok () :=
  ⟨⟨klR, 13, 8⟩, by rfl, by rfl⟩

/-- The hypotheses on public numbers can be met together. At the shape hR, which has the switches,
the first half of the layout returns a layout for the calls pcR; this layout has all that the record
Admitted gathers, Laid among it; and the words klR are scales that pass the tests. The layout is
that of layoutBase: the fields that layoutLook fills are empty in it. -/
theorem publicR : Switches hR ∧ ∃ (y : Lay) (sc : Scales), layoutBase hR pcR = .ok y ∧
    Admitted hR y ∧ scalesOf hR klR = .ok sc ∧ scalesHeld hR sc = .ok () := by
  obtain ⟨y, hy⟩ := baseR
  obtain ⟨sc, h1, h2⟩ := scalesR
  exact ⟨switchesR, y, sc, hy, admitted_of_base hy switchesR.p3, h1, h2⟩

#print axioms switchesR
#print axioms publicR

end OnBytes.Road
