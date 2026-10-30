-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionConfigWhole.lean: a test of the function config of
OnBytes/Model/AttentionConfig.lean as a whole.

The tests run when this file is compiled. The program does not import this file.

The numbers are those of a small configuration (64 tokens, eight layers in two groups of four, four
query heads, two heads of keys and values), spelled out here (layerShape, layerCalls) and in
OnBytes/Model/TestAttentionConfig.lean (exampleScan, exampleScales). Below it is called the example.
No file of the repository is read; the examples under prover/examples may have other numbers. The
layout of the layer sub-proofs is made by its own function (OnBytes/Model/LayerLayout.lean) from the
example's lines. So the tests in which config checks the two kinds of sub-proof against each other
compare what two Lean files compute: that file and OnBytes/Model/AttentionShape.lean.

Where the two counts come from. When the C++ verifier checks a proof at this configuration
(cp_verify <config folder> <ivk folder> <request file> <y file> <proof file>, with a parameter file
and a file of scales that have these numbers), it prints for each attention sub-proof
a line like "read: sub-proof A_0: 1191 claims listed (tested at the chain's end), 3076 slots". The
two numbers were recorded from such a run of the C++ verifier, built from its source without added
lines. To see the line one needs files with these numbers and a proof that the prover has made from
them.

What is tested: config goes through; both attention sub-proofs have these numbers of slots and of
claims; the digest of the call lines is the one that the item request takes; the layout's numbers
that OnBytes/Model/TestAttentionConfig.lean types by hand are those of the layers' own function.
That altered inputs are refused is tested in OnBytes/Model/TestAttentionConfigRefused.lean, with the
functions of this file.
-/
import OnBytes.Model.TestAttentionConfig

namespace OnBytes.Attention.TestConfig

/-- The example's numbers as the layer sub-proofs read them. -/
def layerShape : Model.Layer.Shape :=
  { prof := 4, lt := 6, L := 8, ll := 2, d := 512, H := 4, Gk := 2, dh := 128, f := 1024, fe := 512,
    NE := 4, eps1 := 1, eps2 := 1, epsF := 1, cs := 12, theta0 := 10000, hq := 2, hv := 1, ho := 1,
    hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 8, nmin := 20, D := 2048, tau := 128,
    lmaf := 13, NAf := 3, lmad := 12, NAd := 1, lmar := 12, lmb := 13, lmq := 13, lmx := 13,
    wb := Array.replicate 12 13, iota := #[0, 0, 0, 1, 0, 0, 0, 0], seed := 31, gcl := true,
    rcl := true, xl := 5, lidb := 24 }

/-- The example's lines call, each without its first word. -/
def layerCalls : List (List String) :=
  [["R16a", "R16", "G", "U"], ["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
   ["R16c", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"],
   ["R8", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL", "L3", "G0"],
   ["FC", "FC", "CN1", "CN2", "CQK", "CV", "CLR"], ["FS", "FS", "MR", "CG"], ["FL", "FL", "F"],
   ["R16d", "R16", "UT"]]

/-- Runs config on the parameter file P as read, with the example's layout of the layers. The matrix
qa is number 6 in the list of its owner, and the layer sub-proof of group g has the number 1 + g. -/
def wholeOf (P : Model.PolScan) : Except String Config := do
  let y ← Model.Layer.layout layerShape layerCalls
  config P y exampleScales fun g => 256 * (1 + g) + 6

/-- Runs config on the example's parameter file, with the example's layout of the layers changed
by f. -/
def wholeWith (f : Model.Layer.Lay → Model.Layer.Lay) : Except String Config := do
  let y ← Model.Layer.layout layerShape layerCalls
  config exampleScan (f y) exampleScales fun g => 256 * (1 + g) + 6

/-- Of each plan: the sub-proof's number, its slots and its claims. -/
def countsOf (c : Config) : List (Nat × Nat × Nat) :=
  c.plans.toList.map fun X => (X.inp.gid, X.ns, X.nLin)

-- the numbers that exampleLayers types by hand, and the lengths of the four lists by matrix
#guard ((Model.Layer.layout layerShape layerCalls).toOption.map fun y =>
    [y.T, y.Lam, y.NGr, y.ldh, y.mrow.getD 3 0, y.kcol.getD 3 0]) ==
  some [exampleLayers.T, exampleLayers.Lam, exampleLayers.NGr, exampleLayers.ldh,
    exampleLayers.mrow.getD 3 0, exampleLayers.kcol.getD 3 0]
#guard ((Model.Layer.layout layerShape layerCalls).toOption.map fun y =>
    [y.mrow.size, y.kcol.size, y.filled.size, y.feat.size]) == some [4, 4, 4, 4]

#guard ((wholeOf exampleScan).toOption.map countsOf) == some [(4, 3076, 1191), (5, 3076, 1191)]
-- the digest for the statement is the one that the item request takes from the file's text
#guard ((wholeOf exampleScan).toOption.map (·.hCallsA)) ==
  (Proof.ParamLines.read exampleText.toUTF8).calls "callA"

end OnBytes.Attention.TestConfig
