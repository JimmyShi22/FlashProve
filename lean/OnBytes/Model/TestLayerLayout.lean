-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLayerLayout.lean: refusals of OnBytes/Model/LayerLayout.lean. Of the 65 names in
layoutNames the rows expect 61; the four others are listed below.

Most rows take a small configuration, spelled out here, change one number (in some rows two or
more), and state how the function under test must end: under which name it refuses, or that it goes
through. For most bounds one row stands at the first refused value and one at the last that passes.
Where the last passing value cannot go through for another reason, the row ends under the name of a
later test. The rows on lists of tensors make their lists up. The rows of lookRows change a number
in a finished first half of the layout, some of them to a state that no parameter file gives. No
proof is read.

layoutBase makes large tables at its end. A row shows without that cost that a test of
layoutBase passes: it also sets the line lmb to 25. Of the tests on the shape and on the list of
calls only the one on nmin comes after the test on lmb, so the ending shape-lmb (pastShape) says
that all others have passed.

For a row whose label ends in (C++), the C++ verifier refuses a parameter file or a file of scales
of this configuration with the same one change under the same name (shape-call with the call's name
behind it). That was seen in planning calls (cp_verify -plan, no proof is read) of the C++ verifier
as it ships, on the changed files; the repository holds no script that repeats them. The other rows
are not tied to a run of the C++ verifier: their expected endings were worked out from the Lean code
and the C++ source.

Without a row (the last guards hold this list): internal-forest-pub, and three conditions of noWrap:
W-xr, guard-flag-gate-clamp and one-hot. Each of the three stands behind a stricter condition that
refuses first (U-xr, guard-radix-gate-clamp, MR). The list counts names. A name can stand for
several conditions, and a row sees only the name.

This file is not part of the compiled program.
-/
import OnBytes.Model.LayerLayout

namespace OnBytes.Model.Layer.TestLayout

/-- The configuration's numbers. -/
def h : Shape :=
  { prof := 4, lt := 6, L := 8, ll := 2, d := 512, H := 4, Gk := 2, dh := 128, f := 1024, fe := 512,
    NE := 4, eps1 := 1, eps2 := 1, epsF := 1, cs := 12, theta0 := 10000, hq := 2, hv := 1, ho := 1,
    hgD := 1, huD := 1, hdD := 1, hr := 1, ut := 1, la := 8, nmin := 20, D := 2048, tau := 128,
    lmaf := 13, NAf := 3, lmad := 12, NAd := 1, lmar := 12, lmb := 13, lmq := 13, lmx := 13,
    wb := Array.replicate 12 13, iota := #[0, 0, 0, 1, 0, 0, 0, 0], seed := 31, gcl := true,
    rcl := true, xl := 5, lidb := 24 }

/-- The configuration's lines "call". -/
def pc : List (List String) :=
  [["R16a", "R16", "G", "U"], ["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
   ["R16c", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"],
   ["R8", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL", "L3", "G0"],
   ["FC", "FC", "CN1", "CN2", "CQK", "CV", "CLR"], ["FS", "FS", "MR", "CG"], ["FL", "FL", "F"],
   ["R16d", "R16", "UT"]]

/-- The configuration's file of scales: eight records of 13 words, then four of 3 words. -/
def KL : Array Nat :=
  let rec13 (rp : Nat) : Array Nat := #[29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, rp]
  rec13 1 ++ rec13 1 ++ rec13 1 ++ rec13 0 ++ rec13 1 ++ rec13 1 ++ rec13 1 ++ rec13 0 ++
    #[11, 8, 14, 11, 8, 14, 11, 8, 14, 11, 8, 14]

/-- The name under which x refuses, or "passes". -/
def endOf {α : Type} (x : Except String α) : String :=
  match x with
  | .ok _ => "passes"
  | .error e => e

/-- How layoutBase ends on the shape x with the line lmb set to 25. -/
def base (x : Shape) (calls : List (List String) := pc) : String :=
  endOf (layoutBase { x with lmb := 25 } calls)

/-- The ending that says: every test before the one on lmb has passed. -/
def pastShape : String := "shape-lmb"

/-- The configuration with 2^15 tokens and matrices that are high enough for them. -/
def wide : Shape := { h with lt := 15, lmaf := 17, lmad := 17, lmar := 17, lmq := 17, lmx := 17 }

/-- The configuration without routed experts. Its list of calls names segments that are then
absent, so a row on it that passes the tests on the shape ends policy-call-list. -/
def dense : Shape := { h with NE := 0, hr := 0, gcl := false, rcl := false }

/-- The rows on the shape: label, ending, expected ending. D 2 and D 4096 pass here; the layout of
the committed weights (OnBytes/Model/Weights.lean) has a narrower test of its own under the same
name. The row f 0 also breaks f = 2 fe, under the same name; the row f 0, fe 0 does not. -/
def shapeRows : List (String × String × String) :=
  [("the configuration", base h, pastShape),
   ("prof 2", base { h with prof := 2 }, "policy-profile"),
   ("prof 3", base { h with prof := 3 }, pastShape),
   ("prof 5 (C++)", base { h with prof := 5 }, "policy-profile"),
   ("lt 3 (C++)", base { h with lt := 3 }, "shape-words"),
   ("lt 4", base { h with lt := 4 }, pastShape),
   ("lt 16", base { h with lt := 16 }, "shape-la"),
   ("lt 17", base { h with lt := 17 }, "shape-words"),
   ("ll 0 (C++)", base { h with ll := 0 }, "shape-words"),
   ("ll 1", base { h with ll := 1 }, pastShape),
   ("ll 6, L 64", base { h with ll := 6, L := 64 }, pastShape),
   ("ll 7", base { h with ll := 7 }, "shape-words"),
   ("d 0 (C++)", base { h with d := 0 }, "shape-words"),
   ("d 2^20, dh 2^18", base { h with d := 2 ^ 20, dh := 2 ^ 18 }, pastShape),
   ("d 2^20 + 1", base { h with d := 2 ^ 20 + 1 }, "shape-words"),
   ("f 0 (C++)", base { h with f := 0 }, "shape-words"),
   ("f 0, fe 0", base { h with f := 0, fe := 0 }, "shape-words"),
   ("f 1023 (C++)", base { h with f := 1023 }, "shape-words"),
   ("fe 511 (C++)", base { h with fe := 511 }, "shape-words"),
   ("f 1536, fe 768", base { h with f := 1536, fe := 768 }, "shape-words"),
   ("f 2^20, fe 2^19", base { h with f := 2 ^ 20, fe := 2 ^ 19 }, pastShape),
   ("f 2^21, fe 2^20", base { h with f := 2 ^ 21, fe := 2 ^ 20 }, "shape-words"),
   ("ll 1, f 2, fe 1", base { h with ll := 1, f := 2, fe := 1 }, "shape-words"),
   ("L 0 (C++)", base { h with L := 0 }, "shape-L"),
   ("L 10 (C++)", base { h with L := 10 }, "shape-L"),
   ("L 12", base { h with L := 12 }, pastShape),
   ("28 groups", base { h with L := 112 }, pastShape),
   ("29 groups", base { h with L := 116 }, "plan-groups-base"),
   ("32766 groups", base { h with L := 4 * 32766 }, "plan-groups-base"),
   ("32767 groups", base { h with L := 4 * 32767 }, "shape-groups"),
   ("la 6", base { h with la := 6 }, "shape-la"),
   ("la 7", base { h with la := 7 }, pastShape),
   ("lt 15, la 16", base { wide with la := 16 }, pastShape),
   ("lt 15, la 17", base { wide with la := 17 }, "shape-la"),
   ("la 14, Gk 1", base { h with Gk := 1, la := 14, lmq := 14, lmaf := 14, lmx := 14 }, "shape-la"),
   ("la 14, Gk 2", base { h with la := 14, lmq := 14, lmaf := 14, lmx := 14 }, pastShape),
   ("d 514 (C++)", base { h with d := 514 }, "shape-la"),
   ("la 14, f 256, fe 128",
     base { h with la := 14, lmq := 14, lmaf := 14, lmx := 14, f := 256, fe := 128 }, "shape-la"),
   ("la 14, f 512, fe 256",
     base { h with la := 14, lmq := 14, lmaf := 14, lmx := 14, f := 512, fe := 256 }, pastShape),
   ("no experts, f 1022", base { dense with f := 1022 }, "shape-la"),
   ("no experts, f 1020", base { dense with f := 1020 }, "policy-call-list"),
   ("lmq 7", base { h with lmq := 7 }, "shape-la"),
   ("lmq 8", base { h with lmq := 8 }, pastShape),
   ("lmaf 7", base { h with lmaf := 7 }, "shape-la"),
   ("lmaf 8", base { h with lmaf := 8 }, pastShape),
   ("eps1 0 (C++)", base { h with eps1 := 0 }, "policy-norm"),
   ("eps2 0 (C++)", base { h with eps2 := 0 }, "policy-norm"),
   ("eps1 2^59 - 1", base { h with eps1 := 2 ^ 59 - 1 }, pastShape),
   ("eps1 2^59", base { h with eps1 := 2 ^ 59 }, "policy-norm"),
   ("eps2 2^59", base { h with eps2 := 2 ^ 59 }, "policy-norm"),
   ("H 0 (C++)", base { h with H := 0 }, "shape-heads"),
   ("H 6 (C++)", base { h with H := 6 }, "shape-heads"),
   ("Gk 0 (C++)", base { h with Gk := 0 }, "shape-heads"),
   ("dh 127 (C++)", base { h with dh := 127 }, "shape-heads"),
   ("d 384, H 2, dh 192", base { h with d := 384, H := 2, dh := 192 }, "shape-heads"),
   ("d 384, H 3, dh 128", base { h with d := 384, H := 3 }, pastShape),
   ("d 32, H 32, dh 1", base { h with d := 32, H := 32, dh := 1 }, "shape-heads"),
   ("d 64, H 32, dh 2", base { h with d := 64, H := 32, dh := 2 }, pastShape),
   ("H 32, dh 16, Gk 32", base { h with H := 32, dh := 16, Gk := 32 }, pastShape),
   ("H 32, dh 16, Gk 33", base { h with H := 32, dh := 16, Gk := 33 }, "shape-heads"),
   ("cs 11 (C++)", base { h with cs := 11 }, "policy-cs"),
   ("cs 13 (C++)", base { h with cs := 13 }, "policy-cs"),
   ("hq 3 (C++)", base { h with hq := 3 }, "policy-forms"),
   ("hv 2 (C++)", base { h with hv := 2 }, "policy-call-list"),
   ("hv 3 (C++)", base { h with hv := 3 }, "policy-forms"),
   ("ho 3 (C++)", base { h with ho := 3 }, "policy-forms"),
   ("hgD 3 (C++)", base { h with hgD := 3 }, "policy-forms"),
   ("huD 3 (C++)", base { h with huD := 3 }, "policy-forms"),
   ("hdD 3 (C++)", base { h with hdD := 3 }, "policy-forms"),
   ("hr 3 (C++)", base { h with hr := 3 }, "policy-forms"),
   ("NE 0 (C++)", base { h with NE := 0 }, "header-absent-class"),
   ("ut 0 (C++)", base { h with ut := 0 }, "policy-ut"),
   ("ut 2 (C++)", base { h with ut := 2 }, "policy-ut"),
   ("D 1", base { h with D := 1 }, "shape-D"),
   ("D 2", base { h with D := 2 }, pastShape),
   ("D 2047 (C++)", base { h with D := 2047 }, "shape-D"),
   ("D 4096", base { h with D := 4096 }, pastShape),
   ("D 8192", base { h with D := 8192 }, "shape-D"),
   ("xl 3", base { h with xl := 3 }, "internal-layout-words"),
   ("xl 4", base { h with xl := 4 }, pastShape),
   ("xl 6", base { h with xl := 6 }, "internal-layout-words"),
   ("NE 1", base { h with NE := 1 }, "shape-NE"),
   ("NE 2", base { h with NE := 2 }, pastShape),
   ("NE 3 (C++)", base { h with NE := 3 }, "shape-NE"),
   ("NE 4096", base { h with NE := 4096 }, pastShape),
   ("NE 8192", base { h with NE := 8192 }, "shape-NE"),
   ("no experts, gcl", base { h with NE := 0, hr := 0 }, "policy-gcl"),
   ("no experts, rcl", base { h with NE := 0, hr := 0, gcl := false }, "policy-rcl"),
   ("lmad 5", base { h with lmad := 5 }, "shape-request-matrix"),
   ("lmad 6", base { h with lmad := 6 }, pastShape),
   ("lmaf 24", base { h with lmaf := 24 }, pastShape),
   ("lmaf 25", base { h with lmaf := 25 }, "shape-request-matrix"),
   ("NAf 0 (C++)", base { h with NAf := 0 }, "shape-request-matrix"),
   ("NAf 64", base { h with NAf := 64 }, pastShape),
   ("NAf 65", base { h with NAf := 65 }, "shape-request-matrix"),
   ("NAd 0 (C++)", base { h with NAd := 0 }, "shape-request-matrix"),
   ("lmx 7", base { h with lmx := 7 }, "shape-request-matrix"),
   ("lmx 8", base { h with lmx := 8 }, pastShape),
   ("lmx 24", base { h with lmx := 24 }, pastShape),
   ("lmx 25", base { h with lmx := 25 }, "shape-request-matrix"),
   ("lmb 24, nmin 29", endOf (layoutBase { h with lmb := 24, nmin := 29 } pc), "shape-words"),
   ("lmb 25", endOf (layoutBase { h with lmb := 25, nmin := 29 } pc), "shape-lmb")]

/-- The rows on the list of calls. All refusals have one name, so a row does not show which test
refused. The first two rows of nine lines would also be refused by a later test (a name twice, a
line without a segment); the third is refused for its number of lines alone. -/
def callRows : List (String × String × String) :=
  [("no line call: the built-in list, which lacks UT and four more", base h [], "policy-call-list"),
   ("a call dropped (C++)", base h (pc.drop 1), "policy-call-list"),
   ("a call twice, nine lines (C++)", base h (pc.take 1 ++ pc), "policy-call-list"),
   ("nine calls", base h (pc.dropLast ++ [["R16d", "R16"], ["R16e", "R16", "UT"]]),
     "policy-call-list"),
   ("nine lines, each segment once",
     base h (pc.take 5 ++ [["FS", "FS", "MR"], ["FSb", "FS", "CG"]] ++ pc.drop 6),
     "policy-call-list"),
   ("a line without a segment", base h (pc.dropLast ++ [["R16d", "R16"]]), "policy-call-list"),
   ("an unknown segment", base h (pc.dropLast ++ [["R16d", "R16", "UT", "XX"]]),
     "policy-call-list"),
   ("a segment of another kind", base h (pc.dropLast ++ [["R16d", "R8", "UT"]]),
     "policy-call-list"),
   ("two calls of one name", base h (pc.dropLast ++ [["R16a", "R16", "UT"]]), "policy-call-list"),
   ("a segment twice in a line", base h (pc.dropLast ++ [["R16d", "R16", "UT", "UT"]]),
     "policy-call-list"),
   ("a call named V", base h (pc.dropLast ++ [["V", "R16", "UT"]]), "policy-call-list"),
   ("a call named a", base h (pc.dropLast ++ [["a", "R16", "UT"]]), "policy-call-list"),
   ("a call named b", base h (pc.dropLast ++ [["b", "R16", "UT"]]), "policy-call-list"),
   ("a call named E", base h (pc.dropLast ++ [["E", "R16", "UT"]]), "policy-call-list"),
   ("another name for the last call", base h (pc.dropLast ++ [["W", "R16", "UT"]]), pastShape)]

/-- How the tests on the file of scales end if word i is set to v. -/
def scales (i v : Nat) (x : Shape := h) : String :=
  endOf (do scalesHeld x (← scalesOf x (KL.set! i v)))

/-- The same if two words are set. -/
def two (i v j w : Nat) : String :=
  endOf (do scalesHeld h (← scalesOf h ((KL.set! i v).set! j w)))

/-- The rows on the file of scales. Words 0 to 12 are the first layer's record; word 104 is the
router's shift of the first layer with routed experts. -/
def scaleRows : List (String × String × String) :=
  [("the configuration", scales 0 29, "passes"),
   ("one word less (C++)", endOf (scalesOf h KL.pop), "KL-length"),
   ("one word more (C++)", endOf (scalesOf h (KL.push 0)), "KL-length"),
   ("kq 0 (C++)", scales 0 0, "KL-shift-range"),
   ("kq 32", scales 0 32, "passes"),
   ("kq 33 (C++)", scales 0 33, "KL-shift-range"),
   ("kq 16", scales 0 16, "passes"),
   ("kq 15", scales 0 15, "KL-kq-kk"),
   ("kk 15", scales 1 15, "KL-kq-kk"),
   ("kq 15, kk 15", two 0 15 1 15, "passes"),
   ("kk 0", scales 1 0, "KL-shift-range"),
   ("kk 33", scales 1 33, "KL-shift-range"),
   ("kv 0 (C++)", scales 2 0, "KL-shift-range"),
   ("kv 1", scales 2 1, "passes"),
   ("kv 24", scales 2 24, "passes"),
   ("kv 25 (C++)", scales 2 25, "KL-shift-range"),
   ("a shift of 16 at form 0", endOf (shiftHeld 16 0), "passes"),
   ("a shift of 17 at form 0", endOf (shiftHeld 17 0), "KL-shift-range"),
   ("ko 25 (C++)", scales 3 25, "KL-shift-range"),
   ("kg 25 (C++)", scales 4 25, "KL-shift-range"),
   ("ku 25 (C++)", scales 5 25, "KL-shift-range"),
   ("kd 25 (C++)", scales 6 25, "KL-shift-range"),
   ("M1 45, above K1 + 14 (C++)", scales 7 45, "KL-norm"),
   ("M1 24", scales 7 24, "passes"),
   ("M1 23", scales 7 23, "KL-norm"),
   ("K1 29, below M1 - 14 (C++)", scales 8 29, "KL-norm"),
   ("M1 24, K1 17", two 7 24 8 17, "passes"),
   ("M1 24, K1 16", two 7 24 8 16, "KL-norm"),
   ("K1 32", scales 8 32, "passes"),
   ("K1 33 (C++)", scales 8 33, "KL-norm"),
   ("M2 45, above K2 + 14 (C++)", scales 9 45, "KL-norm"),
   ("K2 33 (C++)", scales 10 33, "KL-norm"),
   ("the last word 0", scales 12 0, "passes"),
   ("the last word 2 (C++)", scales 12 2, "KL-rp"),
   ("the router's shift 0 (C++)", scales 104 0, "KL-shift-range"),
   ("the router's shift 24", scales 104 24, "passes"),
   ("the router's shift 25 (C++)", scales 104 25, "KL-shift-range"),
   ("the routed gate's shift 25 (C++)", scales 105 25, "KL-shift-range"),
   ("the routed up product's shift 25 (C++)", scales 106 25, "KL-shift-range"),
   ("kv 25 in the last layer", scales (13 * 7 + 2) 25, "KL-shift-range"),
   ("the last word 2 in the last layer", scales (13 * 7 + 12) 2, "KL-rp"),
   ("the last router's shift 25", scales 113 25, "KL-shift-range")]

/-- How noWrap ends on the shape x if word i of the file of scales is set to v. -/
def wrap (x : Shape) (i v : Nat) : String :=
  endOf (do noWrap x (← scalesOf x (KL.set! i v)) (x.H * x.dh))

/-- How noWrapWith ends on the shape x if a committed cell is bounded by Ty. The program's own bound
is 2^18. -/
def wrapTy (x : Shape) (Ty : Nat) : String :=
  let words := if x.p3 then KL else KL.extract 0 (13 * x.L)
  endOf (do noWrapWith x (← scalesOf x words) (x.H * x.dh) Ty)

/-- Further rows on the conditions against wrapping. Most of them give noWrap a shift, a width or a
bound on a cell that the tests before noWrap, or the program itself, would not let through. They
show, for each name that they expect, that a condition under it compares in the right direction and
refuses under that name. In a shape with a layer the condition linear stands behind W-norm, which is
stricter, so its two rows have no layer. -/
def wrapRows : List (String × String × String) :=
  [("kg 36", wrap h 4 36, "passes"),
   ("kg 37", wrap h 4 37, "no-wrap-U-gate"),
   ("ku 44", wrap h 5 44, "passes"),
   ("ku 45", wrap h 5 45, "no-wrap-U-up"),
   ("K1 44", wrap h 8 44, "passes"),
   ("K1 45", wrap h 8 45, "no-wrap-U-norm"),
   ("kq 44", wrap h 0 44, "passes"),
   ("kq 45", wrap h 0 45, "no-wrap-U-qk"),
   ("kk 45", wrap h 1 45, "no-wrap-U-qk"),
   ("kv 44", wrap h 2 44, "passes"),
   ("kv 45", wrap h 2 45, "no-wrap-U-v"),
   ("the router's shift 29", wrap h 104 29, "passes"),
   ("the router's shift 30", wrap h 104 30, "no-wrap-U-lr"),
   ("the router's shift 5", wrap h 104 5, "passes"),
   ("the router's shift 4", wrap h 104 4, "no-wrap-guard-radix-clamp"),
   ("d 2^22, kg 1", wrap { h with d := 2 ^ 22 } 4 1, "no-wrap-W-gate"),
   ("d 2^22, ku 1", wrap { h with d := 2 ^ 22 } 5 1, "no-wrap-W-up"),
   ("d 2^22, kv 1", wrap { h with d := 2 ^ 22 } 2 1, "no-wrap-W-v"),
   ("d 2^22, the router's shift 1", wrap { h with d := 2 ^ 22 } 104 1, "no-wrap-W-lr"),
   ("M1 60", wrap h 7 60, "no-wrap-W-norm"),
   ("f 2^20, kd 1", wrap { h with f := 2 ^ 20 } 6 1, "no-wrap-W-down"),
   ("kq 1", wrap h 0 1, "no-wrap-W-qk"),
   ("H 2^20, ko 1", wrap { h with H := 2 ^ 20 } 3 1, "no-wrap-W-o"),
   ("NE 2^20", wrap { h with NE := 2 ^ 20 } 0 29, "no-wrap-MR"),
   ("a cell below 2^18", wrapTy h (2 ^ 18), "passes"),
   ("a cell below 2^20", wrapTy h (2 ^ 20), "no-wrap-guard-radix-gate-clamp"),
   ("a cell below 2^20, no gcl", wrapTy { h with gcl := false } (2 ^ 20), "no-wrap-guard-radix"),
   ("a cell below 2^26, no gcl", wrapTy { h with gcl := false } (2 ^ 26), "no-wrap-guard-radix-FS"),
   ("a cell below 2^27", wrapTy h (2 ^ 27), "no-wrap-clamp-keys"),
   ("a cell below 2^35, no rcl", wrapTy { h with rcl := false } (2 ^ 35), "no-wrap-U-xr"),
   ("no layer, no experts, a cell below 2^35", wrapTy { dense with L := 0 } (2 ^ 35),
     "no-wrap-guard-radix"),
   ("no layer, no experts, a cell below 2^36", wrapTy { dense with L := 0 } (2 ^ 36),
     "no-wrap-linear")]

/-- The rows on the conditions against wrapping, on the widths of the weights, on the base of the
rotary angles and on lists of tensors. -/
def otherRows : List (String × String × String) :=
  [("the configuration", wrap h 0 29, "passes"),
   ("kd 19", wrap h 6 19, "passes"),
   ("kd 20", wrap h 6 20, "no-wrap-U-down"),
   ("kd 24 (C++)", wrap h 6 24, "no-wrap-U-down"),
   ("kd 20 in the last layer", wrap h (13 * 7 + 6) 20, "no-wrap-U-down"),
   ("ko 19", wrap h 3 19, "passes"),
   ("ko 20", wrap h 3 20, "no-wrap-U-o"),
   ("ko 24 (C++)", wrap h 3 24, "no-wrap-U-o"),
   ("d 26214", wrap { h with d := 26214 } 0 29, "passes"),
   ("d 26215", wrap { h with d := 26215 } 0 29, "no-wrap-ledger"),
   ("d 32767 with four limbs", wrap { h with d := 32767, xl := 4 } 0 29, "passes"),
   ("d 32768 with four limbs", wrap { h with d := 32768, xl := 4 } 0 29, "no-wrap-ledger"),
   ("eps1 2^48 - 1", wrap { h with eps1 := 2 ^ 48 - 1 } 0 29, "passes"),
   ("eps1 2^48", wrap { h with eps1 := 2 ^ 48 } 0 29, "no-wrap-ledger-eps"),
   ("eps2 2^48", wrap { h with eps2 := 2 ^ 48 } 0 29, "no-wrap-ledger-eps"),
   ("epsF 2^48", wrap { h with epsF := 2 ^ 48 } 0 29, "no-wrap-ledger-eps"),
   ("eps1 2^48 with four limbs", wrap { h with eps1 := 2 ^ 48, xl := 4 } 0 29, "passes"),
   ("the widths", endOf (weightWidthsHeld h (kindList h 4 2 512 256)), "passes"),
   ("a width of 12 (C++)", endOf (weightWidthsHeld { h with wb := h.wb.set! 0 12 }
     (kindList h 4 2 512 256)), "policy-weight-kind"),
   ("a width of 14 (C++)", endOf (weightWidthsHeld { h with wb := h.wb.set! 11 14 }
     (kindList h 4 2 512 256)), "policy-weight-kind"),
   ("a width for an absent kind", endOf (weightWidthsHeld h
     (kindList { h with NE := 0 } 4 2 512 256)), "header-absent-kind"),
   ("theta0 0 (C++)", endOf (ropeOf { h with theta0 := 0 }), "shape-theta0"),
   ("two lists of tensors that agree",
     endOf (tensorsAgree [("q", ⟨0, 2, 4, 8⟩)] [("q", ⟨0, 2, 4, 8⟩)]), "passes"),
   ("another name", endOf (tensorsAgree [("q", ⟨0, 2, 4, 8⟩)] [("k", ⟨0, 2, 4, 8⟩)]),
     "plan-tensor-layout"),
   ("another place", endOf (tensorsAgree [("q", ⟨0, 2, 4, 8⟩)] [("q", ⟨8, 2, 4, 8⟩)]),
     "plan-tensor-layout"),
   ("a tensor more", endOf (tensorsAgree [("q", ⟨0, 2, 4, 8⟩)]
     [("q", ⟨0, 2, 4, 8⟩), ("k", ⟨64, 2, 4, 8⟩)]), "plan-tensor-layout"),
   ("two tensors that fill 96 features",
     endOf (tensorsFill [("q", ⟨0, 2, 4, 8⟩), ("k", ⟨64, 1, 4, 8⟩)] 96 4 "qa"), "passes"),
   ("a feature left over",
     endOf (tensorsFill [("q", ⟨0, 2, 4, 8⟩), ("k", ⟨64, 1, 4, 8⟩)] 97 4 "qa"),
     "plan-tensor-layout-fill-qa"),
   ("a gap", endOf (tensorsFill [("q", ⟨0, 2, 4, 8⟩), ("k", ⟨72, 1, 4, 8⟩)] 104 4 "qa"),
     "plan-tensor-layout-fill-qa"),
   ("an overlap", endOf (tensorsFill [("q", ⟨0, 2, 4, 8⟩), ("k", ⟨56, 1, 4, 8⟩)] 88 4 "qa"),
     "plan-tensor-layout-fill-qa"),
   ("features that are no multiple of the block", endOf (tensorsFill [("x", ⟨0, 5, 1, 6⟩)] 30 4
     "stream"), "plan-tensor-layout-fill-stream"),
   ("no feature", endOf (tensorsFill [("x", ⟨0, 5, 1, 0⟩)] 0 4 "stream"),
     "plan-tensor-layout-fill-stream")]

/-- The labels of the rows whose ending is not the expected one. -/
def failing (rows : List (String × String × String)) : List String :=
  (rows.filter fun r => r.2.1 != r.2.2).map (·.1)

#guard failing shapeRows == []
#guard failing callRows == []
#guard failing scaleRows == []
#guard failing otherRows == []
#guard failing wrapRows == []

/-- The rows on the second half of the layout and on the tables of reads. The first half is computed
once. A row changes a number in its result: a word iota as a parameter file could, the others by
hand, some of them to a state that no parameter file gives. -/
def lookRows : List (String × String × String) :=
  match layoutBase h pc with
  | .error e => [("the first half", e, "passes")]
  | .ok y =>
    let cd0 := y.calls.getD 0 default
    let c0 := y.callRecord 0 cd0
    -- The tests on one call's size, with nmin and la out of the way.
    let held (c : Call) : String :=
      endOf (Lay.callHeld { y with h := { y.h with nmin := 0, la := 0 } } cd0 c)
    let iota (q v : Nat) : String :=
      endOf (layoutLook { y with h := { y.h with iota := y.h.iota.set! q v } })
    [("the configuration", endOf (layoutLook y), "passes"),
     ("iota_0 1 (C++)", iota 0 1, "shape-call"),
     ("iota_3 0 (C++)", iota 3 0, "shape-call"),
     ("iota_3 2 (C++)", iota 3 2, "shape-call"),
     ("iota_7 1 (C++)", iota 7 1, "shape-call"),
     ("nmin 21", endOf (layoutLook { y with h := { y.h with nmin := 21 } }), "shape-call"),
     ("la 20", endOf (layoutLook { y with h := { y.h with la := 20 } }), "passes"),
     ("la 21", endOf (layoutLook { y with h := { y.h with la := 21 } }), "shape-call"),
     ("la 20, lidb 19", endOf (layoutLook { y with h := { y.h with la := 20, lidb := 19 } }),
       "forest-depth-G"),
     ("ls 13", endOf (layoutLook { y with ls := 13 }), "shape-call"),
     ("iota 2^31 - 1", held { c0 with iota := 2 ^ 31 - 1 }, "passes"),
     ("iota 2^31", held { c0 with iota := 2 ^ 31 }, "shape-call"),
     ("a call of 2^9 keys", held { c0 with n := 9 }, "shape-call"),
     ("a call of 2^10 keys", held { c0 with n := 10 }, "passes"),
     ("a call of 2^44 keys", held { c0 with n := 44 }, "passes"),
     ("a call of 2^45 keys", held { c0 with n := 45 }, "shape-call"),
     ("seven calls", endOf (layoutLook { y with calls := y.calls.pop }), "passes"),
     ("seven calls, iota_7 1", endOf (layoutLook
       { y with calls := y.calls.pop, h := { y.h with iota := y.h.iota.set! 7 1 } }),
       "header-absent-call"),
     ("reads", endOf (do readsOf (← layoutLook y)), "passes"),
     ("a product layer of 8 variables",
       endOf (readsOf { y with lPd := 0, h := { y.h with lt := 5 } }), "shape-product-layer"),
     ("a product layer of 9 variables", endOf (readsOf { y with lPd := 0 }), "passes"),
     ("the gated products' layer of 8 variables", endOf (readsOf { y with lPf := 0 }),
       "shape-product-layer"),
     ("the gated products' layer of 9 variables", endOf (readsOf { y with lPf := 1 }), "passes"),
     ("the routed experts' layer of 8 variables", endOf (readsOf { y with lfe := 1 }),
       "shape-product-layer"),
     ("the routed experts' layer of 9 variables", endOf (readsOf { y with lfe := 2 }), "passes")]

#guard failing lookRows == []

-- The names of layoutNames that no row expects.
#guard (layoutNames.filter fun n =>
    !(shapeRows ++ callRows ++ scaleRows ++ otherRows ++ wrapRows ++ lookRows).any (·.2.2 == n)) ==
  ["internal-forest-pub", "no-wrap-W-xr", "no-wrap-guard-flag-gate-clamp", "no-wrap-one-hot"]
#guard layoutNames.length == 65

end OnBytes.Model.Layer.TestLayout
