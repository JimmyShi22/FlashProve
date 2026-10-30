-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLayer.lean: tests of the layer sub-proof's public numbers.

The tests run at a small configuration, spelled out here: 64 tokens, 8 layers in two groups, routed
experts on every second layer, five limbs. No proof is read.

 1. The layout, the tests on the scales, the conditions against wrapping and the plans all pass.
 2. The numbers of the layout, of the plans, of the tables' places, of the panels and of the weight
    claims' units are those that the C++ verifier computes at this configuration. The expected
    values were printed by a copy of that program with added print lines, in a run on an honest
    proof. That copy is not in the repository. The verifier as it ships does not print them, no
    test here runs it, and the repository holds no script that repeats the comparison.

One refusal is tried here (joinEnds). Every other test on the numbers is seen to pass, none is seen
to fail. OnBytes/Model/TestLayerLayout.lean sees 61 of the 65 names under which
OnBytes/Model/LayerLayout.lean refuses; its head lists the others. Of the check in
OnBytes/Model/Layer.lean only joinStart is run: in a dry run, for the second group, on made-up heard
values (zeros, no second token sumcheck). The form that it returns is not looked at.

This file is not part of the compiled program.
-/
import OnBytes.Model.Layer

namespace OnBytes.Model.Layer.Test

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

/-- All public numbers of the configuration. -/
def pub : Except String Pub := do
  let y ← layout h pc
  let sc ← scalesOf h KL
  scalesHeld h sc
  noWrap h sc y.dq
  weightWidthsHeld h y.kinds
  let wsLay ← wsLayOf
    { D := h.D, L := h.L, d := h.d, dh := h.dh, dkv := y.dkv, dq := y.dq, f := h.f, fe := h.fe,
      NE := h.NE, V := 512 } h.p3 11
  let rope ← ropeOf h
  Pub.of y sc rope wsLay 512 (Array.replicate 64 0) { lidb := 24, tau := 128, hb := 128 }

/-- The plans of the configuration's two groups. -/
def plans : Except String (Pub × Array HPlan2) := do
  let P ← pub
  pure (P, ← plansG P)

/-! ## The numbers that the C++ verifier computes at this configuration -/

/-- How many members of a equal v. -/
def countOf (a : Array Nat) (v : Nat) : Nat := (a.filter (· == v)).size

/-- The sum of all rows of a table, modulo 2^64. -/
def sumOf (a : Array F) : F := a.foldl (· + ·) 0

/-- The matrices of group g. -/
def matsOf (P : Pub) (g : Nat) : List (String × Nat × Nat × Nat × Option Nat × Nat) :=
  (P.tails.getD g {}).mats.toList.map fun M => (M.name, M.m, M.k, M.kind, M.foreign, M.aId)

/-- The counts of the plan of group g: the pairs of a table and a block of rows, the sub-proof's own
claims, then ns, used, NCL, nLin, nBatched, lamS and the length of the reads. -/
def planNumbers (P : Pub) (hps : Array HPlan2) (g : Nat) : Option (List Nat) :=
  hps[g]?.map fun hp =>
    [readsCount P.y P.rd g, claimsOf P.y P.rd g, hp.ns, hp.used, hp.NCL, hp.nLin, hp.nBatched,
     hp.lamS, hp.nU.getD 2 0]

/-- The comparisons on the layout, each with a name. -/
def layoutChecks (y : Lay) : List (String × Bool) :=
  [("sizes", [y.T, y.Lam, y.NGr, y.Pd, y.Pf, y.S2, y.NW, y.NN, y.NI, y.dq, y.dkv, y.nqk, y.lPf,
      y.lfe, y.lPd, y.ls, y.ldh, y.LamM, y.kbm, y.xbFilled, y.kxb, y.mxb] ==
      [64, 4, 2, 512, 1024, 4, 2, 2, 8, 512, 256, 768, 10, 9, 9, 2, 7, 2, 2048, 2560, 20, 8192]),
   ("matrices", (y.feat, y.filled, y.kcol, y.mrow, y.parts) ==
      (#[94720, 10240, 854, 12288], #[94848, 10240, 896, 12288], #[247, 160, 14, 96],
        #[8192, 4096, 4096, 8192], #[3, 1, 1, 1])),
   ("tensors", (y.ten.map fun t => (t.name, t.mat, t.nl, t.cnt, t.J, t.OFF)) ==
      [("g0", 0, 1, 4, 1024, 0), ("gc", 0, 1, 4, 1024, 4096), ("s", 0, 2, 4, 1024, 8192),
       ("u", 0, 2, 4, 1024, 16384), ("rg", 0, 1, 4, 1024, 24576), ("ru", 0, 1, 4, 1024, 28672),
       ("xs", 0, 5, 7, 512, 32768), ("ro", 0, 1, 4, 512, 50688), ("rd", 0, 1, 4, 512, 52736),
       ("aw", 0, 2, 4, 512, 54784), ("ra", 0, 2, 4, 512, 58880), ("mw", 0, 2, 4, 512, 62976),
       ("rm", 0, 2, 4, 512, 67072), ("qkw", 0, 2, 4, 768, 71168), ("rqk", 0, 2, 4, 768, 77312),
       ("vw", 0, 2, 4, 256, 83456), ("rv", 0, 1, 4, 256, 85504), ("gh", 0, 2, 4, 1024, 86528),
       ("a", 1, 2, 4, 512, 0), ("m", 1, 2, 4, 512, 4096), ("xr", 1, 2, 2, 512, 8192),
       ("lr", 2, 2, 2, 4, 0), ("rl", 2, 1, 2, 4, 16), ("sel", 2, 1, 2, 4, 24),
       ("sc", 2, 3, 2, 1, 32),
       ("row", 2, 1, 8, 99, 38), ("ly", 2, 2, 2, 4, 830), ("l3", 2, 1, 2, 4, 846),
       ("q", 3, 2, 4, 512, 0), ("kx", 3, 2, 4, 256, 4096), ("v", 3, 2, 4, 256, 6144),
       ("o", 3, 2, 4, 512, 8192)]),
   ("kinds", (y.kinds.map fun k => (k.idx, k.name, k.L, k.segs)) ==
      [(0, "qk", 64, 524288), (1, "v", 256, 4096), (2, "o", 512, 4096), (3, "g", 1024, 2048),
       (4, "u", 1024, 2048), (5, "gs", 512, 2048), (6, "us", 512, 2048), (7, "gr", 512, 8192),
       (8, "ur", 512, 8192), (9, "dn", 512, 6144), (10, "dnr", 512, 8192), (11, "r", 4, 2048)]),
   ("calls", ((y.calls.zip y.cl).toList.map fun x =>
      (x.1.name, x.1.kind, x.1.J, x.1.lJ, x.2.n, x.2.iota, x.2.k, x.2.fn, x.2.t0)) ==
      [("R16a", "R16", 4096, 12, 20, 0, 16, 0, 0), ("R16b", "R16", 4096, 12, 20, 0, 16, 0, 0),
       ("R16c", "R16", 4096, 12, 20, 0, 16, 0, 0), ("R8", "R8", 8192, 13, 21, 1, 8, 0, 0),
       ("FC", "FC", 4096, 12, 20, 0, 16, 1, 32768), ("FS", "FS", 4096, 12, 20, 0, 16, 1, 32768),
       ("FL", "FL", 4096, 12, 20, 0, 16, 1, 32768), ("R16d", "R16", 4096, 12, 20, 0, 16, 0, 0)]),
   ("columns", (y.calls.toList.map fun c =>
      (countOf c.used 0, countOf c.used 1, countOf c.used 2)) ==
      [(2048, 2048, 0), (768, 3328, 0), (2036, 1536, 524), (3630, 4550, 12), (2044, 2048, 4),
       (3071, 1024, 1), (3072, 1024, 0), (3072, 1024, 0)]),
   ("segments", (y.calls.toList.flatMap fun c => c.segs.map fun s =>
      (s.name, s.n, s.moe, s.pos.getD 0 0, s.pos.getD (s.n - 1) 0, s.pos.foldl (· + ·) 0)) ==
      [("G", 1024, false, 0, 1023, 523776), ("U", 1024, false, 1024, 2047, 1572352),
       ("N1", 512, false, 0, 511, 130816), ("N1H", 512, false, 512, 1023, 392960),
       ("N2", 512, false, 1024, 1535, 655104), ("N2H", 512, false, 1536, 2047, 917248),
       ("O", 512, false, 2048, 2559, 1179392), ("D", 512, false, 2560, 3071, 1441536),
       ("V", 256, false, 3072, 3327, 819072), ("QK", 768, false, 0, 1791, 556672),
       ("QKH", 768, false, 512, 2047, 884352), ("XR", 512, true, 1024, 1535, 655104),
       ("LR", 4, true, 2048, 2051, 8198), ("LT", 4, true, 2052, 2055, 8214),
       ("DD", 4, true, 2056, 2059, 8230), ("GH", 1024, false, 0, 1023, 523776),
       ("UH", 1024, false, 1024, 2047, 1572352), ("OH", 512, false, 3072, 3583, 1703680),
       ("DH", 512, false, 3584, 4095, 1965824), ("VH", 256, false, 4096, 4351, 1081216),
       ("ROW", 198, false, 4352, 4561, 881223), ("LH", 4, true, 4548, 4551, 18198),
       ("SEL", 4, true, 4552, 4555, 18214), ("L3", 4, true, 4556, 4559, 18230),
       ("G0", 1024, false, 2048, 3071, 2620928), ("CN1", 512, false, 0, 511, 130816),
       ("CN2", 512, false, 512, 1023, 392960), ("CQK", 768, false, 1024, 1791, 1080960),
       ("CV", 256, false, 1792, 2047, 491392), ("CLR", 4, true, 2048, 2051, 8198),
       ("MR", 1, true, 1024, 1024, 1024), ("CG", 1024, false, 0, 1023, 523776),
       ("F", 1024, false, 0, 1023, 523776), ("UT", 1024, false, 0, 1023, 523776)]),
   ("look-up", [y.fo.dT, y.fo.kT, y.fo.NT, y.fo.rK, y.fo.NC, y.fo.cK] == [20, 16, 9, 4, 8, 3]),
   ("trees", (y.fo.iota, y.fo.first, y.fo.callOf, y.fo.pub) ==
      (#[0, 0, 0, 1, 0, 0, 0, 0], #[2, 3, 4, 0, 5, 6, 7, 8],
        #[3, 3, 0, 1, 2, 4, 5, 6, 7],
        #[465408, 465408, 524288, 196608, 588288, 523776, 786304, 786432, 786432])),
   ("tables", (sumOf y.tauFC, sumOf y.tauFL, sumOf y.tauFS) ==
      (36028249679036416, 99067033823444992, 37295398175342592))]

/-- The comparisons on the tables of reads, the lists of matrices and the plans. -/
def planChecks (P : Pub) (hps : Array HPlan2) : List (String × Bool) :=
  [("long reads", (P.rd.tscCalls, P.rd.rdAF, P.rd.rdQA, P.rd.rdXI, P.rd.rdXO) ==
      (["R16a", "R16b", "R16c", "FS"], ["Z", "Z_V", "Y", "Z_a", "Z_b"], ["Z"],
        ["Z", "Z_V", "Y"], ["Z"])),
   ("short reads", (P.rd.rdAD, P.rd.rdAR, P.rd.rdQS) ==
      (["zt", "rt"], ["zt", "P_V", "r_tV", "rt"], ["zt"])),
   ("layers", [P.rd.lNI, P.rd.muV, P.rd.muH, P.rd.muH2, P.rd.nW] == [3, 18, 18, 16, 166688]),
   ("matrices of group 0", matsOf P 0 ==
      [("af0", 8192, 247, 0, none, 256), ("af1", 8192, 247, 0, none, 257),
       ("af2", 8192, 247, 0, none, 258), ("ad0", 4096, 160, 0, none, 259),
       ("ar", 4096, 14, 0, none, 260), ("b", 8192, 2048, 0, none, 261),
       ("qa", 8192, 96, 0, none, 262), ("xbO", 8192, 20, 0, none, 263),
       ("xbI", 8192, 20, 0, none, 264)]),
   ("matrices of group 1", matsOf P 1 ==
      [("af0", 8192, 247, 0, none, 512), ("af1", 8192, 247, 0, none, 513),
       ("af2", 8192, 247, 0, none, 514), ("ad0", 4096, 160, 0, none, 515),
       ("ar", 4096, 14, 0, none, 516), ("b", 8192, 2048, 0, none, 517),
       ("qa", 8192, 96, 0, none, 518), ("xbO", 8192, 20, 0, none, 519),
       ("xbI", 8192, 20, 1, some 0, 263)]),
   ("plan of group 0", planNumbers P hps 0 ==
      some [1187, 282, 3204, 3204, 33, 1549, 4347789, 15, 167328]),
   ("plan of group 1", planNumbers P hps 1 ==
      some [1155, 281, 3203, 3203, 32, 1516, 4343660, 15, 166688])]

/-- What the forms of group g read in a dry run: the tables' places, and zeros as the calls' points.
Returns none if the tables cannot be placed. -/
def dryEnv (P : Pub) (g : Nat) : Option Env :=
  (layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0).map
    fun x =>
      { y := P.y, sc := P.sc, g := g, iU3 := 0, K3 := x.2.2, tab := x.1,
        zk := P.y.cl.map fun c => Array.replicate c.n zeroE }

/-- The places of the families of tables of group g: name, first entry, number of entries. -/
def tablePlaces (P : Pub) (g : Nat) : Option (List (String × Nat × Nat)) :=
  (dryEnv P g).map fun v => v.tab.map fun t => (t.name, t.first, t.len)

/-- The public numbers of the panels of group g, in the list's order. -/
def panelNumbers (P : Pub) (g : Nat) :
    Option (List (Bool × Option Nat × Nat × Nat × Nat × Nat × Nat × Nat × Option Nat)) := do
  let v ← dryEnv P g
  let pe : PanelEnv :=
    { v, e := Array.replicate 8 zeroE, shownT := #[], zt := Array.replicate 6 zeroE,
      stubO := fun _ _ _ => 0 }
  let pans ← panelsT pe (← callsTS P) (panelsA pe {})
  pure ((placePanels pans.bl).1.toList.map fun b =>
    (b.tri, b.v0, b.claim, b.ni, b.ny, b.wy, b.w, b.off, b.virt))

/-- The units of the weight claims of group g, in the claims' order. -/
def claimUnits (P : Pub) (g : Nat) : Option (List Nat) := do
  let v ← dryEnv P g
  let ce : ClaimEnv :=
    { v, wsLay := P.wsLay, rope := P.rope, rs := Array.replicate 15 zeroE,
      rt := Array.replicate 6 zeroE }
  let own ← ce.weightClaims (← callsTS P)
  let emb ← if g == 0 then
      (ce.claimE (Array.replicate 8 zeroE) (Array.replicate 7 zeroE) P.V P.tokv).map ([·])
    else some []
  pure ((own ++ emb).map (·.ui))

/-- The comparisons on the tables' places, the panels and the weight claims' units. -/
def ownChecks (P : Pub) : List (String × Bool) :=
  [("tables of group 0", tablePlaces P 0 == some
      [("af@Z", 0, 23712), ("af@Z_V", 23712, 23712), ("af@Y", 47424, 23712),
       ("af@Z_a", 71136, 23712), ("af@Z_b", 94848, 23712), ("qa@Z", 118560, 3072),
       ("xbI@Z", 121632, 640), ("xbI@Z_V", 122272, 640), ("xbI@Y", 122912, 640),
       ("xbI@Z_E", 123552, 640), ("xbO@Z", 124192, 640), ("ad@zt", 124832, 10240),
       ("ad@rt", 135072, 10240), ("ar@zt", 145312, 896), ("ar@P_V", 146208, 896),
       ("ar@r_tV", 147104, 896), ("ar@rt", 148000, 896), ("qa@zt", 148896, 12288),
       ("b-bits-0", 161184, 2048), ("b-bits-1", 163232, 2048), ("b-pin", 165280, 2048)]),
   ("tables of group 1", tablePlaces P 1 == some
      [("af@Z", 0, 23712), ("af@Z_V", 23712, 23712), ("af@Y", 47424, 23712),
       ("af@Z_a", 71136, 23712), ("af@Z_b", 94848, 23712), ("qa@Z", 118560, 3072),
       ("xbI@Z", 121632, 640), ("xbI@Z_V", 122272, 640), ("xbI@Y", 122912, 640),
       ("xbO@Z", 123552, 640), ("ad@zt", 124192, 10240), ("ad@rt", 134432, 10240),
       ("ar@zt", 144672, 896), ("ar@P_V", 145568, 896), ("ar@r_tV", 146464, 896),
       ("ar@rt", 147360, 896), ("qa@zt", 148256, 12288), ("b-bits-0", 160544, 2048),
       ("b-bits-1", 162592, 2048), ("b-pin", 164640, 2048)]),
   ("panels", [panelNumbers P 0, panelNumbers P 1].all (· == some
      [(false, some 0, 0, 4, 512, 9, 11, 4096, none),
       (false, some 4, 0, 4, 512, 9, 11, 6144, none),
       (false, some 8, 0, 4, 512, 9, 11, 8192, none),
       (false, some 12, 0, 4, 1024, 10, 12, 0, some 0),
       (false, some 16, 0, 4, 512, 9, 11, 10240, none),
       (false, some 20, 0, 2, 512, 9, 10, 26624, none),
       (true, some 22, 1, 4, 512, 9, 11, 12288, none),
       (true, some 23, 1, 4, 512, 9, 11, 14336, none),
       (true, some 24, 1, 4, 512, 9, 11, 16384, none),
       (true, some 25, 1, 4, 512, 9, 11, 18432, none), (false, none, 1, 4, 1, 0, 2, 27664, none),
       (false, none, 1, 4, 1, 0, 2, 27668, none),
       (true, some 26, 1, 4, 512, 9, 11, 20480, some 1),
       (true, some 27, 1, 4, 512, 9, 11, 22528, some 2),
       (false, some 28, 1, 4, 512, 9, 11, 24576, none), (false, none, 1, 2, 1, 0, 1, 27672, none),
       (false, none, 1, 2, 4, 2, 3, 27648, none), (false, none, 1, 2, 4, 2, 3, 27656, none)])),
   ("units of group 0", claimUnits P 0 == some
      [3, 9, 19, 25, 4, 10, 20, 26, 2, 8, 18, 24, 5, 13, 21, 29, 1, 7, 17, 23, 15, 31, 11, 27, 12,
       28, 14, 30, 0, 6, 16, 22, 64]),
   ("units of group 1", claimUnits P 1 == some
      [35, 41, 51, 57, 36, 42, 52, 58, 34, 40, 50, 56, 37, 45, 53, 61, 33, 39, 49, 55, 47, 63, 43,
       59, 44, 60, 46, 62, 32, 38, 48, 54])]

/-- The names of the comparisons that fail, or the refusal's name if the public numbers or the plans
are refused. Everything is computed once. -/
def failing : List String :=
  match plans with
  | .error e => [e]
  | .ok (P, hps) =>
    ((layoutChecks P.y ++ planChecks P hps ++ ownChecks P).filter fun c => !c.2).map (·.1)

#guard failing == []

/-- How joinStart of the second group ends in a dry run in which the lookup holds n weights of calls
and the first c of the layout's eight calls: the name under which it fails, or none if it goes
through. If the tables cannot be placed, so that there is no run: "no tables". -/
def joinEnds (P : Pub) (n : Nat) (c : Nat := 8) : Option String :=
  match dryEnv P 1 with
  | none => some "no tables"
  | some v =>
    let fo : Forest.Heard :=
      { shape := { P.y.fo with calls := P.y.fo.calls.extract 0 c }, leaves := {},
        e := Array.replicate n zeroE,
        zy := Array.replicate P.y.fo.rK zeroE }
    let H : Heard :=
      { fo, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[], tV := {} }
    match Blk.dryRunNamed ((joinStart v H #[oneE]).run' default) { entries := [], st := {} } with
    | .error e => some e.name
    | .ok _ => none

-- The layout has eight calls. Eight weights go through. Seven or nine weights fail. Seven weights
-- and a lookup of seven calls fail too: the layout still gives eight parts.
#guard (plans.toOption.map fun x =>
    (joinEnds x.1 8, joinEnds x.1 7, joinEnds x.1 9, joinEnds x.1 7 7)) ==
  some (none, some "internal-forest-join", some "internal-forest-join",
    some "internal-forest-join")

#guard names.contains "internal-forest-join"

end OnBytes.Model.Layer.Test
