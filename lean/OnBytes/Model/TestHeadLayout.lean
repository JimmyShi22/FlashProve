-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHeadLayout.lean: tests of the layout of the output head's sub-proof.

The numbers are those of a small configuration, spelled out here (`smallShape`): 64 positions, width
512, a vocabulary of 512 entries, five limbs. The expected values of the layout are what the C++
verifier computes for that configuration in a planning call. No test here runs that verifier. The
expected names of refusals, and the expected values for the made-up requests, were worked out from
the C++ source: no such call was run. The guards on `Covered.sized` are this library's own. The
table of the clamp is made up, so nothing about that table is tested. Of the 29 names in
`Layout.names` the guards expect 12; none of the no-overflow conditions (`h9`) is seen to fail.
OnBytes/Model/TestHeadLayoutMore.lean has further refusals, ten of the eleven names of `h9` among
them. The program does not import this file.
-/
import OnBytes.Model.HeadLayout

namespace OnBytes.Model.Head

/-- The head's public numbers at the small example configuration. -/
def smallShape : Shape where
  lt := 6
  la := 8
  d := 512
  lPd := 9
  V := 512
  MF := 44
  KF := 30
  epsF := 1
  toksrc := 1
  wbEmb := 21
  wbHead := 13
  clipC := 256
  theta := 256
  cap := 0
  logS := 15
  digSh := 8
  tabS := 4
  famF := 24
  lmhf := 14
  NHf := 1
  lmhd := 12
  lmhr := 12
  lmbH := 13
  iotaH := [0, 0, 0, 0, 0, 0]
  nmin := 20
  NMINH := 0
  LIDB := 24
  XL := 5
  polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"], ["R16b", "R16", "HD1"],
    ["R8", "R8", "ROW", "HD2"], ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]]

/-- A made-up table of 65536 rows in place of the layers' table of the clamp. -/
def someTable : Array F := (Array.range 65536).map (·.toUInt64)

/-- The layout at the small example configuration. -/
def smallLayout : Except String HL := layout smallShape someTable

#guard smallLayout.isOk
#guard (smallLayout.toOption.map fun L => [L.JV, L.JVa, L.oAw, L.oRa, L.oD1, L.oD2, L.oE]) ==
  some [512, 256, 0, 1024, 2048, 3072, 3584]
#guard (smallLayout.toOption.map fun L => [L.feat, L.filled, L.k, L.m]) ==
  some [5120, 5120, 20, 16384]
#guard (smallLayout.toOption.map fun L => [L.fillD, L.kD, L.mD, L.fillR, L.kR, L.mR, L.kb]) ==
  some [1024, 16, 4096, 128, 2, 4096, 1536]
#guard (smallLayout.toOption.map fun L => L.calls.toList.map fun c => (c.name, c.lJ, c.J)) ==
  some [("R16a", 14, 16384), ("R16b", 14, 16384), ("R8", 14, 16384), ("FEa", 14, 16384),
    ("FEb", 14, 16384), ("FC", 14, 16384)]
#guard (smallLayout.toOption.map fun L =>
    L.cl.toList.map fun c => (c.n, c.iota, c.k, c.fn, c.t0)) ==
  some [(20, 0, 16, 0, 0), (20, 0, 16, 0, 0), (20, 0, 8, 0, 0), (20, 0, 16, 1, 0),
    (20, 0, 16, 1, 0), (20, 0, 16, 1, 32768)]
#guard (smallLayout.toOption.map fun L =>
    [L.fs.dT, L.fs.kT, L.fs.NT, L.fs.rK, L.fs.NC, L.fs.cK]) == some [20, 16, 6, 3, 6, 3]
#guard (smallLayout.toOption.map fun L => L.fs.first) == some #[0, 1, 2, 3, 4, 5]
#guard (smallLayout.toOption.map fun L => L.fs.pub) ==
  some #[950272, 1015808, 1008128, 1032192, 1032192, 1015808]

#guard (smallLayout.toOption.map fun L => L.calls.toList.map fun c =>
    c.segs.map fun g => (g.name, g.pos.foldl (· + ·) 0)) ==
  some [[("NF", 130816), ("NFH", 392960), ("HD0", 655104)], [("HD1", 130816)],
    [("ROW", 68580), ("HD2", 130816)], [("HE0", 32640)], [("HE1", 32640)], [("CNF", 130816)]]
#guard (smallLayout.toOption.map fun L => [L.fs.v, L.fs.d, L.fs.emptyKeys, L.fs.padding]) ==
  some [23, 19, 2097152, 8151552]

-- sT - sh = -4, the step table: EX is 2^F, 2, 1, 1 and so on, and row u is u + 2^16 EX[u].
#guard ((tauFEOf 24 8 4).extract 0 4) == #[1099511627776, 131073, 65538, 65539]
#guard (tauFEOf 24 8 4).size == 65536
#guard (tauFEOf 24 8 4).getD 65535 0 == 131071
#guard (tauFEOf 24 8 4).foldl (fun s x => s + x.toNat) 0 == 1105954045952

-- The segments of the call R8: the larger piece comes first.
#guard (smallLayout.toOption.map fun L =>
    (L.calls.getD 2 default).segs.map fun g =>
      (g.name, g.n, g.pos.getD 0 0, g.pos.getD (g.n - 1) 0)) ==
  some [("ROW", 120, 512, 631), ("HD2", 512, 0, 511)]

/-! ## Other settings

The expected values are what the C++ verifier computes in planning calls on that configuration's
parameter file with the named lines changed. -/

/-- Nine rows of a table, and the sum of all its rows. -/
def tableSample (t : Array F) : List Nat × Nat :=
  ([0, 1, 2, 3, 100, 1000, 32767, 32768, 65535].map fun u => (t.getD u 0).toNat,
   t.foldl (fun s x => s + x.toNat) 0)

-- The table of exponentials at sT - sh = 4 to 10.
#guard tableSample (tauFEOf 24 8 12) ==
  ([1099511627776, 1032895594497, 970315661314, 911527182339, 2122580068, 66536, 98303, 98304,
    131071], 18154100326400)
#guard tableSample (tauFEOf 24 8 13) ==
  ([1099511627776, 1065683255297, 1032895594498, 1001116794883, 48309207140, 66536, 98303, 98304,
    131071], 35743413993472)
#guard tableSample (tauFEOf 24 8 14) ==
  ([1099511627776, 1082465320961, 1065683255298, 1049161367555, 230470189156, 197608, 98303, 98304,
    131071], 70926335115264)
#guard tableSample (tauFEOf 24 8 15) ==
  ([1099511627776, 1090955182081, 1082465320962, 1074041520131, 503393157220, 444924904, 98303,
    98304, 131071], 141294328381440)
#guard tableSample (tauFEOf 24 8 16) ==
  ([1099511627776, 1095225049089, 1090955182082, 1086701961219, 743966834788, 22117614568, 98303,
    98304, 131071], 282031388131328)
#guard tableSample (tauFEOf 24 8 17) ==
  ([1099511627776, 1097366241281, 1095225049090, 1093088051203, 904433631332, 155943961576, 98303,
    98304, 131071], 563506043912192)
#guard tableSample (tauFEOf 24 8 18) ==
  ([1099511627776, 1098438410241, 1097366241282, 1096295120899, 997213798500, 414079976424, 98303,
    98304, 131071], 1126455757340672)
-- The table depends on sT - sh alone.
#guard tableSample (tauFEOf 24 7 11) == tableSample (tauFEOf 24 8 12)
#guard tableSample (tauFEOf 24 7 3) == tableSample (tauFEOf 24 8 4)

-- A vocabulary that is not a multiple of S2: the entries from V on are padding.
#guard ((layout { smallShape with V := 510 } someTable).toOption.map fun L =>
    (L.JV, L.JVa, L.fs.pub, L.fs.padding)) ==
  some (512, 256, #[950400, 1015936, 1008256, 1032192, 1032320, 1015808], 8152064)
-- Four limbs: the row ledger is shorter.
#guard ((layout { smallShape with XL := 4 } someTable).toOption.map fun L =>
    ((L.calls.getD 2 default).segs.head?.map fun g =>
      (g.name, g.n, g.pos.getD 0 0, g.pos.getD (g.n - 1) 0, g.pos.foldl (· + ·) 0),
     L.fs.pub, L.fs.padding)) ==
  some (some ("ROW", 95, 512, 606, 53105),
    #[950272, 1015808, 1009728, 1032192, 1032192, 1015808], 8153152)
-- The matrix hf in two parts.
#guard ((layout { smallShape with NHf := 2, lmhf := 13 } someTable).toOption.map fun L =>
    [L.JV, L.JVa, L.oE, L.feat, L.filled, L.k, L.m]) == some [512, 256, 3584, 5120, 5120, 20, 8192]
-- Five calls: all four segments of the kind R16 in one.
#guard ((layout { smallShape with polCallsH := [["R16", "R16", "NF", "NFH", "HD0", "HD1"],
      ["R8", "R8", "ROW", "HD2"], ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]] }
    someTable).toOption.map fun L =>
    (L.kb, [L.fs.dT, L.fs.kT, L.fs.NT, L.fs.rK, L.fs.NC, L.fs.cK], L.fs.pub, L.fs.emptyKeys,
     (L.calls.getD 0 default).segs.map fun g => (g.name, g.pos.getD 0 0, g.pos.foldl (· + ·) 0))) ==
  some (1280, [20, 16, 5, 3, 5, 3], #[917504, 1008128, 1032192, 1032192, 1015808], 3145728,
    [("NF", 0, 130816), ("NFH", 512, 392960), ("HD0", 1024, 655104), ("HD1", 1536, 917248)])
-- A lower floor on a call's keys (the line nmin; in that planning call the lines iota of the layers
-- and of attention were changed with it): the first call of the lookup then takes two trees.
#guard ((layout { smallShape with nmin := 16, iotaH := [1, 0, 0, 0, 0, 0] } someTable).toOption.map
    fun L => (L.calls.toList.map fun c => (c.lJ, c.J), L.cl.toList.map fun c => (c.n, c.iota),
      [L.fs.dT, L.fs.kT, L.fs.NT, L.fs.rK, L.fs.NC, L.fs.cK], L.fs.first, L.fs.callOf, L.fs.pub,
      L.fs.padding)) ==
  some ([(11, 2048), (10, 1024), (10, 1024), (10, 1024), (10, 1024), (10, 1024)],
    [(17, 1), (16, 0), (16, 0), (16, 0), (16, 0), (16, 0)], [16, 16, 7, 3, 6, 3],
    #[0, 2, 3, 4, 5, 6], #[0, 0, 1, 2, 3, 4, 5], #[0, 32768, 32768, 25088, 49152, 49152, 32768],
    287232)

-- Refusals, each with the name of the first test that fails.
#guard (layout { smallShape with MF := 48 } someTable).toOption.isNone
#guard (match layout { smallShape with MF := 48 } someTable with
  | .error e => e == "policy-norm-F" | .ok _ => false)
#guard (match layout { smallShape with theta := 257 } someTable with
  | .error e => e == "policy-gap-words" | .ok _ => false)
#guard (match layout { smallShape with tabS := 5 } someTable with
  | .error e => e == "policy-gap-words" | .ok _ => false)
#guard (match layout { smallShape with lmhf := 7 } someTable with
  | .error e => e == "shape-request-matrix-H" | .ok _ => false)
#guard (match layout { smallShape with polCallsH := [["R16a", "R16", "NF"]] } someTable with
  | .error e => e == "policy-call-list-H" | .ok _ => false)
#guard (match layout { smallShape with iotaH := [1, 0, 0, 0, 0, 0] } someTable with
  | .error e => e == "shape-call-H" | .ok _ => false)

#guard (match layout { smallShape with la := 6 } someTable with
  | .error e => e == "internal-head-shape" | .ok _ => false)
#guard (vocabulary smallShape).isOk
#guard (match vocabulary { smallShape with V := 1 } with
  | .error e => e == "shape-V" | .ok _ => false)
#guard (match vocabulary { smallShape with wbHead := 12 } with
  | .error e => e == "policy-weight-kind" | .ok _ => false)
#guard (match vocabulary { smallShape with wbEmb := 20 } with
  | .error e => e == "policy-weight-width-emb" | .ok _ => false)

/-- A request of 64 tokens 0, 1, 2 and so on, with the given r and e. -/
def someRequest (r e : Nat) : Array UInt32 :=
  ((Array.range 64).map (·.toUInt32)).push r.toUInt32 |>.push e.toUInt32

#guard (stFromCall (someRequest 63 64) #[342] 64).isOk
#guard (match stFromCall (someRequest 62 63) #[342] 64 with
  | .error e => e == "statement-range" | .ok _ => false)
#guard (match stFromCall (someRequest 63 63) #[0] 64 with
  | .error e => e == "statement-range" | .ok _ => false)
#guard (match stFromCall (someRequest 63 65) #[0] 64 with
  | .error e => e == "statement-range" | .ok _ => false)
#guard (match stFromCall #[] #[0] 64 with
  | .error e => e == "statement-required" | .ok _ => false)
#guard (((stFromCall (someRequest 61 64) #[342] 64).bind fun so => coveredOf so 64 512).toOption.map
    fun c => (c.hRC, c.hWin.extract 60 64, c.hOn.extract 60 64, c.hOnC.extract 60 64)) ==
  some (2, #[0, 62, 63, 342], #[false, true, true, true], #[false, true, true, false])
#guard (match (stFromCall (someRequest 63 64) #[512] 64).bind fun so => coveredOf so 64 512 with
  | .error e => e == "token-range" | .ok _ => false)
-- Covered.sized, on one request of 64 positions: true at 64, false at 63, false if any one of the
-- four arrays is one entry short. The default is not sized for 64. The test that uses it
-- (internal-h-covered, OnBytes/Model/Head.lean) is run in OnBytes/Model/TestHeadCovered.lean [not in this library; so here read: not tested in this library].
#guard (((stFromCall (someRequest 61 64) #[342] 64).bind fun so => coveredOf so 64 512).toOption.map
    fun c => (c.sized 64, c.sized 63, { c with hOn := c.hOn.pop }.sized 64,
      { c with hWin := c.hWin.pop }.sized 64, { c with hOnC := c.hOnC.pop }.sized 64,
      { c with tokv := c.tokv.pop }.sized 64)) == some (true, false, false, false, false, false)
#guard !(default : Covered).sized 64

end OnBytes.Model.Head
