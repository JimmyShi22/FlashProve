-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/Names.lean: the four lists of names of the item "request"
(OnBytes/Proof/RequestItem.lean), spelled as lists.

Why. `Proof.names2` and its fellows are strings in which single blanks separate the names, cut by
`String.splitOn`. Here the simplifier walks it once, as in `OnBytes.K.namesFit`
(OnBytes/K/ServedFreeItem.lean), so that a test can be stated over the lists.

Main names. `names2_list`, `names37_list`, `names103_list`, `names130_list`: what `splitOn` gives.

Limits. Four closed facts on strings of names. Nothing on any file. No soundness is claimed.
-/
import OnBytes.K.ServedFreeItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof

/-- The names of `names2`, as a list. -/
def names2L : List String :=
  ["prof", "lt", "L", "ll", "d", "H", "G", "dh", "f", "fe", "NE", "V", "eps1_lo", "eps1_hi",
   "eps2_lo", "eps2_hi", "cs", "theta0_lo", "theta0_hi", "hq", "hv", "ho", "hgD", "huD", "hdD",
   "hr", "ut"]

/-- The names of `names37`, as a list. -/
def names37L : List String :=
  ["la", "nmin", "D", "tau", "lmaf", "NAf", "lmad", "NAd", "lmar", "lmb", "lmq", "lmx", "wb_qk",
   "wb_v", "wb_o", "wb_g", "wb_u", "wb_gs", "wb_us", "wb_gr", "wb_ur", "wb_dn", "wb_dnr", "wb_r",
   "iota_0", "iota_1", "iota_2", "iota_3", "iota_4", "iota_5", "iota_6", "iota_7", "seed_lo",
   "seed_hi"]

/-- The names of `names103`, as a list. -/
def names103L : List String :=
  ["lB", "S", "rx", "kFM", "kFD", "lmS", "NAs", "lmh", "lmo", "lmbA", "iotaA_0"]

/-- The names of `names130`, as a list. -/
def names130L : List String :=
  ["MF", "KF", "epsF_lo", "epsF_hi", "toksrc", "lmhf", "NHf", "lmhd", "lmhr", "lmbH", "wb_emb",
   "wb_head", "iotaH_0", "iotaH_1", "iotaH_2", "iotaH_3", "iotaH_4", "iotaH_5", "C", "theta",
   "cap", "s", "sh", "sT", "F"]

section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- What `splitOn` gives on `names2`. -/
theorem names2_list : names2.splitOn " " = names2L := by
  simp (decide := true) (maxSteps := 10000000)
    [names2, names2L, String.splitOn, String.splitOnAux.eq_def]

/-- What `splitOn` gives on `names37`. -/
theorem names37_list : names37.splitOn " " = names37L := by
  simp (decide := true) (maxSteps := 10000000)
    [names37, names37L, String.splitOn, String.splitOnAux.eq_def]

/-- What `splitOn` gives on `names103`. -/
theorem names103_list : names103.splitOn " " = names103L := by
  simp (decide := true) (maxSteps := 10000000)
    [names103, names103L, String.splitOn, String.splitOnAux.eq_def]

/-- What `splitOn` gives on `names130`. -/
theorem names130_list : names130.splitOn " " = names130L := by
  simp (decide := true) (maxSteps := 10000000)
    [names130, names130L, String.splitOn, String.splitOnAux.eq_def]

end

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.names2_list
#print axioms Johnson.AtFull.Item.names37_list
#print axioms Johnson.AtFull.Item.names103_list
#print axioms Johnson.AtFull.Item.names130_list
#print axioms Johnson.AtFull.Item.names2L
#print axioms Johnson.AtFull.Item.names37L
#print axioms Johnson.AtFull.Item.names103L
#print axioms Johnson.AtFull.Item.names130L
