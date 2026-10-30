-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/TabLit.lean: THE THREE CHAINS' TABLES (`P2Law.OneWalk.Tab`,
Johnson/AtFull/ProofPlan/OneWalk.lean) OF THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean), WRITTEN OUT. Data alone.

A table: for each tree that the chain sends the number of its sending round · the numbers of the
rounds with answers · for each tree whether a tenant is sampled · how many rounds.

Whence. A program made them off the texts of Johnson/Unfolds/DeclRecsLit.lean,
Johnson/G/DryProofLit.lean (the runs) and Johnson/Desc/Ok/PlanWritten/CutLit.lean (the tenants).
NOTHING HERE SAYS THAT THEY ARE `WP`'s: that is asked of Lean's kernel in
Johnson/AtFull/ProofPlan/At/Tab1.lean, Tab2.lean and Tab3.lean.

  `wpTab₁`, `wpTab₂`, `wpTab₃`: the first, the shared, the second chain's.

-/
import Johnson.AtFull.ProofPlan.OneWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open P2Law.OneWalk (Tab)

def wpTab₁ : Tab :=
  { sent := [
      0, 0, 1218, 1221, 1980, 3128, 3131, 3859, 5075, 5078, 5837, 6985, 6988, 7716, 8932, 8935,
      9694, 10842, 10845, 11573, 12789, 12792, 13551, 14699, 14702, 15430, 16646, 16649, 17408,
      18556, 18559, 19287, 20503, 20506, 21265, 22413, 22416, 23144, 24360, 24363, 25122, 26270,
      26273, 27001, 28217, 28220, 28979, 30127, 30130, 30858, 32074, 32077, 32836, 33984, 33987,
      34715, 35931, 35934, 36693, 37841, 37844, 38572, 39788, 39791, 40550, 41698, 41701, 42429,
      43645, 43648, 44407, 45555, 45558, 46287, 47451, 47454, 48235, 48240, 48247, 48253, 48259,
      48266, 48290]
    ans := [
      1, 1219, 1222, 1981, 3129, 3132, 3860, 5076, 5079, 5838, 6986, 6989, 7717, 8933, 8936, 9695,
      10843, 10846, 11574, 12790, 12793, 13552, 14700, 14703, 15431, 16647, 16650, 17409, 18557,
      18560, 19288, 20504, 20507, 21266, 22414, 22417, 23145, 24361, 24364, 25123, 26271, 26274,
      27002, 28218, 28221, 28980, 30128, 30131, 30859, 32075, 32078, 32837, 33985, 33988, 34716,
      35932, 35935, 36694, 37842, 37845, 38573, 39789, 39792, 40551, 41699, 41702, 42430, 43646,
      43649, 44408, 45556, 45559, 46288, 47452, 47455, 48236, 48241, 48248, 48254, 48260, 48267,
      48291]
    smp := [
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true]
    len := 48293 }

def wpTab₂ : Tab :=
  { sent := [
      1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63]
    ans := [
      2, 5, 18, 26, 33, 40, 50, 57, 64]
    smp := [
      true, true, true, true, true, true, true, false, true, true, true]
    len := 68 }

def wpTab₃ : Tab :=
  { sent := [
      7, 14, 20, 26]
    ans := [
      8, 15, 21, 27]
    smp := [
      true, true, true, true]
    len := 30 }

end P2Law.ProofPlan
