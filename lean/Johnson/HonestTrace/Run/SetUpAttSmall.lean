-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpAttSmall.lean

Attention's set-up: what reads the scale file, and closed facts at the shifts 4 to 12. One
definition, and theorems.

Main definition: "allWords v": a record of scales of 696 words, each v.

Main theorems (on OnBytes/Model/AttentionConfig.lean and OnBytes/Model/AttentionShape.lean):
* "fill_congr", "group_congr": "Attention.fill" and "Attention.group" give the same at two records
  of scales whose shifts "klSh" agree at the group's layers.
* "allWords_sh": at "allWords v" the shift of each layer below 48 is v.
* "shTests_congr": "Attention.shTests" gives the same at two configurations with the same kFD, S
  and Ty.
* "shTests_in_range": at kFD = 16, S = 12, Ty = 2^18, at the numbers 2307 and 2^7 * clamp * clamp,
  the tests pass at every shift from 4 to 12. "kfdB_in_range": the like of
  "OnBytes.Road.K4.Trial.kfdB" (Johnson/AtFull/Public/AttLaws.lean) at 4096 and 16.
* "shTests_no": at the shifts 3 and 13 the tests refuse.

Limits. Three closed facts are proved by "decide +kernel": "shTests_closed", "kfdB_closed" and
"shTests_no". They are stated at the numbers named alone.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.AtFull.Public.AttLaws
import Johnson.Goal.Meaning.ScalesReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify

theorem fill_congr {P : PolScan} {y : Layer.Lay} {s s' : Layer.Scales} {lines : List Attention.Line}
    {g g' : Nat} (h : ∀ lam, lam < y.Lam → s.klSh (g * y.Lam + lam) = s'.klSh (g' * y.Lam + lam)) :
    Attention.fill P y s lines g = Attention.fill P y s' lines g' := by
  have e : ((Array.range y.Lam).map fun lam => s.klSh (g * y.Lam + lam)) =
      (Array.range y.Lam).map fun lam => s'.klSh (g' * y.Lam + lam) :=
    Array.map_congr_left fun lam hl => h lam (Array.mem_range.1 hl)
  unfold Attention.fill
  simp only [e]

theorem group_congr {P : PolScan} {y : Layer.Lay} {s s' : Layer.Scales} {mq : Nat → Nat}
    {lines : List Attention.Line} {g : Nat}
    (h : ∀ lam, lam < y.Lam → s.klSh (g * y.Lam + lam) = s'.klSh (g * y.Lam + lam)) :
    Attention.group P y s mq lines g = Attention.group P y s' mq lines g := by
  unfold Attention.group
  rw [fill_congr h]

def allWords (v : Nat) : Layer.Scales := ⟨Array.replicate 696 v, 13, 48⟩

theorem allWords_sh (v : Nat) {l : Nat} (h : l < 48) : (allWords v).klSh l = v := by
  show (Array.replicate 696 v).getD (13 * l + 11) 0 = v
  have hl : 13 * l + 11 < 696 := by omega
  simp [Array.getD, hl]

theorem shTests_congr {cf cf' : Attention.Cfg} (hk : cf.kFD = cf'.kFD) (hS : cf.S = cf'.S)
    (hT : cf.Ty = cf'.Ty) (u0 Smax sh : Nat) :
    Attention.shTests cf u0 Smax sh = Attention.shTests cf' u0 Smax sh := by
  unfold Attention.shTests
  rw [hk, hS, hT]

theorem shTests_closed : ∀ sh ≤ 12, 4 ≤ sh →
    (Attention.shTests { kFD := 16, S := 12, Ty := 2 ^ 18 } 2307
      (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) sh).isOk = true := by decide +kernel

theorem shTests_in_range {cf : Attention.Cfg} (hk : cf.kFD = 16) (hS : cf.S = 12) (hT : cf.Ty = 2 ^ 18)
    {sh : Nat} (h4 : 4 ≤ sh) (h12 : sh ≤ 12) :
    Attention.shTests cf 2307 (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) sh = .ok () := by
  rw [shTests_congr (cf' := { kFD := 16, S := 12, Ty := 2 ^ 18 }) hk hS hT]
  exact Meaning.Ret.ok_of_isOk (shTests_closed sh h12 h4)

theorem kfdB_closed : ∀ sh ≤ 12, 4 ≤ sh →
    OnBytes.Road.K4.Trial.kfdB 4096
      (Attention.shdOf 2307 (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) sh) sh 16 = true := by
  decide +kernel

theorem kfdB_in_range {sh : Nat} (h4 : 4 ≤ sh) (h12 : sh ≤ 12) :
    OnBytes.Road.K4.Trial.kfdB 4096 (Attention.shdOf 2307 (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) sh) sh 16 = true :=
  kfdB_closed sh h12 h4

/-- A negative test, stated positively: at 3 and at 13 the five tests refuse. -/
theorem shTests_no : (Attention.shTests { kFD := 16, S := 12, Ty := 2 ^ 18 } 2307
      (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) 3).isOk = false ∧
    (Attention.shTests { kFD := 16, S := 12, Ty := 2 ^ 18 } 2307
      (2 ^ 7 * OnBytes.Model.clamp * OnBytes.Model.clamp) 13).isOk = false := by decide +kernel

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.fill_congr
#print axioms HonestTraceRun.SetUp.group_congr
#print axioms HonestTraceRun.SetUp.allWords_sh
#print axioms HonestTraceRun.SetUp.shTests_in_range
#print axioms HonestTraceRun.SetUp.kfdB_in_range
#print axioms HonestTraceRun.SetUp.shTests_no
