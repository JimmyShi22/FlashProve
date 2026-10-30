-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortLook.lean: THE LETTERS t3 AND l3 OF WHAT IS LEFT OF A LINK's LAW
(the lookup argument's runs' terms and numbers of claims, by the entry of the link's order) AS ONE
WRITTEN TERM EACH; AND THE DUTY PlainE (Link/Law/LinkExps.lean) AT THEM, AT THE THREE SORTS: THE
PREMISE hP OF numbers_layersC, numbers_attC, numbers_headC (SortNumbersC.lean) AND OF
numbers_layers3 .. (SortNumbers.lean). Definitions; statements and proofs.

Why these terms. They are not free: the lookups' own laws of their runs
(Johnson/Top/H/Keep/RunsPlain.lean: objects_runOk, planes_plainOk, join_plainOk) end at plainTm of
objVals, plVals, jnVals and at objLen, pickLen .. 3, pickLen .. 1. By the entry: "planes" and
"join" are the calls' seat's; "objects" stands twice in every order: at a number below 6 it is the
calls' seat's, from 6 on the digits' (1 | 6; at the head's link 2 | 7).

What is said.
  `v3All lmC jC lmD jD bv pv kv o`: the values by the entry · `t3All .. o` := plainTm (v3All .. o)
    · `l3All lmC jC lmD jD o`: the numbers of claims by the entry. bv, pv, kv: the worths of the
    caller's forms at "planes" and "join": LETTERS (who pays the lookups' premises hb, hp', hkv
    chooses them).
  `v3All_length`: as many values as l3All says, at every entry.
  `t3_calls`, `t3_digits`, `t3_planes`, `t3_join`, `l3_calls`, `l3_digits`, `l3_planes`, `l3_join`:
    the terms read back at an entry, in the lookups' own texts.
  `plainE_look`: PlainE at an entry where the tables answer t3All and l3All.
  `hP_layers`, `hP_att`, `hP_head`: **PlainE at each of the sort's lookup's entries, at every fixed
    part and every data: NO PREMISE.**

Limits. DEFINITIONS AND A DUTY ON EXPONENTS (they differ and lie in [n, n + len)): it says nothing
on the values. objLen and pickLen read the fixed part through a choice: no code. Where that choice
finds nothing the values are [] and the length 0. v3All's LAST ARM ANSWERS EVERY NAME BUT "planes"
AND "join" AS "objects": at the three sorts' orders as they stand no other name of the lookup's
reaches it; a new entry under a new name would be read as "objects" in silence. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Link.Law.LinkExps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.OnPublicFiles (objVals objLen plVals jnVals pickLen objVals_length plVals_length
        jnVals_length)

/-- **THE LOOKUP's RUNS' VALUES, BY THE ENTRY.** -/
noncomputable def v3All (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ →
  GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (o : ℕ × String) :
    Phi BetaAll × Option Pub9 → Bound GE8 → List GE8 :=
  if o.2 == "planes" then plVals hdCalls lmC jC bv pv
  else if o.2 == "join" then jnVals hdCalls lmC jC kv
  else if 6 ≤ o.1 then objVals hdDigits lmD jD
  else objVals hdCalls lmC jC

/-- **t3.** -/
noncomputable def t3All (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ →
  GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (o : ℕ × String) :
    ℕ → Phi BetaAll × Option Pub9 → Bound GE8 → List (ℕ × GE8) :=
  plainTm (v3All lmC jC lmD jD bv pv kv o)

/-- **l3.** -/
noncomputable def l3All (lmC jC lmD jD : ℕ) (o : ℕ × String) : Phi BetaAll × Option Pub9 → ℕ :=
  if o.2 == "planes" then pickLen hdCalls lmC jC 3
  else if o.2 == "join" then pickLen hdCalls lmC jC 1
  else if 6 ≤ o.1 then objLen hdDigits lmD jD
  else objLen hdCalls lmC jC

/-- As many values as l3All says. -/
theorem v3All_length (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (o : ℕ × String)
    (q : Phi BetaAll × Option Pub9) (y : Bound GE8) :
    (v3All lmC jC lmD jD bv pv kv o q y).length = l3All lmC jC lmD jD o q := by
  unfold v3All l3All
  split
  · exact plVals_length hdCalls lmC jC bv pv q y
  · split
    · exact jnVals_length hdCalls lmC jC kv q y
    · split
      · exact objVals_length hdDigits lmD jD q y
      · exact objVals_length hdCalls lmC jC q y

theorem t3_calls (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (k : ℕ) (hk : k < 6) :
    t3All lmC jC lmD jD bv pv kv (k, "objects") = plainTm (objVals hdCalls lmC jC) := by
  simp [t3All, v3All, Nat.not_le.2 hk]

theorem t3_digits (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (k : ℕ) (hk : 6 ≤ k) :
    t3All lmC jC lmD jD bv pv kv (k, "objects") = plainTm (objVals hdDigits lmD jD) := by
  simp [t3All, v3All, hk]

theorem t3_planes (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (k : ℕ) :
    t3All lmC jC lmD jD bv pv kv (k, "planes") = plainTm (plVals hdCalls lmC jC bv pv) := by
  simp [t3All, v3All]

theorem t3_join (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (k : ℕ) :
    t3All lmC jC lmD jD bv pv kv (k, "join") = plainTm (jnVals hdCalls lmC jC kv) := by
  simp [t3All, v3All]

theorem l3_calls (lmC jC lmD jD k : ℕ) (hk : k < 6) :
    l3All lmC jC lmD jD (k, "objects") = objLen hdCalls lmC jC := by
  simp [l3All, Nat.not_le.2 hk]

theorem l3_digits (lmC jC lmD jD k : ℕ) (hk : 6 ≤ k) :
    l3All lmC jC lmD jD (k, "objects") = objLen hdDigits lmD jD := by
  simp [l3All, hk]

theorem l3_planes (lmC jC lmD jD k : ℕ) :
    l3All lmC jC lmD jD (k, "planes") = pickLen hdCalls lmC jC 3 := by
  simp [l3All]

theorem l3_join (lmC jC lmD jD k : ℕ) :
    l3All lmC jC lmD jD (k, "join") = pickLen hdCalls lmC jC 1 := by
  simp [l3All]

/-- PlainE at an entry where the tables answer t3All and l3All. -/
theorem plainE_look (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (tmOf : ℕ × String → ℕ → Phi BetaAll × Option Pub9 → Bound GE8 → List (ℕ × GE8))
    (lenOf : ℕ × String → Phi BetaAll × Option Pub9 → ℕ) (q : Phi BetaAll × Option Pub9) (y : Bound
      GE8)
    (o : ℕ × String) (ht : tmOf o = t3All lmC jC lmD jD bv pv kv o)
    (hl : lenOf o = l3All lmC jC lmD jD o) : PlainE tmOf lenOf q y o :=
  plainE_of tmOf lenOf q y o (v3All lmC jC lmD jD bv pv kv o) ht
    (by rw [hl]; exact Nat.le_of_eq (v3All_length lmC jC lmD jD bv pv kv o q y))

/-- **hP AT A LAYERS' LINK.** -/
theorem hP_layers (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (p4 : OnBytes.Desc.First.K4.Par)
    (ent : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Phi BetaAll × Option Pub9 → Bound GE8 → List (ℕ × GE8)) (q : Phi BetaAll × Option
      Pub9)
    (y : Bound GE8) : ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")],
      PlainE (tmL p4 ent tm4 (t3All lmC jC lmD jD bv pv kv)) (lenL p4 (l3All lmC jC lmD jD)) q
        y o := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;>
    exact plainE_look lmC jC lmD jD bv pv kv _ _ q y _ (by simp [tmL]) (by simp [lenL])

/-- **hP AT AN ATTENTION LINK.** -/
theorem hP_att (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (rd : Phi BetaAll → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (ent : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Phi BetaAll × Option Pub9 → Bound GE8 → List (ℕ × GE8)) (q : Phi BetaAll × Option
      Pub9)
    (y : Bound GE8) :
    ∀ o ∈ [((1 : ℕ), "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      PlainE (tmA rd c ent tm4 (t3All lmC jC lmD jD bv pv kv)) (lenA rd c (l3All lmC jC lmD
        jD)) q y o := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    exact plainE_look lmC jC lmD jD bv pv kv _ _ q y _ (by simp [tmA]) (by simp [lenA])

/-- **hP AT THE HEAD's LINK.** -/
theorem hP_head (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (hS : OnBytes.Model.Head.Shape) (iU3
      : ℕ)
    (p6 : Kinds.Head.Par) (kap : Phi BetaAll → Option Kinds.Head.Law.Seen)
    (ent : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Phi BetaAll × Option Pub9 → Bound GE8 → List (ℕ × GE8)) (q : Phi BetaAll × Option
      Pub9)
    (y : Bound GE8) : ∀ o ∈ [((2 : ℕ), "objects"), (2, "planes"), (7, "objects")],
      PlainE (tmH hS iU3 p6 kap ent tm4 (t3All lmC jC lmD jD bv pv kv))
        (lenH hS iU3 p6 kap (l3All lmC jC lmD jD)) q y o := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;>
    exact plainE_look lmC jC lmD jD bv pv kv _ _ q y _ (by simp [tmH]) (by simp [lenH])

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.v3All_length
#print axioms VerifiableInference.Desc.PhiAll.t3_calls
#print axioms VerifiableInference.Desc.PhiAll.t3_digits
#print axioms VerifiableInference.Desc.PhiAll.t3_planes
#print axioms VerifiableInference.Desc.PhiAll.t3_join
#print axioms VerifiableInference.Desc.PhiAll.l3_calls
#print axioms VerifiableInference.Desc.PhiAll.l3_digits
#print axioms VerifiableInference.Desc.PhiAll.l3_planes
#print axioms VerifiableInference.Desc.PhiAll.l3_join
#print axioms VerifiableInference.Desc.PhiAll.plainE_look
#print axioms VerifiableInference.Desc.PhiAll.hP_layers
#print axioms VerifiableInference.Desc.PhiAll.hP_att
#print axioms VerifiableInference.Desc.PhiAll.hP_head
