-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/JoinBOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: THE TEST joinB
(Johnson/Desc/First/K4/Returns/JoinSkel.lean: each call's factor in the join is there at the blank
structure) IS TRUE, as a theorem and without evaluation, from the verifier's lines that make the
layout, the reads and the tables' places. General in the sizes. Statements and proofs.

  `planRd_of`      PlanRd (LineRdOf.lean) from these lines.
  `famWidth_len`   a family's number of entries in the verifier's numbers is the library's.
  **`joinB_of`**     joinB P hp g iU3 r.1 = true.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. UNDER THE
LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. That the reads' array has a column (hK) and that the
last entry's row fits 32 bits (hb) are hypotheses on the plan's tree. Public data alone: whether a
form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.StreamsThere
import Johnson.Road.K4.C.JoinReturn
import Johnson.Desc.First.K4.Returns.JoinSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Reads Pub HPlan2 TableAsk TableAt layTables tableAsks layout readsOf)
open Inst.Model.FFSeg (Fam len isExp)
open OnBytes.Desc.First.K4.Rt (joinB envBlank)

/-- PlanRd from the verifier's lines. -/
theorem planRd_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {v : Env} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} (hy : layout h pc = .ok v.y)
    (S : Switches h) (hp4 : h.p4 = true) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hK : v.K3 ≠ 0) (hb : r.2.2 / v.K3 < 2 ^ 32) : PlanRd v := by
  have A := admitted_of_layout hy S.p3
  obtain ⟨RL, RS⟩ := reach_six hy S hg hrd hl ht hK hb
  exact {
    L := A.laid
    L2 := laid2_of_layout hy
    S := by
      rw [A.shape]
      exact S
    p4 := by
      rw [A.shape]
      exact hp4
    la := by
      rw [A.shape]
      exact A.la
    long := RL
    short := RS }

/-- A family's number of entries in the verifier's numbers is the library's, at the sizes that the
shape gives. -/
theorem famWidth_len {v : Env} (L : Laid v.y) (S : Switches v.y.h) (s : Fam) :
    famWidth v s = len (dimOf v.y.h) s := by
  cases s <;> first
    | rfl
    | exact L.nqk
    | exact L.dkv
    | (show v.y.NN * ledNR v.y.h.xl = 2 * 99
       rw [L.NN, S.xl]
       rfl)

/-- **THE TEST joinB IS TRUE.** CONDITIONAL: on the verifier's lines, the switches, profile 4, hK
and hb. -/
theorem joinB_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub}
    {hp : HPlan2} {g iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hy : layout h pc = .ok P.y)
    (S : Switches h) (hp4 : h.p4 = true) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok P.rd)
    (hl : layTables (matsR P.y g) (tableAsks P.y P.rd g) 0 = some r)
    (hK : ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32) :
    joinB P hp g iU3 r.1 = true := by
  have B : PlanRd (envBlank P hp g iU3 r.1) :=
    planRd_of (v := envBlank P hp g iU3 r.1) hy S hp4 hg hrd hl rfl hK hb
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  unfold joinB
  rw [List.all_eq_true]
  intro q hq
  have hq' := List.mem_range.mp hq
  have hcd : P.y.calls.getD q default ∈ P.y.calls := by
    have e1 : P.y.calls.getD q default = P.y.calls[q] := by simp [Array.getD, hq']
    rw [e1]
    exact Array.getElem_mem _
  refine joinPart_some fun s hs lam hlam _ => ?_
  obtain ⟨fam, a1, a2, -, a4, -⟩ := segs_of_layout hy S _ hcd s hs
  have hlen : famWidth (envBlank P hp g iU3 r.1) fam = s.n := by
    rw [famWidth_len B.L B.S fam]
    exact a2.symm
  rw [a1]
  refine line_some fam B.S.gcl B.S.rcl (fun _ => lineRd_plan B hlam)
    (fun _ => lineRdM_of B ?_) ?_ ?_
  · have LL : Laid P.y := B.L
    have hlam' : lam < P.y.Lam := hlam
    obtain ⟨k, hk⟩ : ∃ k, P.y.h.ll = k + 1 := ⟨P.y.h.ll - 1, by have := LL.ll; omega⟩
    have e2 : 2 ^ P.y.h.ll = 2 * 2 ^ k := by rw [hk, Nat.pow_succ, Nat.mul_comm]
    rw [LL.Lam, e2] at hlam'
    show lam / 2 < P.y.LamM
    rw [LL.LamM, e2]
    omega
  · rw [hlen]
    split_ifs
    · unfold Env.ewhFrom
      rw [Array.size_map, Array.size_range]
    · exact Nat.zero_le _
  · intro ef
    subst ef
    unfold Env.ewFrom
    rw [Array.size_map, a4]
    exact Nat.le_of_eq hlen.symm

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.planRd_of
#print axioms OnBytes.Road.K4.C.famWidth_len
#print axioms OnBytes.Road.K4.C.joinB_of
