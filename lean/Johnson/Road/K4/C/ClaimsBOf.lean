-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsBOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: THE TEST claimsB
(Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean) IS TRUE, as a theorem and without evaluation. The
test asks, at a structure with every challenge and coordinate 0, that the panels' weight claims
and, in the first group, the embedding's claim return, that they are as many as the plan counts, at
least one and at most 4096, and that each stands on a unit of the layout of the weights with the
sizes that the layout asks. The road: the calls of the second walk are 0, 1, 2, 5 (the library's
ts_of_lines, Johnson/Road/FormsKeysPansTS.lean); the whole list returns, all claims good
(ClaimsAll.lean); so does the embedding's (ClaimEReturn.lean); the count is the plan's function
nclOf (OnBytes/Model/LayerPlan.lean). Statements and proofs. General in the sizes.

  `tests_of_good`   a list of n good claims, n from 1 to 4096, passes the count and the merge's
                    three tests.
  **`claimsB_of`**    claimsB P hp g = true.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A
LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, AND
A LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. WHAT THE CLAIMS READ
AT THE BLANK STRUCTURE (R : ClaimRd, Q : QkRd) IS A HYPOTHESIS HERE. That the plan's count is nclOf
(h2) and at most 4096 (h4096) are hypotheses on the plan. Public data alone: whether a claim IS
THERE and how long its parts are; nothing on its elements. No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsAll
import Johnson.Road.K4.C.ClaimEReturn
import Johnson.Road.FormsKeysPansTS
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Pub HPlan2 layout readsOf nclOf callsTS)
open OnBytes.Desc.First.K4.RtPub (claimsB blankClaims claimTests)
open Inst.Model (Params)

/-- A list of n good claims, n from 1 to 4096, passes the count and the merge's three tests. -/
theorem tests_of_good {lay : WsLay} {n : ℕ} {l : List WsClaim} (hl : l.length = n) (h0 : 0 < n)
    (hn : n ≤ 4096) (hg : ∀ cl ∈ l, GoodCl lay cl) : claimTests lay n l.toArray = true := by
  unfold claimTests
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.size_toArray, hl, beq_self_eq_true]
  · cases l with
    | nil =>
      have : (0 : ℕ) = n := hl
      omega
    | cons a t => rfl
  · rw [List.size_toArray, hl, decide_eq_true_eq]
    exact hn
  · rw [List.all_toArray, List.all_eq_true]
    intro cl hcl
    rw [decide_eq_true_eq]
    exact (hg cl hcl).1
  · rw [List.all_toArray, List.all_eq_true]
    intro cl hcl
    exact (hg cl hcl).2

/-- **THE TEST claimsB IS TRUE.** CONDITIONAL: on the layout's and the reads' return, the switches,
the eight lines, what the claims read at the blank structure (R, Q), four ties of the weights' shape
and the layout's numbers (hL, hV, hlPd, hls), a token in the vocabulary (hV0), and two facts on the
plan's count (h2, h4096). -/
theorem claimsB_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub}
    {hp : HPlan2} {g : ℕ} {s : WsShape} {Pm : Params} {lk : ℕ} (hy : layout h pc = .ok P.y)
    (S : Switches h) (hrd : readsOf P.y = .ok P.rd) (hN : LinesAre P.y)
    (R : ClaimRd (blankClaims P hp g) s Pm lk) (Q : QkRd (blankClaims P hp g) s)
    (hL : s.L = P.y.h.L) (hV : s.V = P.V) (hV0 : 0 < P.V) (hlPd : P.y.lPd = ceilLog2 P.y.h.d)
    (hls : P.y.ls ≤ P.y.lPd) (h2 : hp.NCL = nclOf P.y g) (h4096 : hp.NCL ≤ 4096) :
    claimsB P hp g = true := by
  have hTS : callsTS P = some [0, 1, 2, 5] := ts_of_lines hy S.p3 hN hrd
  have h3 : P.y.h.p3 = true := R.p3
  have hLam : 0 < P.y.Lam := Nat.lt_of_le_of_lt (Nat.zero_le _) (R.odd 0 (by
    have h1 := (admitted_of_layout hy S.p3).laid
    have h2 := h1.LamM
    have h3 := h1.ll
    show 0 < P.y.LamM
    rw [h2]
    obtain ⟨k, hk⟩ : ∃ k, P.y.h.ll = k + 1 := ⟨P.y.h.ll - 1, by omega⟩
    rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    exact Nat.two_pow_pos k))
  obtain ⟨cp, hcp, hlen, hgood⟩ := weightClaims_ret (c := blankClaims P hp g) hN R Q
  have hlen' : cp.length = 6 * P.y.Lam + 4 * P.y.LamM := hlen
  have hncl : nclOf P.y g = 6 * P.y.Lam + 4 * P.y.LamM + (if g == 0 then 1 else 0) := by
    unfold nclOf
    rw [if_pos h3]
  unfold claimsB
  rw [hTS, Option.any_some, hcp, Option.any_some]
  by_cases hg0 : (g == 0) = true
  · obtain ⟨ce, hce, gce⟩ := claimE_ret (c := blankClaims P hp g) R.hlw hL R.d R.d0 hlPd hls
      (ZE := Array.replicate (P.y.ls + P.y.h.lt) zeroE)
      (tkh := Array.replicate (P.y.lPd - P.y.ls) zeroE) (tokv := Array.replicate P.y.T 0)
      Array.size_replicate (fun t ht => by
        have e : t = 0 := by
          rw [Array.toList_replicate] at ht
          exact List.eq_of_mem_replicate ht
        rw [e, hV]
        exact hV0) Array.size_replicate Array.size_replicate
    rw [hV] at hce
    rw [if_pos hg0, hce]
    show claimTests P.wsLay hp.NCL (cp ++ [ce]).toArray = true
    refine tests_of_good ?_ (by omega) h4096 fun cl hcl => ?_
    · rw [List.length_append, hlen', h2, hncl, if_pos hg0]
      rfl
    · rcases List.mem_append.mp hcl with hc | hc
      · exact hgood cl hc
      · rw [List.mem_singleton.mp hc]
        exact gce
  · rw [if_neg hg0]
    show claimTests P.wsLay hp.NCL (cp ++ []).toArray = true
    refine tests_of_good ?_ (by omega) h4096 fun cl hcl => ?_
    · rw [List.append_nil, hlen', h2, hncl, if_neg hg0, Nat.add_zero]
    · rw [List.append_nil] at hcl
      exact hgood cl hcl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tests_of_good
#print axioms OnBytes.Road.K4.C.claimsB_of
