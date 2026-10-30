-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean: CONDITIONAL: THE WEIGHT CLAIMS OF THE SUB-PROTOCOL
K4 RETURN AND PASS THE MERGE's TESTS ON THE CLAIMS THEMSELVES AT ALL CHALLENGES, from one Bool on
the plan and two Bools on sizes and on the request.

Limits. THE LAW IS CONDITIONAL ON THREE TESTS, AND THIS FILE EVALUATES NONE OF THEM: claimsB (on the
plan alone: the same functions at challenges, points and tokens that are all 0, with an empty rotary
table and an empty end point of the second token sumcheck), zkFits (each call's point, which the
lookup samples, has the plan's number of coordinates) and tokensFit (in the first group the request
has T tokens, each below the size of the vocabulary). claimsB is as costly as the verifier's own
making of these claims. A file of tests evaluates the three at the small synthetic plan alone
(ClaimsBTest.lean [not in this library; so here read: not tested in this library]). No file of this
folder proves claimsB true at any plan. WHO GIVES zkFits
IS NOT SHOWN IN THIS FOLDER: it speaks of what the lookup hands over. By a reading of Forest.pad
(OnBytes/Model/Look.lean) what the lookup returns has these sizes at its own shape; the test
shapeFits of K4 compares neither the number of calls nor the calls with the plan's, so neither that
test nor the premises on what the lookup hands over give zkFits. THE MERGE's TESTS THAT ARE MEANT
ARE THOSE ON THE CLAIMS THEMSELVES: the third clause of its first test, which compares their number
with the number of slots (OnBytes/Model/Merge.lean), is not among them. Nothing is said of a
factor's elements. Where Johnson/Road/FormsKeysClaimsRun.lean is imported too, the bare name claimsB
can mean the library's OnBytes.Road.claimsB: write OnBytes.Desc.First.K4.RtPub.claimsB.
No property is claimed.

  zkSize, blankZk, blankClaims   the plan's number of coordinates of a call's point; the points with
                                 every coordinate 0; the environment with these points, challenges
                                 0, and no rotary table, table of the forms or end point.
  zkFits, tokensFit, claimsB     the three tests, with code.
  ClaimsRet       what is concluded, at an environment v of the forms: the numbers of the calls with
                  terms in the second token sumcheck are there, and at all challenges of the plan's
                  sizes the panels' claims and, in the first group, the embedding's claim return,
                  are as many as the plan counts, and pass the merge's tests on the claims
                  themselves.
  zkFits_blank    the points with every coordinate 0 pass zkFits, at every plan.
  zk_of_fits, skel_blank, tokens_of_fits, blank_any, any_some   steps.
  **claims_of_B** the law.
-/
import Johnson.Desc.First.K4.Returns.Pub.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel ClaimAlike optRel_map none_from)

/-- The plan's number of coordinates of the point at which call q's key vector is read. -/
def zkSize (P : Pub) (q : Nat) : Nat := ((P.y.fo.calls[q]?).map (·.n)).getD 0

/-- The calls' points with every coordinate 0. -/
def blankZk (P : Pub) : Array (Array E) :=
  (Array.range P.y.fo.NC).map fun q => Array.replicate (zkSize P q) zeroE

/-- The environment of the weight claims with every challenge and every coordinate 0. No table of
the forms, no rotary table and no end point of the second token sumcheck is laid in. The elements of
one factor are made of the last two; by claimsT_rel (Claims.lean) neither a return nor a factor's
size hangs on them. -/
def blankClaims (P : Pub) (hp : HPlan2) (g : Nat) : ClaimEnv :=
  { v := { y := P.y, sc := P.sc, g := g, iU3 := 0, K3 := 0, tab := [], zk := blankZk P }
    wsLay := P.wsLay, rope := #[], rs := Array.replicate hp.lamS zeroE, rt := #[] }

/-- **Each call has a point, of the plan's number of coordinates.** SIZES ALONE. -/
def zkFits (P : Pub) (zk : Array (Array E)) : Bool :=
  zk.size == P.y.fo.NC &&
    (List.range P.y.fo.NC).all fun q => (zk.getD q #[]).size == zkSize P q

/-- **In the first group the request has T tokens, each below the size of the vocabulary.** -/
def tokensFit (P : Pub) (g : Nat) : Bool :=
  g != 0 || (P.tokv.size == P.y.T && P.tokv.all fun t => decide (t < P.V))

/-- **The test on the plan**: at the environment blankClaims and at tokens 0 the claims
return, are as many as the plan counts, and pass the merge's tests on the claims themselves. It
reads no sampled element and no token. -/
def claimsB (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  (callsTS P).any fun TS =>
    ((blankClaims P hp g).weightClaims TS).any fun claimsP =>
      (if (g == 0) = true then
        ((blankClaims P hp g).claimE (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
          (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)).map ([·])
      else some []).any fun claimsE =>
        claimTests P.wsLay hp.NCL (claimsP ++ claimsE).toArray

/-- **What is concluded**, at an environment v of the forms. -/
def ClaimsRet (P : Pub) (hp : HPlan2) (g : Nat) (v : Env) : Prop :=
  ∃ TS, callsTS P = some TS ∧ ∀ (rs rt ZE tkh : Array E), rs.size = hp.lamS →
    rt.size = P.y.h.lt → ZE.size = (if (g == 0) = true then P.y.ls + P.y.h.lt else 0) →
    tkh.size = (if (g == 0) = true then P.y.lPd - P.y.ls else 0) →
    ∃ claimsP claimsE,
      ({ v := v, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } :
        ClaimEnv).weightClaims TS = some claimsP ∧
      (if (g == 0) = true then
        (({ v := v, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } :
          ClaimEnv).claimE ZE tkh P.V P.tokv).map ([·]) else some []) = some claimsE ∧
      ((claimsP ++ claimsE).toArray.size == hp.NCL) = true ∧
      (!(claimsP ++ claimsE).toArray.isEmpty && decide ((claimsP ++ claimsE).toArray.size ≤ 4096)) =
        true ∧
      ((claimsP ++ claimsE).toArray.all fun c => decide (c.ui < P.wsLay.U.size)) = true ∧
      ((claimsP ++ claimsE).toArray.all fun c => (wsClaimShape P.wsLay c).isOk) = true

/-- Where a test on a value that may be missing accepts, the value is there. -/
theorem any_some {α : Type} {x : Option α} {p : α → Bool} (h : x.any p = true) :
    ∃ a, x = some a ∧ p a = true := by
  cases x with
  | none =>
    have h' : false = true := h
    cases h'
  | some a => exact ⟨a, rfl, h⟩

/-- **The points with every coordinate 0 pass zkFits**, at every plan: the premise has a member. -/
theorem zkFits_blank (P : Pub) : zkFits P (blankZk P) = true := by
  unfold zkFits
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨?_, fun q hq => ?_⟩
  · unfold blankZk
    rw [Array.size_map, Array.size_range]
  · have hq' : q < P.y.fo.NC := List.mem_range.1 hq
    show (((blankZk P).getD q #[]).size == zkSize P q) = true
    rw [beq_iff_eq]
    unfold blankZk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hq']
    show (Array.replicate (zkSize P q) zeroE).size = zkSize P q
    rw [Array.size_replicate]

/-- Points that pass zkFits are as long as the points with every coordinate 0, call by call. -/
theorem zk_of_fits {P : Pub} {zk : Array (Array E)} (h : zkFits P zk = true) (q : Nat) :
    (zk.getD q #[]).size = ((blankZk P).getD q #[]).size := by
  unfold zkFits at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  by_cases hq : q < P.y.fo.NC
  · have e : ((zk.getD q #[]).size == zkSize P q) = true := h2 q (List.mem_range.2 hq)
    rw [beq_iff_eq] at e
    rw [e]
    unfold blankZk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hq]
    show zkSize P q = (Array.replicate (zkSize P q) zeroE).size
    rw [Array.size_replicate]
  · have z1 : zk.getD q #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have z2 : (blankZk P).getD q #[] = #[] := by
      unfold blankZk
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_neg hq]
      rfl
    rw [z1, z2]

/-- An environment of the plan's sizes and the environment blankClaims. -/
theorem skel_blank {P : Pub} {hp : HPlan2} {g : Nat} {v : Env} (hy : v.y = P.y) (hg : v.g = g)
    (hz : zkFits P v.zk = true) {rs : Array E} (hr : rs.size = hp.lamS) (rope : Array Nat)
    (rt : Array E) :
    ClaimSkel { v := v, wsLay := P.wsLay, rope := rope, rs := rs, rt := rt }
      (blankClaims P hp g) := by
  refine ⟨hy, hg, rfl, ?_, zk_of_fits hz⟩
  show rs.size = (Array.replicate hp.lamS zeroE).size
  rw [Array.size_replicate, hr]

/-- The test on the request, in the first group. -/
theorem tokens_of_fits {P : Pub} {g : Nat} (h : tokensFit P g = true) (h0 : (g == 0) = true) :
    P.tokv.size = P.y.T ∧ (P.tokv.all fun t => decide (t < P.V)) = true := by
  unfold tokensFit at h
  have e : (g != 0) = false := by
    rw [bne, h0]
    rfl
  rw [e, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- Where some list of T tokens lies below V, so does the list of T tokens 0. -/
theorem blank_any {T V : Nat} {t : Array Nat} (hs : t.size = T)
    (ha : (t.all fun x => decide (x < V)) = true) : (Array.replicate T 0).any (· ≥ V) = false := by
  rw [Array.any_eq_false]
  rw [Array.all_eq_true] at ha
  intro i hi
  rw [Array.size_replicate] at hi
  have := ha i (by omega)
  simp only [Array.getElem_replicate, decide_eq_true_eq] at this ⊢
  omega

/-- **THE WEIGHT CLAIMS RETURN AND PASS THE MERGE's TESTS ON THE CLAIMS THEMSELVES AT ALL
CHALLENGES**, at every environment of the forms that has the plan's layout and group and whose
calls' points have the plan's sizes. -/
theorem claims_of_B {P : Pub} {hp : HPlan2} {g : Nat} {v : Env} (hB : claimsB P hp g = true)
    (hy : v.y = P.y) (hg : v.g = g) (hz : zkFits P v.zk = true) (ht : tokensFit P g = true) :
    ClaimsRet P hp g v := by
  unfold claimsB at hB
  obtain ⟨TS, hTS, hB⟩ := any_some hB
  obtain ⟨cP₀, hP₀, hB⟩ := any_some hB
  obtain ⟨cE₀, hE₀, hB⟩ := any_some hB
  refine ⟨TS, hTS, fun rs rt ZE tkh hr _ hZ hk => ?_⟩
  have S := skel_blank hy hg hz hr P.rope rt
  obtain ⟨cP, hP, aP⟩ := OptRel.of_right (weightClaims_rel S TS) hP₀
  have hE : ∃ cE, (if (g == 0) = true then
      (({ v := v, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } :
        ClaimEnv).claimE ZE tkh P.V P.tokv).map ([·]) else some []) = some cE ∧
      All2 ClaimAlike cE cE₀ := by
    by_cases h0 : (g == 0) = true
    · rw [if_pos h0] at hE₀ hZ hk ⊢
      have tk := tokens_of_fits ht h0
      refine OptRel.of_right (optRel_map (claimE_rel S ?_ ?_ P.V ?_ ?_)
        fun _ _ h => All2.cons h All2.nil) hE₀
      · rw [hZ, Array.size_replicate]
      · rw [hk, Array.size_replicate]
      · rw [tk.1, Array.size_replicate]
      · rw [none_from tk.2 (Nat.le_refl _), blank_any tk.1 tk.2]
    · rw [if_neg h0] at hE₀ ⊢
      exact ⟨cE₀, hE₀, All2.refl OnBytes.Flat.ClaimAlike.refl _⟩
  obtain ⟨cE, hE, aE⟩ := hE
  have hT := claimTests_true ((claimTests_alike P.wsLay hp.NCL (aP.append aE)).trans hB)
  exact ⟨cP, cE, hP, hE, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.any_some
#print axioms OnBytes.Desc.First.K4.RtPub.zkFits_blank
#print axioms OnBytes.Desc.First.K4.RtPub.zk_of_fits
#print axioms OnBytes.Desc.First.K4.RtPub.skel_blank
#print axioms OnBytes.Desc.First.K4.RtPub.tokens_of_fits
#print axioms OnBytes.Desc.First.K4.RtPub.blank_any
#print axioms OnBytes.Desc.First.K4.RtPub.claims_of_B
