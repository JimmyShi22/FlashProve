-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Hear.lean: CONDITIONAL: THE PUBLIC TESTS AS ONE. hearB joins the
tests on the places of the tables (Tables.lean), on the panels and the end of the batched sumcheck
(PansB.lean) and on the weight claims (ClaimsB.lean) with a flag and an optional number of the plan
that the hearing of the sub-protocol K4 reads first. It reads the public numbers, the plan and the
group's number alone. Where it is true, six pure functions of the verifier return at all later
values, the last two of them under two further tests: layTables, callsTS, panelsT (over panelsA,
with placePanels), stackEnd, weightClaims, claimE.

Limits. NO FILE OF THIS FOLDER PROVES THE TEST TRUE AT ANY PLAN. This folder's tests evaluate it at
a small synthetic plan alone (HearTest.lean), under #guard, which is Lean's evaluator and gives no
proof. It does not hold what the hearing asks of the lookup's join (weighedOf, joinPart, laidOf) nor
its readings pointsOf and funsOf. It reads no token (hearB_tokv): the test on the request is
tokensFit (ClaimsB.lean). six_of_B keeps two premises: the sizes of the calls' points (zkFits) and
the request's tokens. No property is claimed.

  nclpOf       the number of the panels' weight claims by the plan.
  hearB        the test.
  hearB_parts, hearB_of_parts   what it holds, part by part; and back.
  hearB_tokv   it does not read the request's tokens; nor does any of its parts (…_tokv).
  envAt        the environment of the forms by the plan, at given points of the lookup's calls.
  PansRet, SixRet   what is concluded: the panels' readings at every heard state; these with the
               tables' places and the weight claims' readings.
  six_of_B     where the test is true: the plan names the array of the reads, layTables returns, and
               at that number and these places SixRet holds at all tokens and points that pass the
               two tests on them.
-/
import Johnson.Desc.First.K4.Returns.Pub.Tables
import Johnson.Desc.First.K4.Returns.Pub.PansB
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Total (EnvSkel)

/-- The number of the panels' weight claims by the plan: the first group's plan counts the
embedding's claim too. -/
def nclpOf (hp : HPlan2) (g : Nat) : Nat := hp.NCL - (if (g == 0) = true then 1 else 0)

/-- **THE TEST.** The plan's list of tables is open, and the plan names the array of the reads; the
families of tables are placed and end at the plan's length of the reads; the panels' test, at the
environment without a point of the lookup; the weight claims' test. -/
def hearB (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  hp.tl.funOpen && (hp.tl.ix.U.getD 2 none).any fun iU3 =>
    (tablesAt P g).any fun r =>
      r.2.2 == hp.nU.getD 2 0 && pansB P (blankEnv P hp g iU3 r.1) hp.lamS (nclpOf hp g) &&
        claimsB P hp g

/-- What the test holds, part by part. -/
theorem hearB_parts {P : Pub} {hp : HPlan2} {g : Nat} (h : hearB P hp g = true) :
    ∃ iU3 tab laid n, hp.tl.ix.U.getD 2 none = some iU3 ∧ hp.tl.funOpen = true ∧
      tablesAt P g = some (tab, laid, n) ∧ tablesB P hp g = true ∧
      pansB P (blankEnv P hp g iU3 tab) hp.lamS (nclpOf hp g) = true ∧ claimsB P hp g = true := by
  unfold hearB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨iU3, hu, h⟩ := any_some h
  obtain ⟨⟨tab, laid, n⟩, ht, h⟩ := any_some h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨iU3, tab, laid, n, hu, h0, ht, ?_, h2, h3⟩
  unfold tablesB
  rw [ht]
  exact h1

/-- Back: where the parts are true, so is the test. -/
theorem hearB_of_parts {P : Pub} {hp : HPlan2} {g iU3 : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))} {n : Nat}
    (hu : hp.tl.ix.U.getD 2 none = some iU3) (h0 : hp.tl.funOpen = true)
    (ht : tablesAt P g = some (tab, laid, n)) (h1 : tablesB P hp g = true)
    (h2 : pansB P (blankEnv P hp g iU3 tab) hp.lamS (nclpOf hp g) = true)
    (h3 : claimsB P hp g = true) : hearB P hp g = true := by
  unfold tablesB at h1
  rw [ht] at h1
  have h1' : (n == hp.nU.getD 2 0) = true := h1
  unfold hearB
  rw [h0, hu, ht]
  show (true && (n == hp.nU.getD 2 0 &&
    pansB P (blankEnv P hp g iU3 tab) hp.lamS (nclpOf hp g) && claimsB P hp g)) = true
  simp only [h1', h2, h3, Bool.and_true]

/-- The test does not read the request's tokens. -/
theorem hearB_tokv (P : Pub) (t : Array Nat) (hp : HPlan2) (g : Nat) :
    hearB { P with tokv := t } hp g = hearB P hp g := rfl

theorem tablesAt_tokv (P : Pub) (t : Array Nat) (g : Nat) :
    tablesAt { P with tokv := t } g = tablesAt P g := rfl

theorem tablesB_tokv (P : Pub) (t : Array Nat) (hp : HPlan2) (g : Nat) :
    tablesB { P with tokv := t } hp g = tablesB P hp g := rfl

theorem pansB_tokv (P : Pub) (t : Array Nat) (v₀ : Env) (lamS NCLp : Nat) :
    pansB { P with tokv := t } v₀ lamS NCLp = pansB P v₀ lamS NCLp := rfl

theorem claimsB_tokv (P : Pub) (t : Array Nat) (hp : HPlan2) (g : Nat) :
    claimsB { P with tokv := t } hp g = claimsB P hp g := rfl

theorem blankEnv_tokv (P : Pub) (t : Array Nat) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) :
    blankEnv { P with tokv := t } hp g iU3 tab = blankEnv P hp g iU3 tab := rfl

theorem zkFits_tokv (P : Pub) (t : Array Nat) (zk : Array (Array E)) :
    zkFits { P with tokv := t } zk = zkFits P zk := rfl

/-- The environment of the forms by the plan, at the points zk of the lookup's calls. -/
def envAt (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) (zk : Array (Array E)) : Env :=
  { blankEnv P hp g iU3 tab with zk := zk }

/-- That environment and the one without a point of the lookup. -/
theorem envAt_skel (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt)
    (zk : Array (Array E)) : EnvSkel (envAt P hp g iU3 tab zk) (blankEnv P hp g iU3 tab) :=
  ⟨rfl, rfl, rfl⟩

/-- **What is concluded of the panels**, at an environment v of the forms and every heard state. -/
def PansRet (P : Pub) (v : Env) (lamS NCLp : Nat) : Prop :=
  ∀ H : Heard, ∃ TS, callsTS P = some TS ∧ ∀ shownT : Array E, shownT.size = nEndT P.y →
    ∃ pans, panelsT ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ TS
        (panelsA ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ {}) = some pans ∧
      (ceilLog2 (placePanels pans.bl).2 == lamS) = true ∧ (pans.nextV == NCLp) = true ∧
      ∀ (rs om H1 V : Array E) (a b : E), rs.size = lamS → om.size = 2 →
        H1.size = 1 + P.y.LamM → V.size = NCLp →
        ∃ fin, stackEnd P.y (placePanels pans.bl).1 rs lamS om H1 V a b = some fin

/-- **What is concluded**: the tables' places, the panels' readings, the weight claims' readings. -/
structure SixRet (P : Pub) (hp : HPlan2) (g : Nat) (zk : Array (Array E)) (iU3 : Nat)
    (tab : List TableAt) (laid : List (TableAsk × List (Nat × Nat))) : Prop where
  tables : ∃ nU3, layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (tableAsks P.y P.rd g) 0 = some (tab, laid, nU3) ∧ (nU3 == hp.nU.getD 2 0) = true
  pans : PansRet P (envAt P hp g iU3 tab zk) hp.lamS (nclpOf hp g)
  claims : ClaimsRet P hp g (envAt P hp g iU3 tab zk)

/-- The readings return where the parts of the test are true. -/
theorem six_of_parts {P : Pub} {hp : HPlan2} {g iU3 : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))} {n : Nat}
    (ht : tablesAt P g = some (tab, laid, n)) (h1 : tablesB P hp g = true)
    (h2 : pansB P (blankEnv P hp g iU3 tab) hp.lamS (nclpOf hp g) = true)
    (h3 : claimsB P hp g = true) {zk : Array (Array E)} (hz : zkFits P zk = true)
    (hk : tokensFit P g = true) : SixRet P hp g zk iU3 tab laid where
  tables := tables_at ht h1
  pans := fun H => pans_of_B (envAt_skel P hp g iU3 tab zk) h2 H
  claims := claims_of_B (v := envAt P hp g iU3 tab zk) h3 rfl rfl hz hk

/-- **Where the test is true, the readings return** at all tokens and all points of the lookup's
calls that pass the two tests on them; at the number of the array of the reads that the plan names
and at the places that layTables returns. -/
theorem six_of_B {P : Pub} {hp : HPlan2} {g : Nat} (h : hearB P hp g = true) :
    ∃ iU3 tab laid n, hp.tl.ix.U.getD 2 none = some iU3 ∧ tablesAt P g = some (tab, laid, n) ∧
      ∀ (t : Array Nat) (zk : Array (Array E)), zkFits P zk = true →
        tokensFit { P with tokv := t } g = true →
        SixRet { P with tokv := t } hp g zk iU3 tab laid := by
  obtain ⟨iU3, tab, laid, n, hu, -, ht, h1, h2, h3⟩ := hearB_parts h
  refine ⟨iU3, tab, laid, n, hu, ht, fun t zk hz hk => ?_⟩
  refine six_of_parts (n := n) ?_ ?_ ?_ ?_ ?_ hk
  · rw [tablesAt_tokv]
    exact ht
  · rw [tablesB_tokv]
    exact h1
  · rw [pansB_tokv, blankEnv_tokv]
    exact h2
  · rw [claimsB_tokv]
    exact h3
  · rw [zkFits_tokv]
    exact hz

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.hearB_parts
#print axioms OnBytes.Desc.First.K4.RtPub.hearB_of_parts
#print axioms OnBytes.Desc.First.K4.RtPub.hearB_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.tablesAt_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.tablesB_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.pansB_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.claimsB_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.blankEnv_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.zkFits_tokv
#print axioms OnBytes.Desc.First.K4.RtPub.envAt_skel
#print axioms OnBytes.Desc.First.K4.RtPub.six_of_parts
#print axioms OnBytes.Desc.First.K4.RtPub.six_of_B
