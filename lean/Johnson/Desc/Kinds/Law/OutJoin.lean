-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OutJoin.lean: OUT, BY THE CALL, WITH THE HEAD's CHANCE IN IT: STATED AND PROVED. The
law of the head's half by the key (Law/K06Statement.lean: K06OutStatement; proved in Law/Clamp.lean:
k06Out) and the law by the call (HeadOutLaw.lean: OutCallStatement; Law/OutCall.lean: outCall), laid together
at the block's own letters: those that fromLookup makes of the lookup's points.
THE STATEMENT (OutJoinStatement). The letters in front of "there is a rule" are fixed before the head's
sumcheck is heard: the cells, the mask entries, the ledger in front, the lookup's points. The rule and its
ceiling are Lemma 2b's. Then: at a hearing of the head's sumcheck that returns, AT ANY LEDGER G THAT IS
LATER THAN THE ONE BEHIND THAT HEARING (so at the ledger that the caller holds where the claims are judged), with
the run "logits" 0 at the hidden scalars and the sent reads, the head's reads true below their lengths, the claim
on the weights true, no bad draw, AND NormTrue (three reads of the normalization; the claimed sum of its
sumcheck "normed"): EACH OF THE SIX CALLS' KEY VECTORS, at the hidden scalars and the sent reads, IS THE
MULTILINEAR EXTENSION OF THE CALL's TABLE AT THE CALL's KEY POINT; and the two guests are the sums of their
corner values under the weights of zt.
NormTrue's last field has chance in it: its law is Law/Normed.lean's normed_law; the two are laid together in
Law/OutWhole.lean.
THE RULE HAS A NAME (badP) and the law is said of it (outJoin_at, over k06Out_at, Law/Clamp.lean); "there
is a rule" follows.
IMPORTED, NOT THIS FILE's: K06Statement.lean (atWorld, TrueReads, WeightTrue, WeightsOk), Law/K06Glue.lean
(worldE, rd_atWorld), Law/Clamp.lean (k06Out), Law/Closed.lean (S2_dvd_len).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Clamp
import Johnson.Desc.Kinds.Law.OutCall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- What the law says of a rule. -/
def OutJoinAt [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F0 : Fork) (bad : List Fmt.RoundView → List E) : Prop :=
  ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
    [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] [Reads],
    Canonical t →
    sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) → Later F1 G →
    let _ : Heard := { logits := S }
    TrueReads c.toCells G mask ent → WeightTrue c.toCells G mask ent →
    (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
    NoBad bad t → NormTrue (worldE G mask ent) c →
    (∀ call, call < 6 →
      rd (atWorld G mask ent
          (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
        = (Finset.range (2 ^ (zk call).size)).sum fun i =>
            rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
    atWorld G mask ent clip = (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) ∧
    atWorld G mask ent table = (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t))

/-- **OUT, BY THE CALL, WITH THE HEAD's CHANCE IN IT.** -/
def OutJoinStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F0 : Fork),
    planOk sT = true → Request.ok = true → y < V → WellLaid F0 → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      OutJoinAt floor zx zk c mask F0 bad

namespace Came

/-- **OUT, BY THE CALL, AT THE RULE BY NAME**: the head's sumcheck's rule is badP. -/
theorem outJoin_at [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat)
    (zx : Point) (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F0 : Fork)
    (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0)
    (hP : PointsOk floor zx zk) (hn : nI = (fromLookup floor zx zk).norm)
    (hh : hI = (fromLookup floor zx zk).head) :
    OutJoinAt floor zx zk c mask F0 (badP c.toCells mask F0) := by
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have L := fromLookup_law floor zx zk hV (lens_small hplan) hP
  have hS2 : ∀ k : Key, S2 ∣ len k := S2_dvd_len P
  have hw : WeightsOk := by
    subst hn
    subst hh
    letI : FinalNorm.In := (fromLookup floor zx zk).norm
    letI : In := (fromLookup floor zx zk).head
    exact ⟨fun k x hx => L.block (.inr k) (hS2 k) x hx, fun k => L.wsum (.inr k), L.wx, L.below⟩
  have hzt : (FinalNorm.zt).size = lt := by
    subst hn
    exact L.zt
  intro F1 t S G ent _ _ _ _ hcan hsum hL _ hreads hwt hclaims hnb hN
  obtain ⟨hk, hclip, htable⟩ := k06Out_at c.toCells mask F0 hreq hy hWL hw hzt F1 t S G ent hcan hsum hL
    hreads hwt hclaims hnb
  refine ⟨fun call hcall => ?_, hclip, htable⟩
  rw [rd_atWorld]
  refine outCall sT floor zx zk c (worldE G mask ent) hplan hP hn hh (fun k => ?_) hN call hcall
  show vW (worldE G mask ent) (key k) = _
  rw [← rd_atWorld, hk k, rd_sumTo]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => by rw [rd_mul, rd_mul]

theorem outJoin : OutJoinStatement := fun sT floor zx zk c mask F0 hplan hreq hy hWL hP hn hh =>
  ⟨badP c.toCells mask F0, fun h => bad_length _ _ _ _ h,
    outJoin_at sT floor zx zk c mask F0 hplan hreq hy hWL hP hn hh⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outJoin_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outJoin
