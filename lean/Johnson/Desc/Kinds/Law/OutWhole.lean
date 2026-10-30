-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OutWhole.lean: OUT, BY THE CALL, WITH BOTH SUMCHECKS' CHANCE IN IT: STATED AND PROVED: what the place
hands the lookup, from the forms that the place's own runs leave, with no premise on a claimed sum.
Law/OutJoin.lean's outJoin (the head's sumcheck; k06Out with the law by the call) and Law/Normed.lean's
normed_law (the final normalization's sumcheck "normed"), laid together, AT ANY LEDGER G LATER THAN THE ONE BEHIND
THE HEAD's SUMCHECK.
THE ORDER OF THE LETTERS IS THE ORDER IN TIME. Fixed first: the cells, the mask entries, the lookup's points, the
ledger Fa in front of "normed". THERE IS A RULE badN. Then "normed" is heard, from Fa to Fb. THERE IS A RULE badL
(it may hang on Fb, so on what was heard in "normed"). Then the head's sumcheck is heard, from Fb to F1; G is
later than F1. With the run "logits" and normedForms 0 at the hidden scalars of G and the sent reads, the reads
true below the lengths that the forms spend, the claim on the weights true, and no bad draw under either rule:
EACH OF THE SIX CALLS' KEY VECTORS IS THE MULTILINEAR EXTENSION OF THE CALL's TABLE AT THE CALL's KEY POINT; and the two
guests are the sums of their corner values under the weights of zt.
HOW THE BLOCK's ONE HEARING GIVES THE TWO HEARINGS, each at its own rounds from a WellLaid ledger: Law/Cut.lean:
hear_parts; how a rule on a stretch is a rule on the block's rounds: noBad_within.
IMPORTED, NOT PROVED HERE: K06Statement.lean, Law/K06Glue.lean (worldE, rd_atWorld), Law/FilledG.lean
(world_laterG), Law/Keeps.lean (keeps_sumcheck).
WHAT IT DOES NOT SAY. That the reads are true; that the forms are 0; that the claim on the weights is true; time
beyond the order of the letters; how probable a bad draw is: lists are counted. The normalization's 17 row forms
(its other two sumchecks) are no part of it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OutJoin
import Johnson.Desc.Kinds.Law.Normed
import Johnson.Desc.Kinds.Law.Cut
import Johnson.Desc.Kinds.Law.FilledG
import Johnson.Desc.Kinds.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- The three reads that the normalization's four keys spend, each below the length spent: NormTrue
(HeadOutLaw.lean) without its field on the claimed sum. -/
structure NormKeyReads [Sizes] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]
    (W : World K) (c : NCells) : Prop where
  act : ∀ i, i < 2 * d → val W (FinalNorm.entry .actAtKeys i)
    = rd (readAtN c (.act, .short (eq FinalNorm.zt)) i)
  row : ∀ i, i < NR + 21 → val W (FinalNorm.entry .rowAtKeys i)
    = rd (readAtN c (.row, .short (eq FinalNorm.zt)) i)
  wide : ∀ i, i < 4 * d / S2 → val W (FinalNorm.wide i)
    = rd (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) i)

/-- **OUT, BY THE CALL, WHOLE.** -/
def OutWholeStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (Fa : Fork),
    planOk sT = true → Request.ok = true → y < V → WellLaid Fa → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∃ badN : List Fmt.RoundView → List E,
      (∀ h, (badN h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      ∀ (Fb : Fork) (tN : List Fmt.RoundView) (SN : Sum),
        sumcheck FinalNorm.zt 2 Fa tN = some (SN, Fb, []) →
        ∃ badL : List Fmt.RoundView → List E,
          (∀ h, (badL h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
          ∀ (F1 : Fork) (tL : List Fmt.RoundView) (SL : Sum) (G : Fork) (ent : Nat → Nat → Nat → E)
            [Norm.Heard] [FinalNorm.Reads] [Reads],
            Canonical tN → Canonical tL →
            sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (SL, F1, []) → Later F1 G →
            let _ : FinalNorm.Heard := { normed := SN }
            let _ : Heard := { logits := SL }
            TrueReads c.toCells G mask ent → WeightTrue c.toCells G mask ent →
            NormKeyReads (worldE G mask ent) c → NormedReads (worldE G mask ent) c →
            (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
            (∀ f, f ∈ FinalNorm.normedForms → atWorld G mask ent f = 0) →
            NoBad badN tN → NoBad badL tL →
            (∀ call, call < 6 →
              rd (atWorld G mask ent
                  (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
                = (Finset.range (2 ^ (zk call).size)).sum fun i =>
                    rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
            atWorld G mask ent clip = (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) ∧
            atWorld G mask ent table = (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t))

namespace Came

theorem outWhole : OutWholeStatement := by
  intro _ _ _ _ nI hI sT floor zx zk c mask Fa hplan hreq hy hWLa hP hn hh
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have L := fromLookup_law floor zx zk hV (lens_small hplan) hP
  have hzt : (FinalNorm.zt).size = lt := by
    subst hn
    exact L.zt
  have hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2) := by
    subst hn
    intro x hx
    exact L.block (.inl .remLow) hd x hx
  obtain ⟨badN, hlenN, HN⟩ := normed_law c mask Fa hWLa hzt hd hblock
  refine ⟨badN, hlenN, ?_⟩
  intro Fb tN SN hsumN
  have hWLb : WellLaid Fb := wl_sumcheck _ _ _ _ _ _ _ hWLa hsumN
  obtain ⟨badL, hlenL, HL⟩ := outJoin sT floor zx zk c mask Fb hplan hreq hy hWLb hP hn hh
  refine ⟨badL, hlenL, ?_⟩
  intro F1 tL SL G ent _ _ _ hcN hcL hsumL hLater _ _ hreads hwt hNR hNdR hlog hnf hnbN hnbL
  have hLb : Later Fb G := (keeps_sumcheck _ _ _ _ _ _ _ hsumL).trans hLater
  have hclaimed := HN Fb tN SN (worldE G mask ent)
    (fun j h1 h2 => world_laterG FinalNorm.zt 2 mask hWLa hsumN hLb j h1 h2) hcN hsumN hNdR
    (fun f hf => by
      show vW (worldE G mask ent) f = 0
      rw [← rd_atWorld, hnf f hf, rd_zero]) hnbN
  exact HL F1 tL SL G ent hcL hsumL hLater hreads hwt hlog hnbL
    ⟨hNR.act, hNR.row, hNR.wide, hclaimed⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outWhole
