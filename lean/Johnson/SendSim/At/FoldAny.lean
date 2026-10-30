-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FoldAny.lean: the condition on a spender of the coefficients of a table of any
number of rows that is sent along (FoldSpenderAny), the statement of fresh at the level of rows for
such a spender, and the proof that, if the job fits its place and no seed's factor is 0, the general
model's premise MendsOff holds there. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for the instance
and its names, Johnson/SendSim/At/Bridge.lean, "Terms of the instance". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  FoldSpenderAny    FoldSpender without its clause R.h = 0, "the table has one row". p spends by one
                    entry: the first coins of the oracle message that is sent along, as many as
                    Ride.count. None of them is known. No coin of the tail of any row of that table
                    is known.
  Spec.rowsFreshAny   Spec.rowsFresh with FoldSpenderAny in the place of SpenderClear: its other
                    five premises and its equation are the same. Statement only; proved as
                    rowsFreshAny.
  mendsOffOfAny     Proved here. If the job fits its place (sendFits), no seed's factor is 0 and
                    FoldSpenderAny holds, then MendsOff holds at the instance, for the sets of spent
                    and known names (spentN, knownN, knownT).
  clearOfFoldAny    Proved here, under the same premises: the instance has pads at which these three
                    sets satisfy Sender.Clear.
  foldAny_of_fold   Proved here: FoldSpender implies FoldSpenderAny.

Limits. clearOfFoldAny and mendsOffOfAny speak of sets of names and of contributions: no
distribution is named. The conditions on the book are public. What is proved of them with a coin
spent: Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. FoldSpender is in Johnson/SendSim/At/Fresh.lean, Spec.rowsFresh in
Johnson/SendSim/At/CutTie.lean, MendsOff in Johnson/SendSim/Defs.lean, Sender.Clear in
Johnson/SendSim/Pads.lean, the three sets in Johnson/SendSim/At/ClearOf.lean. rowsFreshAny is proved
in Johnson/SendSim/At/FreshWideProofs.lean; mendsOffOfAny serves it through rowsFreshAny_of_core
(Johnson/SendSim/At/FoldAnyRoad.lean). The proof of clearOfFoldAny is that of clearOfFold
(Johnson/SendSim/At/ClearOfFold.lean), which does not use the clause R.h = 0.
-/
import Johnson.SendSim.At.ClearOfFold
import Johnson.SendSim.At.CutTie

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

/-- p spends the coefficients of a table of any number of rows that is sent along. It spends by one
entry, the first Ride.count coins of that oracle message; no coin of the tail of any row of the
table is known (one); and none of the spent coins is known (unknown). -/
structure FoldSpenderAny (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr) : Prop where
  one : ∃ k R e, k < P.sent.size ∧ ride k = some R ∧ Bk.spentBy o p = [e] ∧
    e.count = ⟨0, R.count⟩ ∧ e.start.e = maskStart P ride k ∧
    ∀ r < (shapeAt P k).maskRows, ∀ q < (maskCodeAt P k).r,
      maskTailNo P ride k r q ∉ eAll (Bk.knownBy ord o p)
  unknown : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p))

/-- FoldSpender implies FoldSpenderAny. -/
theorem foldAny_of_fold {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place}
    {o p : Addr} (F : FoldSpender P ride Bk ord o p) : FoldSpenderAny P ride Bk ord o p := by
  obtain ⟨k, R, e, hk, hr, _, hsp, hc, hst, htl⟩ := F.one
  exact ⟨⟨k, R, e, hk, hr, hsp, hc, hst, htl⟩, F.unknown⟩

/-- States Spec.rowsFresh with FoldSpenderAny in the place of SpenderClear. If the job fits its
place, the challenge consists of exactly the seeds, no seed's factor is 0, the queried positions are
within the bound, WithinAt holds and p satisfies FoldSpenderAny, then over uniform coins the triple
(the runs that p spends, shownR, the known runs) has the same distribution as when the first is
replaced by fresh uniform values, independent of the rest. Statement only; proved as rowsFreshAny in
Johnson/SendSim/At/FreshWideProofs.lean. -/
def Spec.rowsFreshAny : Prop :=
  ∀ (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    sendFits P ride = true → seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    budAt P asks → WithinAt P ride Bk ord o p → FoldSpenderAny P ride Bk ord o p →
    (unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), shownR P first ride data ds asks c,
          cutAll c (Bk.knownBy ord o p))) =
      (unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 (Bk.knownBy ord o p))

/-- If the job fits its place, no seed's factor is 0 and FoldSpenderAny holds, the instance has pads
at which the sets of spent names, known names and known tail coins satisfy Sender.Clear. -/
theorem clearOfFoldAny (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn) (Bk : ProverCoinCounts)
    (ord : List Place) (o p : Addr) (hf : sendFits P ride = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) (F : FoldSpenderAny P ride Bk ord o p) :
    ∃ Pd : (sender P ride).Pads (wOf P ds),
      (sender P ride).Clear (wOf P ds) Pd (spentN P ride Bk o p) (knownN P ride Bk ord o p)
        (knownT P ride Bk ord o p) := by
  obtain ⟨k, R, e, _, hr, hsp, hc, hst, htl⟩ := F.one
  obtain ⟨Pd, hPd⟩ := padsAt ds hf hβ
  refine ⟨Pd, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu hk
    obtain ⟨-, hE, hno⟩ := spent_fold k R e hr hsp hc hst u hu
    have h := (mem_namesOf _ _ u).1 hk
    unfold inNos at h
    rw [hE, if_pos rfl] at h
    exact Finset.disjoint_left.1 F.unknown hno h
  · intro a hu
    have h1 := (spent_fold k R e hr hsp hc hst (Pd.pad a) hu).1
    have h2 : ride a.1 = none := fits_noRide P ride a.1 hf a.1.isLt (by have := a.2.1.isLt; omega)
    rw [hPd.msg a] at h1
    rw [h1, hr] at h2
    cases h2
  · intro a hR
    exact absurd hR (no_reads ds hf k R e hr hsp hc hst a)
  · intro x hx u hu a j _
    by_contra hne
    have hk : (show TailN P from x).1.1 = (show CoinN P ride from u).1 := by
      by_contra h
      exact hne (lay_other_msg (inst := (sender P ride).decCn) hf u a x.1 j h)
    have h1 : ((show TailN P from x).1.1 : ℕ) = k := by
      rw [hk]
      exact (spent_fold k R e hr hsp hc hst u hu).1
    subst h1
    have hm := mask_of_ride hf (show TailN P from x).1 R hr
    obtain ⟨hkn, hq⟩ := known_tail x hx hm
    exact htl _ (rowOf_lt _ hm) _ hq hkn
  · intro x _ a hR
    exact absurd hR (no_reads ds hf k R e hr hsp hc hst a)

/-- If the job fits its place, no seed's factor is 0 and FoldSpenderAny holds, MendsOff holds at the
instance for the sets of spent names, known names and known tail coins: any change of the spent
coins extends to a family of message coins, at which lay is additive, that is 0 on the known ones
and contributes 0 to every answer and to every row with a known tail coin. -/
theorem mendsOffOfAny (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn) (Bk : ProverCoinCounts)
    (ord : List Place) (o p : Addr) (hf : sendFits P ride = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) (F : FoldSpenderAny P ride Bk ord o p) :
    (sender P ride).MendsOff (wOf P ds) (spentN P ride Bk o p) (knownN P ride Bk ord o p)
      (knownT P ride Bk ord o p) := by
  obtain ⟨Pd, hC⟩ := clearOfFoldAny P ride ds Bk ord o p hf hβ F
  exact Sender.mendsOff_of_clear (additive_paid P ride hf) Pd hC

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.clearOfFoldAny
#print axioms OnBytes.SendSim.At.mendsOffOfAny
