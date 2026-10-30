-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeptRuns.lean: the three runs of claims of the lookup's make that are run in
front of the run "policy" in the output head's segment keep all that `KeptAll`
(Reads/RowAtSeat.lean) asks.

What is shown. Steps: they speak of the written sub-protocol `K3.Law.blockVia`
(Johnson/Desc/First/Look/Via/Via.lean), of the run `K3.joinRun`
(Johnson/Desc/First/Look/K3Runs.lean) and of the routine `Look.joinF`
(Johnson/Desc/First/Look/LookClaims.lean), at the lookup's seat on a segment's calls
(`K3.seatCalls`, Johnson/Desc/First/Look/K3Seat.lean).
  `paid_cols`: marking an owed claim as added leaves every array's number of columns.
  `joinF_cols`: so does the routine that makes the claim of the run "join": of the ledger it writes
    that mark alone.
  `keptAll_joinRun`: **where the run "join" accepts, `KeptAll` holds**, with no premise on the
    ledger.
  `keptAll_lookRuns`: **where the run "objects" or the run "guests" of the lookup's sub-protocol
    accepts, `KeptAll` holds.** The first writes the mark alone; the second returns the state as it
    stood.

Limits. Still owed between the fifth place and the run "policy": the decisions of the lookup on the
digits, of the merge, and of the batching's own draw. Nothing on soundness.


-/
import Johnson.Desc.Reads.KeptLedger
import Johnson.Desc.First.Look.Via.Via
import OnBytes.Desc.First.P1.FlSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Fork Aff)
open OnBytes.Desc.First.P1 (bind_some pure_some must_some change_some)
open VerifiableInference.Desc (K3.seatCalls K3.joinRun)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok ReadsQuiet.named_ok)

/-- Marking an owed claim as added. -/
theorem paid_cols (F : Fork) (j i : ℕ) : colsAt (F.paid j) i = colsAt F i := rfl

/-- The routine that makes the claim of the run "join". -/
theorem joinF_cols (g : OnBytes.Model.Forest.Heard) (KF : Array Aff) (F : Fork)
    (x : Aff × Fork × OnBytes.K.Kc.Tape)
    (h : VerifiableInference.Desc.First.Look.joinF g KF F [] = some x) (i : ℕ) :
    colsAt x.2.1 i = colsAt F i := by
  obtain ⟨f, G, u⟩ := x
  unfold VerifiableInference.Desc.First.Look.joinF at h
  obtain ⟨_, F1, t1, h1, h⟩ := bind_some.1 h
  obtain ⟨-, rfl, rfl⟩ := must_some.1 h1
  obtain ⟨_, F2, t2, h2, h⟩ := bind_some.1 h
  unfold VerifiableInference.Desc.First.Look.joinAddedF
    VerifiableInference.Desc.First.Look.paidF at h2
  obtain ⟨e2, rfl⟩ := change_some.1 h2
  obtain ⟨-, rfl, -⟩ := pure_some.1 h
  rw [← Option.some.inj e2]
  exact paid_cols _ _ i

/-- **Where the run "join" accepts.** -/
theorem keptAll_joinRun {Cl : Type} (claim : Aff → Cl) (keys : S → Option (Array Aff)) (i : ℕ)
    {n : ℕ} {s : S} {y : List Cl × S} (hr : K3.joinRun (K3.seatCalls claim) keys n s = .ok y) :
    KeptAll i s y.2 :=
  keptAll_join claim keys i hr fun g KF F x h => joinF_cols g KF F x h i

/-- **Where the run "objects" or the run "guests" accepts.** -/
theorem keptAll_lookRuns {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : VerifiableInference.Desc.First.Look.P)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl))
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ (VerifiableInference.Desc.K3.Law.blockVia (K3.seatCalls claim) piece laid before p
      guests).claims) {n : ℕ} {s : S} {y : List Cl × S} (hr : c.2 n s = .ok y) (i : ℕ) :
    KeptAll i s y.2 := by
  unfold VerifiableInference.Desc.K3.Law.blockVia at hc
  dsimp only at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · dsimp only at hr
    obtain ⟨F, h1, hr⟩ := ReadsQuiet.bind_ok hr
    obtain ⟨g, _, hr⟩ := ReadsQuiet.bind_ok hr
    have e := congrArg Prod.snd (Except.ok.inj hr)
    rw [← e]
    refine keptAll_putFork i s (F.paid g.owedObjects) fun F' hF' => ?_
    have hF : s.fork? = some F := ReadsQuiet.named_ok h1
    rw [hF] at hF'
    rw [← Option.some.inj hF']
    exact paid_cols _ _ i
  · obtain rfl := List.mem_singleton.1 hc
    dsimp only at hr
    have h2 := ReadsQuiet.named_ok hr
    cases hm : guests.mapM fun g => g.form s with
    | none =>
      rw [hm] at h2
      cases h2
    | some l =>
      rw [hm] at h2
      rw [← Option.some.inj h2]
      exact keptAll_refl i s

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.paid_cols
#print axioms VerifiableInference.Reads.AtSeat.joinF_cols
#print axioms VerifiableInference.Reads.AtSeat.keptAll_joinRun
#print axioms VerifiableInference.Reads.AtSeat.keptAll_lookRuns
