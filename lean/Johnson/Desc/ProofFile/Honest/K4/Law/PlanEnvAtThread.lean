-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PlanEnvAtThread.lean: CONDITIONAL.

What is here. `planEnvB_at_head` (Law/PlanEnvAtBatch.lean: the premise of the runs "front" and "back" of the feed-forward layers' own rounds, sub-protocol
K4, on the road on shapes) IN THE FORM IN WHICH THE BATCHING's HOUSE TAKES IT for its field "batch" (its premise env; its file is no row yet, so the
text of its `StandJ` is written out): AT ANY THREAD T over the first chain's list that counts its columns from 0 and begins at the description's own
first state: wherever T stands, with Said, in front of the batching of the layers' segment 2 g (border 14 (2 g) + 8 + 1), and J holds there:
`planEnvB Bs.G₀.W.layers s = true`. Said, J: letters; neither is read.

  **`planEnvB_env`**   one call of `thr_reach_of` (Honest/Thread/ReachBack.lean) and one of `planEnvB_at_head`

Limits. THAT T STANDS ANYWHERE is not shown; where it stands nowhere the statement is idle. hbs, hft and hstart are premises on T; that
word they hold at `lettersHead`'s thread; not shown here. Under the head `P5J.AtMgA`; THE FULL SIZE ALONE; the format's second hash function alone.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PlanEnvAtBatch
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Rt (planEnvB)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)

/-- CONDITIONAL on h, hB, hbs, hft and hstart. **THE PREMISE env OF THE FIELD "batch".** -/
theorem planEnvB_env {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) :
    ∀ g, g < 12 → ∀ s, (∃ k m E, ThrS T Said (14 * (2 * g) + 8 + 1) k s m E ∧ J (14 * (2 * g) + 8 + 1) s) →
      planEnvB Bs.G₀.W.layers s = true := by
  rintro g hg s ⟨k, m, E, hT, -⟩
  obtain ⟨z, h0⟩ := hstart k m.st.input (m.st.heard.take T.front)
  have hb : 14 * (2 * g) + 8 + 1 ≤ T.bs.length := by
    rw [hbs, Johnson.AtFull.Shape.flat_len h]
    omega
  have hR := thr_reach_of T (ProofFile.startS Zp) z hb h0 hT.1
  rw [hbs, hft, show 14 * (2 * g) + 8 + 1 = 28 * g + 9 from by omega] at hR
  exact planEnvB_at_head h hB hg hR

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.planEnvB_env
