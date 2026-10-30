-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY PROVER: the prover H is a letter of the thread. The law is on the verifier's states in front
of and behind the lookup on the digits of the head's link, at the first chain's letters at the
library's head. Of H one law is spent, inside `thrS_reach_below`: `storedWords_lt`
(Honest/Law/Run.lean), which holds of every prover.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupWeightsGoOn.lean: the kind "lookup" (K3): what the item
"forms 24 4 weights" says besides its runs, the sentence `wt 24` on the weights, goes on past the
lookup on the digits of the head's link (border 345). Theorems; no definition; nothing is evaluated.

What is shown.
  `headsDigitsKeepWhatTheWeightsSentenceReads`: on states alone: the lookups' clause of "keeps" at
    the digits of the head's link gives the library's `KeptW`
    (Johnson/Desc/Kinds/Law/WeightAtSame.lean).
  `weightsSentenceGoesOnPastTheHeadsDigits`: **from the invariant in front and the thread's "keeps"
    at border 345: what `wt 24` says at the state in front it says at the state behind**, at all
    strings.

How the proof goes. The invariant gives that the state in front is reached (`thrS_reach_below`,
Honest/Thread/ReachAtHead.lean); at a state reached at border 345 the head's own rounds are heard
(`P5J.heard_345`, Johnson/P5J/K03WtBackAt.lean); under `KeptW` and that, the sentence holds at both
states or at none (`weightAt_kept`). The library spends the same three for the way back
(`P5J.k03_hWt`).

At which letters. The structure of letters is the thread's own: the head's `h.𝔇` with the decoder
and the carried sentence set; the field `wt` is not turned by that.

Hypotheses that remain. `h`: `P5J.AtMgA`. `saidGivesWordsBelowThePrime`: the letter `Said` gives
`SaidOk`. `keepsGivesTheLookupClause`: the letter f at the kind K3 implies `k3KeepsAt`.
`invariantInFront`, `kept`: the invariant in front; the thread's "keeps" across the border.

Limits. An implication: nothing here shows that the invariant holds at any run. The full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono
import Johnson.P5J.K03WtBackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.Kinds.Head.Law (KeptW weightAt_kept)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script thrS_reach_below)
open ProofFile.Honest.K3.Law.AtThr

/-- The clause of "keeps" at the digits of the head's link keeps what the sentence on the weights
reads. -/
theorem headsDigitsKeepWhatTheWeightsSentenceReads {shape : OnBytes.Model.Forest.Shape}
    {s s' : TS} (kept : K3KeepsHead shape s s') : KeptW s s' := by
  obtain ⟨-, tl, F, H, G, a₀, claim, -, fork, here, opened, rfl, ledger⟩ := kept
  have forkIs : s.fork? = some a₀.F := by
    simp [VerifiableInference.Desc.First.S.fork?, here, opened]
  obtain rfl : F = a₀.F := Option.some.inj (fork.symm.trans forkIs)
  exact ⟨a₀, _, here, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ledger.1⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

set_option maxHeartbeats 4000000 in
/-- **THE SENTENCE ON THE WEIGHTS GOES ON PAST THE LOOKUP ON THE DIGITS OF THE HEAD's LINK.**
Conditional on the head, the two arrows, the invariant in front and the thread's "keeps". -/
theorem weightsSentenceGoesOnPastTheHeadsDigits
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (invariantInFront : ThrS (LK).thread Said (borderOf 24 true) k s m E)
    (kept : (LK).thread.keeps (borderOf 24 true) s s') (y y' : Strs) (v : WtF)
    (said : ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } : _).wt 24
      (m.st.input.x.pub, s) y v) :
    ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } : _).wt 24
      (m.st.input.x.pub, s') y' v := by
  obtain ⟨shape, atHead⟩ := lookupClauseAtTheHeadsDigits h
    (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
      keepsGivesTheLookupClause (show 24 < 25 by omega) true kept)
  have keptW := headsDigitsKeepWhatTheWeightsSentenceReads atHead
  have invariant : ThrS (LK).thread SaidOk 345 k s m E :=
    thrS_mono _ saidGivesWordsBelowThePrime invariantInFront
  obtain ⟨member, memberAtBorder, -⟩ :=
    member_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w 24 (by omega) true
  have memberInTheChain : cF.blocksInOrder[345]? = some member := memberAtBorder
  have borderInTheChain : 345 ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 memberInTheChain).1
  have reached := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    borderInTheChain invariant
  obtain ⟨Bs, base, opened⟩ := h.laid.opened
  obtain ⟨-, heard⟩ := P5J.heard_345 h.scope h.reads opened h.laid.planOk reached
  rw [opened.W] at heard
  have said' : VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 24
      (m.st.input.x.pub, s) y v := said
  show VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 24
      (m.st.input.x.pub, s') y' v
  intro isTheHeadsLink cellsInRange
  exact (weightAt_kept (P5J.At.X Zp) keptW heard _ _).2 (said' isTheHeadsLink cellsInRange)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.headsDigitsKeepWhatTheWeightsSentenceReads
#print axioms ProofFile.Honest.K3.Term.weightsSentenceGoesOnPastTheHeadsDigits
