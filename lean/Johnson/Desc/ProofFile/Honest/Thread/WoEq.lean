-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoEq.lean: the open item `wo m` of the first chain's invariant
passes over the sub-protocol "the one equation" of a segment (kind K9), from that sub-protocol's
clause of `keeps` (`K9.EqKeeps`, Honest/K9/CloseKeeps.lean) and one fact on the state before the
step. WoForward.lean has the general lemma. No definition.

The clause names the verifier's function `K9.door` and writes the state after the step out. The
library has, for every return of that function (Johnson/Desc/First/Link/Law/DoorBlind.lean,
EqLays.lean, RbDef.lean):
  * the codes stay, and every oracle message keeps its shape (`door_both` at `tri`)
  * the oracle messages stay, or all but one message of the segment's own stay (`door_both`)
  * writing the part back leaves `out`, what is left for the row, and the list of commitment trees
    (`out_set`, `leftOf_set`, `rb_putLink`, `rb_putFork`)
So the message of the index masks stays, if it is none of the segment's own messages
(`LinkJoin.OwnNotIndex`, Johnson/Desc/First/Link/Law/FifthTieEq.lean). The library takes the same
fact for the opposite direction (`eq_rowAt`, `wo_back_eq`, FifthTieEq.lean), off the sub-protocol's
accepting step.

  1  `eqKeeps_five`   what the general lemma asks, from the clause and `OwnNotIndex`
  2  `ridesPastAt_wo_eq`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item at
     `lettersHead`

Limits.
  * Part 2: full size only, and only under the library's hypothesis `AtMgA` at the hash function
    `secondHashFunction` (FirstAt.lean says which that is).
  * That `keeps b` gives the clause, that `OwnNotIndex` holds wherever the invariant holds before
    the step (`hne`), and that the message of the index masks is there (`hidx`) are hypotheses. This
    file shows them for no number `b`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WoForward
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.First.Link.Law.FifthTieEq
import Johnson.Desc.First.Link.Law.RidersLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (OwnNotIndex part_reads door_both tri_blind rb_putLink
  rb_putFork door_link leftOf_set out_set rowAt_of_ledger)
open Johnson.Desc.First.Walk.Law (leftOf)
open OnBytes.Means (Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 From the clause -/

/-- After "the one equation": what is left for the row, `out`, the message of the index masks and
the list of commitment trees stay, and the statement extends the one before the step. -/
theorem eqKeeps_five {s s' : S} (k : ProofFile.Honest.K9.EqKeeps s s') (hne : OwnNotIndex s) :
    leftOf s' = leftOf s ∧ s'.out = s.out ∧
      s'.st.oracles[s.out.indexMasks]? = s.st.oracles[s.out.indexMasks]? ∧
      Extends s.st s'.st ∧ s'.book = s.book := by
  obtain ⟨a, o, ha, hdoor, rfl⟩ := k.laid
  obtain ⟨hL, hst⟩ := part_reads s a ha
  obtain ⟨e1, e2⟩ := door_both tri_blind _ _ _ _ _ _ hdoor
  rw [hst] at e1 e2
  have hb := ((rb_putLink s a.L o.L hL
    (by rw [door_link _ _ _ _ _ _ hdoor])).trans
    (rb_putFork _ o.F)).book
  refine ⟨leftOf_set s _, out_set s _, ?_, ⟨e1.1, fun j x hx => ?_⟩, hb⟩
  · rcases e2 with e | ⟨m, o', ho, hj⟩
    · show o.d.st.oracles[s.out.indexMasks]? = _
      rw [e]
    · exact hj _ (Ne.symm (hne a ha m o' ho))
  · have e := e1.2 j
    rw [hx] at e
    obtain ⟨x', h1, h2⟩ := Option.map_eq_some_iff.1 e
    exact ⟨x', h1, congrArg (·.1) h2⟩

/-! ## 2 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `wo m` passes over a sub-protocol whose `keeps` gives the clause of "the one equation",
if, wherever the invariant holds before the step, the message of the index masks is there and is
none of the open segment's own messages. -/
theorem ridesPastAt_wo_eq {b : Nat} (m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ProofFile.Honest.K9.EqKeeps s s')
    (hne : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      OwnNotIndex s)
    (hidx : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.out.indexMasks < s.st.oracles.size) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.wo m) :=
  ridesPastAt_wo_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m
    fun k s mm E s' hA hK => by
      obtain ⟨e1, e2, e3, e4, e5⟩ := eqKeeps_five (hk s s' hK) (hne k s mm E hA)
      refine ⟨rowAt_of_ledger e2 e1 (by rw [e3]) _ _ _,
        hidx k s mm E hA, e4, fun o _ => ?_⟩
      rw [e5]
      exact ⟨rfl, fun _ _ => rfl⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.eqKeeps_five
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_wo_eq
