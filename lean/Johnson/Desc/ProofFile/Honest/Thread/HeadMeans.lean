-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadMeans.lean: WHAT THE ITEM totalB SAYS AT THE FIRST CHAIN's
LAID LETTERS. The batching's row owes one item, `totalB m`. At `lettersHead`
(Honest/Thread/FirstHead.lean) its sentence is, by unfolding: where the letter `test m` says
nothing of the state, the library's `totalBQ` at what runs behind the batching, at the segment's
group, at the state and at the witness's tables by seat, and the library's test `rw m`. With the
seal's `after_at` what runs behind is the link's own `runBehind`. The second lemma has the form of
the premise `hmeans` of `exchange_totalB_seat` (its share of `ExchangeAtS` at that item): so that
premise is paid at these letters. By unfolding, and one rewrite.

  `head_means_totalB`   the sentence, both ways: by unfolding
  `head_after`          what runs behind, off the data's link
  `head_hmeans`         the premise `hmeans` at these letters

Limits. Nothing shows that the sentence holds at any run. None is one of the library's goals. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.First.Link.Law.TieThreeFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Link)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT totalBQ seatTab)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **WHAT totalB SAYS AT THE LAID LETTERS.** -/
theorem head_means_totalB (m : Nat) (v : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS)
    (y : Strs) (u : WtF) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v (Item.totalB m) a y u ↔
      (test m a.2 = none →
        totalBQ (h.𝔇.after m) (h.𝔇.N.group m) a.2 (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms u) ∧
          h.𝔇.rw m a.2 = true) := Iff.rfl

/-- What runs behind the batching is the link's own, where the data hold that link. -/
theorem head_after {m : Nat} {Lk : Link TS ProofFile.Cl} (hlk : h.𝔇.lk m = some Lk) :
    h.𝔇.after m = Lk.runBehind :=
  VerifiableInference.Desc.LinkJoin.after_at h.𝔇 m Lk hlk

/-- **THE PREMISE `hmeans` AT THE LAID LETTERS.** -/
theorem head_hmeans {m : Nat} {Lk : Link TS ProofFile.Cl} (hlk : h.𝔇.lk m = some Lk)
    (v : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (u : WtF)
    (hh : test m a.2 = none →
      totalBQ Lk.runBehind (h.𝔇.N.group m) a.2 (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms u) ∧
        h.𝔇.rw m a.2 = true) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v (Item.totalB m) a y
      u := by
  refine (head_means_totalB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m v a y u).2 ?_
  rw [head_after h hlk]
  exact hh

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_means_totalB
#print axioms ProofFile.Honest.FirstThread.head_after
#print axioms ProofFile.Honest.FirstThread.head_hmeans
