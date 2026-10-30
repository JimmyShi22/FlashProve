-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointArms.lean: NOT IN FRONT OF A LAW OVER COINS. The clause
taken of a stand of the last chain's proximity test (StandRest.taken, WTable.lean), at a job with
Omega's member: tree 2 shown, trees 0 and 1 by one named premise.

  FirstArms            the premise: at a stand, at the coins lent, trees 0 and 1 are the first chain's
                       tables at .taken 0 1 and .taken 0 82
  tree2_at_W           TakenIs at tree 2, from the table's arm at the shared chain
  taken_of_arms        the clause

By what. omega_is_sent (AtFullSide/K12/LettersAtHead.lean), lendRow_second (K12/TableOfRun.lean),
tree_third_column (WJointOmega.lean), taken_omega, omega_data_behind (WJointTaken.lean).

Limits.
  * FirstArms binds the first chain's table, a letter of that thread, and it can be false.
  * harm, the arm, is the shared thread's; hask, hdue, hcover, hdepth and OmegaAtW are public or of
    the letters, each named.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTaken
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAccepted
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun
import AtFullSide.K12.LettersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Place)
open ProofFile.Honest.K14 (SendPub jobOmega Ask sendTable sendingPart)
open ProofFile.Honest.K12.AtProof (senderO placeW)
open AtFullSide.K12 (omega_is_sent rowOF)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

variable {S Cl V Pb W₂ W X : Type} {Bk : ProverCoinCounts}

/-- **Trees 0 and 1 at the first chain's tables**, at a stand, at the coins lent. The one named
premise. -/
def FirstArms (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → ProofFile.Honest.Mid W X → Prop)
    (A : ManyJob W X) : Prop :=
  ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest]),
    ThrS T Said 2 k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest] 0 = .ok c →
    TakenIs T k m
        (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
          (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
        0 (.taken 0 1) ∧
      TakenIs T k m
        (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
          (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
        1 (.taken 0 82)

section
variable (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk)
  (T : Thread Bk S Cl V W X Pb) (A : ManyJob W X) (mA mB : Mem W X) (An : SendPub) (n r₁ f : ℕ)
  (fs : Option ℕ × Option ℕ) (ask : W → Ask) (wit : W₂ → Ask) (toCommon : W → W₂)
  (Pu : OmegaAtW A mA mB An n fs ask) (hn : n = r₁ + An.atPoint) (hch : T.chain = 2)
  (hpl : A.p.place = placeW)
  (hrow : ProofFile.Honest.K12.AtProof.msgOf senderO (jobOmega ⟨An.P, n⟩) 0 = AtFullSide.K12.rowOF)
  (harm : T.table (.taken 1 1) = fun k w h =>
    sendTable (jobOmega An) wit senderO.place 1 0 k (toCommon w) (h.drop r₁))
  (hfix : T.fixed (.taken 1 1) = r₁ + f) (hf : An.atPoint + 1 ≤ f)
  (hask : ∀ w, (ask w).rows = (wit (toCommon w)).rows)
  (hdue : (sendingPart (jobOmega An)).takes = dueAt AtFullSide.K14.rawRowsSharedW senderO)
  (hcover : ∀ k : Coins Bk, ∃ own, (k.look 1 ⟨senderO.place, 0⟩).2.cut ⟨0, 0⟩
    (sendingPart (jobOmega An)).takes = some own)
  (hdepth : ∀ (k : Coins Bk) (c : W₂) (h : List Fmt.Drawn),
    (sendTable (jobOmega An) wit senderO.place 1 0 k c h).2.logLength = 22)
include hB Pu hn hch hpl hrow harm hfix hf hask hdue hcover hdepth

/-- **Tree 2 at the shared chain's table.** -/
theorem tree2_at_W (k : Coins Bk) (m : ProofFile.Honest.Mid W X)
    (c : RowCoins [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
      [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest] 0 = .ok c) :
    TakenIs T k m
      (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
        (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
      2 (.taken 1 1) := by
  subst hn
  rw [hch, hpl] at hc
  have hl := lendRow_second hc
  obtain ⟨own, hcut⟩ := hcover k
  obtain ⟨c₀, h₀, ec⟩ := cut_same_due hdue hcut
  have hd := omega_data_behind An.P r₁ An.atPoint f (ask m.st.input) (wit (toCommon m.st.input))
    (hask _) m.st.heard hf
  have hrw := omega_is_sent hB (j := 1) (by simp) k hl An (r₁ + An.atPoint) fs ask hrow h₀
    m.st.input (frontOf m) ⟨wit (toCommon m.st.input), (m.st.heard.take (r₁ + f)).drop r₁, ()⟩ hd
  refine taken_omega T k m _ (jobOmega An) wit senderO.place r₁ toCommon harm hcut Pu.width ?_ ?_
  · rw [depth_three A mA mB _ Pu.mems m.st.input (frontOf m) _ _ 2 22 [.main 2] Pu.tree]
    have e : T.tableAt (.taken 1 1) k m = sendTable (jobOmega An) wit senderO.place 1 0 k
        (toCommon m.st.input) ((m.st.heard.take (T.fixed (.taken 1 1))).drop r₁) := by
      show T.table (.taken 1 1) k m.st.input (m.st.heard.take (T.fixed (.taken 1 1))) = _
      rw [harm]
    rw [e, hdepth]
  · intro x
    rw [hfix, ← ec]
    exact tree_third_column A mA mB An (r₁ + An.atPoint) senderO fs ask Pu.mems Pu.tree m.st.input
      (frontOf m) (restCoins A.toRun.toTest c.2.1) x _ hrw Pu.stage Pu.code Pu.base Pu.room
      Pu.clear₀ Pu.clear₁ Pu.mine Pu.noMask

/-- **The clause taken.** -/
theorem taken_of_arms (Said : ℕ → Coins Bk → ProofFile.Honest.Mid W X → Prop) (first : FirstArms T Said A) :
    ∀ k st m E (c : RowCoins [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest]),
      ThrS T Said 2 k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) A.p.place
        [(firstPart A.toRun.toTest : Part W W X), restPart A.toRun.toTest] 0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs T k m
        (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
          (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
        i takenLast[i] := by
  intro k st m E c u hc i hi
  have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
  have hi3 : i < 3 := by
    rw [e] at hi
    exact hi
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · simpa [e] using (first k st m E c u hc).1
  · simpa [e] using (first k st m E c u hc).2
  · simpa [e] using tree2_at_W hB T A mA mB An n r₁ f fs ask wit toCommon Pu hn hch hpl hrow harm hfix
      hf hask hdue hcover hdepth k m c hc

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.FirstArms
#print axioms ProofFile.Honest.K12.AtFile.tree2_at_W
#print axioms ProofFile.Honest.K12.AtFile.taken_of_arms
