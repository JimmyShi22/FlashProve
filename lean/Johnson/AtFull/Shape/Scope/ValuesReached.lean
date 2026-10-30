-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ValuesReached.lean: FOUR FIELDS OF SortValues (ValuesFold.lean) PAID: the code switch
at the links 1 to 23, the finish, the 24 closings and the head's: 49 members. Their tests "on values" (switchW,
closeInOrdB) are tests on structure that accept at every state reached at a border up to 353
(switchW_under_head, LinkGuardCell.lean; closeInOrdB_reached, CloseInOrder.lean); a thread's pair gives
"reached" by reach_below (Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean). Under the head. Nothing is
evaluated.

WHAT IT READS OF THE THREAD: `ReachSeat`, five clauses: T.bs = cF.blocksInOrder · T.ft = 0 · at a valid input the chain
begins at ProofFile.startS Zp z for one z · what is stored is below the prime · Said gives SaidOk.

Limits. THAT A THREAD MEETS ReachSeat IS NOT SHOWN HERE. At a Said that never holds, at a thread whose Thr never
holds, the laws are idle. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValuesFold
import Johnson.AtFull.Shape.LinkGuardCell
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain fieldPrimeWord)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Coins Mid ProverCoinCounts Env ValuesJ ThrS SaidOk reach_below)

/-- **What the four fields read of the thread.** It is a definition: a premise's form. -/
structure ReachSeat {V W X Pb : Type} {Bk : ProverCoinCounts} (Zp : ProofFile.Pub) (cF : Chain S ProofFile.Cl)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) : Prop where
  bs : T.bs = cF.blocksInOrder
  ft : T.ft = 0
  begun : ∀ k w hh, T.valid w → ∃ z : ProofFile.InstPub, ∀ s₀, T.begun k w hh s₀ → s₀ = ProofFile.startS Zp z
  stored : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord
  said : ∀ b k m, Said b k m → SaidOk b k m

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S ProofFile.Cl V W X Pb}
  {Said : Nat → Coins Bk → Mid W X → Prop}

/-- **From the thread's pair to the library's "reached".** -/
theorem reach_of_seat (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : ReachSeat Zp cF T Said) {b : Nat}
    (hb : b ≤ 358) {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hA : ThrS T Said b k s m E) :
    ∃ z, Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) b (z, s) := by
  have hv : T.valid m.st.input := by
    have h1 := hA.1
    unfold ProofFile.Honest.Thr at h1
    exact h1.2.2.2.2.2.2
  obtain ⟨z, hz⟩ := R.begun k m.st.input (m.st.heard.take T.front) hv
  have e := reach_below T (ProofFile.startS Zp) z (b := b) (k := k) (s := s) (m := m) (E := E)
    (by rw [R.bs, flat_len h]; exact hb) hz R.stored ⟨hA.1, R.said _ _ _ hA.2⟩
  rw [R.ft, R.bs] at e
  exact ⟨z, e⟩

section
variable (Zq : ProofFile.Pub) (G : ProofFile.Ground) (s : S) (rs : List Fmt.RoundView)
  (gs : List (List (Nat × List UInt64)))

theorem switch_v (l : Nat) (h : switchW s = true) : (Tab.switch Zq G l).2 s rs gs = true := by
  unfold Tab.switch
  repeat' split
  all_goals first | rfl | exact h

theorem finish_v (h : switchW s = true) : (Tab.finish Zq G).2 s rs gs = true := by
  unfold Tab.finish
  repeat' split
  all_goals first | rfl | exact h

theorem close_v (l : Nat) (h : closeInOrdB s = true) : (Tab.close Zq l).2 s rs gs = true := by
  unfold Tab.close
  repeat' split
  all_goals first | rfl | exact h

end

variable {J : Nat → S → Prop} {fall : Nat → S → List Fmt.Drawn → Option String} {G : ProofFile.Ground}

/-- **The code switch at the links 1 to 23.** -/
theorem switch_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : ReachSeat Zp cF T Said) (l : Nat)
    (h0 : 0 < l) (hl : l < 24) :
    ValuesJ T Said J (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (14 * l + 1 + 1) := by
  intro blk _ k s m E ds y cols hA _ _ _ _ _
  obtain ⟨z, hr⟩ := reach_of_seat h R (by omega) hA
  show Tab.vals Zp G (14 * l + 1 + 1) s _ _ = true
  unfold Tab.vals Tab.cells
  rw [table_link _ _ _ _ l 1 hl (by omega)]
  show (if l == 0 then Tab.opening Zp G else Tab.switch Zp G l).2 s _ _ = true
  rw [if_neg (by simp; omega)]
  exact switch_v Zp G s _ _ l (switchW_under_head h (by omega) hr)

/-- **The finish.** -/
theorem finish_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : ReachSeat Zp cF T Said) :
    ValuesJ T Said J (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (353 + 0) := by
  intro blk _ k s m E ds y cols hA _ _ _ _ _
  obtain ⟨z, hr⟩ := reach_of_seat h R (by omega) hA
  show Tab.vals Zp G (353 + 0) s _ _ = true
  unfold Tab.vals Tab.cells
  rw [table_back _ _ _ _ 0]
  exact finish_v Zp G s _ _ (switchW_under_head h (by omega) hr)

/-- **The closings at the links 0 to 23.** -/
theorem close_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : ReachSeat Zp cF T Said) (l : Nat)
    (hl : l < 24) :
    ValuesJ T Said J (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (14 * l + 11 + 1) := by
  intro blk _ k s m E ds y cols hA _ _ _ _ _
  obtain ⟨z, hr⟩ := reach_of_seat h R (by omega) hA
  show Tab.vals Zp G (14 * l + 11 + 1) s _ _ = true
  unfold Tab.vals Tab.cells
  rw [table_link _ _ _ _ l 11 hl (by omega)]
  exact close_v Zp s _ _ l (closeInOrdB_reached h (by omega) hr)

/-- **The closing at the head's link.** -/
theorem closeHead_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : ReachSeat Zp cF T Said) :
    ValuesJ T Said J (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (337 + 13) := by
  intro blk _ k s m E ds y cols hA _ _ _ _ _
  obtain ⟨z, hr⟩ := reach_of_seat h R (by omega) hA
  show Tab.vals Zp G (337 + 13) s _ _ = true
  unfold Tab.vals Tab.cells
  rw [table_head _ _ _ _ 13 (by omega)]
  exact close_v Zp s _ _ 24 (closeInOrdB_reached h (by omega) hr)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reach_of_seat
#print axioms Johnson.AtFull.Shape.switch_values
#print axioms Johnson.AtFull.Shape.finish_values
#print axioms Johnson.AtFull.Shape.close_values
#print axioms Johnson.AtFull.Shape.closeHead_values
