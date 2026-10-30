-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsAll.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), whole but for one number.
The files FHeadKeepsA.lean to FHeadKeepsJ.lean, Law/NoHouse/KeepsFrameStep.lean, Law/KeepsAtK8.lean
and Law/KeepsAtK4.lean prove, family by family, that an accepting step of the sub-protocol at a
number gives the clause of `fHead` at its place. Here `head_hK_of_familiesM` (SteppedYesMark.lean)
puts them together. The arguments of `fHead` are those at which the families are proved: `Bs.G₀`,
`P1L20.bearing`, `K11.parOf Zp Bs.G₀` and `K13.whereOf Zp`, where `Bs` is what `ProofFile.baseOf` returns
at the public part. No definition.

  1  `borderOf_lt`   the number of a lookup in a segment other than the output head's
  2  `fHead_hear`   the clause at the sub-protocols before a segment's batching
  3  `fHead_hK`   the column `hK`

What `fHead_hK` leaves as a hypothesis: `h354`, the clause at number 354, the proximity test (K12).
No lemma proves it yet.

Limits.
  * That an accepting step exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYesMark
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsA
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsB
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsC
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsD
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsE
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsF
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsG
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsH
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsI
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsJ
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrameStep
import Johnson.Desc.ProofFile.Honest.Law.KeepsAtK8
import Johnson.Desc.ProofFile.Honest.Law.KeepsAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- The number of a lookup in a segment other than the output head's. -/
theorem borderOf_lt {l : Nat} (hl : l < 24) (d : Bool) :
    borderOf l d = 14 * l + (if d then 6 else 1) + 2 := by
  unfold borderOf ixOf
  rw [if_neg (show ¬ l = 24 by omega)]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p12 : VerifiableInference.Desc.K12.P12)

include h

/-- **The clause at the sub-protocols before a segment's batching.** -/
theorem fHead_hear {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {l : Nat} (hl : l < 25)
    {i : Nat} (hi : i < IM.nAt l) :
    ∀ blk, cF.blocksInOrder[14 * l + i + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s' := by
  by_cases h24 : l = 24
  · subst h24
    rw [nAt_head] at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fHead_keeps_k7 h _ _ _ _ hB
    · exact fHead_keeps_k2_head h _ _ _ _ _
    · exact fHead_keeps_k3 h _ _ _ _ _ (l := 24) (by decide) false
    · exact fHead_keeps_k6 h _ _ _ _ _
    · exact fHead_keeps_k1 h _ _ _ _ _ (l := 24) (i := 4) (by decide) rfl (by decide)
    · intro blk hb s s' hy
      obtain ⟨hk, hc⟩ := k8_keeps_head h blk hb
      rw [hk]
      exact hc s s' hy
    · exact fHead_keeps_k1 h _ _ _ _ _ (l := 24) (i := 6) (by decide) rfl (by decide)
    · exact fHead_keeps_k3 h _ _ _ _ _ (l := 24) (by decide) true
    · exact fHead_keeps_k11 h _ _ _ _ hB
  · have hl' : l < 24 := by omega
    rw [nAt_lt hl'] at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    obtain ⟨g, hg, hgl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    have k3 : ∀ d : Bool, ∀ blk, cF.blocksInOrder[14 * l + (if d then 6 else 1) + 2]? = some blk →
        ∀ s s', StepYes 0 blk s s' →
        fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s' := by
      intro d blk hb
      rw [← borderOf_lt hl' d] at hb
      exact fHead_keeps_k3 h _ _ _ _ _ hl d blk hb
    rcases hgl with rfl | rfl
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases g0 : g = 0
        · subst g0
          exact fHead_keeps_two h _ _ _ _ _
        · exact fHead_keeps_k2_link h _ _ _ _ _ (by omega) hl'
      · exact k3 false
      · intro blk hb s s' hy
        obtain ⟨hk, hc⟩ := k4_keeps_lay h hg blk hb
        rw [hk]
        exact hc s s' hy
      · exact fHead_keeps_k1 h _ _ _ _ _ hl (head_kind_lay hg rfl) (by decide)
      · intro blk hb s s' hy
        obtain ⟨hk, hc⟩ := k8_keeps_lay h hg blk hb
        rw [hk]
        exact hc s s' hy
      · exact fHead_keeps_k1 h _ _ _ _ _ hl (head_kind_lay hg rfl) (by decide)
      · exact k3 true
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fHead_keeps_k2_link h _ _ _ _ _ (by omega) hl'
      · exact k3 false
      · exact fHead_keeps_k5 h _ _ _ _ _ hg
      · exact fHead_keeps_k1 h _ _ _ _ _ hl (head_kind_att hg rfl) (by decide)
      · intro blk hb s s' hy
        obtain ⟨hk, hc⟩ := k8_keeps_att h hg blk hb
        rw [hk]
        exact hc s s' hy
      · exact fHead_keeps_k1 h _ _ _ _ _ hl (head_kind_att hg rfl) (by decide)
      · exact k3 true

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The column `hK` at `fHead`**, from the clause at number 354. -/
theorem fHead_hK (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (h354 : ∀ blk, cF.blocksInOrder[354]? = some blk → ∀ s s', s.failed = none → StepYes 0 blk s s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s') :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s' := by
  refine head_hK_of_familiesM h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
      (VerifiableInference.Desc.K13.whereOf Zp))
    (K := fun b => ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ s s', s.failed = none → StepYes 0 blk s s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) p12
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s')
    (fun _ => Iff.rfl) ?_ ?_ ?_ ?_ ?_ h354 ?_ ?_ ?_
  · intro blk hb s s' h0 hy
    obtain ⟨hk, hc⟩ := frame_keeps_front h P1L20.bearing blk hb
    rw [hk]
    exact hc s s' h0 hy
  · intro l hl blk hb s s' _ hy
    obtain ⟨hk, hc⟩ := frame_keeps_laid h P1L20.bearing hl blk hb
    rw [hk]
    exact hc s s' hy
  · intro l hl i hi blk hb s s' _ hy
    exact fHead_hear h p12 hB hl hi blk hb s s' hy
  · intro l hl j j2 j7 blk hb s s' h0 hy
    have hc : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fHead_keeps_bat h _ _ _ _ _ hl blk hb s s' hy
    · obtain ⟨hk, hc⟩ := frame_keeps_behind h P1L20.bearing hl blk hb
      rw [hk]
      exact hc s s' h0 hy
    · exact fHead_keeps_eq h _ _ _ _ _ hl blk hb s s' hy
    · exact fHead_keeps_k10 h _ _ _ _ _ hl blk hb s s' hy
    · exact fHead_keeps_shut h _ _ _ _ _ hl blk hb s s' hy
    · obtain ⟨hk, hc⟩ := frame_keeps_cleared h hl blk hb
      rw [hk]
      exact hc s s' hy
  · intro blk hb s s' _ hy
    exact fHead_keeps_k2_finish h _ _ _ _ _ blk hb s s' hy
  · intro blk hb s s' _ hy
    exact fHead_keeps_k13 h _ _ _ _ blk hb s s' hy
  · intro blk hb s s' _ hy
    exact fHead_keeps_w h _ _ _ _ blk hb s s' hy
  · intro blk hb s s' _ hy
    obtain ⟨hk, hc⟩ := frame_keeps_seal h P1L20.bearing blk hb
    rw [hk]
    exact hc s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.borderOf_lt
#print axioms ProofFile.Honest.FirstThread.fHead_hear
#print axioms ProofFile.Honest.FirstThread.fHead_hK
