-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsHead.lean: THE TESTS ON THE LETTERS (`Thread.fits`) AT THE
FIRST CHAIN's THREAD AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean): the
premise f₁ of `sits_at_head` (Honest/Thread/SitsHead.lean), CUT. By `Thread.fits_of`
(Honest/Thread/Fits.lean). One lemma.

  `fits_head`

PAID HERE. (ii) rounds against oracle messages at every member: from the head's own field that the
plan's tests pass (`head_planOk`, Honest/Thread/FirstSits.lean): no evaluation · (iii) no tree is
taken over · (v) near = front = 0: both by unfolding.
LEFT, BY NAME. hone: (i) in its one-pass form (`fwdFit_of_opens`, Honest/Thread/FirstFits.lean), at
the library's own written lists P5J.At.links and P5J.At.ps: a Bool on written lists alone · hfix:
(iv): at every border each tree that the members in front have stated is fixed by the rounds in
front: A PREMISE ON THE SCRIPT's LETTER fixed.

Limits. THE FULL SIZE ALONE. The library's head has a member at the name under four premises on the
public files (the seal's `P5J.head_exists_at_name`); this file does not call it; no member of the
head together with the thread's sentence is shown. `lettersHead` is without code: no test with code
reaches the thread itself. None is one of the library's goals. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.Thread.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (start)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open FirstRows (opens rowAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`Thread.fits` AT THE HEAD's FIRST THREAD.** A conditional lemma on our own definitions. It is
none of the library's goals. -/
theorem fits_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hone : (((opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ((rowAt P5J.At.links x.2).asks ++ (rowAt P5J.At.links x.2).shuts).all x.1.contains) = true)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fits
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true := by
  refine Thread.fits_of _ (FirstRows.fwdFit_of_opens hone _)
    (fun z hz => ((planOk_all (head_planOk h)).1 z hz).2) (fun σ hσ => ?_)
    (fun b hb σ hσ => ?_) (Nat.le_refl 0)
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · have hσ' : σ ∈ (List.range (treesTo cF.blocksInOrder b)).map Fmt.TreeSource.own := hσ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hσ'
    show Q.fixed (.own j) ≤ 0 + roundsTo cF.blocksInOrder b
    rw [Nat.zero_add]
    exact hfix b hb j (List.mem_range.1 hj)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fits_head
