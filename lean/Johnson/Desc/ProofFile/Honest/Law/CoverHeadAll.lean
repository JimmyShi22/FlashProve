-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverHeadAll.lean: the bound of `falls_asks`
(Honest/Law/CoverAsks.lean) on the chance that a run meets a fall, at the proof file's description
`P5J.F0T o Zp Np cF`, under the library's hypothesis `P5J.AtMg`. Of the hypotheses that `falls_asks`
takes beside the structure `FirstAsks`, seven are proved here from `P5J.AtMg` (`s₁` with the field
`St.hfs`): the file's data (`hdata`), the test on the places (`hpl`), that the last sub-protocol has
one round (`he₁`), that there are gated sub-protocols (`hne`), that no fall is met before the first
round (`s₁`), and that the marks of the other two chains never speak at a typed message (`hmk₂`,
`hmk₃`, at our own `fitMarks` alone).

  1  `pre_ne_cut`   GENERAL: a chain with the library's written cut has gated sub-protocols
  2  `falls_head`   the bound

Limits.
  * What is left as a hypothesis: `P5J.AtMg` itself (the library shows the head to have a member at
    one example, the full-size files with synthetic weights: `headMember_zFull`,
    AtFullSide/Top/HeadMemberAtFull.lean, in a side library); `cut` (the first chain is `pre₁ ++
    [e₁]`), which `Sf` holds too; a member `St` of `FirstAsks` at `fallSeat`; `hC` (on the kit of
    challenges; `kit_two` proves it at one kit); `hR` (`ready` returns at these coins) and `Sf` (on
    the prover's rows); `hf₂` and `hf₃` (the other two chains have no falls: whoever lays the rows
    lays these lists).
  * The event. A run that returns an error (a stop, a fault) meets no fall here: `fallAt`
    (Honest/Fall.lean) is `none` there. A fall is a record of the three lists of `G`. Nothing here
    says that the lists hold every event at which the verifier rejects an honest run: that is
    `SaysYes`, a hypothesis of `runC_accepts` (Honest/Law/AcceptC.lean).
  * The measure is over the verifier's typed challenges alone, at one input and one list of the
    run's coins, under "for all". A bound at each coin has no seat in the library's `Honest.Acc` and
    `BatchProtocol.Complete` (see the Limits of Honest/Law/SharesFalls.lean). `hm`, `p₁`, `PM`, `qM`, `P`,
    `qF` and `reps` are bound behind the input and the coins: the right side may hang on both.
  * The kit `C` is a letter. `hC` says that what a challenge shows fits its round, and nothing on
    how the challenges are spread. The owners' bounds in `St` and this bound stand at one and the
    same `C`.
  * `G` and `H` are letters: no prover of the protocol is laid here.
  * No member of `FirstAsks` is shown. `firstAsks_reps` (Honest/Law/CoverAsksReps.lean) gives one
    from eight of its fields; of these `hz_head` (Honest/Law/CoverDraws.lean) and, at the list
    `fallsHead`, `fallsHead_seats_full` (Honest/Law/FallsHeadFull.lean) prove two.
  * The marks of the other two chains hold no owner's mark, and `hf₂` and `hf₃` stay hypotheses.
    K12 on these two chains: by reading; proved at no place of these chains (see
     Honest/Law/CoverOthers.lean).
  * All that is assumed of the other two chains sits in `hf₂` and `hf₃`, which are hypotheses. The
    lists `ms₂` and `ms₃` occur in `falls_asks` in `hmk₂` and `hmk₃` and in the gates of these
    chains, of which the bound reads the prices alone. So laying them as `fitMarks` says nothing on
    whether an owner has a mark there. None of the three groups of authors that were asked answered
    that these chains have no fall. If a fall is found there, `falls_asks` itself must turn: it has
    no bounds for these chains.
  * Four sub-protocols of the other two chains are of the kind `frame` and so are ours. We lay no
    fall and no mark there, by our own reading of the blocks' texts; what is owed for three of them
    is said in Honest/Law/CoverOthers.lean.
  * `p₂` and `p₃` are free: the bound holds at 0 for both.
  * No number follows from the theorem. The full size alone.
  * The theorem proves no property of a prover or a protocol.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverAsks
import Johnson.Desc.ProofFile.Honest.Law.CoverCutFirst
import Johnson.Desc.ProofFile.Honest.Law.CoverOthers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open P5J (TS)

/-- A chain with the written cut has gated sub-protocols. -/
theorem pre_ne_cut {S Cl : Type} {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hcut : cutOf all = cutFirstFull) (cut : all = pre ++ [e₁]) : pre ≠ [] := by
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps_cut hcut, List.length_map]
  intro e
  rw [cut, e] at hlen
  simp at hlen

variable {W₀ Rc Ky Tr X₀ X TF TJ T3 : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxHeartbeats 2000000 in
/-- The bound on the chance that a run meets a fall, at the proof file's description, under
`P5J.AtMg`, from a member of `FirstAsks` and six further hypotheses (`hC`, `cut`, `hR`, `Sf`, `hf₂`,
`hf₃`). -/
theorem falls_head (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts}
    (G : Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (hm : List Mark) (p₁ p₂ p₃ : Nat → ℝ≥0∞)
    {pre₁ : List (Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl)}
    {e₁ : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl}
    (h : P5J.AtMg o Z D r Zp Np cF) (cut : (P5J.F0T o Zp Np cF).first.blocksInOrder = pre₁ ++ [e₁])
    (hR : ready (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit (P5J.F0T o Zp Np cF) (G.prover H) D pre₁ e₁)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) {seatM : Place → Bool}
    {PM : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl → List Fmt.Drawn → Prop}
    {qM : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl → Mark → ℝ≥0∞}
    {P : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl → List Fmt.Drawn →
      (P5J.F0T o Zp Np cF).S₁ → Prop}
    {qF : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl →
      Fall (P5J.F0T o Zp Np cF).S₁ → ℝ≥0∞}
    {reps : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl →
      List (Fall (P5J.F0T o Zp Np cF).S₁)}
    (St : FirstAsks C G.falls₁ hm p₁ pre₁ e₁ x
      (fun _ => at₁ (P5J.F0T o Zp Np cF) (G.prover H) w₀ rc x R) (fallSeat P5J.At.links) seatM PM
      qM P qF reps) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (hm ++ fitMarks pre₁) p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T o Zp Np cF).shared.blocksInOrder) p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T o Zp Np cF).second.blocksInOrder) p₃).map
            (·.p)).sum) := by
  have hcut := (file_head h).2.2
  obtain ⟨z₁, he₁⟩ := (members_cut hcut cut).2.2.2.2.2
  have s₁ : fellBy (P5J.F0T o Zp Np cF).first.blocksInOrder G.falls₁
      (at₁ (P5J.F0T o Zp Np cF) (G.prover H) w₀ rc x R) 0 [] = false :=
    fellBy_cut hcut G.falls₁ St.hfs _ (fun a s₀ ha hs => by
      obtain ⟨m₀, h1, h2⟩ :=
        letter_starts (P5J.F0T o Zp Np cF) (G.prover H) w₀ rc x R _ rfl [] a ha
      have e : (P5J.F0T o Zp Np cF).start₁ ((P5J.F0T o Zp Np cF).pub x) = s₀ := Option.some.inj hs
      rw [← e]
      exact ⟨m₀, [], h1, h2⟩) []
  exact falls_asks C hC D tF tJ t3 G H w₀ rc x k R hm _ _ p₁ p₂ p₃ hR Sf (pre_ne_cut hcut cut) hf₂
    hf₃ s₁ h.laid.data he₁ (file_head h).2.1 _ rfl St (hmk₂_head C hC h) (hmk₃_head C hC h)

end ProofFile.Honest

#print axioms ProofFile.Honest.pre_ne_cut
#print axioms ProofFile.Honest.falls_head
