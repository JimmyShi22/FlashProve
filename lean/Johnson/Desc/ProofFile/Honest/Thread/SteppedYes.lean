-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SteppedYes.lean: the column `hK` of `owesS_head`
(GatherHead.lean) from the library's relation `StepYes` (Johnson/Top/H0/Walk/Reach.lean). The column
asks the clause `f` of a sub-protocol's kind at its place, from the honest side's step
(`Thread.Stepped`, Pays.lean). The lemmas of the several groups of authors prove their clauses from
`StepYes`, the verifier's side alone, and speak of a sub-protocol by its number in its family. No
definition.

  1  `stepYes_of_stepped`   at any `Thread`: a step of the honest side is a `StepYes`
  2  `head_len`   under the library's hypothesis `AtMgA` the first chain has 358 sub-protocols
  3  `head_hK_of_yes`   the column `hK`, from the clause at every `StepYes` at every number
  4  `head_hK_of_families`   the same, family by family (`all_numbers`, Numbers358.lean)

Limits.
  * `f` is an argument. Nothing shows that a clause holds at any step.
  * Full size only, and only under `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says which
    that is).
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `stepYes_of_stepped`, `head_hK_of_yes`,
    `head_hK_of_families`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MovedDrawn
import Johnson.Desc.ProofFile.Honest.Thread.Numbers358
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- A step of the honest side is an accepting step of the sub-protocol. -/
theorem stepYes_of_stepped {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} {s' : S} (hd : drawsFit blk.rounds ds = true)
    (hS : T.Stepped blk k s m E ds y cols s') : StepYes T.ft blk s s' := by
  refine ⟨roundsOf y.1, cols, ?_, hS.2⟩
  have e := congrArg List.length (moved_drawn T hS.1)
  rw [List.length_map] at e
  rw [e]
  exact drawsFit_length _ _ hd

end ProofFile.Honest

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- The first chain has 358 sub-protocols. -/
theorem head_len : cF.blocksInOrder.length = 358 := by
  have e := congrArg List.length (P5J.At.places_paid h.scope h.reads h.laid)
  unfold blockPlaces at e
  rw [List.length_map] at e
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  rw [e, ← e']
  exact IM.places_len

/-- **The column `hK` from `StepYes`.** -/
theorem head_hK_of_yes (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (f : KindName → Place → TS → TS → Prop)
    (hY : ∀ b, b < 358 → ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ s s', StepYes 0 blk s s' →
      f blk.place.kind blk.place s s') :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' := by
  intro b hb blk hblk k s m E ds y cols s' _ hd hS
  have hb' : b < cF.blocksInOrder.length := hb
  rw [head_len h] at hb'
  exact hY b hb' blk hblk s s' (stepYes_of_stepped _ hd hS)

/-- **The same, family by family.** `K b`: the clause holds at every `StepYes` at number `b`. -/
theorem head_hK_of_families (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (f : KindName → Place → TS → TS → Prop) {K : Nat → Prop}
    (hKdef : ∀ b, K b ↔ ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ s s', StepYes 0 blk s s' →
      f blk.place.kind blk.place s s')
    (hfront : K 0) (hlaid : ∀ l, l < 25 → K (14 * l + 1))
    (hhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → K (14 * l + i + 2))
    (hback : ∀ l, l < 25 → ∀ j, 2 ≤ j → j ≤ 7 → K (14 * l + IM.nAt l + j))
    (h353 : K 353) (h354 : K 354) (h355 : K 355) (h356 : K 356) (h357 : K 357) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' :=
  head_hK_of_yes h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said f fun b hb =>
    (hKdef b).1 (all_numbers K hfront hlaid hhear hback h353 h354 h355 h356 h357 b hb)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.stepYes_of_stepped
#print axioms ProofFile.Honest.FirstThread.head_len
#print axioms ProofFile.Honest.FirstThread.head_hK_of_yes
#print axioms ProofFile.Honest.FirstThread.head_hK_of_families
