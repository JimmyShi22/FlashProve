-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiedAtItem.lean: three theorems of this folder stated a
second time, at a prover whose stored table is the committer's at one item alone
(`Committer.proverAt`, Honest/CommitterAt.lean), where the first texts have the committer's table at
every item (`Committer.prover`, Honest/Committer.lean). General in the item. Statements and proofs;
no definition.

  `tied_atItem`: `tied` (Tied.lean) at `Cm.proverAt item₀ H`
  `one_exact_atItem`: `one_exact_at` (OneAt.lean) there
  `one_exact_atItem_mute`: `one_exact_at_mute` (Mute.lean) there

Why a second text. The first texts name `Cm.prover H` in their statements, so they cannot be called
at `Cm.proverAt item₀ H`. Other files go on citing the first texts.

By what. `Committer.proverAt` differs from `Committer.prover` in the field `stored` alone. Of the
five clauses of `Tied`, `table` alone reads that field, at the item of a declared stored table;
under hz that item is item₀, where the two provers have the same columns. `one_exact_atItem` is
`one_exact_paid` (OneAt.lean) at `tied_atItem`; the muted form follows as in Mute.lean.

Hypotheses. Those of the first texts, and hz: every stored table that a round of the description F
declares stands under the item item₀.

Limits. All limits of the heads of Honest/Law/Rule/Tied.lean, Honest/Law/Rule/OneAt.lean and
Honest/Law/Rule/Mute.lean. hz is a hypothesis: it is proved of no description here.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute
import Johnson.Desc.ProofFile.Honest.CommitterAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

variable {I X RI Seed Ans Xi Ky Tr X₀ Xh TF TJ T3 R2 R3 : Type} {ans : I → RI → Seed → Ans}
  {Ryes : I → X → Prop} {wr : X × (Seed × Ans) → Xi} {Cm : Committer I RI Seed X Xi Ky}
  {kp : Seed × Ans → Ky} {n : ℕ} {C : CK} {D : WholeD} {tF : TF} {tJ : TJ} {t3 : T3}
  {F : FileDescription Xi} {silent : Xi → TF → TJ → T3 → Bool} {Bk : ProverCoinCounts} {sh : Ky → F.S₂}
  {front : ℕ → R2 → R3 → I → RI → Seed → Xi → TF} {join : R2 → I → RI → Seed → TJ}
  {seam : R2 → R3 → I → RI → Seed → Xi → T3} {pubJ : ℕ → R2 → R3 → Xi → TF × TJ × T3}
  [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3] {H : Prover I RI Xi Ky Tr X₀ Xh}
  {G : Sides F Bk I RI Ky Tr X₀ Xh}

omit [Fintype R2] [Nonempty R2] [Fintype R3] in
/-- `tied` at a prover whose stored table is the committer's at the item item₀ alone. -/
theorem tied_atItem (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ) {item₀ : ℕ}
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, s.item = item₀)
    (H : Prover I RI Xi Ky Tr X₀ Xh) (w : I × RI × Seed) (a : X × (Seed × Ans))
    (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1) :
    Tied D F (Cm.proverAt item₀ H) (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3))
      (Cm.ext D.a) (pubJ n) sh (relAt ans Ryes wr) w (wr a) := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := tied h H w a ha
  refine ⟨t1, t2, fun d hd s hs p hp => ?_, t4, t5⟩
  have e := t3 d hd s hs p hp
  unfold Prover.storedWords Committer.prover at e
  unfold Prover.storedWords Committer.proverAt
  simp only [hz d hd s hs, beq_self_eq_true, if_true]
  exact e

/-- `one_exact_at` there. -/
theorem one_exact_atItem (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ) {item₀ : ℕ}
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, s.item = item₀)
    (hO : Owed F Bk (Cm.proverAt item₀ H) G (relAt ans Ryes wr)) (hE : G.owns = true)
    (hD : DataFits F D)
    (w : I × RI × Seed)
    (a : X × (Seed × Ans)) (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w (wr
          a)) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w
          (wr a) ρ =
      simOne C D tF tJ t3 F silent Bk G.sims (Cm.proverAt item₀ H).key (pubJ n)
        (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Bad (wr a)
          ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns (wr a) ρ (Cm.ext D.a w)) :=
  one_exact_paid hO hE hD w (wr a) (tied_atItem h hz H w a ha) ρ hdue hρ

/-- `one_exact_at_mute` there. -/
theorem one_exact_atItem_mute (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ)
    {item₀ : ℕ}
    (hz : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, s.item = item₀)
    (hO : Owed F Bk (Cm.proverAt item₀ H) G.mute (relAt ans Ryes wr)) (hE : G.owns = true)
    (hD : DataFits F D)
    (w : I × RI × Seed)
    (a : X × (Seed × Ans)) (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w (wr
          a)) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w
          (wr a) ρ =
      simOne C D tF tJ t3 F silent Bk G.sims (Cm.proverAt item₀ H).key (pubJ n)
        (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.proverAt item₀ H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Bad (wr a)
          ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns (wr a) ρ (Cm.ext D.a w)) := by
  have h' := one_exact_atItem h hz hO ((owns_mute G).trans hE) hD w a ha ρ hdue (by
    rw [prover_mute]
    exact hρ)
  rw [prover_mute, sims_mute] at h'
  exact h'

end ProofFile.Honest

#print axioms ProofFile.Honest.tied_atItem
#print axioms ProofFile.Honest.one_exact_atItem
#print axioms ProofFile.Honest.one_exact_atItem_mute
