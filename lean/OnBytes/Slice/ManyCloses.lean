-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyCloses.lean: the hypothesis on the rounds after the link's fifth, for a chain of
any number of stages.

OnBytes/Slice/LinkSound.lean states one hypothesis on the written link, on the rounds after
the fifth, `Closes`, which speaks of a list of written rounds.

OnBytes/Slice/ManySem.lean takes the rounds of a chain off over the blocks' shapes joined. The shape
of the chain's list of rounds and the joined shapes are equal, by induction on the chain. This file
carries `chain_many` along that equation and puts the batching in front.
OnBytes/Slice/ChainCloses.lean does the same for three stages written out.

Main definitions.
 `Chain.errL`   the chain's error counts, carried to the shape of its list of rounds.
Main theorems.
 `Chain.uL_rds`     the two shapes are equal.
 `Chain.trL_heq`, `Chain.tr_cast`   the transcript over the joined shapes is the one over the list;
                    carried to the list's shape, it is equal to it. `Chain.pass_trL`: the tests of
                    work are the same.
 `chain_many_acc`, `chain_many_list`   `chain_many` for a verdict, over either shape.
 `closes_many`      `Closes` holds at the batching's round and the chain's rounds, for every
                    decision whose yes in the written protocol gives the chain's yes in the field.
                    That all tests of work pass need not be asked: the written yes has it.
 `closes_many_at`   the same with the first stage under a name of its own.
 `Chain.stepMid_heq`, `Chain.stepEnd_heq`   a standard step from a stage under two names.
Asked in `closes_many`: the batching's statement (`BatSem`), the blocks' statements (`Chain.Holds`),
and of the first tree's readings `IsRows` and `WordTie`.
Not claimed. That any decision's yes gives the yes in the field. That the blocks' statements hold.
Nothing on the sizes of the error counts. No theorem of this library takes `Closes` as a hypothesis;
the link's soundness theorems ask `ClosesR`.
-/
import OnBytes.Slice.ManySem
import OnBytes.Slice.ChainCloses

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

namespace Chain

/-- The shape of a chain's list of rounds is the blocks' shapes joined. -/
theorem uL_rds {s : Sg} (c : Chain s) : PQ.uL (ckP .two) c.rds = c.sh := by
  induction c with
  | last s e dL dB fu fs εb => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    show PQ.uL (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds)) =
      PQ.uL (ckP .two) (foldRds s dE dT) ++ (PQ.uL (ckP .two) [dS, dC] ++ next.sh)
    rw [uL_append, uL_append, ih]

/-- The error counts, carried to the shape of the list of rounds. -/
def errL {s : Sg} (c : Chain s) : Err (PQ.uL (ckP .two) c.rds) := c.uL_rds ▸ c.err

/-- The two joined transcripts are the same. -/
theorem trL_heq {s : Sg} (c : Chain s) (b : c.Bl) : HEq (c.trL b) (c.tr b) := by
  induction c with
  | last s e dL dB fu fs εb => exact HEq.rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    have h2 := joinT_heq_app [dS, dC] next.rds next.sh next.uL_rds b.2.1 (next.trL b.2.2)
      (next.tr b.2.2) (ih b.2.2)
    exact joinT_heq_app (foldRds s dE dT) ([dS, dC] ++ next.rds)
      (PQ.uL (ckP .two) [dS, dC] ++ next.sh)
      ((uL_append _ _).trans (congrArg _ next.uL_rds)) b.1 _ _ h2

/-- The transcript over the joined shapes, carried to the list's shape, is the one over the
list. -/
theorem tr_cast {s : Sg} (c : Chain s) (b : c.Bl) :
    cast (congrArg Iop.Tr c.uL_rds.symm) (c.tr b) = c.trL b :=
  eq_of_heq ((cast_heq _ _).trans (c.trL_heq b).symm)

/-- The tests of work of the list of rounds are those of the blocks. -/
theorem pass_trL {s : Sg} (c : Chain s) (b : c.Bl) :
    PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = c.pass b := by
  induction c with
  | last s e dL dB fu fs εb => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    show PQ.passSL (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
      (PQ.rhoSL (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
        (joinT _ _ b.1 (joinT _ _ b.2.1 (next.trL b.2.2)))) =
      (PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ b.1) &&
        (PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ b.2.1) && next.pass b.2.2))
    rw [pass_joinT, pass_joinT, ih]

end Chain

/-- The chain, for a verdict. Let acc be any verdict on the chain's rounds. If a yes of acc has all
tests of work passed and gives the yes in the field, the prover has lost towards a no of acc. Asked
besides: what `chain_many` asks. -/
theorem chain_many_acc {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (hno : ∀ w, ¬ s.RIn c.rad (q, y) w)
    (acc : Tr c.sh → Bool)
    (hacc : ∀ b, acc (c.tr b) = true → c.pass b = true ∧ c.Acc q y z g b) :
    Doomed c.sh c.err fun τ => acc τ = false := by
  refine chain_many c h q y z g hno _ ?_ ?_
  · intro b hp
    refine Bool.eq_false_iff.2 fun ha => ?_
    rw [(hacc b ha).1] at hp
    cases hp
  · intro b hs
    exact Bool.eq_false_iff.2 fun ha => hs (hacc b ha).2

/-- The chain over the list of rounds, for a verdict. Let acc be any verdict on the chain's list of
rounds. If a yes of acc gives the yes in the field and has all tests of work passed, the prover has
lost towards a no of acc. Asked besides: what `chain_many` asks. -/
theorem chain_many_list {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (hno : ∀ w, ¬ s.RIn c.rad (q, y) w)
    (acc : Tr (PQ.uL (ckP .two) c.rds) → Bool)
    (hacc : ∀ b, acc (c.trL b) = true → c.Acc q y z g b ∧
      PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true) :
    Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => acc τ = false := by
  refine doomed_cast c.uL_rds _ _ ?_
  refine chain_many_acc c h q y z g hno
    (fun τ => acc (cast (congrArg Iop.Tr c.uL_rds.symm) τ)) fun b hb => ?_
  beta_reduce at hb
  rw [c.tr_cast] at hb
  exact ⟨(c.pass_trL b).symm.trans (hacc b hb).2, (hacc b hb).1⟩

section
variable {S : Sz} {t₀ : ℕ} (d1 d2 d3 d4 d5 dA : PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool)

/-- The rounds after the fifth close the link (`Closes`), where they are the batching's round dA and
the rounds of a chain c from the link's first stage on, for any decision whose yes in the written
protocol gives the chain's yes in the field (`hsem`): at the claim that the batching makes of the
rows, and at the first tree read by w1, z1, g1. Asked besides: the batching's statement at the
chain's first radius, the blocks' statements, and `IsRows` and `WordTie` of the readings. -/
theorem closes_many (c : Chain (S.sg t₀)) (εa : ℕ)
    (rows : S.lk.X4 → (ℕ → GE) × (ℕ → (S.sg t₀).cIn.J → GE))
    (w1 : (wRound d2).Orc → (S.sg t₀).cIn.Word) (z1 : (wRound d2).Orc → (S.sg t₀).cFr.Word)
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (hBat : BatSem S t₀ c.rad d2 dA εa) (hc : c.Holds)
    (hrows : ∀ x, IsRows S t₀ x (rows x).1 (rows x).2) (hw1 : ∀ o, WordTie S t₀ d2 o (w1 o))
    (hsem : ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true →
      c.Acc (sumStm S t₀ (rows (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rows (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (w1 m2.1) (z1 m2.1) (g1 m2.1) b) :
    Closes S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec (εa, c.errL) := by
  intro y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 hno
  have hpass : ∀ mA cA (τ : Tr (PQ.uL (ckP .two) c.rds)),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ) = true →
      GChal.pass (b := dA.entry.work) cA = true ∧
        PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true := by
    intro mA cA τ hacc
    have hp : PQ.passSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: dA :: c.rds)
        (PQ.rhoSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: dA :: c.rds)
          (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ)) = true := by
      have h4 : (PQ.passSL (ckP .two) _ _ && _ && _ && _) = true := hacc
      simp only [Bool.and_eq_true] at h4
      exact h4.1.1.1
    simp only [PQ.passSL, PQ.rhoSL, Bool.and_eq_true] at hp
    exact ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩
  refine hBat _ c.errL m2.1 (w1 m2.1) (hw1 m2.1) (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 hno
    _ _ (hrows _) _ ?_ ?_
  · intro mA cA τ hw
    refine Bool.eq_false_iff.2 fun ha => ?_
    rw [(hpass mA cA τ ha).1] at hw
    cases hw
  · intro mA cA h0
    exact chain_many_list c hc _ (w1 m2.1) (z1 m2.1) (g1 m2.1) h0
      (fun τ => (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τ))
      fun b hb => ⟨hsem y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hb, (hpass mA cA _ hb).2⟩

/-- The same with the first stage under a name of its own. c' is the chain c, written from the stage
s1 on. What is asked of the blocks, and the conclusion, speak of c'; what is asked of the decision
speaks of c. -/
theorem closes_many_at (s1 : Sg) (hs : S.sg t₀ = s1) (c : Chain (S.sg t₀)) (c' : Chain s1)
    (hcc : HEq c c') (εa : ℕ)
    (rows : S.lk.X4 → (ℕ → GE) × (ℕ → (S.sg t₀).cIn.J → GE))
    (w1 : (wRound d2).Orc → (S.sg t₀).cIn.Word) (z1 : (wRound d2).Orc → (S.sg t₀).cFr.Word)
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (hBat : BatSem S t₀ c'.rad d2 dA εa) (hc : c'.Holds)
    (hrows : ∀ x, IsRows S t₀ x (rows x).1 (rows x).2) (hw1 : ∀ o, WordTie S t₀ d2 o (w1 o))
    (hsem : ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl),
      (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true →
      c.Acc (sumStm S t₀ (rows (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rows (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (w1 m2.1) (z1 m2.1) (g1 m2.1) b) :
    Closes S d1 d2 d3 d4 d5 (dA :: c'.rds) xs dec (εa, c'.errL) := by
  subst hs
  obtain rfl := eq_of_heq hcc
  exact closes_many d1 d2 d3 d4 d5 dA xs dec c εa rows w1 z1 g1 hBat hc hrows hw1 hsem

end

/-! ## The same chain from a stage under two names -/

/-- A step to a stage that is not the last, written from two stages that are equal. -/
theorem Chain.stepMid_heq {s s1 s' : Sg} (h : s = s1) (hf : CsFit s s') (hf1 : CsFit s1 s') (e : ℕ)
    (dE dT dS dC : PQ.RD) (next : Chain s') :
    HEq (Chain.stepMid s s' hf e dE dT dS dC next)
      (Chain.stepMid s1 s' hf1 e dE dT dS dC next) := by
  subst h
  rfl

/-- A step to the last stage, written from two stages that are equal. -/
theorem Chain.stepEnd_heq {s s1 s' : Sg} (h : s = s1) (hf : CsFit s s') (hf1 : CsFit s1 s') (e : ℕ)
    (dE dT dS dC : PQ.RD) (next : Chain s') :
    HEq (Chain.stepEnd s s' hf e dE dT dS dC next)
      (Chain.stepEnd s1 s' hf1 e dE dT dS dC next) := by
  subst h
  rfl

end OnBytes.Slice
