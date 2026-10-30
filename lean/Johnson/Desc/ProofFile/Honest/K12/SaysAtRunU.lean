-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SaysAtRunU.lean

A conditional with no known member: at no prover and no book is it shown that ready and runC return
and that the part is called.

The sentence on values (`SaysAt`, AsksWhole.lean) at the second part of the proximity test on G_u of
the proof file's shared chain, under the head `P5J.AtMg`, at a run of the frame's walking prover
(`runC`): from premises at the state d8 that the description's own fold over the eight sub-protocols
in front returns at the shared view. Three theorems.

  `saysAt_run_U`: `door_at_run`'s three clauses (DoorAtRun.lean), to the letter; the job's state on
      entry is what the seat's way in makes of d8; and, at all coins and all words: all that d8's
      statement claims holds of the words (`AllMet`), no open row of it is marked as a sample row
      (`OpenKinds`), and the tie of the words (`WordsTied`, SaysOfMet.lean) ⟹ `SaysAt`, in the
      letters of `onFreeT_head_U`'s premise hSays (OnFreeTAtHeadU.lean).
  `saysAt_run_U_shown`: the same with `AllMet` had from the library's five premises on what was
      shown, by name (`ShownU`, `OwnAnswers`, `OwnColumns`, `ShownO`, `ShownMu`:
      Johnson/Desc/K14/Honest/ItemsEach.lean), at the run's own shared view: the fold's return is
      opened by `Eight.stepTo8_of_fold`, and `Steps.met8` is called over it
      (Johnson/Desc/K14/Honest/StepsTwins.lean). The plan's premises are paid under the head
      (`planFacts_head`, `own_head`: DoorReturnsAt.lean).
  `saysAt_run_U_six`: the same with `OpenKinds` paid (`openKinds_behind_eight`,
      OpenKindsAtEight.lean): six premises on values are left.

Why this form. `saysAt_of_eight` (SaysOfMet.lean) makes the fold's return anew from premises on the
form of what was shown. At a run that return is had already: `door_at_run` concludes it from the
walk itself. So here no premise on form is left.

Limits.
- IT PAYS NONE OF ITS PREMISES ON VALUES: in the first theorem `AllMet` and the tie, beside
  `OpenKinds`; in the second the library's five and the tie, beside `OpenKinds`; in the third these
  six. That the six can be had together is shown by no example here.
- `saysAt_of_eight` (SaysOfMet.lean) has the honest words at the first round as a view holds it,
  `saysAt_run_U_shown` at that round without its digest, each as the library's law that it calls.
  That the two families of words are one is not said here.
- hα is a premise on the prover: the key that its shared parts are given is the instance's.
  `onFreeT_head_U` has no such premise: a caller brings it besides.
- hR, S and h9 are on the filling and the book; hrun and hc on the run.
- Of the walk (`runC`); m is the stand that `midSharedAtW` returns. The test on G_u alone.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import Johnson.Desc.ProofFile.Honest.K12.DoorAtRun
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.DoorReturnsAt
import Johnson.Desc.K14.Honest.StepsTwins
import Johnson.Desc.ProofFile.Honest.K12.OpenKindsAtEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllMet OpenKinds Words layoutOf)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks first)
open Desc.K14.Honest (Eight Seen8 States8 StepTo8 Start8 Inputs ShownU OwnAnswers OwnColumns ShownO
  ShownMu words2 first_kept)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  midSharedAtW)
open ProofFile.Honest.K12 (TestCoins TestJob SimJob restMember restFront firstLen)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **At a run: `SaysAt` at the second part of the test on G_u, from three premises at the state
that the description's own fold over the eight returns at the shared view.** Under the head, at
every book and every prover whose key is the instance's: where `ready` and `runC` return and the
second part is called. The first three clauses are `door_at_run`'s (DoorAtRun.lean), to the letter,
at the second member. The fourth: the job's state on entry, at the stand's input and at the front as
the second part's moves lay it, is what the seat's way in makes of d8: not the fall-back. The last:
at all coins C and all words mW: all that d8's statement claims holds of mW; no open row of it is
marked as a sample row; on the members' tables mW is what the job's own rows make at C ⟹ `SaysAt`,
in the letters of `onFreeT_head_U`'s premise hSays. J is free: it is read at its stages' first
length and in the member alone; that law has it at the job's own test. -/
theorem saysAt_run_U {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (d8 : St) (rest : List Fmt.RoundView)
      (more : List OpenedColumn),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length +
        firstLen J.p.nums.stages ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).rec₀
          m.st.input (restFront J m) =
        { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing,
          mask := d8.loc.firstMask } ∧
      ∀ (C : TestCoins) (mW : Words GE), AllMet rdE d8.st mW → OpenKinds d8.st →
        (∀ G, d8.st.groups[d8.loc.gU]? = some G →
          WordsTied d8.st d8.loc.gU G mW (layoutOf d8.st G)
            (plainMany
              (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
              m.st.input (restFront J m) C)) →
        SaysAt (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
          m.st.input (restFront J m) C := by
  obtain ⟨m, d8, rest, more, a1, a2, a3, a4⟩ :=
    door_at_run (X := X₀) h b1 b2 b3 b4 b5 b6 b7 b8 hb hα hR σ (restMember J Js) pre t
      (firstLen J.p.nums.stages) S h9 hrun hc
  have hfr : (restFront J m).seen.rounds =
      m.seen.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length := by
    show m.seen.take (m.seen.length - firstLen J.p.nums.stages) = _
    rw [a2, Nat.add_sub_cancel]
  have hrec : (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).rec₀
        m.st.input (restFront J m) =
      { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing,
        mask := d8.loc.firstMask } :=
    (Except.ok.inj (a4 (restFront J m) hfr)).symm
  refine ⟨m, d8, rest, more, a1, a2, a3, hrec,
    fun C mW hM hK hT => saysAt_of_met _ _ _ C mW ?_ ?_ ?_⟩
  · rw [hrec]
    exact hM
  · rw [hrec]
    exact hK
  · rw [hrec]
    exact hT

/-- **At a run: `SaysAt` from the library's five premises on what was shown, at the run's own shared
view, one fact of shape and the tie.** `saysAt_run_U`'s premises and first four clauses; the fold's
return opened by the library's own law (`Eight.stepTo8_of_fold`,
Johnson/Desc/K14/Honest/StepsTwins.lean): the shared view's rounds begin with eight rounds W, its
columns with W's; D8 holds the eight states, the last of them d8. Then, at everything H that an
honest prover may hold and at all coins C: the first sending's answers, the key's answers, the
columns at "LOC", the second sending's answers and the scalar at "SPLIT" are H's own (`ShownU`,
`OwnAnswers`, `OwnColumns`, `ShownO`, `ShownMu`: Johnson/Desc/K14/Honest/ItemsEach.lean), no open
row of d8's statement is marked as a sample row, and H's words are on the members' tables what the
job's own rows make at C ⟹ all that d8's statement claims holds of H's words, and `SaysAt`. Beside
hb, which names the eight, and h9 no premise on the plan or on the form of what was shown is left:
the head pays the first (`planFacts_head`, `own_head`: DoorReturnsAt.lean), the walk the second. -/
theorem saysAt_run_U_shown {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (d8 : St) (rest : List Fmt.RoundView)
      (more : List OpenedColumn) (W : Seen8) (D8 : States8),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length +
        firstLen J.p.nums.stages ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).rec₀
          m.st.input (restFront J m) =
        { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing,
          mask := d8.loc.firstMask } ∧
      r.run.views.2.1.rounds =
        [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest ∧
      r.run.views.2.1.opened = W.cs ++ more ∧ D8.d8 = d8 ∧
      StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
        (first (K1.qAt Zp Np).codes x.pub.key) W D8 ∧
      ∀ (H : Inputs) (C : TestCoins),
        ShownU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view D8 H →
        OwnAnswers (K1.qAt Zp Np) x.pub.key H → OwnColumns (K1.qAt Zp Np) W.view H →
        ShownO (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view D8 H →
        ShownMu (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view H →
        OpenKinds d8.st →
        (∀ G, d8.st.groups[d8.loc.gU]? = some G →
          WordsTied d8.st d8.loc.gU G
            (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
              (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H)
            (layoutOf d8.st G)
            (plainMany
              (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
              m.st.input (restFront J m) C)) →
        AllMet rdE d8.st
            (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
              (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) ∧
          SaysAt (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
            m.st.input (restFront J m) C := by
  obtain ⟨m, d8, rest, more, a1, a2, a3, hrec, hsay⟩ :=
    saysAt_run_U h b1 b2 b3 b4 b5 b6 b7 b8 hb hα weights rand u? J Js hR σ pre t S h9 hrun hc
  obtain ⟨W, D8, e1, e2, e3, u⟩ :=
    Eight.stepTo8_of_fold (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np))
      (facts_at_head h).2.2 (facts_at_head h).1 0 _ d8 _ rest _ more a3
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  refine ⟨m, d8, rest, more, W, D8, a1, a2, a3, hrec, e1, e2, e3, u,
    fun H C p1 p2 p3 p4 p5 hK hT => ?_⟩
  have hM := Desc.K14.Honest.Steps.met8
    (⟨⟨hP, hBU, hBO, rfl, rfl⟩, first_kept rdE _ _ _⟩ :
      Start8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
        (first (K1.qAt Zp Np).codes x.pub.key) H) u p1 p2 p3 p4 p5
  rw [e3] at hM
  exact ⟨hM, hsay C _ hM hK hT⟩

/-- **`saysAt_run_U_shown` with the fact of shape paid**: six premises on values are left: the
library's five on what was shown, and the tie of the words. -/
theorem saysAt_run_U_six {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (d8 : St) (rest : List Fmt.RoundView)
      (more : List OpenedColumn) (W : Seen8) (D8 : States8),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      m.seen.length = ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length +
        firstLen J.p.nums.stages ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).rec₀
          m.st.input (restFront J m) =
        { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing,
          mask := d8.loc.firstMask } ∧
      r.run.views.2.1.rounds =
        [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest ∧
      r.run.views.2.1.opened = W.cs ++ more ∧ D8.d8 = d8 ∧
      StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
        (first (K1.qAt Zp Np).codes x.pub.key) W D8 ∧
      ∀ (H : Inputs) (C : TestCoins),
        ShownU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view D8 H →
        OwnAnswers (K1.qAt Zp Np) x.pub.key H → OwnColumns (K1.qAt Zp Np) W.view H →
        ShownO (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view D8 H →
        ShownMu (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view H →
        (∀ G, d8.st.groups[d8.loc.gU]? = some G →
          WordsTied d8.st d8.loc.gU G
            (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
              (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H)
            (layoutOf d8.st G)
            (plainMany
              (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
              m.st.input (restFront J m) C)) →
        AllMet rdE d8.st
            (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
              (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) ∧
          SaysAt (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
            m.st.input (restFront J m) C := by
  obtain ⟨m, d8, rest, more, W, D8, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
    saysAt_run_U_shown h b1 b2 b3 b4 b5 b6 b7 b8 hb hα weights rand u? J Js hR σ pre t S h9 hrun
      hc
  exact ⟨m, d8, rest, more, W, D8, a1, a2, a3, a4, a5, a6, a7, a8,
    fun H C p1 p2 p3 p4 p5 hT =>
      a9 H C p1 p2 p3 p4 p5 (openKinds_behind_eight _ _ hb _ 0 _ _ _ a3) hT⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.saysAt_run_U
#print axioms ProofFile.Honest.K12.Light.saysAt_run_U_shown
#print axioms ProofFile.Honest.K12.Light.saysAt_run_U_six
