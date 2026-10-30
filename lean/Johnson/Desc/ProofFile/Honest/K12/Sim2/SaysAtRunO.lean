-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the sentence on values at the test on G_omega, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SaysAtRunO.lean: CONDITIONAL.

Can the hypotheses be met together at a real run? NOT KNOWN: at no prover and no book is it shown that
ready and runC return and that the part is called.

What is here. The sentence on values (`SaysAt`, K12/AsksWhole.lean) at the second part of the proximity
test on G_omega of the proof file's shared chain, at a run of the frame's walking prover, in the form of
`saysAt_run_U_six` (K12/SaysAtRunU.lean): at the state d8 that the fold over the eight returns, and d9
behind the test on G_u.

  `saysAt_run_O`   the run's fold opened, and from two of the library's premises on what was shown (ShownO,
      ShownMu) and the tie of the words on G_omega's members ⟹ `SaysAt`.
At the maker's return, with no premise on values left: Sim2/SaysAtOPaid.lean.

Road. At a called part F's fold over the ten in front returns (`called_at_run`). It opens into the eight
(`Eight.stepTo8_of_fold`) and one decision of the test on G_u. At O three facts at d8 serve, not `AllMet`:
`Steps.sampleOwn5` from ShownO alone, carried over the sixth, seventh and eighth block by `SmpOwn.quiet`,
`SmpOwn.zeta`; `Steps.foldOmega_behind8` from ShownMu alone; `Steps.order8` from the plan. So the answers of
the key and the columns at "LOC" are not asked here. The step across member 9: `allSay_onGu`, `samples_onGu`
(K12/Coin/RowsBack.lean), `onGu_leaves` (K12/Coin/SamplesThrough.lean). Then `saysAt_of_items`. The tie:
`tie_omega`, `tie_sp` (K12/AtFile/OTie.lean) at what a called stand gives.

Of the premises on values: ShownO and ShownMu by what the run played (K12/Sim/ShownAtRun.lean); the
tie as said.

Every letter under «there are» in `saysAt_run_O`'s end is tied to the run: m by the walk's equation; d8, rest,
more by the fold over the eight at the run's own shared view; d9, rest₉, more₉ by the fold over the test on G_u
at what is left of it; W by the two equations on the view; D8's eight states by StepTo8, its four other fields
are read by nothing here.

The road calls no law with a thread: `saysAt_of_items` has no coin among its binders. `tie_omega`, `tie_sp` bear the
label «NOT IN FRONT OF A LAW OVER COINS»; whoever pays the tie by them says which premises of the first kind
are discharged at the made terms.

Limits. No property of the protocol is claimed. Of the walk (`runC`).
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListOAtReturn
import Johnson.Desc.ProofFile.Honest.K12.SaysAtRunU
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey E)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllMet OpenKinds Words layoutOf)
open VerifiableInference.Desc (Block OpenedColumn Chain foldBlocks K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks first)
open Desc.K14.Law (rowsOn)
open Desc.K14.Honest (Eight Seen8 States8 StepTo8 Inputs ShownU OwnAnswers OwnColumns ShownO ShownMu
  words2)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof

private theorem take_add_take {α : Type} (a b : ℕ) (l : List α) :
    (l.take (a + b)).take a = l.take a := by
  rw [List.take_take]
  congr 1
  omega

/-- **The job at the test on G_omega at free readers, as a ManyJob.** -/
abbrev jobManyO {W₀ Rc X₀ : Type} (Zp : ProofFile.Pub) (Np : H2U.Places4) (bs : List (Block St Unit)) (pO : P12)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
    (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U
      (fun w : Common W₀ Rc TableKey => w.key) colsOpened) weights rand none

/-- CONDITIONAL. **`SaysAt` AT A CALLED SECOND PART OF THE TEST ON G_omega, FROM TWO OF THE
LIBRARY's PREMISES ON WHAT WAS SHOWN (ShownO, ShownMu) AND THE TIE.** -/
theorem saysAt_run_O {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
    {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
      (restMember (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest
        Js : Member Empty _ _ _).guarded pre t
      (firstLen pO.nums.stages))
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true) :
    ∃ (m : Mid (Common W₀ Rc TableKey) X₀) (d8 d9 : St) (rest rest₉ : List Fmt.RoundView)
      (more more₉ : List OpenedColumn) (W : Seen8) (D8 : States8),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest, more) ∧
      foldBlocks 0 [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)] d8 rest more =
        .ok (d9, rest₉, more₉) ∧
      r.run.views.2.1.rounds =
        [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest ∧
      r.run.views.2.1.opened = W.cs ++ more ∧ D8.d8 = d8 ∧
      StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
        (first (K1.qAt Zp Np).codes x.pub.key) W D8 ∧
      VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) d9 =
        .ok ((jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).rec₀
          m.st.input
          (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights
            rand).toRun.toTest m)) ∧
      ∀ (H : Inputs) (C : TestCoins),
        ShownO (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
          (first (K1.qAt Zp Np).codes x.pub.key) W.view D8 H →
        ShownMu (K1.qAt Zp Np) (first (K1.qAt Zp Np).codes x.pub.key) W.view H →
        (∀ G, d9.st.groups[d9.loc.gOmega]? = some G →
          WordsTied d9.st d9.loc.gOmega G
            (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
              (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H)
            (layoutOf d9.st G)
            (plainMany (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand)
              m.st.input
              (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights
                rand).toRun.toTest m) C)) →
        SaysAt (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand)
          m.st.input
          (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights
            rand).toRun.toTest m) C := by
  obtain ⟨pre₀, tl, e, hl₀, hLk, -⟩ := flat_ten (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) Np
    b1 b2 b3 b4 b5 b6 b7 b8 hb
  have e' : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ tl := e
  have hp : pre = pre₀ := h10.trans ((congrArg (List.take 10) e').trans (List.take_left' hl₀))
  subst hp
  have hpl := h.laid.planOk
  obtain ⟨m, s, cols, more, rest, hm, hin, hrounds, hlen, hcols, hfold, hfill⟩ :=
    called_at_run hpl hR σ _ pre t _ S hrun hc
  obtain ⟨m₂, s₂, cols₂, hm₂, ho₂, -, hfill₂⟩ := called_columns hpl hR hrun σ _ pre t _ S hc
  obtain ⟨m₃, -, -, hm₃, -, -, hseen, -⟩ :=
    stateFromViewOnSharedChain_at_stand hpl hR hrun σ _ pre t _ S hc
      (first (K1.qAt Zp Np).codes) (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      idleT12 x.pub.key rfl
  obtain rfl : m₂ = m := Option.some.inj (Except.ok.inj (hm₂.symm.trans hm))
  obtain rfl : m₃ = m₂ := Option.some.inj (Except.ok.inj (hm₃.symm.trans hm₂))
  have hdr : (m₃.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn) =
      (r.run.played.2.1.take (pre.flatMap (·.rounds)).length).map (·.drawn) := by
    rw [hseen]
    unfold roundsOf
    rw [← List.map_take, List.map_map]
    exact (congrArg (List.map _) (take_add_take (pre.flatMap (·.rounds)).length
      (firstLen pO.nums.stages) r.run.played.2.1)).trans rfl
  have hfa : fillCols (readsOf 1 0 (P.storedWords w₀ rc)
      (treeOwn (r.run.played.2.1.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
      ((m₃.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := hfill
  rw [hdr] at hfa
  have ecols : cols = cols₂ := Except.ok.inj (hfa.symm.trans hfill₂)
  subst ecols
  have hfold' : foldBlocks 0 pre (first (K1.qAt Zp Np).codes x.pub.key)
      (m₃.seen.take (pre.flatMap (·.rounds)).length) cols = .ok (s, [], []) := hfold
  have gE := Desc.K14.Honest.peel_front Zp.p.chains 0 _ _ _ _ _
    (Desc.K14.Honest.fold_like 0 _ _ hLk _ _ _ _ hfold')
  have hview := ProofFile.Honest.K12.Light.foldBlocks_more 0 _ _ _ _ _ gE
    (m₃.seen.drop (pre.flatMap (·.rounds)).length ++ rest) more
  rw [← List.append_assoc, List.take_append_drop, ← hrounds, ← hcols] at hview
  obtain ⟨d8, rest₈, more₈, h8, h9⟩ :=
    (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 hview
  obtain ⟨W, D8, e1, e2, e3, u⟩ :=
    Eight.stepTo8_of_fold (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np))
      (facts_at_head h).2.2 (facts_at_head h).1 0 _ d8 _ rest₈ _ more₈ h8
  have hl' : m₃.seen.length = (pre.flatMap (·.rounds)).length +
      firstLen (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest.p.nums.stages := hlen
  obtain ⟨f1, f2⟩ := rest_front_at (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃ (pre.flatMap (·.rounds)).length hl'
  have hrec := door_of_opened Zp.p.chains (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
    [b1, b2, b3, b4, b5, b6, b7, b8] (fourOf Np).U pre hLk x.pub.key (m₃.seen.take (pre.flatMap (·.rounds)).length) cols s hfold'
    (fun w : Common W₀ Rc TableKey => w.key) m₃.st.input (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃)
    (by rw [hin]; exact hα x) f1 (f2.trans ho₂)
  refine ⟨m₃, d8, s, rest₈, _, more₈, _, W, D8, hm, h8, h9, e1, e2, e3, u, hrec,
    fun H C p4 p5 hT => ?_⟩
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  have Pub : Desc.K14.Honest.Public8 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO
      (first (K1.qAt Zp Np).codes x.pub.key) := ⟨hP, hBU, hBO, rfl, rfl⟩
  have hI8 : OnBytes.Means.InOrder D8.d8.st :=
    Desc.K14.Honest.Steps.order8 Pub u (OnBytes.Means.InOrder.start _)
  rw [e3] at hI8
  have hRo := Desc.K14.Honest.Steps.foldOmega_behind8 Pub u p5
  rw [e3] at hRo
  obtain ⟨s5o, s5s⟩ := Desc.K14.Honest.Steps.sampleOwn5 Pub u.front.front.front p4
  obtain ⟨x₈, ids₈, x₉, ids₉, t₈⟩ := Pub.to8 u
  obtain ⟨c6, n6, st6⟩ := u.front.front.s6
  obtain ⟨_, _, e6⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ st6
  obtain ⟨c8, n8, st8⟩ := u.s8
  obtain ⟨_, _, e8⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ st8
  have q6 := (Desc.K14.Honest.quiet_each (K1.qAt Zp Np) (facts_at_head h).1 b1 b2 b3 b4 b5 b6 b7 b8 hb
    _ _ _ _).2.2.1 e6
  have q8 := (Desc.K14.Honest.quiet_each (K1.qAt Zp Np) (facts_at_head h).1 b1 b2 b3 b4 b5 b6 b7 b8 hb
    _ _ _ _).2.2.2 e8
  have carry : ∀ o, Desc.K14.Honest.SmpOwn o D8.d5 (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) →
      Desc.K14.Honest.SmpOwn o d8 (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) := fun o hs => by
    rw [← e3]
    exact Desc.K14.Honest.SmpOwn.quiet q8
      (Desc.K14.Honest.SmpOwn.zeta t₈.front.k7 (Desc.K14.Honest.SmpOwn.quiet q6 hs))
  have s8o := carry 2 s5o
  have s8s := carry 3 s5s
  have B := behind_fold (K1.qAt Zp Np) _ hb (facts_at_head h).1 (facts_at_head h).2.1
    (sentOf (K1.qAt Zp Np).S) (facts_at_head h).2.2 x.pub.key _ _ _ h8
  obtain ⟨-, d9', k9, s9, h9'⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h9
  simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h9'
  obtain ⟨rfl, -, -⟩ := h9'
  obtain ⟨rs9, gs9, e9⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s9
  have hpU := planOk_head_U h
  have heU := H2K.JointK.early_of_planOk _ hpU
  have haU := H2K.JointK.answers_of_planOk _ hpU
  obtain ⟨c9, -, g9, l9, -⟩ := VerifiableInference.Desc.K12.Coin.onGu_leaves _ heU haU _ _ _ _ e9
  have hq : d8.loc.gOmega ≠ d8.loc.gU := by
    rw [B.gU, B.gOmega]
    decide
  have lt : d8.loc.gOmega < d8.st.groups.size := by
    rw [B.gOmega, B.mid.groups]
    decide
  have hst : ((jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).rec₀ m₃.st.input (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃)).st = d9'.st :=
    (congrArg (fun t : T12 => t.st) (Except.ok.inj hrec)).symm
  have hg : ((jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).rec₀ m₃.st.input (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃)).g = d9'.loc.gOmega :=
    (congrArg (fun t : T12 => t.g) (Except.ok.inj hrec)).symm
  have T3 := three_head_OmegaF h [b1, b2, b3, b4, b5, b6, b7, b8] hb (fun w : Common W₀ Rc TableKey => w.key) colsOpened
    m₃.st.input (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃)
  have hTd := VerifiableInference.Desc.Ground.Sh.tidy_of T3.tidy
  have hSh := shape_head_OmegaF h [b1, b2, b3, b4, b5, b6, b7, b8] hb (fun w : Common W₀ Rc TableKey => w.key) colsOpened
    m₃.st.input (restFront (jobManyO (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO weights rand).toRun.toTest m₃)
  refine Light.ItemLaws.saysAt_of_items _ _ _ C (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
    (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) hTd.inOrder hTd.kinds ?_ ?_ ?_
  · intro i
    rw [hst, hg]
    refine AtFile.open_of_rowsOn ?_ i
    have hall := (VerifiableInference.Desc.K12.Coin.allSay_onGu rdE _ heU haU _ _ _ _ e9 hI8
      d8.loc.gOmega lt hq 0 1 _).2 hRo.1
    have eR : rowsOn d9' d8.loc.gOmega = rowsOn d8 d8.loc.gOmega := by
      unfold rowsOn
      rw [g9 _ lt hq]
    have hlen : (rowsOn d9' d8.loc.gOmega).length = 1 := by
      rw [eR]
      exact hRo.2
    have e1' : ((rowsOn d9' d8.loc.gOmega).drop 0).take 1 = rowsOn d9' d8.loc.gOmega := by
      rw [List.drop_zero]
      exact List.take_of_length_le (Nat.le_of_eq hlen)
    rw [e1'] at hall
    rw [l9]
    exact hall
  · intro G hG
    have hmem := (AtFile.group_at_stand h _ hSh G hG).2
    rw [hmem, hst]
    intro o ho x' hx'
    have hs : Desc.K14.Honest.SmpOwn o d8 (words2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
        (first (K1.qAt Zp Np).codes x.pub.key) W.view.r1 H) := by
      rcases List.mem_cons.1 ho with rfl | ho
      · exact s8o
      · rcases List.mem_cons.1 ho with rfl | ho
        · exact s8s
        · cases ho
    obtain ⟨x₀, hx₀, hs₀⟩ := hs
    have hlt : o < d8.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx₀).1
    have hne : d8.loc.firstMask ≠ some o := by
      rw [B.mask]
      intro e₁
      have e₂ : (1 : ℕ) = o := Option.some.inj e₁
      subst e₂
      simp at ho
    exact (VerifiableInference.Desc.K12.Coin.samples_onGu rdE _ heU haU _ _ _ _ e9 hI8 o hlt hne _).2
      (fun y hy r₁ hr₁ => by
        rw [hx₀] at hy
        obtain rfl := Option.some.inj hy
        exact hs₀ r₁ hr₁) x' hx'
  · intro G hG
    rw [hst, hg] at hG ⊢
    exact hT G hG

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.saysAt_run_O
