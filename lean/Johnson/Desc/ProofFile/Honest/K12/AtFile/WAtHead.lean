-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WAtHead.lean: what the library's head pays at the last chain's
proximity test, at every job of several members at its seated place: the plan's side of `OwnStand`
(WStand.lean) and two of its clauses.

  `first_k_W`, `k_head_W`   k = h + g at the first stage
  `rounds_head_W`  the seated block's declared rounds are the written place's
  `public_head_W`  the five facts on the plan that `acceptedS_at_own` asks, and the stages
  `opensFit_head_W`   `OpensFit` at the three trees taken over
  `agree_head_W`   the two parts' readers agree at the coins that the frame lends: `agree_of_ties_letter`
                 at the book's ties (`hT_of_made`)
  `trees_depths`   a job's trees have the depths that it states
  `col_of_hand`    at a stand, a tree in hand shows the thread's table, column for column
  `TakenIs`, `oldAt_taken`   `OldAt` at the three trees taken over, from what each of them is
  `opens_at_own`   the clause `opens` of `OwnStand`

The premises of `oldAt_taken`. `TakenIs` says of one tree of the job and one source that they have one
depth and one column below it. It is the tie of the job's rows at the coins lent to the tables of
the chains that sent them: of the index masks' message and of W to the first chain's, of Omega to the
shared chain's (the sources `.taken 0 1`, `.taken 0 82`, `.taken 1 1`).

Limits.
- `TakenIs` is a premise here, at each of the three trees, and it can be false: it binds the first
  chain's table, a letter of that thread.
- `agree_head_W` takes the book as the maker's (hB).
- At the full size, under the head: the head has a member at named public files alone.
- NOT IN FRONT OF A LAW OVER COINS: `col_of_hand`, `oldAt_taken`, `opens_at_own` stand behind `Thr`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanAtSeat
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensFitLines
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstAtU
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import AtFullSide.K12.TiesAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Johnson.G (proofSendsFull)
open H2K.Member (piWFull codesFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf placeW p12At_place)
open ProofFile.Honest.K12.Light (ManyJob nums_head_W reads_head_W alike_head_W planB_head_W facts_head_W
  facts_WFull rowsMu_many)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
variable {W X : Type}

/-- k = h + g at the first stage of the written place. By the kernel. -/
theorem first_k_W : (piWFull.nums.stages.headD default).k =
    (sgOf (piWFull.nums.stages.headD default)).h + (sgOf (piWFull.nums.stages.headD default)).g := by
  decide +kernel

/-- Under the head k = h + g at the first stage of the seated place. -/
theorem k_head_W (h : P5J.AtMg o Z D r Zp Np cF) :
    ((fourOf Np).W.nums.stages.headD default).k =
      (sgOf ((fourOf Np).W.nums.stages.headD default)).h +
        (sgOf ((fourOf Np).W.nums.stages.headD default)).g := by
  rw [nums_head_W h]
  exact first_k_W

/-- **Under the head the seated test's rounds are the written ones.** -/
theorem rounds_head_W (h : P5J.AtMg o Z D r Zp Np cF) :
    (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).rounds =
      (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds := by
  refine Option.some.inj ?_
  rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ (reads_head_W h).2.2.2,
    ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ facts_WFull.plan, nums_head_W h]

/-- **The facts on the plan**, at a job at the seated place whose fresh table has come earlier. -/
theorem public_head_W (h : P5J.AtMg o Z D r Zp Np cF) (A : ManyJob W X)
    (hp : A.p = (fourOf Np).W) (hfr : A.fresh.isNone = false) :
    planB A.p codesFull 3 = true ∧ formPubB A.p = true ∧
      (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).planOk = true ∧ A.p.early = true ∧
      termLen A.p.nums.stages = (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds.length ∧
      ∃ s t rest, A.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
        PlanPlays A.toRun.toTest s (t :: rest) 0 := by
  have hs : ∃ s t rest, A.p.nums.stages = s :: t :: rest := by
    rw [hp, nums_head_W h]
    exact ⟨_, _, _, rfl⟩
  obtain ⟨s, t, rest, hst⟩ := hs
  have P : PlanPlays A.toRun.toTest s (t :: rest) 0 :=
    planPlays_head_W h A.toRun.toTest hp hfr s (t :: rest) hst
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have e := k_head_W h
    rw [← hp, hst] at e
    exact e
  refine ⟨?_, ?_, ?_, ?_, P.count, s, t, rest, hst, hk, P⟩
  · rw [hp]
    exact planB_head_W h
  · rw [hp]
    exact (facts_head_W h).form
  · rw [hp]
    exact (reads_head_W h).2.2.2
  · rw [hp]
    exact (alike_head_W h).early.trans rfl

/-- **`OpensFit` at a job at the seated place** whose fresh table has come earlier. -/
theorem opensFit_head_W (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false) :
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds [13, 22, 22]
      (fun k => takenLast.getD k (.own 0)) 0 :=
  opensFit_of_B _ _ _ _ _ (by
    rw [hfr, hJ, rounds_head_W h, congrArg (·.stages) (nums_head_W h)]
    exact opensFit_W)

/-- **The two parts' readers agree**, at every coin that the frame lends, at whatever book the maker
returns at the proof file's own description. -/
theorem agree_head_W {V : Type} (h : P5J.AtMg o Z D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (A : ManyJob W X) (hp : A.p = (fourOf Np).W) (f : Addr × ℕ) (hfr : A.fresh = some f)
    (hl : A.mems.length = 3) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hc : lendRow Bk rows look A.p.place
      [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree A.toRun.toTest w fr A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
      (restCoins A.toRun.toTest c.2.1) := by
  refine agree_of_ties_letter A.toRun.toTest f hfr Bk rows look c hc w fr
    (AtFullSide.K12.hT_of_made h.scope h.laid hB A.toRun.toTest (.inr ⟨?_, ?_⟩)) ?_
    fun mem mem' e => rowsMu_many A _ w fr mem mem' e
  · show A.p.place = placeW
    rw [hp]
    exact p12At_place _ _
  · show (A.mems.map (·.sent)).length = 3
    rw [List.length_map]
    exact hl
  · show (A.p.nums.stages.headD default).k = (sgOf (A.p.nums.stages.headD default)).h +
      (sgOf (A.p.nums.stages.headD default)).g
    rw [hp]
    exact k_head_W h

/-- **A job's trees have the depths that it states.** -/
theorem trees_depths (A : ManyJob W X) (w : W) (fr : Front X) (mem : ℕ → Stretch)
    (P : Johnson.Prover.Link.PS) :
    (A.toRun.toTest.trees₀ w fr mem P).map (·.1) = A.trees.map (·.1) := by
  show (((A.trees.map fun T => (T.1, T.2.flatMap (ProofFile.Honest.K12.Light.selsOf A.s₀
    (A.mems.map (·.shape))))).map fun T => ProofFile.Honest.K12.Light.treeOf A.s₀ T P).map (·.1)) = _
  simp only [List.map_map]
  rfl

section
variable {S Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **At a stand, a tree in hand shows the thread's table, column for column, below its depth.** -/
theorem col_of_hand (T : Thread Bk S Cl V W X Pb) {b : ℕ} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} (u : Thr T b k s m E) {σ : Fmt.TreeSource} (hin : σ ∈ T.hand b) {x : ℕ}
    (hx : x < 2 ^ (T.tableAt σ k m).2.logLength) :
    colAt E.tree σ x = (T.tableAt σ k m).2.col x := by
  obtain ⟨⟨-, hH⟩, -⟩ := u
  obtain ⟨pt, hE, -, hs⟩ := Thread.handAt_elim _ (hH _ hin)
  obtain ⟨hlen, hcol⟩ := Table.same_elim hs
  unfold colAt
  rw [hE]
  show pt.2.col x = _
  rw [hcol x (by rw [hlen]; exact hx)]

/-- **One tree of the job and one source have one depth and one column below it.** -/
structure TakenIs (T : Thread Bk S Cl V W X Pb) (k : Coins Bk) (m : Mid W X) (T₀ : List Tree)
    (i : ℕ) (σ : Fmt.TreeSource) : Prop where
  depth : (T₀.getD i (0, fun _ => [])).1 = (T.tableAt σ k m).2.logLength
  col : ∀ x, x < 2 ^ (T₀.getD i (0, fun _ => [])).1 →
    (T.tableAt σ k m).2.col x = (T₀.getD i (0, fun _ => [])).2 x

/-- **`OldAt` at the three trees taken over.** -/
theorem oldAt_taken (T : Thread Bk S Cl V W X Pb) {b : ℕ} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} (u : Thr T b k s m E) (ht : T.taken = takenLast) (T₀ : List Tree)
    (hlen : T₀.length = takenLast.length)
    (h : ∀ i (hi : i < takenLast.length), TakenIs T k m T₀ i takenLast[i]) :
    OldAt E T₀ (fun j => takenLast.getD j (.own 0)) := by
  refine ⟨fun j hj n hn => ?_, fun j hj x hx => ?_⟩
  · have e : takenLast = [.taken 0 1, .taken 0 82, .taken 1 1] := by decide
    have hj' : j < 3 := by
      rw [hlen, e] at hj
      exact hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [e] at hn
  · have hj' : j < takenLast.length := by
      rw [← hlen]
      exact hj
    have I := h j hj'
    have eσ : takenLast.getD j (.own 0) = takenLast[j] := List.getD_eq_getElem _ _ hj'
    have hin : takenLast[j] ∈ T.hand b := by
      show _ ∈ T.taken ++ _
      rw [ht]
      exact List.mem_append_left _ (List.getElem_mem _)
    show colAt E.tree (takenLast.getD j (.own 0)) x = _
    rw [eσ, col_of_hand T u hin (by rw [← I.depth]; exact hx)]
    exact I.col x hx

/-- **The clause `opens` of `OwnStand`.** -/
theorem opens_at_own (h : P5J.AtMg o Z D r Zp Np cF) (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    (A : ManyJob W X) (hp : A.p = (fourOf Np).W) (hfr : A.fresh.isNone = false)
    (hd : A.trees.map (·.1) = [13, 22, 22]) (ht : T.taken = takenLast)
    (hsent : treesTo T.bs b = 0) {k : Coins Bk} {st : S} {m : Mid W X} {E : Env}
    (u : Thr T b k st m E) (mem : ℕ → Stretch) (P : Johnson.Prover.Link.PS)
    (hc : ∀ i (hi : i < takenLast.length),
      TakenIs T k m (A.toRun.toTest.trees₀ m.st.input (frontOf m) mem P) i takenLast[i]) :
    ∃ depths src₀,
      (A.toRun.toTest.trees₀ m.st.input (frontOf m) mem P).map (·.1) = depths ∧
      OpensFit A.toRun.toTest (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E (A.toRun.toTest.trees₀ m.st.input (frontOf m) mem P) src₀ := by
  have hs : E.sent = 0 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := u
    rw [h3, hsent]
  have hm := trees_depths A m.st.input (frontOf m) mem P
  refine ⟨[13, 22, 22], fun j => takenLast.getD j (.own 0), hm.trans hd, ?_,
    oldAt_taken T u ht _ ?_ hc⟩
  · rw [hs]
    exact opensFit_head_W h _ hp hfr
  · have e := congrArg List.length (hm.trans hd)
    rw [List.length_map] at e
    rw [e]
    decide

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.first_k_W
#print axioms ProofFile.Honest.K12.AtFile.k_head_W
#print axioms ProofFile.Honest.K12.AtFile.rounds_head_W
#print axioms ProofFile.Honest.K12.AtFile.public_head_W
#print axioms ProofFile.Honest.K12.AtFile.opensFit_head_W
#print axioms ProofFile.Honest.K12.AtFile.agree_head_W
#print axioms ProofFile.Honest.K12.AtFile.trees_depths
#print axioms ProofFile.Honest.K12.AtFile.col_of_hand
#print axioms ProofFile.Honest.K12.AtFile.oldAt_taken
#print axioms ProofFile.Honest.K12.AtFile.opens_at_own
