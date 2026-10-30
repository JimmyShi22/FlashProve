-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean: THE NAMED TEST ON VALUES AT THE SUB-PROTOCOL "THE ONE EQUATION" PASSES, IN THE FORM IN
WHICH THE RULE ON SHAPES ASKS IT (`ValuesJ`, Honest/Thread/ShapeJV.lean), at the table of steps of the first chain
(`Tab.g`, `Tab.vals`, Johnson/AtFull/Shape/TableOfSteps.lean), at all 25 segments, under the library's hypothesis `AtMgA`. The thread
T, `Said`, the table of falls and the shape a₀ at which the run on shapes starts are variables.

The table's test at these numbers is `oneV` (Johnson/AtFull/Shape/ValsBool.lean): the slots in use are told · four tests on sizes ·
four tests on values.

WHAT IS READ OF THE THREAD: its list of sub-protocols is the chain's own (`hbs`) · the first tree's number is 0 (`hft`) · it begins at the
chain's own first state at some public part of an instance (`hbegun`).

PROVED HERE, BY CALLS. "The slots in use are told", and that a link and a ledger are open: by the yeses of the two sub-protocols in front
(Honest/K9/EqBack.lean). Three of the four tests on values (no weight outside the list; the written-out weights are the product
forms'; a slot with a coefficient is filled): Honest/K9/EqValues.lean's `values_at`. The clause "each product form is well formed" of the
first test on sizes, but for one comparison: by the walk over the verifier's own writes (Honest/K9/EqFormFits.lean), from "in front of the
batching every virtual row is empty but for its weights on columns" (Honest/K9/FrontIs.lean's `bare_at_front`). The fourth test on values
(the row that is made has no coefficient on a pad): Honest/K9/PadShape.lean's `padB_of_shape`, from a Bool on the shape.

TWO FURTHER HYPOTHESES, BOTH CLOSED AND EXECUTABLE.
  `hyes`     the rule's own: the run on shapes returns over n sub-protocols, n beyond this one
  `hsizes`   **A CLOSED, EXECUTABLE TEST ON PUBLIC DATA**, of the same sort: `eqSizesYes g vals a₀ b = true`: the run on shapes over the
             first b sub-protocols returns, and at the shape that it returns the one Bool `oneShape` (Honest/K9/EqShape.lean) accepts. It
             reads no field element, and of the shape the link's context, the ledger and the core alone (`oneShape_reads`). WHAT IT COSTS
             beside the run itself, which `hyes` evaluates anyhow: one pass over the listed arrays of the segment; for each virtual
             row four comparisons of numbers and, for each block of the array's layout, the test on sizes `blockB`
             (Johnson/Desc/First/Batch/Shape/DoorTensor.lean: some tens of steps on lists no longer than the number of index bits);
             for each array two look-ups (the layout's list; the frame's lists of messages) and a membership in the group; and one
             pass over the layout's arrays of all segments: for each that the segment reads, each place of its message's pad against
             each of its blocks. The run's step at this number (`oneA`) makes the first pass's look-ups once more for the row's make.

  `oneV_of`               `oneV` from its clauses
  `eqSizesYes`            the closed test        `vals_at`, `g_at`   the table's test and step at 14 l + `IM.nAt l` + 4 are `oneV`, `oneA`
  `noForm_of_bareL`        rows that are empty but for the weights on columns have no form and no lists
  **`equation_valuesJ`**   the theorem        `equation_field`, `equationHead_field`   the same at the numbers 14 l + 10 + 1 (l < 24) and 337 + 12

Limits. None of the premises is proved here at any thread, shape or public data. Where the thread's invariant never holds, or the table of
falls always speaks, the theorem says nothing. The full size and the hash function `secondHashFunction` alone: the hypothesis's. `ValuesJ` is one of the
hypotheses on one sub-protocol; this file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqShape
import Johnson.Desc.ProofFile.Honest.K9.EqValues
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.K9 (equation asRow St usedOf)
open VerifiableInference.Desc.K9.Shape (outsideV termsB termsV slotsV madeB seatsB maskB padB part_reads)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open Johnson.AtFull.Shape (oneV oneA oneGS ShA shA firstZA cells_link cells_head cell_v cell_g)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- `oneV` from its clauses. -/
theorem oneV_of {s : S} {L : LinkCtx} {F : Fork} {G : Group} (hL : s.link? = some L) (hF : s.fork? = some F)
    (hu : (usedOf s).isSome = true) (t1 : termsB L { F with doorShutF := true } = true)
    (t2 : madeB L { F with doorShutF := true } s.st = true) (hG : s.st.groups[L.check.group]? = some G)
    (t3 : seatsB L { F with doorShutF := true } s.st G = true) (t4 : maskB L.check.frame s.st G F.ns = true)
    (v1 : outsideV L F = true) (v2 : termsV L { F with doorShutF := true } = true)
    (v3 : slotsV { F with doorShutF := true } = true)
    (hp : ∀ q F' y, equation L F = .ok (q, F') →
      asRow L.check.rows L.check.frame q
        ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) = .ok y →
      padB y.2.st L.check.group y.1 = true) : oneV s = true := by
  unfold oneV
  rw [hL, hF]
  simp only [Bool.and_eq_true]
  refine ⟨hu, ⟨⟨⟨⟨⟨⟨t1, t2⟩, ?_⟩, v1⟩, v2⟩, v3⟩, ?_⟩⟩
  · rw [hG]
    show (seatsB L { F with doorShutF := true } s.st G && maskB L.check.frame s.st G F.ns) = true
    rw [t3, t4]
    rfl
  · cases hq : equation L F with
    | error e => rfl
    | ok q =>
      dsimp only
      cases hy : asRow L.check.rows L.check.frame q.1
          ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) with
      | error e => rfl
      | ok y => exact hp q.1 q.2 y hq hy

/-- **The closed test**: the run on shapes over the first b sub-protocols returns, and the one Bool accepts at the shape that it
returns. -/
def eqSizesYes (g : ℕ → ShA → Except String ShA)
    (vals : ℕ → S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Bool) (a₀ : ShA) (b : ℕ) : Bool :=
  match (firstZA g vals).run b a₀ with
  | .ok a => oneShape a.1
  | .error _ => false

/-- The table's cell at the one equation's number. -/
theorem cell_at (Z₀ : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) :
    Johnson.AtFull.Shape.Tab.cells Z₀ G (14 * l + IM.nAt l + 4) = Johnson.AtFull.Shape.Tab.equation := by
  by_cases e24 : l = 24
  · subst e24
    exact cells_head Z₀ G 12 (by omega) rfl
  · have en : 14 * l + IM.nAt l + 4 = 14 * l + 10 + 1 := by
      unfold IM.nAt
      rw [if_neg e24]
    exact cells_link Z₀ G l 10 (by omega) (by omega) en

/-- The table's test there is `oneV`. -/
theorem vals_at (Z₀ : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) : Johnson.AtFull.Shape.Tab.vals Z₀ G (14 * l + IM.nAt l + 4) s rs gs = oneV s := by
  rw [cell_v (cell_at Z₀ G l hl)]
  rfl

/-- The table's step there is `oneA`. -/
theorem g_at (Z₀ : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) : Johnson.AtFull.Shape.Tab.g Z₀ G (14 * l + IM.nAt l + 4) = oneA := by
  rw [cell_g (cell_at Z₀ G l hl)]
  rfl

/-- Rows that are empty but for the weights on columns have no product form and no lists of factors. -/
theorem noForm_of_bareL {G : Fork} (h : BareL G.trees) : NoForm G := by
  intro t e hr
  obtain ⟨h1, h2⟩ := hr
  have e1 : G.trees.getD t {} = G.trees[t] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1]
    rfl
  rw [e1] at h2
  have e2 : _root_.Fo.rowAt G t e = (G.trees[t]).rows[e] := by
    unfold _root_.Fo.rowAt
    rw [e1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
    rfl
  have k := h _ (Array.getElem_mem h1) _ (Array.getElem_mem h2)
  rw [e2]
  exact ⟨congrArg (·.rowForm) k, congrArg (·.rowLo) k, congrArg (·.rowHi) k⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **The named test on values at "the one equation" passes.** -/
theorem equation_valuesJ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hbegun : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ z, s₀ = ProofFile.startS Zp z)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (fall : ℕ → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    (l : ℕ) (hl : l < 25) {n : ℕ} (hn : 14 * l + IM.nAt l + 4 < n)
    (hyes : (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)).yes a₀ n = true)
    (hsizes : eqSizesYes (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀) a₀ (14 * l + IM.nAt l + 4) = true) :
    ValuesJ T Said (shapeJ (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * l + IM.nAt l + 4) := by
  intro blk hblk k s m E ds y cols hA hJ _ _ _ _
  show Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ (14 * l + IM.nAt l + 4) s _ _ = true
  rw [vals_at Zp Bs.G₀ l hl]
  -- the state is reached from the chain's own first state
  have hle : 14 * l + IM.nAt l + 4 ≤ T.bs.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hblk
    exact Nat.le_of_lt hlt
  have hA1 := hA.1
  unfold Thr Thread.Made at hA1
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩, -, -⟩ := hA1
  obtain ⟨z, rfl⟩ := hbegun _ _ _ _ hbeg
  have hr : Reach T.ft T.bs (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s) :=
    reach_of_fold _ hle s _ _ _ _ hfold
  rw [hbs, hft] at hr
  obtain ⟨Lk, p, w, s₂, s₁, χ, y', G, Sd, hr2, -, hBat, -, hrun⟩ := eq_two_back h l hl hr
  obtain ⟨⟨L, hL⟩, ⟨F, hF⟩, hu⟩ := open_of_back h l hl Sd.link hBat hrun
  -- the step on the shape returns
  have hJ' : (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)).run (14 * l + IM.nAt l + 4) a₀ = .ok (shA s) := hJ
  obtain ⟨t, ht⟩ := run_front (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) a₀ n (14 * l + IM.nAt l + 4 + 1) hn hyes
  have ht' : ((firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)).run (14 * l + IM.nAt l + 4) a₀).bind
      (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀ (14 * l + IM.nAt l + 4)) = .ok t := ht
  rw [hJ', g_at Zp Bs.G₀ l hl] at ht'
  have ht2 : oneA (shA s) = .ok t := ht'
  obtain ⟨u, hg⟩ : ∃ u, oneGS (chainSh s) = .ok u := by
    unfold oneA at ht2
    cases hq : oneGS (shA s).1 with
    | error e => rw [hq] at ht2; exact nomatch ht2
    | ok u => exact ⟨u, hq⟩
  -- the one Bool on the shape
  unfold eqSizesYes at hsizes
  rw [hJ'] at hsizes
  have hsz : (oneSizes (chainSh s) && oneFirsts (chainSh s) && padsS (chainSh s)) = true := hsizes
  rw [Bool.and_eq_true, Bool.and_eq_true] at hsz
  -- the clause that the shape does not hold
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain ⟨t₁, hdraw, -, -⟩ := gathered_split p _ s₂ _ y' hBat.gathered
  obtain ⟨a, ha⟩ := draw_open p s₂ t₁ _ hdraw
  have hG : NoForm G := noForm_behind Sd hBat fun F₂ hF₂ =>
    noForm_of_bareL (bare_at_front h.scope h.reads O hl hr2 (part_reads ha).1 hF₂)
  have hfit : fitsB L F = true :=
    fitsB_behind h l hl Lk Sd.link s₁ s hrun
      (fun F₁ hF₁ => by
        obtain rfl : G = F₁ := Option.some.inj (hBat.ledger.symm.trans hF₁)
        exact hG) hsz.1.2 hL hF
  obtain ⟨t1, t2, Gr, hGr, t3, t4⟩ := sizes_of_shape hL hF hsz.1.1 hfit
  obtain ⟨v1, v2, v3⟩ := values_at h l hl hr hg L F hL hF
  exact oneV_of hL hF hu t1 t2 hGr t3 t4 v1 v2 v3 (padB_of_shape hL hF (by rw [hGr]; rfl) hsz.2)

/-- The same at a segment below the head's, at the number as the fold of the sorts spells it. -/
theorem equation_field (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hbegun : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ z, s₀ = ProofFile.startS Zp z)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (fall : ℕ → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    {n : ℕ} (hn : 349 < n) (hyes : (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)).yes a₀ n = true)
    (l : ℕ) (hl : l < 24)
    (hsizes : eqSizesYes (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀) a₀ (14 * l + 10 + 1) = true) :
    ValuesJ T Said (shapeJ (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * l + 10 + 1) := by
  have e : 14 * l + IM.nAt l + 4 = 14 * l + 10 + 1 := by
    unfold IM.nAt
    rw [if_neg (by omega)]
  have k := equation_valuesJ h T hbs hft hbegun Said fall a₀ l (by omega) (n := n) (by rw [e]; omega) hyes
    (by rw [e]; exact hsizes)
  rw [e] at k
  exact k

/-- The same at the head's segment. -/
theorem equationHead_field (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hbegun : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ z, s₀ = ProofFile.startS Zp z)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (fall : ℕ → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    {n : ℕ} (hn : 349 < n) (hyes : (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)).yes a₀ n = true)
    (hsizes : eqSizesYes (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀) a₀ (337 + 12) = true) :
    ValuesJ T Said (shapeJ (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (337 + 12) :=
  equation_valuesJ h T hbs hft hbegun Said fall a₀ 24 (by omega) (n := n) hn hyes hsizes

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.oneV_of
#print axioms ProofFile.Honest.K9.cell_at
#print axioms ProofFile.Honest.K9.vals_at
#print axioms ProofFile.Honest.K9.g_at
#print axioms ProofFile.Honest.K9.noForm_of_bareL
#print axioms ProofFile.Honest.K9.equation_valuesJ
#print axioms ProofFile.Honest.K9.equation_field
#print axioms ProofFile.Honest.K9.equationHead_field
