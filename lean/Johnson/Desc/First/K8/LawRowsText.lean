-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRowsText.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE LAWS OF ITS RUNNING
TEXT AS CLOSED PROPOSITIONS BY NAME, each with a theorem of just that type: for a list of laws that
counts by name.

Each speaks of the kind's own text, at all its parameters. WHAT ELSE A STATEMENT NAMES (the proved
block's letters, a caller, a setting, a file's description, a seat) IS BOUND BY "FOR ALL" AND PAID
BY NOBODY HERE. Nothing is proved anew: each theorem is one of Law.lean, LawAtS.lean,
LawBefore.lean, LawAnswers.lean, LawView.lean, LawRounds.lean, LawPlaced.lean, with its arguments
bound. The laws under letters stand in Johnson/Desc/First/K8/LawRows.lean [not in this library].
  `HearLaw`: the law at all written transcripts of the round (`hear_law_view`): the block says yes
    and hands on st' if and only if its eight tests hold and st' is what the seat lays from the list
    of the typed challenge of the written verifier message.
  `HearAtRecord`: at the first chain's carried record, with no premise on the place's numbers
    (`yes_atS`).
  `HearOut`: every written transcript of the round has an image, on which the proved block puts out
    the statement with that typed challenge (`out_matrix_all`).
  `HearRounds`: the kind's round has the proved block's shape, and WITH ONE INSTANCE the block's
    error is at most the bound that the planner's routine books at a setting st, which is a letter
    (`rounds_law`). `HearRoundsOfEntry`: the same from the one equation of entries
    (`rounds_law_of_entry`).
  `HearCondition`: the proved block is good at every caller whose sizes are the library's sizes of a
    record (`block_good_atS`): of the numbers it asks lo * hi <= 2 * beta and no more.
  `HearBeforeDraw`: from the file's one test on the plan: every message that the block names is sent
    strictly in front of the round of the draw (`file_before_draw`). `HearBeforeDrawLike`,
    `HearAnswersBeforeDraw`: the same, and the clause on sampled messages, at every block that has
    the kind's rounds, decision, field `before` and tests on the plan. THE ROWS: `K08LawHearing`
    := `HearLaw` and `HearAtRecord` and `HearOut` · `K08RoundsHearing` := `HearRounds` ·
    `K08ConditionHearing` := `HearConditionAt` (wherever the kind's own block says yes at the
    carried record, the place's numbers are those of the library's sizes of the record there, and
    the proved block is good at every caller with these sizes) · `K08Before` :=
    `HearBeforeDrawLike` and `HearAnswersBeforeDraw`.
Limits: those of the files named: each proposition has the premises of its theorem, bound by "for
all": none is paid here.


-/
import Johnson.Desc.First.K8.LawRounds
import Johnson.Desc.First.K8.LawPlaced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Params OnBytes.G4 OnBytes.Slice OnBytes.Maker
  OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles

def HearLaw : Prop :=
  ∀ (S Cl : Type) (p : Par) (s : Size) (hf : Fits p s) (seat : Seat S) (m : (roundT (Run.ckP .two)
      (rdt p)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) (ft : Nat) (st st' : S) (n : Nat) (cols : List
        Col),
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])))
        cols =
        .ok (st', n) ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' ∧ n = 0)

theorem hearLaw : HearLaw := fun _ Cl _ _ hf seat m c ft st st' n cols =>
  hear_law_view (Cl := Cl) hf seat m c ft st st' n cols

def HearAtRecord : Prop :=
  ∀ (Cl : Type) (p : Par) (tl : HTailF2) (c : (wRound (rd p)).Chal) (ft : Nat) (st st' : S) (n :
      Nat)
    (cols : List Col) (r : Fmt.RoundView), st.tl? = some tl → r.vals = [] → r.drawn.elems = [] →
        r.drawn.poss = [] →
    r.drawn.trits = kitTrits c → (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [r] cols = .ok (st', n) →
    ∃ hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size,
      st' = st.putTl { tl with
        cfF := listOf (matrixOf hf c)
        cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } ∧ n = 0

theorem hearAtRecord : HearAtRecord := fun Cl p tl c ft st st' n cols r hst h1 h2 h3 h4 h =>
  yes_atS (Cl := Cl) p tl c ft st st' n cols r hst h1 h2 h3 h4 h

def HearOut : Prop :=
  ∀ (p : Par) (s : Size) (hf : Fits p s) (K : Type) [CommRing K] (Λ : Letters K s) (x : Λ.X) (y :
      Λ.E.Str)
    (m : (wRound (rd p)).Msg) (c : (wRound (rd p)).Chal),
    ∃ t, (carryRng s (rd p) (onlyTrits hf)).tr ((m, c, ()) : Tr [wRound (rd p)]) = some t ∧
      (R Λ).red.out (x, y) t = some ((x, matrixOf hf c), y)

theorem hearOut : HearOut := fun _ _ hf _ _ Λ x y m c => out_matrix_all hf Λ x y m c

def HearRounds : Prop :=
  ∀ (K : Type) (p : Par) (s : Size), Fits p s → ∀ (Λ : Letters K s) (st : Setting),
    p.tau = rngCombinations st .request → st.workOf .small .request = 0 → ∀ (pl q : PlanState), Idle
        st pl →
    planRng (columns p) pl = .ok ((), q) →
    Idle st q ∧ q.rounds = pl.rounds.push (rngRound st (rngSize st (columns p))) ∧
      (rngRound st (rngSize st (columns p))).entry = (round p).entry ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(round p).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st (columns p))).error])

theorem hearRounds : HearRounds := fun _ _ _ hf Λ st ht hw pl q hp h => rounds_law hf Λ st ht hw pl
    q hp h

def HearCondition : Prop :=
  ∀ (d : TailCallerOn) (tl : HTailF2), d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size →
      (KTailRngOn.blk d).Good

theorem hearCondition : HearCondition := fun d tl h => block_good_atS d tl h

def HearBeforeDraw : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (pre post : List (Block F.S₁ F.Cl)),
    F.first.blocksInOrder = pre ++ approximateRangeProofDrawKind seat p :: post → F.planOk = true → ∀ n ∈ p.matsIn ++ p.readsIn,
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ i < roundsIn pre

theorem hearBeforeDraw : HearBeforeDraw := fun _ F seat p pre post hflat hF n hn =>
  file_before_draw F seat p pre post hflat hF n hn

def HearRoundsOfEntry : Prop :=
  ∀ (K : Type) (p : Par) (s : Size), Fits p s → ∀ (Λ : Letters K s) (st : Setting), columns p ≠ 0 →
    (rngRound st (rngSize st (columns p))).entry = (round p).entry → ∀ (pl q : PlanState),
    Idle st pl → planRng (columns p) pl = .ok ((), q) →
    ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(round p).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st (columns p))).error])

theorem hearRoundsOfEntry : HearRoundsOfEntry := fun _ _ _ hf Λ st hc he pl q hp h =>
  rounds_law_of_entry hf Λ st hc he pl q hp h

def HearAnswersBeforeDraw : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (b : Block F.S₁ F.Cl),
    Like seat p b → ∀ (pre post : List (Block F.S₁ F.Cl)), F.first.blocksInOrder = pre ++ b :: post →
    F.planOk = true → ∀ n ∈ p.matsIn ++ p.readsIn,
    ((oraclesOf F.first.blocksInOrder)[n]?).any (fun o => o.tenants.any (·.sampled)) = true →
    ∃ i j r, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ F.roundsDeclaredByBlocks.1[j]? = some r ∧ r.entry.answers ≠ 0 ∧ i < j ∧
      j < roundsIn pre

theorem hearAnswersBeforeDraw : HearAnswersBeforeDraw :=
  fun _ F _ _ _ h pre post hflat hF n hn hs =>
    file_answers_before_draw_like F h pre post hflat hF n hn hs

def HearBeforeDrawLike : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (b : Block F.S₁ F.Cl),
    Like seat p b → ∀ (pre post : List (Block F.S₁ F.Cl)), F.first.blocksInOrder = pre ++ b :: post →
    F.planOk = true → ∀ n ∈ p.matsIn ++ p.readsIn,
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ i < roundsIn pre

theorem hearBeforeDrawLike : HearBeforeDrawLike := fun _ F _ _ _ h pre post hflat hF n hn =>
  file_before_draw_like F h pre post hflat hF n hn

/-- The row: what the kind's block hears at the draw is the proved block's matrix. It holds the
kind's text; of the seat's readings it holds (d), (e), (f) and the writing alone: the row with all
of them held is `K08LawHearingAtRecord` (Johnson/Desc/First/K8/LawRowsMeans.lean). -/
def K08LawHearing : Prop := HearLaw ∧ HearAtRecord ∧ HearOut

theorem k08LawHearing : K08LawHearing := ⟨hearLaw, hearAtRecord, hearOut⟩

/-- The row: the kind's round has the proved block's shape; with ONE instance the block's error, as
a share of the TYPED matrices, is at most the bound that the planner's routine books at a free
setting st. That the made plan's round is that routine's is not said. -/
def K08RoundsHearing : Prop := HearRounds

theorem k08RoundsHearing : K08RoundsHearing := hearRounds

/-- Wherever the kind's own block says yes at the carried record, the place's numbers are those of
the library's sizes of the record that lies there, and the proved block is good at every caller with
these sizes. -/
def HearConditionAt : Prop :=
  ∀ (Cl : Type) (p : Par) (tl : HTailF2) (c : (wRound (rd p)).Chal) (ft : Nat) (st st' : S)
    (n : Nat) (cols : List Col) (r : Fmt.RoundView), st.tl? = some tl → r.vals = [] →
    r.drawn.elems = [] → r.drawn.poss = [] → r.drawn.trits = kitTrits c →
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [r] cols = .ok (st', n) →
    Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size ∧
      ∀ d : TailCallerOn, d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size → (KTailRngOn.blk d).Good

theorem hearConditionAt : HearConditionAt := fun Cl p tl c ft st st' n cols r hst h1 h2 h3 h4 h =>
  ⟨(yes_atS (Cl := Cl) p tl c ft st st' n cols r hst h1 h2 h3 h4 h).choose,
    fun d hd => block_good_atS d tl hd⟩

/-- The row: the proved block's condition on public numbers, at the record at which the kind's own
text says yes. ITS SECOND HALF HANGS ON NO YES AND NO RECORD: the condition is one inequality of
constants, and the caller d is free. It is a part of a condition's row, not the whole: no closed
caller is made of the public record at a place here. -/
def K08ConditionHearing : Prop := HearConditionAt

theorem k08ConditionHearing : K08ConditionHearing := hearConditionAt

/-- The row: THE ORDER OF THE NUMBERS THAT THE PLACE NAMES, from the file's one test on the plan:
each is sent in front of the draw. NOT: that these are the messages which the test's second half
multiplies: any earlier number passes. -/
def K08Before : Prop := HearBeforeDrawLike ∧ HearAnswersBeforeDraw

theorem k08Before : K08Before := ⟨hearBeforeDrawLike, hearAnswersBeforeDraw⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hearLaw
#print axioms VerifiableInference.Desc.First.K8.hearAtRecord
#print axioms VerifiableInference.Desc.First.K8.hearOut
#print axioms VerifiableInference.Desc.First.K8.hearRounds
#print axioms VerifiableInference.Desc.First.K8.hearCondition
#print axioms VerifiableInference.Desc.First.K8.hearBeforeDraw
#print axioms VerifiableInference.Desc.First.K8.hearRoundsOfEntry
#print axioms VerifiableInference.Desc.First.K8.hearAnswersBeforeDraw
#print axioms VerifiableInference.Desc.First.K8.hearBeforeDrawLike
#print axioms VerifiableInference.Desc.First.K8.hearConditionAt
#print axioms VerifiableInference.Desc.First.K8.k08LawHearing
#print axioms VerifiableInference.Desc.First.K8.k08RoundsHearing
#print axioms VerifiableInference.Desc.First.K8.k08ConditionHearing
#print axioms VerifiableInference.Desc.First.K8.k08Before
