-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Member.lean: an example. The premises of two rows on the smallness test's
first half (`K08LawHearingAtRecord`, Johnson/Desc/First/K8/LawRowsMeans.lean; `K08ConditionHearing`,
Johnson/Desc/First/K8/LawRowsText.lean) can be met together: at the rounds "RNG" of the library's
written list of the full-size proof file's first chain, and at a made-up state.

Two words. A row is here a proposition stated by name, with a theorem of just that type (the word of
these two files). The state is what the verifier carries along the first chain (`S`,
Johnson/Desc/First/State.lean), with the smallness test's own state in it (`HTailF2`,
OnBytes/Model/Tail.lean). The neighbouring files, the docstrings below and names such as
`HearAtRecord` say "record" for that state: there the word means no out-of-domain sample. In
`recordSet` and `record_setting` it does: they are named after the parameter setting "record with
work" (OnBytes/Params/EntryStagesRecord.lean), in which the stored table has such a sample
(lean/GLOSSARY.md, "record").

What it shows, and what not. The two rows are proved "for all", so they would be proved just as well
if nothing met their premises. Here something does: so they are not empty. The place and the state
that meet them are made up, and poor: matrices without rows, no asks, no tables; they are no plan's
and no run's. Tools, and an example; no row is stated here. No theorem here names a description of
the whole protocol; this file is tied to the full-size example by the kernel's facts on the written
list alone.

Where what stands left of the rows' arrows holds.
  `AtWritten st p x`, nine clauses: x is a round of the written chain with `isSmall`; p's number of
    combinations is the setting's (`rngCombinations st .request`); the setting asks no work of this
    round; p's columns times that number are x's matrix entries; p names a message for the matrices
    and one for the reads; p has as many numbers of rows as of columns; none of p's asks has a 0 in
    its two numbers. The setting is a free variable: by itself the structure says of tau nothing
    beyond the product. `at_128`: under `settingB st` (Johnson/Desc/First/K8/MemberPlace.lean) p has
    128 combinations and 24,086 or 10,248 or 20,703 columns.
  For `HearLaw` and `HearOut`: their one premise is `Fits p s`. It holds at every p, by make, at the
    sizes `sizeAt p rest`, which are made of p (`fits_sizeAt`): so by itself it pins nothing, and
    these are not the sizes of a plan's state of the smallness test. What is added here is
    `member_fits`: under `AtWritten` the kind's block at p declares just x's declared form, passes
    its own tests on the plan, and its entry is the one that the planner's routine adds under the
    setting (`placeOk`). `law_at_written`, `out_at_written`: the two conjuncts' conclusions at that
    p and these sizes.
  `HearMeansAtRecord` has no premise.
  For `HearAtRecord` and `HearConditionAt` (six premises): `member_atRecord`: under `ReadyAt p st
    tl` (Johnson/Desc/First/K8/MemberReady.lean): at every written transcript (m, c) of the round
    the six hold together at the round that the library's reading makes of it.
    `atRecord_under_ready`, `condition_under_ready`: so the two conjuncts' conclusions there.
  For `HearOneRound` (a yes of the decision): `member_decide`: under `ReadyAt` the decision says yes
    on every one round.
  `member_both`: a written round, a place that fits it, a ready state: `placeOk`, `Fits` at the
    library's sizes of the state, the state's columns' sum times the setting's number is the
    round's number of matrix entries, and the step's yes.
  The two premises are met together, at made-up values: `exists_both`: at every setting that passes
    `settingB`, for each of the three sorts of written rounds there is a round x of the list with
    `AtWritten` and `ReadyAt` at `madeUpPar`, `madeUpTl` (`madeUp_ready`). Made up are: the split of
    the columns (one column, and the rest), the matrices' numbers of rows (0 and 0), the asks and
    the tables (none), the messages (0 and 1) and the state (`toyIn`,
    Johnson/Desc/First/K8/LawTeeth.lean). They show that the two structures can hold at one p.
    `both_at_madeUp`: `member_both`'s four conclusions there. Which settings pass: the structure's
    default (`default_setting`), which is no plan's; and the library's written setting of the
    full-size parameter lines (`record_setting`, Johnson/Desc/First/K8/MemberSetting.lean).

Limits. All that stands here is a theorem; the facts on the written list are by evaluations in
Lean's kernel (Johnson/G/DryProofSmall.lean), the closed tests here by `decide`. Not shown here:
  that the written list is what the planner makes of the public files (see the head of
    Johnson/G/DryProofLit.lean). The written data `writtenPFull`
    (Johnson/Flat/Dec/FitAtWritten.lean) are made of this list, and in the goals' scope the data
    that the verifier's description holds for the proof file are these written data, or the verifier
    says no to everything (`FlashProve.written_or_no_all`,
    Johnson/Goal/Description/KeyWritten.lean): the description compares what it makes with the
    written values and refuses otherwise (Johnson/Desc/Laid/ProofFullScope.lean). Of the list
    itself: in scope, where `LPFD.Full.proofDataAndDecisionOfPublicFiles` returns, the declared rounds of the description that
    is made, written out, are `dryProofFull`, whose first list this is (`LPFD.Full.laidPOf_rounds`,
    same file). None of these speaks of `planned`;
  that the plan's setting passes `settingB`: the setting is a free variable (in the goals' scope,
    where the planner returns: Johnson/Goal/Numbers/K8SettingInScope.lean);
  that the state in front of the place is ready in a run. Of `ReadyAt`'s nine clauses `link` says
    that tl is what lies in s; that this is the plan's is for whoever opens the link; `matrices`,
    `ks`, `ms`, `tau`, `tabs` are public numbers, evaluated at no public files here; `closed`,
    `nothingOwed`, `notDrawn` (which is double) are the state of the walk: laws on the blocks in
    front of this one in a link, or a run (the form of what a block in front has to leave:
    Johnson/Desc/First/K8/LawReadyRow.lean);
  the plan's own place: of p all but tau, the columns' sum and four conditions of form is free; a
    round of the list is taken by its value, three values, not 25 places.
The second row says something in `Fits` alone: its other half, that the proved block is good at
every caller with the library's sizes of the state, holds at every state with no premise
(`good_at_sizes`), and no caller is named here. No example is given here for the row `K08Before`,
whose premises ask a description of a whole file; for the row on the round's price,
`K08RoundsHearing` (of its five premises the first holds by make, `AtWritten` holds the second and
the third; the two on the planner's state are met by no term here); or for the rows on the round's
count. So "the rows on this block are not empty" is not shown whole. How much the made-up values
bear: of the eighteen clauses of `AtWritten` and `ReadyAt` two hold idly there (`AtWritten.asks`
speaks of the members of an empty list; `ReadyAt.tabs` equates two empty lists), `ReadyAt.ms`
equates [0, 0] with [0, 0], and `nothingOwed` and `notDrawn` hold because nothing was ever owed or
drawn in that state. Of the other thirteen, five stand at the written list's and the setting's own
numbers (`mem`, `small`, `AtWritten.tau`, `work`, `columns`); the other eight hold between values
that one hand made up (two of them say "not empty" and no more). The made-up state itself: `toyIn`
is made of `S.blank` (Johnson/Desc/First/State.lean), the state that stands for "no lawful start".
It bears a mark of failure (`failed`), which this block does not read and at which the chain's last
test (`S.fin`) says no. An example cannot say no: it fails by not compiling; where the tests named
here say no is in Johnson/Desc/First/K8/MemberTeeth.lean. Nothing on soundness.
-/
import Johnson.Desc.First.K8.MemberPlace
import Johnson.Desc.First.K8.LawTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open VerifiableInference.Number (isSmall)
open VerifiableInference.Number.Written (written_shape written_div exists_written)
open OnBytes.Params (Setting rngCombinations)
open Johnson.G (dryProofFull)
open Iop Prob Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
  OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles

/-- A place's numbers fit a written round and a setting. -/
structure AtWritten (st : Setting) (p : Par) (x : Fmt.Round × List Fmt.Stored) : Prop where
  mem : x ∈ dryProofFull.1
  small : isSmall x.1.entry = true
  tau : p.tau = rngCombinations st .request
  work : st.workOf .small .request = 0
  columns : columns p * p.tau = x.1.entry.trits
  mats : p.matsIn ≠ []
  reads : p.readsIn ≠ []
  rows : p.ms.length = p.ks.length
  asks : ∀ a ∈ p.asks, a.2.1 ≠ 0 ∧ a.2.2 ≠ 0

/-- **Under `AtWritten`**: the test on the place; and the premise of `HearLaw` and `HearOut`, which
holds at every p. -/
theorem member_fits {st : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored}
    (A : AtWritten st p x) (rest : Size) :
    placeOk st p { entry := x.1.entry } = true ∧ Fits p (sizeAt p rest) :=
  ⟨(member_place A.mem A.small st p A.tau A.work A.columns A.mats A.reads A.rows A.asks).1,
    fits_sizeAt p rest⟩

/-- **Under the test on the setting**: 128 combinations, and one of the three sums of columns. -/
theorem at_128 {st : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored}
    (hs : settingB st = true) (A : AtWritten st p x) :
    p.tau = 128 ∧ columns p ∈ [24086, 10248, 20703] := by
  have t : p.tau = 128 := A.tau.trans (settingB_yes hs).1
  obtain ⟨_, _, _, _, _, hm, _⟩ := written_shape A.mem A.small
  have c := A.columns
  rw [t] at c
  rw [← c] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact ⟨t, by omega⟩

/-- `HearLaw`'s conclusion there. -/
theorem law_at_written {S' Cl : Type} {st₀ : Setting} {p : Par}
    {x : Fmt.Round × List Fmt.Stored} (A : AtWritten st₀ p x) (rest : Size) (seat : Seat S')
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (ft : Nat) (st st' : S') (n : Nat) (cols : List Col) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st
        (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) cols = .ok (st', n) ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st (listOf (matrixOf (member_fits A rest).2 c)) (firstColumns p) = .ok st' ∧
        n = 0) :=
  hearLaw S' Cl p _ (member_fits A rest).2 seat m c ft st st' n cols

/-- `HearOut`'s conclusion there. -/
theorem out_at_written {st₀ : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored}
    (A : AtWritten st₀ p x) (rest : Size) (K : Type) [CommRing K] (Λ : Letters K (sizeAt p rest))
    (a : Λ.X) (y : Λ.E.Str) (m : (wRound (rd p)).Msg) (c : (wRound (rd p)).Chal) :
    ∃ t, (carryRng (sizeAt p rest) (rd p) (onlyTrits (member_fits A rest).2)).tr
        ((m, c, ()) : Tr [wRound (rd p)]) = some t ∧
      (R Λ).red.out (a, y) t = some ((a, matrixOf (member_fits A rest).2 c), y) :=
  hearOut p _ (member_fits A rest).2 K Λ a y m c

/-- **The six premises of `HearAtRecord` and `HearConditionAt`, together, under `ReadyAt`.** -/
theorem member_atRecord {Cl : Type} {p : Par} {st : S} {tl : HTailF2} (R : ReadyAt p st tl)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (ft : Nat) (cols : List Col) :
    st.tl? = some tl ∧ (rvOne (rdt p) m c).vals = [] ∧ (rvOne (rdt p) m c).drawn.elems = [] ∧
      (rvOne (rdt p) m c).drawn.poss = [] ∧
      (rvOne (rdt p) m c).drawn.trits = kitTrits (p := p) c ∧
      (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [rvOne (rdt p) m c] cols =
        .ok (st.putTl { tl with
          cfF := listOf (matrixOf (fits_of_ready R) c), cfFirst := firstColumns p }, 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := view_round (fits_of_ready R) m c
  have h := step_yes_of_ready (Cl := Cl) R m c ft cols
  rw [vT_one] at h
  exact ⟨R.link, h1, h2, h3, h4, h⟩

/-- **The premise of `HearOneRound`, under `ReadyAt`**: the decision says yes on every one round. -/
theorem member_decide {Cl : Type} {p : Par} {st : S} {tl : HTailF2} (R : ReadyAt p st tl)
    (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide st [r] gs =
      .ok (st.putTl { tl with cfF := r.drawn.trits.toArray, cfFirst := firstColumns p }) :=
  (decide_iff_ready p st _ r gs).2 ⟨tl, R, rfl⟩

/-- `HearAtRecord`'s conclusion under `ReadyAt`. By proof irrelevance its equation says that the
first columns of the place are the record's walk, and no more. -/
theorem atRecord_under_ready {p : Par} {st : S} {tl : HTailF2} (R : ReadyAt p st tl)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) :
    ∃ hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size,
      st.putTl { tl with
          cfF := listOf (matrixOf (fits_of_ready R) c), cfFirst := firstColumns p } =
        st.putTl { tl with
          cfF := listOf (matrixOf hf c)
          cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := member_atRecord (Cl := Unit) R m c 0 []
  obtain ⟨hf, e, _⟩ := hearAtRecord Unit p tl c 0 st _ 0 [] _ a0 a1 a2 a3 a4 a5
  exact ⟨hf, e⟩

/-- `HearConditionAt`'s conclusion under `ReadyAt`. Its second half reads no clause of it. -/
theorem condition_under_ready {p : Par} {st : S} {tl : HTailF2} (R : ReadyAt p st tl)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) :
    Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size ∧
      ∀ d : TailCallerOn, d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size →
        (KTailRngOn.blk d).Good := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := member_atRecord (Cl := Unit) R m c 0 []
  exact hearConditionAt Unit p tl c 0 st _ 0 [] _ a0 a1 a2 a3 a4 a5

/-- **Both together**: a written round, a place that fits it, a ready record. -/
theorem member_both {Cl : Type} {st₀ : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored}
    {st : S} {tl : HTailF2} (A : AtWritten st₀ p x) (R : ReadyAt p st tl)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (ft : Nat) (cols : List Col) :
    placeOk st₀ p { entry := x.1.entry } = true ∧
      Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size ∧
      (tl.mats.toList.map (·.k)).sum * rngCombinations st₀ .request = x.1.entry.trits ∧
      ∃ st', (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [rvOne (rdt p) m c] cols = .ok (st', 0) := by
  refine ⟨(member_fits A (OnBytes.Tie.Pv.Tail.sizeOf tl).size).1, fits_of_ready R, ?_,
    _, (member_atRecord (Cl := Cl) R m c ft cols).2.2.2.2.2⟩
  rw [R.ks, ← A.columns, ← A.tau]
  unfold columns
  rw [foldl_add, Nat.zero_add]

/-! ## The two premises can hold together: at made-up values -/

/-- The default setting gives 128 combinations. -/
theorem default_combinations : rngCombinations {} .request = 128 := by decide

/-- The default setting passes the test on a setting. -/
theorem default_setting : settingB {} = true := by decide

/-- A made-up place: two matrices, of one column and of c. -/
def madeUpPar (c : Nat) : Par :=
  { link := 0, piece := 5, ks := [1, c], ms := [0, 0], tau := 128, asks := [], matsIn := [0]
    readsIn := [1] }

/-- A made-up record of the smallness test with these numbers, its list of tables closed. -/
def madeUpTl (c : Nat) : HTailF2 :=
  { tau := 128, NM := 2, mats := #[{ k := 1 }, { k := c }], funClosed := true }

/-- The made-up record is ready for the made-up place. -/
theorem madeUp_ready (c : Nat) : ReadyAt (madeUpPar c) (toyIn (madeUpTl c)) (madeUpTl c) :=
  ⟨rfl, rfl, Or.inl rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- **`AtWritten` and `ReadyAt` hold together, for each of the three sorts**, at every setting that
passes `settingB`, and the made-up place and record. -/
theorem exists_both {st : Setting} (hb : settingB st = true) {n : Nat}
    (h : n ∈ [3083008, 1311744, 2649984]) :
    ∃ x : Fmt.Round × List Fmt.Stored, x.1.entry.trits = n ∧
      AtWritten st (madeUpPar (n / 128 - 1)) x ∧
      ReadyAt (madeUpPar (n / 128 - 1)) (toyIn (madeUpTl (n / 128 - 1)))
        (madeUpTl (n / 128 - 1)) := by
  obtain ⟨x, hx, hs, e⟩ := exists_written h
  obtain ⟨hd, hm⟩ := written_div h
  have h1 : 1 ≤ n / 128 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  refine ⟨x, e, ⟨hx, hs, (settingB_yes hb).1.symm, (settingB_yes hb).2.1, ?_,
    List.cons_ne_nil _ _, List.cons_ne_nil _ _, rfl, fun _ h => nomatch h⟩, madeUp_ready _⟩
  rw [e]
  show List.foldl (· + ·) 0 [1, n / 128 - 1] * 128 = n
  simp only [List.foldl_cons, List.foldl_nil]
  omega

/-- `member_both`'s four conclusions there, at every written transcript of the round. -/
theorem both_at_madeUp {Cl : Type} {st : Setting} (hb : settingB st = true) {n : Nat}
    (h : n ∈ [3083008, 1311744, 2649984])
    (m : (roundT (Run.ckP .two) (rdt (madeUpPar (n / 128 - 1)))).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt (madeUpPar (n / 128 - 1)))).up.Chal)
    (ft : Nat) (cols : List Col) :
    ∃ x : Fmt.Round × List Fmt.Stored, x.1.entry.trits = n ∧
      placeOk st (madeUpPar (n / 128 - 1)) { entry := x.1.entry } = true ∧
      Fits (madeUpPar (n / 128 - 1)) (OnBytes.Tie.Pv.Tail.sizeOf (madeUpTl (n / 128 - 1))).size ∧
      ((madeUpTl (n / 128 - 1)).mats.toList.map (·.k)).sum * rngCombinations st .request = n ∧
      ∃ st', (approximateRangeProofDrawKind (Cl := Cl) atS (madeUpPar (n / 128 - 1))).step ft
        (toyIn (madeUpTl (n / 128 - 1))) [rvOne (rdt (madeUpPar (n / 128 - 1))) m c] cols =
          .ok (st', 0) := by
  obtain ⟨x, e, A, R⟩ := exists_both hb h
  obtain ⟨a, b, c', d⟩ := member_both (Cl := Cl) A R m c ft cols
  exact ⟨x, e, a, b, c'.trans e, d⟩

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.member_fits
#print axioms VerifiableInference.Desc.First.K8.Member.at_128
#print axioms VerifiableInference.Desc.First.K8.Member.law_at_written
#print axioms VerifiableInference.Desc.First.K8.Member.out_at_written
#print axioms VerifiableInference.Desc.First.K8.Member.member_atRecord
#print axioms VerifiableInference.Desc.First.K8.Member.member_decide
#print axioms VerifiableInference.Desc.First.K8.Member.atRecord_under_ready
#print axioms VerifiableInference.Desc.First.K8.Member.condition_under_ready
#print axioms VerifiableInference.Desc.First.K8.Member.member_both
#print axioms VerifiableInference.Desc.First.K8.Member.default_combinations
#print axioms VerifiableInference.Desc.First.K8.Member.default_setting
#print axioms VerifiableInference.Desc.First.K8.Member.madeUp_ready
#print axioms VerifiableInference.Desc.First.K8.Member.exists_both
#print axioms VerifiableInference.Desc.First.K8.Member.both_at_madeUp
