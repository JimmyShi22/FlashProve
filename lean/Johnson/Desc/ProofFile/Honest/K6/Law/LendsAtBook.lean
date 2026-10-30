-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/LendsAtBook.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): THE
BOOK LENDS K6's ROW OF PARTS, AT EVERY BOOK THAT THE WHOLE BOOK's MAKER RETURNS AT THE HEAD's OWN
DESCRIPTION: under the hypothesis h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) AND "THE MAKER RETURNS".
No definition; ten theorems.

  `k6_rounds_at_head`     under h the member at K6's place declares the kind's rounds at 10 and 13
  `k6_seedless_at_head`   none of them is named "SEND seed"
  `k6_parts_written`      the maker's eight parts at such a block, written
  `k6_stated_closed`      a closed fact, by Lean's kernel: what the maker lays for these eight
                          parts, by name and count
  `k6_stated_is_spends`   K6's OWN "stated = spends": that is what the eight parts state
  `k6_plain`              the parts take no coin of their own and carry nothing
  `k6_fits_at_book`       h, hB: THE THREE EQUATIONS OF PUBLIC LISTS at each of the eight parts
  `k6_lends_at_book`      h, hB: the public test `lendsRow` says yes
  `k6_lends_at_atPure`    h, hA: the same at the book of the prover that the frame's maker returns
  `k6_row_is_lent`        h, hA: so the seated row is given its coins at every run's coins

By, of other authors, all called and none typed anew: `lendsRow_of_fit`
(Honest/Small/LendsRowOf.lean) over `lendPart_of_fit` (Honest/BookLends.lean); `wants_at_plain`,
`no_merge_of_kind` and `stated` (Honest/Small/WantsStated.lean): no kind is named in them;
`plain_no_row`, `plain_all_spent` (Honest/BookPlain.lean); `pick_whole`
(Honest/BookRowStretch.lean), whose `BookRow.pick a l` is the text of `spentE` on a list;
`bookWhole_word` (Honest/AtPureLaw.lean); `orderOf_nodup` (Honest/Law/Rule/Tests.lean);
`lendsRow_iff` through our `k6_lent_iff` (Honest/K6/Law/LentIsPublic.lean).

What it is not.
  * hB | hA ARE PREMISES: that the book's maker, or the frame's, returns at any files is not shown
    here.
  * NOTHING ON WHAT IS LENT: a test on counts and names; "something is returned".
  * It pays no field of `K6HeadBelow`. At the book A.B and chain 0 its end is the text of the
    premise on the lending of `k6_spent_in_range_public` (Honest/K6/Law/LentIsPublic.lean), which
    stands at the thread's own chain's number: that join is not typed here.
  * The public test on the sender's part, under which the reader of the mask row is had
    (Honest/K6/Law/ReaderAtTake.lean), is ANOTHER TEST, at a part that carries: not reached here.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRowOf
import Johnson.Desc.ProofFile.Honest.Small.WantsStated
import Johnson.Desc.ProofFile.Honest.BookPlain
import Johnson.Desc.ProofFile.Honest.K6.Law.StretchAtBook
import Johnson.Desc.ProofFile.Honest.K6.Law.SpendsWritten
import Johnson.Desc.ProofFile.Honest.K6.Law.CarriesNone
import Johnson.Desc.ProofFile.Honest.K6.Law.LentIsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Kinds (Head.Par Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- CONDITIONAL: the hypothesis h. The member at K6's place declares the kind's rounds at lt = 10
and lPd = 13. -/
theorem k6_rounds_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) :
    b.rounds = (headRoundsOf 10 13).map fun q =>
      { entry := q.entry (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).work } := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have Fu : HeadFull (P5J.At.X Zp) := by
    have q := headFull_in_scope h.scope h.reads O.public
    rw [O.W] at q
    exact q
  have hlt : headLt (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 10 := Fu.lt
  have hlP : headLPd (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 13 := by
    show (letI := (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes;
      VerifiableInference.Desc.Kinds.Norm.lPd) = 13
    unfold VerifiableInference.Desc.Kinds.Norm.lPd
    rw [show (letI := (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes;
      VerifiableInference.Desc.Kinds.Norm.d) = 5120 from Fu.num.d]
    decide
  rw [(head_seated_at_head h b hb hp).1, headRounds_are, hlt, hlP]

/-- CONDITIONAL: the hypothesis h. None of its rounds is named "SEND seed". -/
theorem k6_seedless_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) :
    ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed" := by
  intro r' hr'
  rw [k6_rounds_at_head h hb hp] at hr'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr'
  exact bne_iff_ne.1 (List.all_eq_true.1 k6_no_seed q hq)

/-- The maker's eight parts at a block of the kind K6 that declares these rounds, written. -/
theorem k6_parts_written {S Cl : Type} {b : Block S Cl} {w : Nat} (hk : b.place.kind = .K6)
    (hr : b.rounds = (headRoundsOf 10 13).map fun q => { entry := q.entry w }) :
    planParts b = (stretchesBy ((headRoundsOf 10 13).map fun q => (q.name, q.sent))
      [1, 1, 26, 1, 1, 13, 13, 26]).zipIdx.map fun y => ⟨⟨b.place, y.2⟩, y.1⟩ := by
  unfold planParts partsCut
  rw [hr, hk, k6_names_of, k6_pairs_of, k6_cut_closed]

set_option maxRecDepth 100000 in
/-- A CLOSED FACT, BY LEAN's KERNEL: what the book's maker lays for these eight parts, by name and
count. -/
theorem k6_stated_closed :
    ((stretchesBy ((headRoundsOf 10 13).map fun q => (q.name, q.sent))
      [1, 1, 26, 1, 1, 13, 13, 26]).zipIdx.map fun y =>
        Small.stated ⟨⟨IM.k6Place, y.2⟩, y.1⟩) =
      [[], [(headRunName IM.k6Place 1 "scalars", ⟨0, 9⟩)],
       [(headRunName IM.k6Place 2 "sum", ⟨0, 49⟩), (headRunName IM.k6Place 2 "ends", ⟨0, 2⟩)],
       [], [(headRunName IM.k6Place 4 "scalars", ⟨0, 7⟩)],
       [(headRunName IM.k6Place 5 "sum", ⟨0, 24⟩), (headRunName IM.k6Place 5 "ends", ⟨0, 4⟩)],
       [(headRunName IM.k6Place 6 "sum", ⟨0, 24⟩), (headRunName IM.k6Place 6 "ends", ⟨0, 2⟩)],
       [(headRunName IM.k6Place 7 "sum", ⟨0, 50⟩), (headRunName IM.k6Place 7 "ends", ⟨0, 2⟩)]] := by
  decide +kernel

/-- CONDITIONAL: the hypothesis h. **K6's OWN "stated = spends".** -/
theorem k6_stated_is_spends (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) :
    (planParts b).map Small.stated =
      (headParts (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).map
        (·.spends) := by
  have hk : b.place.kind = .K6 := by rw [hp]
  rw [k6_parts_written hk (k6_rounds_at_head h hb hp), List.map_map, hp,
    k6_spends_at_head h IM.k6Place]
  exact k6_stated_closed

/-- GENERAL. K6's parts are plain: they take no coin of their own and carry nothing. -/
theorem k6_plain (p : Head.Par) (at_ : Place) :
    ∀ q ∈ headParts p at_, q.takes = ⟨0, 0⟩ ∧ q.carries = [] := by
  intro q hq
  refine ⟨?_, k6_carries_nil p at_ q hq⟩
  have h : q.takes ∈ (headParts p at_).map (·.takes) := List.mem_map.2 ⟨q, hq, rfl⟩
  rw [k6_takes_closed] at h
  exact List.eq_of_mem_replicate h

/-- CONDITIONAL: h; hB. **THE THREE EQUATIONS OF PUBLIC LISTS, AT EACH OF K6's EIGHT PARTS.** -/
theorem k6_fits_at_book (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {p0 p1 p2 : Johnson.G.ChainSends} {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    ∀ i p, (headParts (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place)[i]? =
        some p →
      p.takes = dueAt (Bk.rowsOf 0) ⟨IM.k6Place, i⟩ ∧
      (spentE Bk ⟨IM.k6Place, i⟩).map Ahead.named = p.spends ∧
      (carryE Bk ⟨IM.k6Place, i⟩).map Ahead.named = p.carries := by
  intro i p hi
  obtain ⟨b, hb, hp⟩ := k6_member_there h
  have hpo := k6_placesOk_at_head h
  have hk : b.place.kind = .K6 := by rw [hp]
  have hs := k6_seedless_at_head h hb hp
  have hf : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon" :=
    (k6_numbers_of_rounds hk (k6_rounds_at_head h hb hp) cF.blocksInOrder).2.2.2
  obtain ⟨t1, t2⟩ := k6_plain _ _ p (List.mem_of_getElem? hi)
  have h3 : dueAt Bk.first ⟨b.place, i⟩ = ⟨0, 0⟩ :=
    plain_no_row (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) hB hpo (b := b) hb hs i
  have h4 : ∀ e ∈ Bk.ahead, e.spender.place = b.place → e.once = true :=
    plain_all_spent (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) hB hpo (b := b) hb hs hf
  rw [← hp]
  refine ⟨?_, ?_, ?_⟩
  · rw [t1]
    exact h3.symm
  · obtain ⟨idx, a, -, ha, -, hpk⟩ :=
      pick_whole (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) hB hpo (b := b) hb hf
    have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
      (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hpo)).1).1
    have hw := Small.wants_at_plain ha hn hb (l := 24) (congrArg Place.link hp) i
      (Small.no_merge_of_kind _ ⟨b.place, i⟩ (by rw [hk]; decide) (by rw [hk]; decide))
    have e2 : ((planParts b)[i]?).map Small.stated = some p.spends := by
      have e := congrArg (fun l => l[i]?) (k6_stated_is_spends h hb hp)
      simp only [List.getElem?_map] at e
      rw [hi] at e
      exact e
    show (BookRow.pick ⟨b.place, i⟩ Bk.ahead).map Ahead.named = p.spends
    rw [hpk i, hw]
    -- the same sentence, with the description's own types unfolded
    show (((planParts b)[i]?).toList).flatMap Small.stated = p.spends
    cases hq : (planParts b)[i]? with
    | none =>
      rw [hq] at e2
      exact absurd e2 (by simp)
    | some q =>
      rw [hq] at e2
      have e3 : Small.stated q = p.spends := Option.some.inj e2
      simpa using e3
  · rw [t2]
    have e0 : carryE Bk ⟨b.place, i⟩ = [] := by
      unfold carryE
      apply List.filter_eq_nil_iff.2
      intro e he
      have h1 := List.mem_filter.1 he
      have h2 : e.spender = ⟨b.place, i⟩ := beq_iff_eq.1 h1.2
      rw [h4 e h1.1 (by rw [h2])]
      decide
    rw [e0]
    rfl

/-- CONDITIONAL: h; hB. **THE BOOK LENDS K6's ROW, AT EVERY BOOK THAT THE WHOLE BOOK's MAKER RETURNS
AT THE HEAD's OWN DESCRIPTION.** -/
theorem k6_lends_at_book (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {p0 p1 p2 : Johnson.G.ChainSends} {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    lendsRow Bk 0 IM.k6Place
      (headParts (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place) = true := by
  obtain ⟨b, hb, hp⟩ := k6_member_there h
  have ha : IM.k6Place ∈ placesAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 0 := by
    show IM.k6Place ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)
    exact List.mem_map.2 ⟨b, hb, hp⟩
  exact lendsRow_of_fit (bookWhole_word hB) (k6_placesOk_at_head h) (Or.inl rfl) ha _
    (k6_fits_at_book h hB)

/-- CONDITIONAL: h; hA. The same at the book of the prover that the frame's maker returns at the
head's own files, at any filling P. -/
theorem k6_lends_at_atPure (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    lendsRow A.B 0 IM.k6Place
      (headParts (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place) = true := by
  obtain ⟨p0, p1, p2, hB⟩ := k6_book_of_atPure hA
  have eF : A.F = (P5J.F0T OnBytes.secondHashFunction Zp Np cF) :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  rw [eF] at hB
  exact k6_lends_at_book h hB

/-- CONDITIONAL: h; hA. **SO THE SEATED ROW IS GIVEN ITS COINS AT EVERY RUN's COINS**, at every
maker of the small input. What it is given is not said. -/
theorem k6_row_is_lent (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (k : Coins A.B) :
    ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) IM.k6Place
      (headRow (X := X) wit (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place) 0 =
        .ok c :=
  (k6_lent_iff k 0 wit _ IM.k6Place).2 (k6_lends_at_atPure h hA)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_rounds_at_head
#print axioms ProofFile.Honest.K6.k6_seedless_at_head
#print axioms ProofFile.Honest.K6.k6_parts_written
#print axioms ProofFile.Honest.K6.k6_stated_closed
#print axioms ProofFile.Honest.K6.k6_stated_is_spends
#print axioms ProofFile.Honest.K6.k6_plain
#print axioms ProofFile.Honest.K6.k6_fits_at_book
#print axioms ProofFile.Honest.K6.k6_lends_at_book
#print axioms ProofFile.Honest.K6.k6_lends_at_atPure
#print axioms ProofFile.Honest.K6.k6_row_is_lent
