-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietLaws.lean: what a yes of the two blocks of
Johnson/Desc/K8/ReadsQuiet.lean says, and what they leave as it is.

Every statement here is on the text's own functions and on those of
Johnson/Desc/First/K8/Order.lean: what a returned value implies about the arguments and the result.

Main names:
  closed_ok, closed_of, closed_fields: the closing: a yes only if the list was open, there is one
    shape a matrix and the guard of order holds; then this very record; and the converse.
  tables_ok: a yes of the head's tables: the plan's list is open, and the tables fill the vector of
    reads.
  layers_ok, head_ok: a yes of a block: the record stands inside such a link; the part that the
    block reads (the own rounds' record; what the head heard) is laid; the closing said yes; and
    the next record, written out.
  layers_frame, head_frame: all that is not the link's part is the same behind a yes.
  orderOk_fixed, fixed_sampled: the guard of order read out, down to the statement's mark
    "sampled".

What is not claimed. What the mark "sampled" means: that is the matter of whoever lays it. That
there is an array at which Order.fixed says yes: no member is shown. That the text is the program's
step. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K8.ReadsQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc (Block Place need named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Order.close Order.front Order.orderOk Order.fixed
  Order.liesAt Order.sentInFront Order.namedNow Order.answered)

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  unfold need at h
  split at h
  · assumption
  · cases h

theorem named_ok {α : Type} {n : String} {x : Option α} {a : α} (h : named n x = .ok a) :
    x = some a := by
  cases x with
  | none => simp [named] at h
  | some y => simp [named] at h; simp [h]

theorem under_ok {α : Type} {n : String} {x : Except String α} {a : α} (h : under n x = .ok a) :
    x = .ok a := by
  cases x with
  | error e => simp [under] at h
  | ok y => simp [under] at h; simp [h]

theorem front_ok {tl : HTailF2} {L : LinkCtx} {S : Statement} {u : Unit}
    (h : Order.front tl L S = .ok u) :
    tl.funClosed = true ∧ (tl.shp.size == tl.NM) = true ∧ Order.orderOk tl L S = true := by
  unfold Order.front at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp_all

theorem close_ok {tl tl' : HTailF2} {funs : Array HFun} (h : Order.close tl funs = .ok tl') :
    tl.funClosed = false ∧ tl' = { tl with funClosed := true, funs := funs } := by
  unfold Order.close at h
  cases hc : tl.funClosed with
  | true => simp [hc] at h
  | false =>
    simp [hc] at h
    exact ⟨rfl, h.symm⟩

/-- **What a yes of the closing says.** -/
theorem closed_ok {tl : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    {tl' : HTailF2} (h : closed tl funs L st = .ok tl') :
    tl.funClosed = false ∧ tl' = { tl with funClosed := true, funs := funs } ∧
      (tl'.shp.size == tl'.NM) = true ∧ Order.orderOk tl' L st = true := by
  unfold closed at h
  cases h1 : Order.close tl funs with
  | error e => simp [h1, bind, Except.bind] at h
  | ok t =>
    simp only [h1, bind, Except.bind] at h
    cases h2 : Order.front t L st with
    | error e => simp [h2] at h
    | ok u =>
      simp only [h2, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨c1, c2⟩ := close_ok h1
      obtain ⟨_, d2, d3⟩ := front_ok h2
      subst h
      subst c2
      exact ⟨c1, rfl, d2, d3⟩

/-- **When the closing says yes**: the converse of closed_ok. -/
theorem closed_of {tl : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    (h0 : tl.funClosed = false)
    (h1 : (tl.shp.size == tl.NM) = true)
    (h2 : Order.orderOk { tl with funClosed := true, funs := funs } L st = true) :
    closed tl funs L st = .ok { tl with funClosed := true, funs := funs } := by
  have h1' : tl.shp.size = tl.NM := by simpa using h1
  unfold closed Order.close Order.front
  simp [h0, h1', h2, bind, Except.bind, pure, Except.pure]

/-- **The record that the closing lays**, field by field, for the block at the next place: the list
is closed; the list is the one handed in; every other field is the plan's record's: among them the
matrices, their number, the number of combinations, the drawn entries and the count of draws. -/
theorem closed_fields {tl : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    {tl' : HTailF2} (h : closed tl funs L st = .ok tl') :
    tl'.funClosed = true ∧ tl'.funs = funs ∧ tl'.NM = tl.NM ∧ tl'.mats = tl.mats ∧
      tl'.tau = tl.tau ∧
      tl'.cfF = tl.cfF ∧ tl'.cfFirst = tl.cfFirst ∧ tl'.foldDrawn = tl.foldDrawn ∧
      tl'.shp = tl.shp ∧ tl'.gtTree = tl.gtTree ∧ tl'.ix = tl.ix := by
  obtain ⟨_, e, _, _⟩ := closed_ok h
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A bind of two refusing steps that returns: both return. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- **What a yes of the head's tables says of the plan's numbers**: the plan's list of tables is
open, and the tables fill the vector of reads. -/
theorem tables_ok {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered} {x : Heard} {t : Tables}
    (e : tables h L hp cov x = .ok t) :
    hp.tl.funClosed = false ∧ (t.p == hp.nU.getD 2 0) = true := by
  unfold tables at e
  obtain ⟨_, e0, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨t', _, e⟩ := bind_ok e
  obtain ⟨_, e9, e⟩ := bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  exact ⟨by simpa using need_ok e0, need_ok e9⟩

/-- **What a yes of the block at a layers' link says, and what it leaves.** -/
theorem layers_ok {P : PG} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (layers P).decide s rs gs = .ok s') :
    ∃ a own tl', s.here = .lay a ∧ a.own = some own ∧
      closed P.tl own.funs a.L s.st = .ok tl' ∧
      s' = { s with here := .lay { a with tl := tl' } } := by
  simp only [layers] at h
  split at h
  · rename_i a ha
    cases ho : a.own with
    | none => simp [ho, bind, Except.bind] at h
    | some own =>
      simp only [ho, Option.elim, bind, Except.bind] at h
      cases hc : closed P.tl own.funs a.L s.st with
      | error e => simp [hc] at h
      | ok tl' =>
        simp only [hc, pure, Except.pure, Except.ok.injEq] at h
        exact ⟨a, own, tl', ha, ho, hc, by rw [ho]; exact h.symm⟩
  · cases h

/-- **What a yes of the block at the head's link says, and what it leaves.** -/
theorem head_ok {P : PH} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (head P).decide s rs gs = .ok s') :
    ∃ a cov x t tl', s.here = .head a ∧ a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧
      a.x = some x ∧ tables P.h P.L P.hp cov x = .ok t ∧
      closed P.hp.tl t.funs a.L s.st = .ok tl' ∧
      s' = { s with here := .head { a with t := some t, tl := tl' } } := by
  simp only [head] at h
  split at h
  · rename_i a ha
    cases h0 : need "reads: the head's link is not opened" a.opened with
    | error e => simp [h0, bind, Except.bind] at h
    | ok u =>
      simp only [h0, bind, Except.bind] at h
      cases h1 : under "reads: the covered positions cannot be said" (s.covered P.h.T P.h.V) with
      | error e => simp [h1] at h
      | ok cov =>
        simp only [h1] at h
        cases hx : a.x with
        | none => simp [hx] at h
        | some x =>
          simp only [hx, Option.elim] at h
          cases h2 : tables P.h P.L P.hp cov x with
          | error e => simp [h2] at h
          | ok t =>
            simp only [h2] at h
            cases h3 : closed P.hp.tl t.funs a.L s.st with
            | error e => simp [h3] at h
            | ok tl' =>
              simp only [h3, pure, Except.pure, Except.ok.injEq] at h
              exact ⟨a, cov, x, t, tl', ha, need_ok h0, under_ok h1, hx, h2, h3,
                by rw [hx]; exact h.symm⟩
  · cases h

/-- **What is owed, and all that is not the link's part, is the same** behind a yes of either
block. -/
theorem layers_frame {P : PG} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (layers P).decide s rs gs = .ok s') :
    s'.rowsOwed = s.rowsOwed ∧ s'.failed = s.failed ∧ s'.st = s.st ∧ s'.book = s.book ∧
      s'.roots = s.roots ∧ s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req := by
  obtain ⟨_, _, _, _, _, _, e⟩ := layers_ok h
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem head_frame {P : PH} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (head P).decide s rs gs = .ok s') :
    s'.rowsOwed = s.rowsOwed ∧ s'.failed = s.failed ∧ s'.st = s.st ∧ s'.book = s.book ∧
      s'.roots = s.roots ∧ s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e⟩ := head_ok h
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The test on one array (Order.fixed), read out: the link's table, the layout and the shape say
where the array lies; its message is sent in front of this place; the frame names that message in
the statement; and the statement marks it as sampled. What the mark means is the matter of whoever
lays it. -/
theorem fixed_sampled {L : LinkCtx} {st : Statement} {t : Nat} (h : Order.fixed L st t = true) :
    ∃ w o x, Order.liesAt L t = some w ∧ Order.sentInFront L w = true ∧
      Order.namedNow L.check.frame w = some o ∧ st.oracles[o]? = some x ∧ x.sampled = true := by
  unfold Order.fixed at h
  cases hw : Order.liesAt L t with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    unfold Order.answered at h2
    cases hn : Order.namedNow L.check.frame w with
    | none => simp [hn] at h2
    | some o =>
      simp only [hn] at h2
      cases ho : st.oracles[o]? with
      | none => simp [ho] at h2
      | some x =>
        simp only [ho] at h2
        exact ⟨w, o, x, rfl, h1, hn, ho, h2⟩

/-- The guard of order, read out: at every symbol array of a matrix, and at each of the four vectors
that is there, the test on one array says yes (fixed_sampled reads that out). -/
theorem orderOk_fixed {tl : HTailF2} {L : LinkCtx} {st : Statement}
    (h : Order.orderOk tl L st = true) :
    tl.gtTree.size = tl.NM ∧ (∀ t ∈ tl.gtTree, Order.fixed L st t = true) ∧
      ∀ n, n < 4 → ∀ t, tl.ix.U.getD n none = some t → Order.fixed L st t = true := by
  unfold Order.orderOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h3, h4, fun n hn t ht => ?_⟩
  have := h5 n hn
  simpa [ht] using this

end VerifiableInference.Desc.K8.ReadsQuiet
