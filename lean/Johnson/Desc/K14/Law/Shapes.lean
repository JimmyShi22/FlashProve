-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Shapes.lean: THE BOOK-KEEPING ON THE SHARED CHAIN's OWN RECORD BEHIND o_u's
SENDING, AS A TEST WITH CODE, AND WHAT RIDES PAST "(rec_gamma)" AND "LOC". For the filling of a
table of joints whose promise has a Bool "shape k" and whose items are classes of open rows.

  shapedUB, seatedUB, seatedUB_iff   o_u's entry in the statement has the public shape; its layout
                  in the small record is that of the shape at the record's own codes; the public
                  shape meets its conditions at these codes.
  on4_of_seatedUB it gives what the laws of "(rec_gamma)" and "LOC" spend of the promise (On4).
  noted_of_seatedUB   and that the number noted for o_u is a number of a message.
  shapeU p nU c s **the test**: the key fits and the point has kCol coordinates (shape2,
                  Johnson/Desc/K14/Law/PointCounts.lean); seatedUB; the number that the record notes
                  for o_u is nU (the plan's); G_u has just c open rows.
  laysRec_rows, loc_rows   the rows that the two places lay, and how many.
  shapeU_rec, shapeU_loc   **it is earned**: at a yes of "(rec_gamma)" c grows by the record's
                  answers; at a yes of "LOC" by the number of positions drawn.
  value_same, allSay_same   where the statement grows and no message comes, a constraint says the
                  same of words.
  slice_old, rowsU_back   **the older rows ride back**: past a place that lays its rows behind them.

What is not claimed. That any record passes the test. Nothing on o_omega, the joinings, "LIN zeta"
or "SPLIT". No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.RowsCore
import Johnson.Desc.K14.Law.KeepsMsgs
import Johnson.Desc.K14.Law.PointCounts
import Johnson.Desc.K1.Law.GoodSendAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (SameMsgs size_of_same)

/-- o_u's entry in the statement has the public shape. -/
def shapedUB (p : Par) (s : St) : Bool :=
  match s.st.oracles[s.loc.oU.oracle]? with
  | some x => decide (x.shape = p.S.fold.u)
  | none => false

/-- o_u is seated, as a test on the record. -/
def seatedUB (p : Par) (s : St) : Bool :=
  shapedUB p s && decide (s.loc.oU.lay = vectorLay s.st.codes p.S.fold.u p.S.fold.rowsHigh) &&
    linOk s.st.codes p.S

/-- What the test says. -/
theorem seatedUB_iff (p : Par) (s : St) : seatedUB p s = true ↔
    (∃ x, s.st.oracles[s.loc.oU.oracle]? = some x ∧ x.shape = p.S.fold.u) ∧
      s.loc.oU.lay = vectorLay s.st.codes p.S.fold.u p.S.fold.rowsHigh ∧
      linOk s.st.codes p.S = true := by
  unfold seatedUB shapedUB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h2, h3⟩
    cases hx : s.st.oracles[s.loc.oU.oracle]? with
    | none =>
      rw [hx] at h1
      cases h1
    | some x =>
      rw [hx] at h1
      exact ⟨x, rfl, of_decide_eq_true h1⟩
  · rintro ⟨⟨x, hx, hs⟩, h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [hx]
    exact decide_eq_true hs

/-- It gives what the laws of "(rec_gamma)" and "LOC" spend of the promise. -/
theorem on4_of_seatedUB (p : Par) (s : St) (h : seatedUB p s = true) :
    p.S.fold.index.ok = true ∧ ∀ T', Grows s.st T' → PlacedU T' p.S.fold s.loc.oU := by
  obtain ⟨hx, h2, h3⟩ := (seatedUB_iff p s).1 h
  have hSeat : SeatedU s.st s.st.codes p.S s.loc.oU := ⟨rfl, hx, h2⟩
  exact ⟨index_ok_of_linOk _ _ h3, fun T g => placedU_of_seatedU (hSeat.grows g) h3⟩

/-- The number noted for o_u is a number of a message. -/
theorem noted_of_seatedUB (p : Par) (s : St) (h : seatedUB p s = true) :
    s.loc.oU.oracle < s.st.oracles.size := by
  obtain ⟨⟨x, hx, _⟩, _, _⟩ := (seatedUB_iff p s).1 h
  exact (Array.getElem?_eq_some_iff.1 hx).1

/-- A step onward that leaves the small record keeps it. -/
theorem seatedUB_onward (p : Par) (a b : St) (o : Onward a b) (l : b.loc = a.loc)
    (h : seatedUB p a = true) : seatedUB p b = true := by
  obtain ⟨⟨x, hx, hs⟩, h2, h3⟩ := (seatedUB_iff p a).1 h
  obtain ⟨x', hx', gx⟩ := o.grows.2.2 _ x hx
  refine (seatedUB_iff p b).2 ⟨⟨x', ?_, gx.1.trans hs⟩, ?_, ?_⟩
  · rw [l]
    exact hx'
  · rw [l, o.grows.1]
    exact h2
  · rw [o.grows.1]
    exact h3

/-- **The book-keeping behind o_u's sending, as a test.** nU: o_u's number in the chain's statement,
by the plan; c: the number of open rows on G_u. -/
def shapeU (p : Par) (nU c : Nat) (s : St) : Bool :=
  shape2 p s && seatedUB p s && decide (s.loc.oU.oracle = nU) &&
    decide ((rowsOn s s.loc.gU).length = c)

/-- What the test says. -/
theorem shapeU_iff (p : Par) (nU c : Nat) (s : St) : shapeU p nU c s = true ↔
    shape2 p s = true ∧ seatedUB p s = true ∧ s.loc.oU.oracle = nU ∧
      (rowsOn s s.loc.gU).length = c := by
  unfold shapeU
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The rows that "(rec_gamma)" lays: as many as the record has answers. -/
theorem laysRec_rows (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    ∃ rows, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows ∧
      rows.length = p.S.fold.index.answers := by
  obtain ⟨hok, _, rows, hrows, hU, _⟩ := laysRecW p d d' rs h
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have hfit : d.loc.key.fits p.S.fold.index = true := hok.1
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  refine ⟨rows, hU, ?_⟩
  rw [length_mapM _ _ _ hrows, List.length_zipIdx]
  exact hfit.1.2

/-- The rows that "LOC" lays: one a position drawn. -/
theorem loc_rows (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : loc p d [r] [cols] = some d') :
    ∃ rows, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows ∧
      rows.length = r.drawn.poss.length := by
  obtain ⟨_, rows, _, hlen, hU, _⟩ := laysLocW p d d' r cols h
  exact ⟨rows, hU, hlen⟩

/-- The test goes on past a step onward that leaves the small record and lays n rows on G_u. -/
theorem shapeU_step (p : Par) (nU c n : Nat) (a b : St) (o : Onward a b) (l : b.loc = a.loc)
    (hr : ∃ rows, rowsOn b a.loc.gU = rowsOn a a.loc.gU ++ rows ∧ rows.length = n)
    (h : shapeU p nU c a = true) : shapeU p nU (c + n) b = true := by
  obtain ⟨h1, h2, hN, h3⟩ := (shapeU_iff p nU c a).1 h
  obtain ⟨rows, hU, hn⟩ := hr
  refine (shapeU_iff p nU (c + n) b).2 ⟨?_, seatedUB_onward p a b o l h2, ?_, ?_⟩
  · unfold shape2 shape1 at h1 ⊢
    rw [l]
    exact h1
  · rw [l]
    exact hN
  · rw [l, hU, List.length_append, h3, hn]

/-- **At a yes of "(rec_gamma)".** -/
theorem shapeU_rec (p : Par) (nU c : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : laysRec p a rs = some b) (h : shapeU p nU c a = true) :
    shapeU p nU (c + p.S.fold.index.answers) b = true :=
  shapeU_step p nU c _ a b (onward_laysRec p a b rs k).1 (onward_laysRec p a b rs k).2
    (laysRec_rows p a b rs k) h

/-- **At a yes of "LOC".** -/
theorem shapeU_loc (p : Par) (nU c : Nat) (a b : St) (r : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (k : loc p a [r] [cols] = some b)
    (h : shapeU p nU c a = true) : shapeU p nU (c + r.drawn.poss.length) b = true :=
  shapeU_step p nU c _ a b (onward_loc p a b r cols k).1 (onward_loc p a b r cols k).2
    (loc_rows p a b r cols k) h

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- Where the statement grows and no message comes, a constraint applied to words gives the same. -/
theorem value_same (T T' : Statement) (g : Grows T T') (hs : T'.oracles.size = T.oracles.size)
    (r : Row) (m : Words K) : Means.value ρ T' r m = Means.value ρ T r m := by
  unfold Means.value
  rw [hs]
  refine Finset.sum_congr rfl fun o ho => ?_
  unfold Means.onTable
  rw [tableSize_grows T T' g o (Finset.mem_range.1 ho),
    tableSize_grows T T' g o (Finset.mem_range.1 ho)]

/-- So a list of constraints says the same. -/
theorem allSay_same (T T' : Statement) (g : Grows T T') (hs : T'.oracles.size = T.oracles.size)
    (L : List Row) (m : Words K) (h : Means.AllSay ρ T' L m) : Means.AllSay ρ T L m := by
  intro r hr
  have h0 := h r hr
  unfold Means.Says at h0 ⊢
  rw [value_same ρ T T' g hs r m] at h0
  exact h0

/-- A slice that lies within the older rows is a slice of these. -/
theorem slice_old {α : Type} (old new : List α) (i n : Nat) (h : i + n ≤ old.length) :
    ((old ++ new).drop i).take n = (old.drop i).take n := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-- **The older rows ride back** past a step onward that leaves the small record, brings no message,
and lays its rows behind them. -/
theorem rowsU_back (i n : Nat) (a b : St) (m : Words K) (o : Onward a b) (l : b.loc = a.loc)
    (hs : b.st.oracles.size = a.st.oracles.size)
    (hin : i + n ≤ (rowsOn a a.loc.gU).length) (h : RowsU ρ i n b m) : RowsU ρ i n a m := by
  obtain ⟨more, hm⟩ := o.later a.loc.gU
  unfold RowsU at h ⊢
  rw [l, hm, slice_old _ _ _ _ hin] at h
  exact allSay_same ρ a.st b.st o.grows hs _ m h

/-- **The rows said at a later statement ride back over every step onward** that leaves G_u's number
and lays its rows behind them: a sending too. -/
theorem rowsUL_back (i n : Nat) (a b : St) (m : Words K) (o : Onward a b)
    (lg : b.loc.gU = a.loc.gU) (hin : i + n ≤ (rowsOn a a.loc.gU).length)
    (h : RowsUL ρ i n b m) : RowsUL ρ i n a m := by
  obtain ⟨T, g, h⟩ := h
  obtain ⟨more, hm⟩ := o.later a.loc.gU
  refine ⟨T, o.grows.trans g, ?_⟩
  rw [lg, hm, slice_old _ _ _ _ hin] at h
  exact h

end Desc.K14.Law
