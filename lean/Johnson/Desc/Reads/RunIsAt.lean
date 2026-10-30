-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RunIsAt.lean: at the output head's seat at the first chain's carried record: the
run's points and vectors are the kind's letters (`RunIs`, Johnson/Desc/Kinds/Law/TwelveOurs.lean).

What is shown. `RunIs R` has fourteen clauses and eight on sizes. Law/TwelveOurs.lean shows six of
the fourteen at what the seat lays. Here the other eight are shown, and the fourteen are put
together at a record behind the reads' quiet step.
  `cov_at`: the clause on the request. Where the record's covered positions can be said, the marks
    of the positions with a cost are the kind's `costed` at the record's own request.
  `zt_at`, `low_at`: the four clauses on the lookup's key points, from the kind's own test on these
    points (`PointsOk`, Johnson/Desc/Kinds/HeadInLaw.lean), by Reads/KeyPoints.lean.
  `back_points`: what the way back from the record (`allOf`, Johnson/Stored/HeadSeat.lean) lays for
    the five points that the block heard.
  `runIs_at`: **`RunIs` at the record.**

Premises of `runIs_at`. The record stands in the head's link, opened; its covered positions can be
said; it holds what was heard (x); the text that makes the tables says yes at x; all the kind's
letters are there. These come with a yes of the reads' quiet step and of the run of claims. Beside
them, by name, and shown by no theorem here:
  hJ: the layout's number of coordinates on the columns of each of the six calls is the kind's.
  hlsJ: that number is ls at least, at each of the six.
  hc6: a call that the layout finds under a segment's name has a number below 6.
  hqH, hqN: the two numbers of calls in what was heard are below 6.
  hz: the lookup's point has ls + lt coordinates at least.
  hsPV, hsSq, hsTV, hsTN, hsTH: the sizes of the five points that the block heard.
  hls: ls is at most the number of coordinates on the norms and the padded features.
  hX1, hX2: what the seat laid of the lookup's record into what was heard still lies there: the copy
    g1 is the lookup's record, and Zl is the last ls + lt coordinates of its point.

Limits. None of these fourteen is shown here. Nothing on soundness.


-/
import Johnson.Desc.Kinds.Law.TwelveOurs
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.Own.HeadTabsAgree
import Johnson.Desc.Reads.KeyPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E)
open OnBytes.Model (cutLast)
open OnBytes.Model.Head (Shape HL Covered ztOf zjOf callNo)
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.bind_ok ReadsQuiet.named_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-! ## 1. The request -/

/-- Where the covered positions can be said, the record holds T + 2 words, and the marks of the
positions with a cost are these. -/
theorem covered_marks {T V : ℕ} {s : S} {cov : Covered} (h : s.covered T V = .ok cov) :
    s.reqT = T ∧ ∀ t, t < T → cov.hOnC.getD t false =
      ((decide (s.rowR ≤ t) && decide (t < s.rowE)) && decide (t + 1 < T)) := by
  unfold S.covered at h
  split at h
  · rename_i y _
    unfold S.coveredAt at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hsize
        split at h
        · cases h
        · split at h
          · cases h
          · have hT : s.reqT = T := by
              have e : s.req.size = T + 2 := by simpa using hsize
              unfold S.reqT
              omega
            refine ⟨hT, fun t ht => ?_⟩
            have e := (Except.ok.inj h).symm
            subst e
            unfold S.rowR S.rowE
            rw [hT]
            simp [Array.getD, ht]
  · cases h

/-- **The clause on the request.** -/
theorem cov_at (h : Shape) {s : S} {cov : Covered} (hc : s.covered h.T h.V = .ok cov) :
    letI := sizesOf h
    letI := requestOf s
    ∀ t, t < Norm.T → cov.hOnC.getD t false = costed t :=
  fun t ht => (covered_marks hc).2 t ht

/-! ## 2. The lookup's key points -/

section Points
variable (h : Shape) (L : HL) (G : OnBytes.Model.Forest.Heard) (floor : ℕ)

/-- The positions' part of the key point of a call is the kind's zt. -/
theorem zt_at
    (hP : @PointsOk (sizesOf h) floor G.zx fun c => G.zk.getD c #[]) {q : ℕ} (hq : q < 6)
    (hJ : (L.calls.getD q default).lJ = (letI := sizesOf h; lJ floor (callKeys q)))
    (hls : h.ls ≤ (L.calls.getD q default).lJ) (hz : h.ls + h.lt ≤ G.zx.size) :
    ztOf h L G q = (@fromLookup (sizesOf h) floor G.zx fun c => G.zk.getD c #[]).norm.zt := by
  obtain ⟨p1, p2⟩ := hP q _ (Came.call_get hq)
  exact ztOf_tail h L G q (ls := h.ls) (by rw [hJ]; exact p1) p2 hls hz

/-- The tail of the column part of the key point of a call is the kind's zl. -/
theorem low_at
    (hP : @PointsOk (sizesOf h) floor G.zx fun c => G.zk.getD c #[]) {q : ℕ} (hq : q < 6)
    (hJ : (L.calls.getD q default).lJ = (letI := sizesOf h; lJ floor (callKeys q)))
    (hls : h.ls ≤ (L.calls.getD q default).lJ) (hz : h.ls + h.lt ≤ G.zx.size) :
    ∃ lowN, cutLast (zjOf L G q) h.ls = .ok lowN ∧
      lowN.2 = (@fromLookup (sizesOf h) floor G.zx fun c => G.zk.getD c #[]).norm.zl := by
  obtain ⟨p1, p2⟩ := hP q _ (Came.call_get hq)
  exact zjOf_tail h L G q (ls := h.ls) (by rw [hJ]; exact p1) p2 hls hz

end Points

/-! ## 3. The way back from the record -/

/-- The challenges of a sumcheck that is read back are those handed in. -/
theorem sumOf_r {F : OnBytes.Model.Fork} {t : OnBytes.Model.Tsc} {r : Point} {n : ℕ} {S0 : Sum}
    (e : sumOf F t r n = some S0) : S0.r = r := by
  unfold sumOf at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at e
  obtain ⟨_, _, _, _, rfl⟩ := e
  rfl

/-- **The five points that the block heard, as the way back lays them.** -/
theorem back_points {F : OnBytes.Model.Fork} {x : OnBytes.Model.Head.Heard}
    {sq : Option VerifiableInference.Desc.Part.MaskedSum.Heard} {H : HeardAll}
    (e : allOf F x sq = some H) :
    H.1.pV = x.PV ∧ H.1.squares.r = x.wpl.r ∧ H.1.products.r = x.tV.r ∧
      H.2.1.normed.r = x.tN.r ∧ H.2.2.logits.r = x.tH.r ++ x.rs.reverse := by
  unfold allOf at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at e
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, s1, h1, s2, h2, s3, h3, rfl⟩ := e
  exact ⟨rfl, rfl, sumOf_r h1, sumOf_r h2, sumOf_r h3⟩

/-- Where all letters are there: the letters in front of the hearing, and what was heard. -/
theorem lettersAt_ok {S' : Type} {p : Par} {L : Seat S'} {s : S'} {g : Given} {bh : Behind}
    {pl : Places} (h : lettersAt p L s = .ok (g, bh, pl)) :
    given p L s = .ok g ∧ ∃ H : HeardAll, L.heard s = some H ∧ bh = ⟨H.1, H.2.1, H.2.2⟩ := by
  unfold lettersAt at h
  cases hg : given p L s with
  | error e => simp [hg, bind, Except.bind] at h
  | ok g' =>
    cases hH : L.heard s with
    | none => simp [hg, hH, named, bind, Except.bind] at h
    | some H =>
      cases hr : L.reads s with
      | none => simp [hg, hH, hr, named, bind, Except.bind] at h
      | some x =>
        simp only [hg, hH, hr, named, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, H, rfl, rfl⟩

/-! ## 4. What a yes of the text that makes the tables says of the calls -/

/-- A yes of the head's tables: there are calls with the two segments that the text asks for. -/
theorem tables_calls {h : Shape} {L : HL} {hp : OnBytes.Model.Head.HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : OnBytes.Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    (∃ q, callNo L "CNF" = some q) ∧ ∃ q, callNo L "ROW" = some q := by
  unfold ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qFC, p3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qROW, p4, _⟩ := ReadsQuiet.bind_ok e
  exact ⟨⟨qFC, ReadsQuiet.named_ok p3⟩, ⟨qROW, ReadsQuiet.named_ok p4⟩⟩

/-! ## 5. At the record -/

/-- **The run's points and vectors are the kind's letters, at the record.** -/
theorem runIs_at (h : Shape) (L : HL) (b : OnBytes.Model.Head.Border)
    (hp : OnBytes.Model.Head.HPlanH2) (iU3 work : ℕ) (s : S) (o : HeadOwn) (cov : Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables)
    (here : s.here = .head o) (opened : o.opened = true)
    (hcov : s.covered h.T h.V = .ok cov) (hx : o.x = some x)
    (made : ReadsQuiet.tables h L hp cov x = .ok t)
    (hX1 : o.lookHeard = some x.g1) (hX2 : x.Zl = Point.last x.g1.zx (h.ls + h.lt))
    [g : Given] [bh : Behind] {pl : Places}
    (hl : lettersAt (parOf h work) (seatAt h iU3) s = .ok (g, bh, pl))
    (hJ : ∀ q, q < 6 → (L.calls.getD q default).lJ =
      (letI := sizesOf h; lJ (OnBytes.Model.Head.keyFloor h) (callKeys q)))
    (hlsJ : ∀ q, q < 6 → h.ls ≤ (L.calls.getD q default).lJ)
    (hc6 : ∀ seg q, callNo L seg = some q → q < 6) (hqH : x.qH < 6) (hqN : x.qN < 6)
    (hz : h.ls + h.lt ≤ x.g1.zx.size)
    (hsPV : x.PV.size = h.lt)
    (hsSq : x.wpl.r.size = (letI := sizesOf h; Norm.lNI + Norm.lPd) + h.lt)
    (hsTV : x.tV.r.size = h.lt) (hsTN : x.tN.r.size = h.lt) (hsTH : x.tH.r.size = h.lt)
    (hls : h.ls ≤ (letI := sizesOf h; Norm.lNI + Norm.lPd)) :
    RunIs ⟨h, L, b, hp, cov, x, t, iU3⟩ := by
  obtain ⟨hg, H, hH, hb⟩ := lettersAt_ok hl
  obtain ⟨z, y, hz1, -, hP, hgE⟩ := Came.given_ok _ _ _ _ hg
  have hlook : s.lookHeard? = some x.g1 := by
    unfold S.lookHeard?
    rw [here]
    simp [opened, hX1]
  have hz2 : z = (x.g1.zx, fun c => x.g1.zk.getD c #[]) := by
    have e : (s.lookHeard?.map fun G => (G.zx, fun c => G.zk.getD c #[])) = some z := hz1
    rw [hlook] at e
    exact (Option.some.inj e).symm
  subst hz2
  have hall : ∃ q, allOf o.F x (some (keptOf q x.wpl.sL)) = some H := by
    have e : (match s.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = some H := hH
    rw [here] at e
    obtain ⟨q, -, e⟩ := Option.bind_eq_some_iff.1 e
    rw [hx] at e
    exact ⟨q, e⟩
  obtain ⟨q, hall⟩ := hall
  obtain ⟨b1, b2, b3, b4, b5⟩ := back_points hall
  obtain ⟨hFC, hROW⟩ := tables_calls made
  obtain ⟨lowN0, hlow1, hlow2⟩ :=
    low_at h L x.g1 (OnBytes.Model.Head.keyFloor h) hP hqN (hJ _ hqN) (hlsJ _ hqN) hz
  constructor <;> (subst hb; subst hgE)
  · exact b1.symm
  · exact b2.symm
  · exact b3.symm
  · exact b4.symm
  · show x.tH.r = H.2.2.logits.r.extract 0 h.lt
    rw [b5]
    exact (take_append _ _ hsTH).symm
  · exact hX2.trans (Came.last_cut x.g1.zx h.ls h.lt hz).symm
  · exact fun q hq =>
      zt_at h L x.g1 _ hP (hc6 _ _ hq) (hJ _ (hc6 _ _ hq)) (hlsJ _ (hc6 _ _ hq)) hz
  · exact fun q hq =>
      zt_at h L x.g1 _ hP (hc6 _ _ hq) (hJ _ (hc6 _ _ hq)) (hlsJ _ (hc6 _ _ hq)) hz
  · exact zt_at h L x.g1 _ hP hqH (hJ _ hqH) (hlsJ _ hqH) hz
  · intro lowN hlow
    have hlow' : cutLast (zjOf L x.g1 x.qN) h.ls = .ok lowN := hlow
    rw [hlow1] at hlow'
    rw [← Except.ok.inj hlow']
    exact hlow2
  · exact cov_at h hcov
  · exact hFC
  · exact hROW
  · intro m hm
    have hm' : cutLast (zjOf L x.g1 x.qN) h.ls = .error m := hm
    rw [hlow1] at hm'
    cases hm'
  · exact last_size x.g1.zx (n := h.lt) (Nat.le_trans (Nat.le_add_left _ _) hz)
  · exact last_head_size x.g1.zx hz
  · show H.1.pV.size = h.lt
    rw [b1]
    exact hsPV
  · show H.1.squares.r.size = _
    rw [b2]
    exact hsSq
  · show H.1.products.r.size = h.lt
    rw [b3]
    exact hsTV
  · show H.2.1.normed.r.size = h.lt
    rw [b4]
    exact hsTN
  · show (H.2.2.logits.r.extract 0 h.lt).size = h.lt
    rw [b5, take_append _ _ hsTH]
    exact hsTH
  · exact hls

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.covered_marks
#print axioms VerifiableInference.Reads.AtSeat.cov_at
#print axioms VerifiableInference.Reads.AtSeat.zt_at
#print axioms VerifiableInference.Reads.AtSeat.low_at
#print axioms VerifiableInference.Reads.AtSeat.sumOf_r
#print axioms VerifiableInference.Reads.AtSeat.back_points
#print axioms VerifiableInference.Reads.AtSeat.lettersAt_ok
#print axioms VerifiableInference.Reads.AtSeat.tables_calls
#print axioms VerifiableInference.Reads.AtSeat.runIs_at
