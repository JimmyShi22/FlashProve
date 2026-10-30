-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(The lemma is named part_bookOf because the name part_book stands in
another file, SeatsRide.lean.)
Johnson/Desc/First/Link/Law/PartFitsReached.lean: `PartFits cs ms own pa`
(Johnson/Desc/Sound/Clamp/InsideOfPlan.lean), AND SO `InsideAt cs ms own pa`
(Johnson/Desc/Sound/Clamp/FormsClamp.lean: "every entry that the open segment's data read lies
inside the ranges of the member at its seat"), AT THE OPEN SEGMENT's PART OF A REACHED STATE: from
seven fields of the list of lemmas along "reached" (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean),
one Bool of the table's promise (`bookAt`), two facts on the ledger, and `PlanFits`: sentences ON
PUBLIC DATA ALONE. Definitions and theorems.

Why. The link law's third and fourth ties are paid at the reader of the witness that is clamped to
each member's ranges; the sentences on linear forms at that reader are the composed meaning's under
`InsideAt`, which is asked at states with the promise and "reached". Here no premise on a state is
left that is not a field of `FoldFacts`, a Bool of the promise, or a fact on the open ledger.

What is said.
  `whereD d m t born j`: THE PLAN's TERM for `ReqFrame.whereIs` in segment m with t moments sent:
    off `FoldData`'s ownAt | keptAt and the request's shape's groups. `maskD`: the like for the
    number of the message that holds the segment's mask row.
  `PlanFits d ms own m t n ns`: on public data alone: the two tests of the programs (the codes'
    lengths; the layout); `shapes`: where the plan's term finds a message of the request's shape,
    its number is below n and the listed shape there is the message's; `members`: the member at
    the listed seat of a message below n, if the seat is of own, has the listed shape; `mask`: the
    mask message is below n and has one mask row, the request's mask code and answers; an answer;
    `room`: ns and the answers have room in the mask code's length (the programs' "plan-mask-row").
  `live_link`, `part_bookOf`: two readings.
  `whereIs_reached`, `mask_reached`: the open link's frame finds a message where the plan's term
    does (FoldFacts.frameIs | liveShape | liveGroups).
  `partFits_reached`: **THE SIX CLAUSES.** `insideAt_reached`: **so `InsideAt`.**
  `insideAt_congr`: what `InsideAt` reads of a part: for a state that is not itself "reached"
    (behind the runs that follow the batching) but has these readings of one that is.

Limits. `FoldFacts` at "reached", `PlanFits` at the release's values, and the two facts on the
ledger (its number of slots is the plan's; its list of coefficients is no longer) are premises:
shown here of nothing. The places: inside a link, up to its piece 11 (13 at the output head): the
batching, the sub-protocol behind it, the one equation and K10's among them; the shutting not. No
soundness statement.

-/
import Johnson.Desc.Sound.Clamp.InsideOfPlan
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.Link.Law.RbRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers FoldData FoldFacts momentAt shiftAt bookAt)

/-- The plan's term for `ReqFrame.whereIs` in segment m, with t moments sent. -/
def whereD (d : FoldData) (m t born j : ℕ) : Option ℕ :=
  if born == m then (d.ownAt m t)[j]?
  else (((reqGroups d.sent.shape).getD m {}).born.idxOf? (born, j)).bind fun i => (d.keptAt m)[i]?

/-- The plan's term for the number of the message that holds segment m's mask row. -/
def maskD (d : FoldData) (m t : ℕ) : Option ℕ :=
  (((d.sent.shape.link[m]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0).bind fun i => whereD d m t m i

/-- **On public data alone.** n: how many oracle messages are sent; ns: the plan's number of slots
of the segment's ledger. -/
structure PlanFits (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (m t n ns : ℕ) : Prop where
  lengths : d.sent.codes.lengthsOk = true
  layoutOk : reqLayoutOk d.sent.codes d.sent.shape d.sent.layout = true
  shapes : ∀ born j o msg, whereD d m t born j = some o →
    Meaning.messageAt d.sent.shape born j = some msg → o < n ∧ d.M[o]? = some msg.shape
  members : ∀ o x y sh, o < n → d.M[o]? = some sh → d.L.places[o]? = some x → x ∈ own →
    (ms.find? fun y => decide (seatOf y = x)) = some y → (y.1.l.get y.2).1 = sh
  mask : ∀ o, maskD d m t = some o → o < n ∧ ∃ sh, d.M[o]? = some sh ∧ sh.maskRows = 1 ∧
    sh.maskCode = d.sent.shape.maskCode ∧ sh.answers = d.sent.shape.answers
  answers : 1 ≤ d.sent.shape.answers
  room : ns + d.sent.shape.answers ≤ (d.sent.codes.mask.getD d.sent.shape.maskCode default).ell

theorem live_link {s : S} {L : LinkCtx} (h : s.link? = some L) : s.live = L.check := by
  unfold S.live
  rw [h]

/-- The lens reads the state's own book. -/
theorem part_bookOf (e : S) (q : K9.Part) (hq : atS.get? e = some q) : q.d.book = e.book := by
  unfold atS at hq
  simp only [Option.bind_eq_bind, Option.pure_def] at hq
  obtain ⟨L, hL, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  rw [← Option.some.inj hq]

section
variable {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
  {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
  (FF : FoldFacts Rch at_ d reqW links ps) {k : ℕ} {a : X} {p : Place} {m : ℕ} {L : LinkCtx}
  (hR : Rch k a) (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hl : p.link = some m)
  (hpc : p.piece ≤ 11 + 2 * shiftAt links m) (hL : (at_ a).2.link? = some L)
include FF hR hu hp hl hpc hL

/-- **The open link's frame finds a message where the plan's term does.** -/
theorem whereIs_reached (born j : ℕ) :
    L.check.frame.whereIs born j = whereD d m (momentAt (shiftAt links m) p.piece) born j := by
  obtain ⟨-, h2, h3, h4⟩ := FF.frameIs k a p m L hR hu hp hl hL
  obtain ⟨h5, h6⟩ := h4 hpc
  have hg : L.check.frame.groups = reqGroups d.sent.shape := by
    have e1 := FF.liveGroups k a hR hu
    have e2 := FF.liveShape k a hR hu
    rw [live_link hL] at e1 e2
    rw [e1, e2]
  have e : (ReqNext.laterOrClose != ReqNext.laterOrClose) = false := by decide
  unfold ReqFrame.whereIs whereD
  rw [h6, h5, h2, h3, hg, e]
  rfl

/-- The message with the mask row. -/
theorem mask_reached :
    K9L.maskOracle L.check.frame = maskD d m (momentAt (shiftAt links m) p.piece) := by
  have e2 := FF.liveShape k a hR hu
  rw [live_link hL] at e2
  have h5 := ((FF.frameIs k a p m L hR hu hp hl hL).2.2.2 hpc).1
  unfold K9L.maskOracle maskD
  rw [e2, h5]
  congr 1
  funext i
  exact whereIs_reached FF hR hu hp hl hpc hL m i

end

/-- **`PartFits` AT THE OPEN SEGMENT's PART OF A REACHED STATE.** -/
theorem partFits_reached {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (N : Numbers) (ms : List Mem) (own : List (ℕ × ℕ))
    {k : ℕ} {a : X} {p : Place} {m ns : ℕ} {pa : K9.Part} (hR : Rch k a)
    (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links m) (hpa : atS.get? (at_ a).2 = some pa)
    (hB : bookAt N ps[k]? (at_ a).2 = true)
    (T : PlanFits d ms own m (momentAt (shiftAt links m) p.piece) (N.msgsAt ps[k]?) ns)
    (hns : pa.F.ns = ns) (hLS : pa.F.LS.size ≤ pa.F.ns) :
    PartFits d.sent.codes ms own pa := by
  obtain ⟨hL, hst⟩ := part_reads _ pa hpa
  have hbk := part_bookOf _ pa hpa
  have hsz : (at_ a).2.st.oracles.size = N.msgsAt ps[k]? := by
    unfold bookAt at hB
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    exact hB.2
  have hM : ∀ o, o < N.msgsAt ps[k]? → (pa.d.st.oracles[o]?).map (·.shape) = d.M[o]? := by
    intro o ho
    rw [hst]
    exact K12.Door.msgShape_at (FF.msgShapes k a hR hu) o (by rw [hsz]; exact ho)
  have hsh : pa.L.check.frame.shape = d.sent.shape := by
    have e := FF.liveShape k a hR hu
    rwa [live_link hL] at e
  have hly : pa.L.check.rows.layout = d.sent.layout := by
    have e := FF.liveLayout k a hR hu
    rwa [live_link hL] at e
  refine ⟨by rw [hst]; exact FF.codes k a hR hu, T.lengths, by rw [hsh, hly]; exact T.layoutOk,
    ?_, ?_, ?_⟩
  · intro born j o msg hw hm
    rw [whereIs_reached FF hR hu hp hl hpc hL] at hw
    rw [hsh] at hm
    obtain ⟨h1, h2⟩ := T.shapes born j o msg hw hm
    rw [hM o h1, h2]
  · intro o x y sh ho hx hy
    have hlt : o < N.msgsAt ps[k]? := by
      rw [← hsz, ← hst]
      cases e : pa.d.st.oracles[o]? with
      | none => rw [e] at ho; cases ho
      | some z => exact (Array.getElem?_eq_some_iff.1 e).1
    rw [hM o hlt] at ho
    have hxo := K9.seatAt_mem own pa.d.book o x hx
    have hpl : d.L.places[o]? = some x := by
      unfold K9.seatAt at hx
      obtain ⟨x', h1, h2⟩ := Option.bind_eq_some_iff.1 hx
      have ex : x' = x := by
        by_cases hc : own.contains x' = true
        · rw [if_pos hc] at h2
          exact Option.some.inj h2
        · rw [if_neg hc] at h2
          cases h2
      subst ex
      rw [hbk] at h1
      have hS := FF.seatsCarried k a hR hu
      unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at hS
      simp only [Bool.and_eq_true, beq_iff_eq] at hS
      have e0 : (at_ a).2.book.place.toList = d.L.places.take (at_ a).2.book.place.size :=
        hS.1.1.1
      have h3 : (at_ a).2.book.place.toList[o]? = some x' := by
        rw [Array.getElem?_toList]
        exact h1
      rw [e0, List.getElem?_take] at h3
      split at h3
      · exact h3
      · cases h3
    exact T.members o x y sh hlt ho hpl hxo hy
  · intro o ho
    rw [mask_reached FF hR hu hp hl hpc hL] at ho
    obtain ⟨h1, sh, h2, h3, h4, h5⟩ := T.mask o ho
    have hr : ns ≤ Send.freeMaskEntries 1
        (d.sent.codes.mask.getD d.sent.shape.maskCode default).ell d.sent.shape.answers := by
      rw [free_one (by have := T.room; omega)]
      have := T.room
      omega
    refine ⟨sh, by rw [hM o h1, h2], by rw [h3]; rfl, by rw [h5]; exact T.answers, ?_, ?_⟩ <;>
      rw [h3, h4, h5] <;> omega

/-- `InsideAt` reads of a part the link's own copy of the calls' state, the statement, the book, and
how far the ledger's slots and its list of coefficients reach. -/
theorem insideAt_congr {cs : OnBytes.Codes} {ms : List Mem} {own : List (ℕ × ℕ)} {a a' : K9.Part}
    (h : InsideAt cs ms own a) (hL : a'.L.check = a.L.check) (hst : a'.d.st = a.d.st)
    (hbk : a'.d.book = a.d.book)
    (hF : ∀ j, j < a'.F.ns ∨ j < a'.F.LS.size → j < a.F.ns ∨ j < a.F.LS.size) :
    InsideAt cs ms own a' := by
  refine ⟨?_, fun o j x y ho hj hx hy => ?_⟩
  · rw [hL, hst, hbk]
    exact h.main
  · rw [hL] at ho
    rw [hbk] at hx
    rw [hst]
    exact h.mask o j x y ho (hF j hj) hx hy

/-- **SO `InsideAt`.** -/
theorem insideAt_reached {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (N : Numbers) (ms : List Mem) (own : List (ℕ × ℕ))
    {k : ℕ} {a : X} {p : Place} {m ns : ℕ} {pa : K9.Part} (hR : Rch k a)
    (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links m) (hpa : atS.get? (at_ a).2 = some pa)
    (hB : bookAt N ps[k]? (at_ a).2 = true)
    (T : PlanFits d ms own m (momentAt (shiftAt links m) p.piece) (N.msgsAt ps[k]?) ns)
    (hns : pa.F.ns = ns) (hLS : pa.F.LS.size ≤ pa.F.ns) :
    InsideAt d.sent.codes ms own pa :=
  insideAt_of_fits d.sent.codes ms own pa
    (partFits_reached FF N ms own hR hu hp hl hpc hpa hB T hns hLS)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.whereIs_reached
#print axioms VerifiableInference.Desc.LinkJoin.mask_reached
#print axioms VerifiableInference.Desc.LinkJoin.partFits_reached
#print axioms VerifiableInference.Desc.LinkJoin.insideAt_congr
#print axioms VerifiableInference.Desc.LinkJoin.insideAt_reached
