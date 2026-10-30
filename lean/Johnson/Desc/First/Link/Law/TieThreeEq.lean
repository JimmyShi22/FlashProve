-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieThreeEq.lean: THE DEBT t3
OF THE TIES OF A LINK's THIRD
PIECE (the
one equation's) AT THE TABLE (`TieRestR`, LinkTiedR.lean), AT THE COMPOSED MEANING (`mgAll 𝔇 Mg₀`)
AND AT THE LAW's LETTERS AS TieThreeFour.lean HAS THEM: what the row opens (the item "row m
equation") gives the kind's own relation behind the piece (`relRow`: the group's last row holds on
the accessor's tables, at the clamped reader `rdC`). Definitions and theorems.

THE ROAD. The item says: every row of the class "equation" of segment m says its claim of the words
that the ruled reader gives (`rowSays` at `wordsFirst`). (1) LastRowSays.lean carries
that to `LastRowAt` AT THESE WORDS (placeSays_of_run · lastSays_of_place · lastRow_of_inOrder).
(2) HERE: at every entry on which the row has a weight other than 0 the words are the accessor's
table at `seatTab` (`words_tabQ`, over tabFirst_at_plan, Johnson/Desc/Sound/WordsAtPlan.lean): so
the row's sum is the same at both (`rowSum_words`). (3) rowEqQ_clamp (RowClamp.lean)
carries `seatTab` to `rdC`.

What is said.
  `book_part`: K9's part holds the state's own book.
  `words_tabQ`: one entry. `rowSum_words`: the row's sum.
  `EqRowAsks`: WHAT IS ASKED OF A STATE BEHIND THE PIECE, A FIELD A PREMISE, each a plain sentence:
    EIGHT FIELDS.
  `rowEq_of_says`: from the item's sentence, EqRowAsks and two conclusions
    (hseat, hins) to `rowEqQ` at `rdC`.
  `t3_eq`: **t3 AT THE ONE EQUATION's PIECE**, ending in the field's own type.

rowInside_step (RowInsideOf.lean) and
seats_first (SeatsOf.lean) pay, BEHIND A YES OF THE ONE EQUATION's STEP, "the last row's weights lie
inside the members' ranges" and "a message with a weight sits at a seat of the segment's own list",
from two things IN FRONT of the step: InsideAt (which TieThreeFour.lean's four ties ask too)
and the promise's public test `K9.totalIn`. So t3_eq asks these two in front, and that the piece's
yes is a yes of the step (hstep).

Limits. PREMISES: what the table's row at the place opens (a closed fact on the written list) · the
class has a row (a closed fact on the numbers) · hstep · `K9.totalIn` and `InsideAt` at every
state in front of the piece, `EqRowAsks` at every state behind it, all asked only inside the
condition
`onTR`: SHOWN AT NO STATE HERE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TieThreeFour
import Johnson.Desc.First.Batch.Law.LastRowSays
import Johnson.Desc.First.Batch.Law.RowClamp
import Johnson.Desc.First.Batch.Law.SeatsOf
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.Sound.WordsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf rowSays wordsAtFirst)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- K9's part holds the state's own book. -/
theorem book_part (s : S) (a : K9.Part) (h : atS.get? s = some a) : a.d.book = s.book := by
  simp only [atS] at h
  obtain ⟨L, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [← Option.some.inj h]

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (own : List (ℕ × ℕ))

/-- **ONE ENTRY: the ruled reader's word is the accessor's table at the member of that seat.** -/
theorem words_tabQ (st : Statement) (B : TreeBook) (w : Wit Cells Tok MsgT) (o : ℕ)
    (part : OnBytes.Part) (J : ℕ) (sh : OracleShape) (q : ℕ × ℕ) (y : Mem)
    (hT : tabAt st.codes arr (seatBy noFirst B) st w o = w.tab st.codes sh (arr q.1 q.2) q.1 q.2)
    (hq : B.place[o]? = some q) (hown : own.contains q = true)
    (hy : (ms.find? fun y => decide (seatOf y = q)) = some y) (hsh : (y.1.l.get y.2).1 = sh)
    (hcs : st.codes = cs)
    (hreal : J % 2 ^ st.rowBits o part < OnBytes.Means.realRows st o part) :
    wordsFirst arr st B w o part J = tabQ own st B (seatTab cs arr ms w) o part J := by
  have hs : seatOf y = q := by
    have hd := List.find?_some (p := fun y : Mem => decide (seatOf y = q)) hy
    simpa using hd
  have e1 : wordsFirst arr st B w o part J =
      w.tab st.codes sh (arr q.1 q.2) q.1 q.2 (part == .mask) (J % 2 ^ st.rowBits o part)
        (J / 2 ^ st.rowBits o part) := by
    show OnBytes.Means.wordsOn st (tabAt st.codes arr (seatBy noFirst B) st w) o part J = _
    unfold OnBytes.Means.wordsOn
    rw [if_pos hreal, hT]
  have e2 : K9.seatAt own B o = some q := by
    unfold K9.seatAt
    rw [hq, Option.bind_some, if_pos hown]
  have e3 : seatTab cs arr ms w q = w.tab cs sh (arr q.1 q.2) q.1 q.2 := by
    unfold seatTab
    rw [hy]
    show w.tab cs (y.1.l.get y.2).1 (arr (seatOf y).1 (seatOf y).2) (seatOf y).1 (seatOf y).2 = _
    rw [hsh, hs]
  rw [e1]
  unfold tabQ
  rw [e2]
  show _ = seatTab cs arr ms w q (part == .mask) _ _
  rw [e3, hcs]

/-- Inside a member's ranges a row is one of the table's real rows, where the message has the
member's shape. -/
theorem real_of_inMsg (st : Statement) (o : ℕ) (part : OnBytes.Part) (sh : OracleShape) (r p : ℕ)
    (hx : (st.oracles[o]?).map (·.shape) = some sh) (h : InMsg cs sh (part == .mask) r p) :
    r < OnBytes.Means.realRows st o part := by
  obtain ⟨x, hx1, hx2⟩ := Option.map_eq_some_iff.1 hx
  unfold OnBytes.Means.realRows
  rw [hx1]
  show r < x.shape.rows part
  rw [hx2]
  unfold InMsg at h
  cases part with
  | main =>
    rw [if_neg (by decide)] at h
    exact h.1
  | mask =>
    rw [if_pos (by decide)] at h
    exact h.1

/-- **THE ROW's SUM IS THE SAME AT THE WORDS AND AT THE ACCESSOR's TABLES**, where they agree at
every entry on which the row has a weight other than 0. -/
theorem rowSum_words (st : Statement) (N : ℕ) (m m' : ℕ → OnBytes.Part → ℕ → GQ)
    (row : OnBytes.Row)
    (h : ∀ o < N, ∀ (part : OnBytes.Part) (J : ℕ),
      J < 2 ^ (st.rowBits o part + st.placeBits o part) →
      Reading.gl.val (row.coefficient o part J) ≠ 0 → m o part J = m' o part J) :
    rowSum Reading.gl st N m row = rowSum Reading.gl st N m' row := by
  have hp : ∀ o < N, ∀ part : OnBytes.Part,
      (∑ J ∈ Finset.range (2 ^ (st.rowBits o part + st.placeBits o part)),
        Reading.gl.val (row.coefficient o part J) * m o part J) =
      ∑ J ∈ Finset.range (2 ^ (st.rowBits o part + st.placeBits o part)),
        Reading.gl.val (row.coefficient o part J) * m' o part J := by
    intro o ho part
    refine Finset.sum_congr rfl fun J hJ => ?_
    by_cases hz : Reading.gl.val (row.coefficient o part J) = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [h o ho part J (Finset.mem_range.1 hJ) hz]
  unfold rowSum
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [hp o (Finset.mem_range.1 ho) .main, hp o (Finset.mem_range.1 ho) .mask]

/-- **WHAT IS ASKED OF A STATE BEHIND THE ONE EQUATION's PIECE.** g i: the plan's numbers of the
segment's group and of the place of the equation's row in its list. M: the plan's sendings' shapes,
in order. N: the law's bound on the number of oracle messages. -/
structure EqRowAsks (M : List OracleShape) (g i N : ℕ) (s : S) : Prop where
  /-- the statement is in order (the library's InOrder); it has at most N oracle messages -/
  order : OnBytes.Means.InOrder s.st ∧ s.st.oracles.size ≤ N
  /-- the link's check names the plan's group -/
  grp : ∀ a, atS.get? s = some a → a.L.check.group = g
  /-- that group's list ends with the equation's row -/
  rows : ∀ G, s.st.groups[g]? = some G → G.rows.size = i + 1
  /-- the state's table of codes is the plan's -/
  codes : s.st.codes = cs
  /-- "K12.msgShapes", as a sentence -/
  shapes : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = M[o]?
  /-- "K12.bookInOrder" at 0, as a sentence -/
  numbers : ∀ (z : ℕ) (T : Tree), s.book.trees[z]? = some T → T.number = z
  /-- every message has a place in the book, at a tree that is there -/
  places : ∀ o, o < s.st.oracles.size → ∃ q : ℕ × ℕ, s.book.place[o]? = some q ∧
    q.1 < s.book.trees.size
  /-- at the seat of a message on which the last row has a weight sits a member, and it has the
  plan's shape of that message -/
  member : ∀ G row, s.st.groups[g]? = some G → G.rows.back? = some row → ∀ o part J,
    Reading.gl.val (row.coefficient o part J) ≠ 0 → ∀ q, s.book.place[o]? = some q →
    ∃ y, (ms.find? fun y => decide (seatOf y = q)) = some y ∧ M[o]? = some (y.1.l.get y.2).1

/-- **FROM THE ITEM's SENTENCE TO THE KIND's OWN RELATION.** -/
theorem rowEq_of_says (M : List OracleShape) (g i n N : ℕ) (hn : 0 < n) (s : S)
    (w : Wit Cells Tok MsgT) (A : EqRowAsks cs ms M g i N s)
    (hseat : ∀ a G row, atS.get? s = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, a.d.book.place[o]? = some q → own.contains q = true)
    (hins : ∀ a G row, atS.get? s = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → RowInside cs ms own a N row)
    (h : OnBytes.Means.AllSay Reading.gl s.st
      (match s.st.groups[g]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[i + j]?)
      (wordsFirst arr s.st s.book w)) :
    rowEqQ own N s (rdC cs arr ms w) := by
  have hst := fun a (ha : atS.get? s = some a) => st_part s a ha
  have hbk := fun a (ha : atS.get? s = some a) => book_part s a ha
  have L : LastRowAt atS Reading.gl N s (wordsFirst arr s.st s.book w) :=
    lastRow_of_inOrder atS Reading.gl N s _
      (lastSays_of_place atS Reading.gl g i s _ (placeSays_of_run Reading.gl g i n hn s _ h) A.grp
        (fun a ha G hG => A.rows G (by rw [← hst a ha]; exact hG)))
      (fun a ha => by rw [hst a ha]; exact A.order)
  refine (rowEqQ_clamp cs arr ms own N s w hins).2 ?_
  intro a ha G hG row hr
  have hG' : s.st.groups[g]? = some G := by rw [← hst a ha, ← A.grp a ha]; exact hG
  have hfit := fit_of_inOrder atS Reading.gl N s (fun a ha => by rw [hst a ha]; exact A.order)
    a ha G hG row hr
  have e : tabAt own (seatTab cs arr ms w) s = tabQ own a.d.st a.d.book (seatTab cs arr ms w) := by
    unfold K9L.tabAt
    rw [ha]
  have hin := hins a G row ha hG hr
  have hse := hseat a G row ha hG hr
  unfold RowInside at hin
  rw [e, ← L a ha G hG row hr]
  rw [hbk a ha] at hse
  rw [hst a ha, hbk a ha] at hin ⊢
  refine (rowSum_words s.st N _ _ row fun o hoN part J hJ hz => ?_).symm
  have ho : o < s.st.oracles.size := by
    by_contra hc
    exact hz (hfit.2.2 o (by rw [hst a ha]; omega) part J)
  obtain ⟨sh, q, hM, hq, hT⟩ :=
    tabFirst_at_plan arr M s.st s.book A.shapes A.numbers A.places w o ho
  have hown := hse o part J hz q hq
  obtain ⟨y, hy, hMy⟩ := A.member G row hG' hr o part J hz q hq
  have hsh : (y.1.l.get y.2).1 = sh := Option.some.inj (hMy.symm.trans hM)
  have hseat : K9.seatAt own s.book o = some q := by
    unfold K9.seatAt
    rw [hq, Option.bind_some, if_pos hown]
  have hI := hin o hoN part J hJ hz q y hseat hy
  rw [hsh] at hI
  exact words_tabQ cs arr ms own s.st s.book w o part J sh q y hT hq hown hy hsh A.codes
    (real_of_inMsg cs s.st o part sh _ _ ((A.shapes o ho).trans hM) hI)

end

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **t3 AT THE ONE EQUATION's PIECE.** -/
theorem t3_eq {C : CK} (M : List OracleShape) (N : ℕ)
    (houts : (rowQ links pl k).outs = [.row m .equation])
    (hn : 0 < (𝔇.N.rowsAt m .equation).2)
    (hA : ∀ b, onK (k + 1) b →
      EqRowAsks 𝔇.cs 𝔇.ms M (𝔇.N.groupAt m) (𝔇.N.rowsAt m .equation).1 N b.1)
    (hT : ∀ a, onK k a → K9.totalIn own a.1 = true)
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, onK k a → pe.ior.red.out a τ = some b → ∃ p ft rs cols n,
      (K9.oneEquation (Cl := Claim) atS p).step ft a.1 rs cols = .ok (b.1, n)) :
    ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relRow own N rdW b w := by
  intro a τ b w ha hout hb h
  obtain ⟨p, ft, rs, cols, n, hs⟩ := hstep a τ b ha hout
  have h1 : rowSays 𝔇.N (wordsAtFirst 𝔇.arr) m .equation (z, b.1) (strsOf F b.2) w :=
    h (.row m .equation) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  exact rowEq_of_says 𝔇.cs 𝔇.arr 𝔇.ms own M _ _ _ N hn b.1 w (hA b hb)
    (seats_first own p ft a.1 rs cols b.1 n hs (hT a ha))
    (rowInside_step 𝔇.cs 𝔇.ms own p ft a.1 rs cols b.1 n N hs (hin a ha)) h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.words_tabQ
#print axioms VerifiableInference.Desc.LinkJoin.rowSum_words
#print axioms VerifiableInference.Desc.LinkJoin.rowEq_of_says
#print axioms VerifiableInference.Desc.LinkJoin.t3_eq
