--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Send/Says.lean: THE SHARED "SENDING" (the kind K1), THE PROVER's SIDE: THE VALUES'
HALF: behind the sending every new sample row says true of the held words, every old row says what
it said, and so all that the statement claims is kept. Statements and proofs.

General in the place P : K1.Par, in the carried record, in the words in front and in the rows V that
the caller hands. The letters: d' := K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂) (the record
behind: Johnson/Prover/Send/Form.lean); H := held w d.st.oracles.size P V (Core.lean).

  ext_behind, ext_sent   the statement behind the sending is a later statement of the one in front,
                   and of the one that has received the messages; these two have the same tables
                   (same_sent), so a row has one value at both (the landed K3.KeyLaw.value_same)
  flat_at, answers_at    answer i of message k stands at K1.offset P k + i
  rowsOf_at, rowsOf_mem_at, rows_written, rows_written_all   the sample rows of message k, by index:
                   K1's own sampleRow at seed i, with the written answer i as its target
  send_says        SO EVERY NEW SAMPLE ROW SAYS TRUE OF H: the answer was made as the row's own left
                   side at H
  says_held, old_says    an old row's Says is untouched: an equivalence
  send_inOrder     the statement stays in order (the landed K1.decideSend_keeps at send_yes)
  send_claims, send_claims_of_yes   Claims goes forwards over the sending (Holds:
                   Johnson/Prover/Send/SaysForth.lean)
  send_padded      the words stay 0 on the rows beyond the real ones
  held_self        words that hold the place's messages already are not turned by held
  wr_shape, size_sent, answersIn_written, number_cases   tools

By: K3.KeyLaw.value_same (Johnson/Desc/First/Look/KeyLaw/SameTables.lean), says_extends
(Johnson/Desc/Means/Keeps.lean), says_agree (Means/ItemsRead.lean),
K1.decideSend_keeps (Johnson/Desc/K1/Law/KeepsOrder.lean).

Limits. The premise on round 2 is an equation: it holds just the answers of Core.lean. That a
message holds what a caller's LATER rows claim of it is the caller's. Padded
(Johnson/Desc/Means/Says.lean) asks 0 at every number that the statement does not have: so
send_padded is a law of growing words; words that hold later messages from the first step on do not
meet its premise. Nothing on a verifier's yes (Form.lean), on columns (Enc.lean), on soundness, or
on what any entry shows or does not show.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Form
import Johnson.Desc.K1.Law.KeepsOrder
import Johnson.Desc.Means.ItemsRead
import Johnson.Desc.First.Look.KeyLaw.SameTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open _root_.Desc.Plain (DState)

/-! ## The statement behind, against the statement in front -/

theorem wr_shape (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) : (K1.wr codes seeds o s ys).shape = s := by
  unfold K1.wr
  split <;> rfl

variable {L : Type}

/-- The statement behind the sending is a later statement of the one in front. -/
theorem ext_behind (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) :
    Extends d.st (K1.behind P d seeds ys).st :=
  ⟨rfl, fun o x hx => by
    have ho : o < d.st.oracles.size := by
      by_contra c
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
      cases hx
    exact ⟨x, by rw [(behind_rest P d seeds ys).2.2.2.2.2.1 o ho]; exact hx, rfl⟩⟩

/-- And of the one that has received the messages. -/
theorem ext_sent (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) :
    Extends (stSent d.st P.sent) (K1.behind P d seeds ys).st :=
  ⟨rfl, fun o x hx => by
    by_cases ho : o < d.st.oracles.size
    · rw [stSent_old d.st P.sent o ho] at hx
      exact ⟨x, by rw [(behind_rest P d seeds ys).2.2.2.2.2.1 o ho]; exact hx, rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
      rw [stSent_new] at hx
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hx
      have hk : k < P.sent.size := (Array.getElem?_eq_some_iff.1 hn).1
      refine ⟨_, behind_at P d seeds ys k hk, ?_⟩
      rw [wr_shape]
      unfold shapeAt
      rw [Array.getD_eq_getD_getElem?, hn]
      rfl⟩

theorem size_sent (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) :
    (K1.behind P d seeds ys).st.oracles.size = (stSent d.st P.sent).oracles.size := by
  rw [(behind_rest P d seeds ys).2.2.2.2.1]
  show _ = (d.st.oracles ++ P.sent.map _).size
  rw [Array.size_append, Array.size_map]

/-- These two statements have the same tables. -/
theorem same_sent (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) :
    K3.KeyLaw.SameTables (stSent d.st P.sent) (K1.behind P d seeds ys).st := by
  refine ⟨size_sent P d seeds ys, fun o part => ?_⟩
  by_cases ho : o < (stSent d.st P.sent).oracles.size
  · exact (ext_sent P d seeds ys).tableSize ho part
  · have h1 : (stSent d.st P.sent).oracles[o]? = none :=
      Array.getElem?_eq_none (Nat.le_of_not_lt ho)
    have h2 : (K1.behind P d seeds ys).st.oracles[o]? = none :=
      Array.getElem?_eq_none (by rw [size_sent]; exact Nat.le_of_not_lt ho)
    unfold tableSize Statement.has
    rw [h1, h2]
    rfl

/-! ## The written answers and the sample rows, by index -/

/-- Entry i of the k-th list stands behind the lists in front of it. -/
theorem flat_at {α : Type} (f : ℕ → List α) : ∀ (n k i : ℕ), k < n → i < (f k).length →
    ((List.range n).flatMap f)[((List.range k).map fun j => (f j).length).sum + i]? = (f k)[i]?
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, k, i, hk, hi => by
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_or_ge k n with h | h
    · have ih := flat_at f n k i h hi
      have hlt : ((List.range k).map fun j => (f j).length).sum + i <
          ((List.range n).flatMap f).length := by
        rw [List.getElem?_eq_getElem hi] at ih
        exact (List.getElem?_eq_some_iff.1 ih).1
      rw [List.getElem?_append_left hlt, ih]
    · obtain rfl : k = n := by omega
      rw [List.getElem?_append_right (by rw [List.length_flatMap]; exact Nat.le_add_right _ _),
        List.length_flatMap, Nat.add_sub_cancel_left]

/-- **Answer i of message k stands at K1.offset P k + i.** -/
theorem answers_at (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (k i : ℕ) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) :
    (answers P S' first w' seeds)[K1.offset P k + i]? =
      some (ofE (value rdE S'
        (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
          (seeds.getD i default).2 i zeroE) w')) := by
  have h := flat_at (answersAt P S' first w' seeds) P.sent.size k i hk
    (by rw [length_answersAt]; exact hi)
  simp only [length_answersAt] at h
  rw [sum_range_shapes P k (Nat.le_of_lt hk)] at h
  rw [answers_flat, h]
  unfold answersAt
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- Row i of a message's sample rows. -/
theorem rowsOf_at (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) (i : ℕ) (hi : i < s.answers) (sd : List E × E) (y : E)
    (h1 : seeds[i]? = some sd) (h2 : ys[i]? = some y) :
    (K1.rowsOf codes seeds o s ys)[i]? =
      some (K1.sampleRow (K1.Msg.of codes s) o sd.1 sd.2 i y) := by
  unfold K1.rowsOf
  have hz : ((seeds.take s.answers).zip (ys.take s.answers))[i]? = some (sd, y) :=
    List.getElem?_zip_eq_some.2 ⟨by rw [List.getElem?_take_of_lt hi]; exact h1,
      by rw [List.getElem?_take_of_lt hi]; exact h2⟩
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx, hz]
  simp

/-- Each of a message's sample rows is such a row. -/
theorem rowsOf_mem_at (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) (r : Row) (h : r ∈ (K1.rowsOf codes seeds o s ys).toList) :
    ∃ (i : ℕ) (sd : List E × E) (y : E), i < s.answers ∧ seeds[i]? = some sd ∧ ys[i]? = some y ∧
      r = K1.sampleRow (K1.Msg.of codes s) o sd.1 sd.2 i y := by
  unfold K1.rowsOf at h
  simp only [List.mem_map] at h
  obtain ⟨⟨⟨sd, y⟩, i⟩, hm, rfl⟩ := h
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at hm
  obtain ⟨a1, a2⟩ := hm
  have hi : i < s.answers := by
    have := (List.getElem?_eq_some_iff.1 a1).1
    rw [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hi] at a1 a2
  exact ⟨i, sd, y, hi, a1, a2, rfl⟩

/-- **The sample rows of message k at the written answers, by index.** -/
theorem rows_written (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (k i : ℕ) (hk : k < P.sent.size) (hi : i < (shapeAt P k).answers)
    (hs : (shapeAt P k).answers ≤ seeds.length) :
    (K1.rowsOf P.codes seeds (first + k) (shapeAt P k)
        (((answers P S' first w' seeds).map E.ofTriple).drop (K1.offset P k)))[i]? =
      some (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
        (seeds.getD i default).2 i
        (E.ofTriple (ofE (value rdE S'
          (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
            (seeds.getD i default).2 i zeroE) w')))) := by
  have hl : i < seeds.length := Nat.lt_of_lt_of_le hi hs
  refine rowsOf_at _ _ _ _ _ i hi (seeds.getD i default) _ ?_ ?_
  · rw [List.getD_eq_getElem _ _ hl, List.getElem?_eq_getElem hl]
  · rw [List.getElem?_drop, List.getElem?_map, answers_at P S' first w' seeds k i hk hi]
    rfl

/-- The same, as one array. -/
theorem rows_written_all (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (k : ℕ) (hk : k < P.sent.size)
    (hs : (shapeAt P k).answers ≤ seeds.length) :
    K1.rowsOf P.codes seeds (first + k) (shapeAt P k)
        (((answers P S' first w' seeds).map E.ofTriple).drop (K1.offset P k)) =
      ((List.range (shapeAt P k).answers).map fun i =>
        K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
          (seeds.getD i default).2 i
          (E.ofTriple ((answersAt P S' first w' seeds k).getD i default))).toArray := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < (shapeAt P k).answers
  · have e : (answersAt P S' first w' seeds k).getD i default =
        ofE (value rdE S'
          (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
            (seeds.getD i default).2 i zeroE) w') := by
      unfold answersAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    rw [rows_written P S' first w' seeds k i hk hi hs, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hi]
    simp only [Option.map_some, e]
  · rw [Array.getElem?_eq_none (by simp [K1.rowsOf]; omega), List.getElem?_toArray,
      List.getElem?_eq_none (by simp; omega)]

/-! ## The new rows -/

/-- The answer in round 2, as the decision reads it. -/
theorem answersIn_written (r₂ : Fmt.RoundView) (l : List Fmt.Ext3) (h : r₂.vals = l.map .answer) :
    K1.answersIn r₂ = l.map E.ofTriple := by
  unfold K1.answersIn
  rw [h]
  clear h
  induction l with
  | nil => rfl
  | cons a l ih =>
    show E.ofTriple a :: List.filterMap _ (l.map Fmt.ItemValue.answer) = _
    rw [ih]
    rfl

/-- **EVERY NEW SAMPLE ROW SAYS TRUE OF THE HELD WORDS.** -/
theorem send_says (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (w : Words GE) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (held w d.st.oracles.size P V) (K1.seedsOf P r₁)).map .answer)
    (k : ℕ) (x : OnBytes.Oracle) (hk : k < P.sent.size)
    (hx : (K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)).st.oracles[d.st.oracles.size + k]? =
      some x) :
    AllSay rdE (K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)).st x.sampleRows.toList
      (held w d.st.oracles.size P V) := by
  intro r hr
  rw [behind_at P d _ _ k hk] at hx
  obtain rfl := Option.some.inj hx
  by_cases h0 : (shapeAt P k).answers = 0
  · rw [wr_unsampled _ _ _ _ _ h0] at hr
    simp at hr
  · rw [(wr_sampled _ _ _ _ _ h0).2.2.1] at hr
    obtain ⟨i, sd, y, hi, h1, h2, rfl⟩ := rowsOf_mem_at _ _ _ _ _ r hr
    rw [answersIn_written r₂ _ hans, List.getElem?_drop, List.getElem?_map,
      answers_at P _ _ _ _ k i hk hi] at h2
    have hsd : (K1.seedsOf P r₁).getD i default = sd := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    rw [hsd] at h2
    obtain rfl := Option.some.inj h2
    unfold Says
    rw [K3.KeyLaw.value_same rdE (same_sent P d _ _)]
    show _ = readE (E.ofTriple (ofE _))
    rw [readE_ofTriple, toE_ofE]
    rfl

/-! ## The old rows -/

/-- At the statement in front a row that has passed the tests says of the held words what it says of
the words in front. -/
theorem says_held (S : Statement) (P : K1.Par) (w : Words GE) (V : ℕ → Rows) (G : Group) (r : Row)
    (hr : RowIn S G r) :
    Says rdE S r (held w S.oracles.size P V) ↔ Says rdE S r w := by
  have hall : RowIn S { code := 0, members := Array.range S.oracles.size } r :=
    ⟨fun t ht => placeOk_all (hr.terms t ht), fun u hu => placeOk_all (hr.units u hu),
      fun a ha => ⟨(hr.runs a ha).1, (hr.runs a ha).2.1, placeOk_all (hr.runs a ha).2.2⟩,
      fun f hf => ⟨placeOk_all (hr.forms f hf).1, (hr.forms f hf).2⟩⟩
  refine says_agree rdE hall fun o ho part i => held_old w _ P V o part i fun c => ?_
  have : o < S.oracles.size := Array.mem_range.1 (Array.mem_toList_iff.1 ho)
  omega

/-- **AN OLD ROW's Says IS UNTOUCHED.** -/
theorem old_says (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E)
    (w : Words GE) (V : ℕ → Rows) (G : Group) (r : Row) (hr : RowIn d.st G r) :
    Says rdE (K1.behind P d seeds ys).st r (held w d.st.oracles.size P V) ↔ Says rdE d.st r w :=
  (says_extends rdE (ext_behind P d seeds ys) hr _).trans (says_held d.st P w V G r hr)

/-! ## What the statement claims is kept -/

/-- The statement stays in order. -/
theorem send_inOrder (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (F : SendFront P d)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true) (hI : InOrder d.st) :
    InOrder (K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)).st :=
  K1.decideSend_keeps P none d _ r₁ r₂ _ F.plan hfit (send_yes P d r₁ r₂ F hfit) hI

/-- A number behind the sending is an old one or one of the place's. -/
theorem number_cases (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) (o : ℕ)
    (x : OnBytes.Oracle) (hx : (K1.behind P d seeds ys).st.oracles[o]? = some x) :
    (o < d.st.oracles.size ∧ d.st.oracles[o]? = some x) ∨
      ∃ k, k < P.sent.size ∧ o = d.st.oracles.size + k := by
  by_cases ho : o < d.st.oracles.size
  · rw [(behind_rest P d seeds ys).2.2.2.2.2.1 o ho] at hx
    exact Or.inl ⟨ho, hx⟩
  · have h1 : o < (K1.behind P d seeds ys).st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    rw [(behind_rest P d seeds ys).2.2.2.2.1] at h1
    exact Or.inr ⟨o - d.st.oracles.size, by omega, by omega⟩

/-- **Claims goes forwards over the sending.** -/
theorem send_claims (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (w : Words GE) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (held w d.st.oracles.size P V) (K1.seedsOf P r₁)).map .answer)
    (hI : InOrder d.st) (hC : Claims rdE d.st w) :
    Claims rdE (K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)).st
      (held w d.st.oracles.size P V) := by
  refine ⟨fun g G hG r hr => ?_, fun o x hx hp r hr => ?_⟩
  · have hG' : d.st.groups[g]? = some G := hG
    exact (old_says P d _ _ w V G r (hI.rows g G hG' r hr)).2 (hC.rows g G hG' r hr)
  · rcases number_cases P d _ _ o x hx with ⟨_, hx'⟩ | ⟨k, hk, rfl⟩
    · exact (old_says P d _ _ w V _ r (hI.samples o x hx' r hr)).2
        (hC.samples o x hx' (fun g G hG => hp g G hG) r hr)
    · exact send_says P d r₁ r₂ w V hans k x hk hx r hr

/-- The same behind any yes of K1's decision: the record behind a yes is K1.behind. -/
theorem send_claims_of_yes (P : K1.Par) (owed : Option ℕ) (d x : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array ℕ) (w : Words GE) (V : ℕ → Rows)
    (hyes : K1.decideSend P owed d [r₁, r₂] = .ok (ids, x))
    (hans : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (held w d.st.oracles.size P V)
      (K1.cutSeeds P.coordinates P.seeds (r₁.drawn.elems.map E.ofTriple))).map .answer)
    (hI : InOrder d.st) (hC : Claims rdE d.st w) :
    Claims rdE x.st (held w d.st.oracles.size P V) := by
  obtain ⟨_, _, rfl⟩ := (K1.decideSend_iff P owed d x r₁ r₂ ids).1 hyes
  exact send_claims P d r₁ r₂ w V hans hI hC

/-- **The words stay 0 on the rows beyond the real ones.** -/
theorem send_padded (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E)
    (w : Words GE) (V : ℕ → Rows) (hP : Padded d.st w) :
    Padded (K1.behind P d seeds ys).st (held w d.st.oracles.size P V) := by
  intro o part i h
  by_cases h1 : o < d.st.oracles.size
  · rw [held_old w _ P V o part i (fun c => by omega)]
    refine hP o part i ?_
    rw [(ext_behind P d seeds ys).rowBits h1 part] at h
    unfold realRows at h ⊢
    rw [(behind_rest P d seeds ys).2.2.2.2.2.1 o h1] at h
    exact h
  · by_cases h2 : o < d.st.oracles.size + P.sent.size
    · obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
      have hk : k < P.sent.size := by omega
      exact padded_new w _ P V _ k hk _ (behind_at P d seeds ys k hk) (wr_shape _ _ _ _ _) part i h
    · rw [held_old w _ P V o part i (fun c => by omega)]
      refine hP o part i ?_
      unfold realRows
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt h1)]
      exact Nat.zero_le _

/-- Words that hold the place's messages already are not turned. -/
theorem held_self (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows)
    (h : ∀ k, k < P.sent.size → w (first + k) = (V k).word (shapeAt P k)) :
    held w first P V = w := by
  funext o part i
  unfold held
  split
  · rename_i c
    have e := congrFun (congrFun (h (o - first) (by omega)) part) i
    rw [show first + (o - first) = o by omega] at e
    exact e.symm
  · rfl

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.wr_shape
#print axioms Johnson.Prover.Send.ext_behind
#print axioms Johnson.Prover.Send.ext_sent
#print axioms Johnson.Prover.Send.size_sent
#print axioms Johnson.Prover.Send.same_sent
#print axioms Johnson.Prover.Send.flat_at
#print axioms Johnson.Prover.Send.answers_at
#print axioms Johnson.Prover.Send.rowsOf_at
#print axioms Johnson.Prover.Send.rowsOf_mem_at
#print axioms Johnson.Prover.Send.rows_written
#print axioms Johnson.Prover.Send.rows_written_all
#print axioms Johnson.Prover.Send.answersIn_written
#print axioms Johnson.Prover.Send.send_says
#print axioms Johnson.Prover.Send.says_held
#print axioms Johnson.Prover.Send.old_says
#print axioms Johnson.Prover.Send.send_inOrder
#print axioms Johnson.Prover.Send.number_cases
#print axioms Johnson.Prover.Send.send_claims
#print axioms Johnson.Prover.Send.send_claims_of_yes
#print axioms Johnson.Prover.Send.send_padded
#print axioms Johnson.Prover.Send.held_self
