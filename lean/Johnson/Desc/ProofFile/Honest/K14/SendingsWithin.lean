-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/SendingsWithin.lean: AT A SENDING WHOSE SHAPES FIT (sendShapeFits,
Honest/K14/SendingsShapes.lean), AT AN ARRAY OF JUST THE PART's COUNT OF COINS, THE TABLES AND THE
ANSWERS OF Honest/K14/Sendings.lean ARE THE SAME WHATEVER VALUES STAND IN, NUMBER BY NUMBER, FOR
COINS BEYOND THE ARRAY. One form, one definition and statements, each with its proof. An equation at
each value of the coins: no distribution occurs.

  LaidAgree       a form: two messages' rows are one at the shape's real rows, at places below the
                  code's message length and at tails below the code's tail. THAT IS ALL THAT A
                  COLUMN READS (tables_within); ALL THAT AN ANSWER READS WHERE THE SHAPES FIT
                  (answers_within); at one shape that fails (5) an answer reads beyond it
  laid_within     **one message**: coins that are one BELOW THE MESSAGE's COUNT (dueOf) give one
                  message, in that form. The test on the message's shape is spent at a fold's fresh
                  table alone: h ≤ k
  due_in_count    each message's coins lie within the part's count: at every job
  rowsFilled      the part's own reading with d n, any function of the number, in the place of the 0
                  that SendJob.rows lays for the coin number n beyond the array; rows_filled_zero:
                  at the function 0 it is SendJob.rows
  rows_within     **at the part's own reading the fillers are idle**, in that form
  symbols_within, column_within, tables_within   the tables read the rows through the form alone: at
                  every list of messages
  words_within, value_within, answers_within   so do the answers, where the shapes fit: there a
                  table has just the code's message length of places a row
  sent_within     **both in one**; sent_within_coins: at the array that is made of the coins of a
                  count (coinsE; coins_size: it has just that count)
  cell_below, freshRow_reads, offset_step, offset_le, msgFits_at, ell_base, ell_mask, local_shape
                  small steps

What is spent of the test on a sending's shapes: of (1): the codes' numbers lie in the arrays; of
(4): h ≤ k; (5): every code's message length is a power of two. The clauses' numbers are those of
Honest/K14/SendingsShapes.lean's head. The tables want the messages' tests alone; (5) and (1) are
spent at the answers. BOTH (4) AND (5) BITE, which is shown neither in this file nor in any file
that it imports: there is a small shape that fails (5) alone, at which an answer reads a filler, and
one that fails, of (4), h ≤ k and 1 ≤ k
alone, UNDER A MASK CODE WITHOUT A TAIL, at which a column does; under a mask code with a tail the
numbers that such a fresh table asks beyond its coefficients are its own tails', one coin at two
places and no filler: THAT IS ARITHMETIC AT laid's TEXT, NOT SHOWN HERE. Of these two clauses of (4)
this proof spends the first; that the second would serve as well is not shown here.

Limits. WITHIN, NOT ALL OF: nothing here says that a coin below the count IS read. NO THEOREM HERE
NAMES
THE PART's TWO MOVES: by their text (sendingPart, Honest/K14/Sendings.lean) the first says
sentTables, the second answersOf at the seeds that it cuts off the challenge, both at SendJob.rows
at the array of sent_within_coins. Nothing on a seed's elements, on the point, on the committed
table's pads and tails, or on a vector that does not fit its main rows: no premise here bars these.
That a tree's column has as many words as the tree's width is NOT shown here. Most of the small
steps, and symbols_within and coins_size, are proved under other names in files that import more
than this one. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.K14.Law.WalkFromOmega
import Johnson.Desc.K1.Law.SaysTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice Statement ceilLog2)
open OnBytes.Means (Words)
open VerifiableInference.Desc (K1.Par K1.Msg.of)

/-- **Two messages' rows are one at the shape's real rows, at places below the code's message length
and at tails below the code's tail.** -/
structure LaidAgree (codes : Codes) (s : OracleShape) (L L' : Laid) : Prop where
  main : ∀ r, r < s.mainRows → ∀ j, j < (codes.base.getD s.code default).ell →
    L.main r j = L'.main r j
  mainTail : ∀ r, r < s.mainRows → ∀ t, t < (codes.base.getD s.code default).r →
    L.mainTail r t = L'.mainTail r t
  mask : ∀ r, r < s.maskRows → ∀ j, j < (codes.mask.getD s.maskCode default).ell →
    L.mask r j = L'.mask r j
  maskTail : ∀ r, r < s.maskRows → ∀ t, t < (codes.mask.getD s.maskCode default).r →
    L.maskTail r t = L'.maskTail r t

/-! ## One message -/

/-- a b + c lies below n b where a is below n and c below b. (The library has the same sentence as
K5Law.cell_lt, Johnson/Desc/First/Att/Claims/SlotsCovered.lean: three lines, not imported here.) -/
theorem cell_below {a b c n : Nat} (ha : a < n) (hc : c < b) : a * b + c < n * b :=
  Nat.lt_of_lt_of_le (by rw [Nat.succ_mul]; omega) (Nat.mul_le_mul_right _ ha)

/-- What the packing of a fold's hiding polynomial reads of the coefficients, where h ≤ k. -/
theorem freshRow_reads (f : Fmt.Fld) (k h : Nat) (U U' : Fmt.M1.FoldOwn.Hide) (b : Nat)
    (hh : h ≤ k) (hw : ∀ l, 1 ≤ l → l ≤ k → ∀ t, t = 1 ∨ t = 2 → U.w l t = U'.w l t)
    (h0 : U.w0 = U'.w0) :
    Fmt.M1.FoldOwn.freshRow f k h U b = Fmt.M1.FoldOwn.freshRow f k h U' b := by
  have e1 : ∀ (n : Nat), n ≤ h → ∀ s : Fmt.Ext3,
      (List.range n).foldl (fun s i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then
        f.addE s (U.w (i + 1) 1) else s) s =
      (List.range n).foldl (fun s i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then
        f.addE s (U'.w (i + 1) 1) else s) s := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro hn s
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega) s]
      show (if _ then f.addE _ (U.w (n + 1) 1) else _) =
        (if _ then f.addE _ (U'.w (n + 1) 1) else _)
      rw [hw (n + 1) (by omega) (by omega) 1 (Or.inl rfl)]
  have e2 : ((List.range h).map fun i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then U.w (i + 1) 2
      else Fmt.Fld.zeroE) = (List.range h).map fun i =>
        if Fmt.M1.FoldOwn.reaches h b (i + 1) then U'.w (i + 1) 2 else Fmt.Fld.zeroE :=
    List.map_congr_left fun i hi => by
      rw [hw (i + 1) (by omega) (by have := List.mem_range.1 hi; omega) 2 (Or.inr rfl)]
  have e3 : ((List.range (k - h - 1)).flatMap fun i => [U.w (h + 2 + i) 1, U.w (h + 2 + i) 2]) =
      (List.range (k - h - 1)).flatMap fun i => [U'.w (h + 2 + i) 1, U'.w (h + 2 + i) 2] :=
    List.flatMap_congr fun i hi => by
      have := List.mem_range.1 hi
      rw [hw (h + 2 + i) (by omega) (by omega) 1 (Or.inl rfl),
        hw (h + 2 + i) (by omega) (by omega) 2 (Or.inr rfl)]
  unfold Fmt.M1.FoldOwn.freshRow
  rw [e1 h (Nat.le_refl h), e2, e3, h0]
  by_cases hk : h < k
  · rw [if_pos hk, if_pos hk, if_pos hk, if_pos hk, hw (h + 1) (by omega) (by omega) 1 (Or.inl rfl),
      hw (h + 1) (by omega) (by omega) 2 (Or.inr rfl)]
  · rw [if_neg hk, if_neg hk, if_neg hk, if_neg hk]

/-- **ONE MESSAGE: COINS THAT ARE ONE BELOW THE MESSAGE's COUNT GIVE ONE MESSAGE**: at its real
rows, at places below the code's message length and at tails below the code's tail. -/
theorem laid_within (codes : Codes) (s : OracleShape) (v cs cs' : Nat → E) (sort : MsgSort)
    (hfit : msgShapeFits codes s sort = true) (h : ∀ i, i < dueOf codes s sort → cs i = cs' i) :
    LaidAgree codes s (laid codes s v cs sort) (laid codes s v cs' sort) := by
  cases sort with
  | plain high =>
    refine ⟨fun r _ j _ => ?_, fun r hr t ht => ?_, fun r hr j hj => ?_, fun r hr t ht => ?_⟩
    · show (if _ then cs _ else _) = (if _ then cs' _ else _)
      split_ifs with hc
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        refine h _ ?_
        show _ < s.mainRows * _ + (if s.maskRows == 0 then s.answers else 0) + s.maskRows * _ +
          s.maskRows * _
        rw [hc.1.1.1, if_pos (by decide)]
        omega
      · rfl
    · show cs _ = cs' _
      refine h _ ?_
      have h1 := cell_below hr ht
      simp only [dueOf]
      omega
    · show cs _ = cs' _
      refine h _ ?_
      have h1 := cell_below hj hr
      rw [Nat.mul_comm (codes.mask.getD s.maskCode default).ell] at h1
      simp only [dueOf]
      omega
    · show cs _ = cs' _
      refine h _ ?_
      have h1 := cell_below hr ht
      simp only [dueOf]
      omega
  | fresh k h' =>
    simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
    obtain ⟨⟨⟨-, hh⟩, -⟩, -⟩ := hfit
    refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun r _ j _ => ?_, fun r hr t ht => ?_⟩
    · show E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two k h' _ r).getD j Fmt.Fld.zeroE) =
        E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two k h' _ r).getD j Fmt.Fld.zeroE)
      have hw : ∀ l, 1 ≤ l → l ≤ k → ∀ t, t = 1 ∨ t = 2 →
          (cs (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)).triple =
            (cs' (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)).triple := by
        intro l hl1 hl2 t ht
        rw [h _ ?_]
        simp only [dueOf]
        split_ifs <;> rcases ht with rfl | rfl <;> omega
      have h0 : (cs (2 * (k - 1))).triple = (cs' (2 * (k - 1))).triple := by
        rw [h _ ?_]
        simp only [dueOf]
        omega
      exact congrArg (fun x => E.ofTriple (x.getD j Fmt.Fld.zeroE))
        (freshRow_reads .two k h'
          ⟨fun l t => (cs (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)).triple,
            (cs (2 * (k - 1))).triple⟩
          ⟨fun l t => (cs' (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)).triple,
            (cs' (2 * (k - 1))).triple⟩ r hh hw h0)
    · show cs _ = cs' _
      refine h _ ?_
      have h1 := cell_below hr ht
      simp only [dueOf]
      omega

/-! ## A message's coins within the part's count -/

/-- offsetOf at the next message. -/
theorem offset_step (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) (k : Nat)
    (hk : k < sent.size) :
    offsetOf codes sent sort (k + 1) =
      offsetOf codes sent sort k + dueOf codes (sent.getD k default).shape (sort k) := by
  have hl : k < sent.toList.length := by
    rw [Array.length_toList]
    exact hk
  have hg : sent.toList[k]? = some (sent.getD k default) := by
    rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    rfl
  unfold offsetOf
  rw [List.take_add_one, hg, Option.toList_some, List.zipIdx_append, List.foldl_append,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hl)]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, Nat.zero_add]

/-- Where messages' coins begin grows with the message's number. -/
theorem offset_le (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) :
    ∀ n k, k ≤ n → n ≤ sent.size → offsetOf codes sent sort k ≤ offsetOf codes sent sort n := by
  intro n
  induction n with
  | zero =>
    intro k hk _
    have e : k = 0 := by omega
    subst e
    exact Nat.le_refl _
  | succ n ih =>
    intro k hk hn
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have h1 := ih k (by omega) (by omega)
      rw [offset_step codes sent sort n (by omega)]
      omega
    · have e : k = n + 1 := by omega
      subst e
      exact Nat.le_refl _

/-- **Each message's coins lie within the part's count**: at every job. -/
theorem due_in_count (J : SendJob) (k : Nat) (hk : k < J.Q.sent.size) :
    offsetOf J.Q.codes J.Q.sent J.sort k +
        dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k) ≤
      (sendingPart J).takes.e := by
  have h := offset_le J.Q.codes J.Q.sent J.sort J.Q.sent.size (k + 1) hk (Nat.le_refl _)
  rw [offset_step _ _ _ k hk] at h
  exact h

/-- What the test on a sending's shapes says of message number k. -/
theorem msgFits_at (J : SendJob) (hfit : sendShapeFits J = true) (k : Nat)
    (hk : k < J.Q.sent.size) :
    msgShapeFits J.Q.codes (J.Q.sent.getD k default).shape (J.sort k) = true := by
  unfold sendShapeFits at hfit
  rw [Bool.and_eq_true] at hfit
  exact List.all_eq_true.1 hfit.2 k (List.mem_range.2 hk)

/-- The rows of all messages, with d n in the place of the coin number n beyond the array. -/
def rowsFilled (J : SendJob) (t : State Ask Unit) (cs : Array E) (d : Nat → E) (k : Nat) : Laid :=
  laid J.Q.codes (J.Q.sent.getD k default).shape (J.data t k)
    (fun i => cs.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i)
      (d (offsetOf J.Q.codes J.Q.sent J.sort k + i))) (J.sort k)

/-- At the function 0 it is the part's own reading. -/
theorem rows_filled_zero (J : SendJob) (t : State Ask Unit) (cs : Array E) :
    J.rows t cs = rowsFilled J t cs fun _ => zeroE := rfl

/-- **AT THE PART's OWN READING THE FILLERS ARE IDLE**: any function of the number. -/
theorem rows_within (J : SendJob) (hfit : sendShapeFits J = true) (t : State Ask Unit)
    (cs : Array E) (hsz : cs.size = (sendingPart J).takes.e) (d : Nat → E) (k : Nat)
    (hk : k < J.Q.sent.size) :
    LaidAgree J.Q.codes (J.Q.sent.getD k default).shape (J.rows t cs k)
      (rowsFilled J t cs d k) := by
  refine laid_within _ _ _ _ _ _ (msgFits_at J hfit k hk) fun i hi => ?_
  have h1 := due_in_count J k hk
  have h2 : offsetOf J.Q.codes J.Q.sent J.sort k + i < cs.size := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
  rfl

/-! ## The tables -/

/-- The symbols of n rows read the rows at the places below the code's message length and the tails
below its tail. -/
theorem symbols_within (c : OnBytes.Code) (x n : Nat) (row row' tail tail' : Nat → Nat → E)
    (h1 : ∀ r, r < n → ∀ j, j < c.ell → row r j = row' r j)
    (h2 : ∀ r, r < n → ∀ t, t < c.r → tail r t = tail' r t) :
    symbolsOf c x n row tail = symbolsOf c x n row' tail' := by
  unfold symbolsOf
  refine List.flatMap_congr fun r hr => ?_
  have hr' := List.mem_range.1 hr
  have e1 : ((List.range c.ell).map fun j => (row r j).triple) =
      (List.range c.ell).map fun j => (row' r j).triple :=
    List.map_congr_left fun j hj => by rw [h1 r hr' j (List.mem_range.1 hj)]
  have e2 : ((List.range c.r).map fun t => (tail r t).triple) =
      (List.range c.r).map fun t => (tail' r t).triple :=
    List.map_congr_left fun t ht => by rw [h2 r hr' t (List.mem_range.1 ht)]
  simp only [e1, e2]

/-- A tree's column. -/
theorem column_within (codes : Codes) (sent : Array OracleNotice) (L L' : Nat → Laid)
    (h : ∀ k, k < sent.size → LaidAgree codes (sent.getD k default).shape (L k) (L' k))
    (tree x : Nat) : columnOf codes sent L tree x = columnOf codes sent L' tree x := by
  simp only [columnOf]
  congr 1 <;> refine List.flatMap_congr fun k hk => ?_
  · have hk' := List.mem_range.1 (List.mem_filter.1 hk).1
    exact symbols_within _ _ _ _ _ _ _ (h k hk').main (h k hk').mainTail
  · have hk' := List.mem_range.1 (List.mem_filter.1 hk).1
    exact symbols_within _ _ _ _ _ _ _ (h k hk').mask (h k hk').maskTail

/-- **The tables read the rows through the form alone**: at every list of messages. -/
theorem tables_within (codes : Codes) (sent : Array OracleNotice) (L L' : Nat → Laid)
    (h : ∀ k, k < sent.size → LaidAgree codes (sent.getD k default).shape (L k) (L' k)) :
    sentTables codes sent L = sentTables codes sent L' := by
  simp only [sentTables, column_within codes sent L L' h]

/-! ## The answers -/

/-- Where every code's message length is a power of two: of a base code in the array. -/
theorem ell_base (codes : Codes) (c : Nat)
    (h : VerifiableInference.Desc.Own.lengthsFit codes = true) (hc : c < codes.base.size) :
    2 ^ (codes.base.getD c default).logEll = (codes.base.getD c default).ell := by
  simp only [VerifiableInference.Desc.Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true] at h
  have := h.1 c hc
  simp only [VerifiableInference.Desc.Own.twoPower, Bool.and_eq_true, beq_iff_eq] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc]
  exact this.2

/-- The like of a mask code in the array. -/
theorem ell_mask (codes : Codes) (c : Nat)
    (h : VerifiableInference.Desc.Own.lengthsFit codes = true) (hc : c < codes.mask.size) :
    2 ^ (codes.mask.getD c default).logEll = (codes.mask.getD c default).ell := by
  simp only [VerifiableInference.Desc.Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true] at h
  have := h.2 c hc
  simp only [VerifiableInference.Desc.Own.twoPower, Bool.and_eq_true, beq_iff_eq] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc]
  exact this.2

/-- **The two tables by index, below their sizes.** -/
theorem words_within (codes : Codes) (sent : Array OracleNotice) (L L' : Nat → Laid)
    (h : ∀ k, k < sent.size → LaidAgree codes (sent.getD k default).shape (L k) (L' k))
    (hlen : VerifiableInference.Desc.Own.lengthsFit codes = true)
    (hsh : ∀ k, k < sent.size →
      VerifiableInference.Desc.Own.sentShapeFits codes (sent.getD k default).shape = true)
    (k : Nat) (hk : k < sent.size) (part : OnBytes.Part) (i : Nat)
    (hi : i < (K1.Msg.of codes (sent.getD k default).shape).size part) :
    wordsOf sent L k part i = wordsOf sent L' k part i := by
  have hs0 := hsh k hk
  simp only [VerifiableInference.Desc.Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hs0
  cases part with
  | main =>
    show (if i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows <
          (sent.getD k default).shape.mainRows then
        (L k).main (i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows)
          (i / 2 ^ ceilLog2 (sent.getD k default).shape.mainRows) else zeroE) =
      (if i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows <
          (sent.getD k default).shape.mainRows then
        (L' k).main (i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows)
          (i / 2 ^ ceilLog2 (sent.getD k default).shape.mainRows) else zeroE)
    by_cases hr : i % 2 ^ ceilLog2 (sent.getD k default).shape.mainRows <
        (sent.getD k default).shape.mainRows
    · rw [if_pos hr, if_pos hr]
      have hne : (sent.getD k default).shape.mainRows ≠ 0 := by omega
      have hc : (sent.getD k default).shape.code < codes.base.size := by
        rcases hs0.1.1.2 with e | e
        · exact absurd e hne
        · exact e
      have h2 := ell_base codes (sent.getD k default).shape.code hlen hc
      have hK : ((sent.getD k default).shape.mainRows != 0) = true := bne_iff_ne.2 hne
      have hK' : ((sent.getD k default).shape.mainRows == 0) = false := beq_eq_false_iff_ne.2 hne
      have hs : (K1.Msg.of codes (sent.getD k default).shape).size .main =
          2 ^ ceilLog2 (sent.getD k default).shape.mainRows *
            2 ^ (codes.base.getD (sent.getD k default).shape.code default).logEll := by
        rw [← Nat.pow_add]
        show (if ((sent.getD k default).shape.mainRows != 0) = true then
          2 ^ (if ((sent.getD k default).shape.mainRows == 0) = true then 0 else
            ceilLog2 (sent.getD k default).shape.mainRows +
              (codes.base.getD (sent.getD k default).shape.code default).logEll) else 0) = _
        rw [if_pos hK, hK', if_neg Bool.false_ne_true]
      rw [hs, h2] at hi
      exact (h k hk).main _ hr _ (Nat.div_lt_of_lt_mul hi)
    · rw [if_neg hr, if_neg hr]
  | mask =>
    show (if i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows <
          (sent.getD k default).shape.maskRows then
        (L k).mask (i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows)
          (i / 2 ^ ceilLog2 (sent.getD k default).shape.maskRows) else zeroE) =
      (if i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows <
          (sent.getD k default).shape.maskRows then
        (L' k).mask (i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows)
          (i / 2 ^ ceilLog2 (sent.getD k default).shape.maskRows) else zeroE)
    by_cases hr : i % 2 ^ ceilLog2 (sent.getD k default).shape.maskRows <
        (sent.getD k default).shape.maskRows
    · rw [if_pos hr, if_pos hr]
      have hne : (sent.getD k default).shape.maskRows ≠ 0 := by omega
      have hc : (sent.getD k default).shape.maskCode < codes.mask.size := by
        rcases hs0.1.2 with e | e
        · exact absurd e hne
        · exact e
      have h2 := ell_mask codes (sent.getD k default).shape.maskCode hlen hc
      have hK : ((sent.getD k default).shape.maskRows != 0) = true := bne_iff_ne.2 hne
      have hK' : ((sent.getD k default).shape.maskRows == 0) = false := beq_eq_false_iff_ne.2 hne
      have hs : (K1.Msg.of codes (sent.getD k default).shape).size .mask =
          2 ^ ceilLog2 (sent.getD k default).shape.maskRows *
            2 ^ (codes.mask.getD (sent.getD k default).shape.maskCode default).logEll := by
        rw [← Nat.pow_add]
        show (if ((sent.getD k default).shape.maskRows != 0) = true then
          2 ^ (if ((sent.getD k default).shape.maskRows == 0) = true then 0 else
            ceilLog2 (sent.getD k default).shape.maskRows +
              (codes.mask.getD (sent.getD k default).shape.maskCode default).logEll) else 0) = _
        rw [if_pos hK, hK', if_neg Bool.false_ne_true]
      rw [hs, h2] at hi
      exact (h k hk).mask _ hr _ (Nat.div_lt_of_lt_mul hi)
    · rw [if_neg hr, if_neg hr]

/-- What a row sums to, computed, hangs on the words below the statement's tables' sizes alone. -/
theorem value_within (S : Statement) (r : OnBytes.Row) (m m' : Words E)
    (h : ∀ o, o < S.oracles.size → ∀ part i, i < OnBytes.Means.tableSize S o part →
      m o part i = m' o part i) :
    Desc.K14.Law.valueE S r m = Desc.K14.Law.valueE S r m' := by
  unfold Desc.K14.Law.valueE Desc.K14.Law.onTableE
  refine Desc.K14.Law.sumE_congr _ _ _ fun o ho => ?_
  have e1 : Desc.K14.Law.sumE (OnBytes.Means.tableSize S o .main)
        (fun i => OnBytes.mulE (r.coefficient o .main i) (m o .main i)) =
      Desc.K14.Law.sumE (OnBytes.Means.tableSize S o .main)
        (fun i => OnBytes.mulE (r.coefficient o .main i) (m' o .main i)) :=
    Desc.K14.Law.sumE_congr _ _ _ fun i hi => by
      show OnBytes.mulE _ (m o .main i) = OnBytes.mulE _ (m' o .main i)
      rw [h o ho .main i hi]
  have e2 : Desc.K14.Law.sumE (OnBytes.Means.tableSize S o .mask)
        (fun i => OnBytes.mulE (r.coefficient o .mask i) (m o .mask i)) =
      Desc.K14.Law.sumE (OnBytes.Means.tableSize S o .mask)
        (fun i => OnBytes.mulE (r.coefficient o .mask i) (m' o .mask i)) :=
    Desc.K14.Law.sumE_congr _ _ _ fun i hi => by
      show OnBytes.mulE _ (m o .mask i) = OnBytes.mulE _ (m' o .mask i)
      rw [h o ho .mask i hi]
  show OnBytes.addE _ _ = OnBytes.addE _ _
  rw [e1, e2]

/-- The part's own small statement has message number k's shape at the number k. -/
theorem local_shape (codes : Codes) (sent : Array OracleNotice) (k : Nat) (hk : k < sent.size) :
    (localOf codes sent).oracles[k]? = some { shape := (sent.getD k default).shape } := by
  show (sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[k]? = _
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hk, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hk]
  rfl

/-- **The answers read the rows through the form alone**, where the shapes fit. -/
theorem answers_within (J : SendJob) (hfit : sendShapeFits J = true) (L L' : Nat → Laid)
    (h : ∀ k, k < J.Q.sent.size →
      LaidAgree J.Q.codes (J.Q.sent.getD k default).shape (L k) (L' k))
    (seeds : List (List E × E)) : answersOf J.Q L seeds = answersOf J.Q L' seeds := by
  have hlen : VerifiableInference.Desc.Own.lengthsFit J.Q.codes = true := by
    unfold sendShapeFits at hfit
    simp only [Bool.and_eq_true] at hfit
    exact hfit.1.1
  have hsh : ∀ k, k < J.Q.sent.size → VerifiableInference.Desc.Own.sentShapeFits J.Q.codes
      (J.Q.sent.getD k default).shape = true := fun k hk => by
    have hm := msgFits_at J hfit k hk
    cases hs : J.sort k with
    | plain high =>
      rw [hs] at hm
      simp only [msgShapeFits, Bool.and_eq_true] at hm
      exact hm.1.1
    | fresh k' h' =>
      rw [hs] at hm
      simp only [msgShapeFits, Bool.and_eq_true] at hm
      exact hm.1.1.1.1.1.1
  have hv : ∀ r : OnBytes.Row, Desc.K14.Law.valueE (localOf J.Q.codes J.Q.sent) r
      (wordsOf J.Q.sent L) = Desc.K14.Law.valueE (localOf J.Q.codes J.Q.sent) r
      (wordsOf J.Q.sent L') := fun r => by
    refine value_within _ r _ _ fun o ho part i hi => ?_
    have ho' : o < J.Q.sent.size := by
      have e : (localOf J.Q.codes J.Q.sent).oracles.size = J.Q.sent.size := Array.size_map ..
      omega
    rw [VerifiableInference.Desc.K1.tableSize_eq _ o _ (local_shape _ _ o ho') part] at hi
    exact words_within _ _ L L' h hlen hsh o ho' part i hi
  simp only [answersOf, hv]

/-! ## Both in one -/

/-- **THE TABLES AND THE ANSWERS ARE ONE AT ANY FILLERS**: at the part's own reading of an array of
just its count of coins, and with d n, any function of the number, in the place of the 0 that stands
in for the coin number n beyond the array. -/
theorem sent_within (J : SendJob) (hfit : sendShapeFits J = true) (t : State Ask Unit)
    (cs : Array E) (hsz : cs.size = (sendingPart J).takes.e) (d : Nat → E)
    (seeds : List (List E × E)) :
    sentTables J.Q.codes J.Q.sent (J.rows t cs) =
        sentTables J.Q.codes J.Q.sent (rowsFilled J t cs d) ∧
      answersOf J.Q (J.rows t cs) seeds = answersOf J.Q (rowsFilled J t cs d) seeds :=
  ⟨tables_within _ _ _ _ fun k hk => rows_within J hfit t cs hsz d k hk,
    answers_within J hfit _ _ (fun k hk => rows_within J hfit t cs hsz d k hk) seeds⟩

/-- The array that the part's moves make of the coins that they are handed has just the part's
count. -/
theorem coins_size {d : Due} (c : Cs d) : (coinsE c).toArray.size = d.e := by
  unfold coinsE
  simp

/-- **The same at the array that is made of the coins of the part's count**: no premise on its
size. -/
theorem sent_within_coins (J : SendJob) (hfit : sendShapeFits J = true) (t : State Ask Unit)
    (c : Cs (sendingPart J).takes) (d : Nat → E) (seeds : List (List E × E)) :
    sentTables J.Q.codes J.Q.sent (J.rows t (coinsE c).toArray) =
        sentTables J.Q.codes J.Q.sent (rowsFilled J t (coinsE c).toArray d) ∧
      answersOf J.Q (J.rows t (coinsE c).toArray) seeds =
        answersOf J.Q (rowsFilled J t (coinsE c).toArray d) seeds :=
  sent_within J hfit t _ (coins_size c) d seeds

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.cell_below
#print axioms ProofFile.Honest.K14.freshRow_reads
#print axioms ProofFile.Honest.K14.laid_within
#print axioms ProofFile.Honest.K14.offset_step
#print axioms ProofFile.Honest.K14.offset_le
#print axioms ProofFile.Honest.K14.due_in_count
#print axioms ProofFile.Honest.K14.msgFits_at
#print axioms ProofFile.Honest.K14.rows_filled_zero
#print axioms ProofFile.Honest.K14.rows_within
#print axioms ProofFile.Honest.K14.symbols_within
#print axioms ProofFile.Honest.K14.column_within
#print axioms ProofFile.Honest.K14.tables_within
#print axioms ProofFile.Honest.K14.ell_base
#print axioms ProofFile.Honest.K14.ell_mask
#print axioms ProofFile.Honest.K14.words_within
#print axioms ProofFile.Honest.K14.value_within
#print axioms ProofFile.Honest.K14.local_shape
#print axioms ProofFile.Honest.K14.answers_within
#print axioms ProofFile.Honest.K14.sent_within
#print axioms ProofFile.Honest.K14.coins_size
#print axioms ProofFile.Honest.K14.sent_within_coins
