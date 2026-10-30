-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/SendingsReach.lean: AT A MESSAGE WHOSE SHAPE FITS (msgShapeFits,
Honest/K14/SendingsShapes.lean): WHICH PLACES OF THE MESSAGE's ROWS IN FULL (laid,
Honest/K14/Sendings.lean) A COIN's NUMBER REACHES: TWO REAL PLACES SHARE NO COIN, BUT FOR ONE CASE:
ONE PLACE's NUMBER IN TWO ROWS OF A FOLD's FRESH TABLE; SO A MASK ROW's COIN REACHES NO TAIL AND NO
SECOND PLACE OF ITS ROW; and, at a sending whose shapes fit (sendShapeFits), two messages share no
coin. A form, four definitions with code, and statements with their proofs. General in the coins: an
equation or a congruence at each value: no distribution occurs.

A PLACE IS A PLACE OF THE ROWS IN FULL: of what the encoder is handed (RowSpot; real: a real row, a
place below the code's message length, a tail's place below the code's tail). NOT A PLACE OF A
COLUMN: what is sent are columns of the rows' codewords and the answers: there a coin of a row may
reach every symbol of that row.

  RowSpot, Laid.atSpot, RowSpot.isReal, isReal_agree   the places; agreement at every real place is
                  LaidAgree; tables_of_real, answers_of_real: so the tables, and where the shapes
                  fit the answers, read the rows at their real places alone
  spotCoins       **the numbers, among the message's own coins, of the coins that a place is made
                  of**: a further text of laid's arithmetic, tied to laid by the statements below
  "AT MOST THESE" (three statements):
  fresh_mask_reads, spot_reads   a place reads the coins of its list alone: at every shape
  one_coin_turns  **change one coin of the part, at one state: two real places that turn lie in one
                  message and are one place, or one place's number in two rows of a fresh table**
  "JUST THESE" (nine statements; the first eight at every shape):
  spot_coin, fresh_tail_coin   **a place whose list is one number IS that coin**, at the program's
                  own element: every tail that has a coin, the pad, a plain message's mask entries,
                  a fresh table's entries of one coin
  row_plan, fresh_mask_eq   an entry of a fresh table is the program's own sum of the coins of the
                  plan's list: at the program's own elements: nothing is lost
  fresh_mask_sum, spot_sum   **a place, read in the field, is the sum of the coins of its list**,
                  each as often as its number stands in the list: at every place but the vector's.
                  EACH WITH THE COEFFICIENT 1 WHERE THE SHAPE FITS: with spot_once
  spot_vector, spot_zero   a plain main place with the empty list is the vector's entry; **a place
                  of a fresh table with the empty list holds 0**: which places these are no theorem
                  of this file says
  spot_all        where the shape fits: every coin below the message's count stands at a real place
  ON THE LISTS, where the shape fits:
  spot_below, spot_once   within the count; no list has a number twice
  spot_share, spot_apart   **the statement of the first sentence**
  mask_no_tail, mask_one_place   **a mask row's coin reaches no tail; and no second place of its
                  row**. mask_no_tail's half on main rows' tails is empty: where the shape fits, a
                  message with a mask row has no main row
  messages_apart  two messages of a sending share no coin
  The others: small steps.

THE PACKING's OWN WAY AT A FRESH TABLE (Honest/K14/SendingsPlan.lean: plan_rows_low,
plan_rows_high): a coin stands in several rows, always at one place's number; the place 0 of a row
is a sum of up to h + 1 coins; AND REAL PLACES ARE MADE OF NO COIN: where h ≤ k the places 1 to h of
a row that does not reach the variable, and every place from 2 k - h + 1 up to the mask code's
message length, have the empty list (by plan's text and plan_places: no theorem here joins them),
and a
place with the empty list holds 0 (spot_zero). BARRED WHERE THE SHAPE FITS: a coin twice in one
place; at two places of one row; in a mask row and in a tail; in two tails; in two messages; at a
plain message: at any two places.
What is spent of the test on a message's shape (the clauses' numbers are those of
Honest/K14/SendingsShapes.lean's head): of (4): h ≤ k, for all that bars; maskRows = 2 ^ h and that
the packing's places lie inside the message length, for spot_all alone; of (3): its two arms and
that the answers are no more than the message length, for spot_all alone. 1 ≤ k is not spent. At a
plain message spot_share's proof spends nothing of the test. Of the test on a sending's shapes:
one_coin_turns takes it for the messages' tests alone; answers_of_real hands it to answers_within,
which spends (5) and (1).
Kin. plan, ixOf, sumAt (Johnson/SendSim/At/RideLay.lean), K1.mul_add_inj (the frame's folder
Honest/K1/) and cell_below, offset_step, offset_le, msgFits_at (Honest/K14/SendingsWithin.lean) are
called. There are small shapes that fail h ≤ k, at which one coin stands in a mask row and in a
tail, and at two places of one row: shown neither in this file nor in any file that it imports.
What is not claimed. WHAT FOLLOWS FROM ANY OF THIS. That the book lends by these numbers, or that a
spender's run is these coefficients. The sending part's own rows alone: where else a run reads the
same coins is not counted. one_coin_turns holds one state on both sides of the change: one input and
the same challenges heard. Nothing on columns, answers, roots or paths beyond tables_of_real and
answers_of_real. The vector's entries read no coin of the part: what they hold is a free letter
here. Nothing on how coins are sampled. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlan
import Johnson.Desc.ProofFile.Honest.K14.SendingsWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.SendSim.At (ixOf plan firstPlan sumAt)
open Fmt.M1.FoldOwn (reaches freshRow)
open OnBytes (E zeroE Codes OracleShape)
open OnBytes.Slice (readE readE_ofTriple toE toE_addE toE_zeroE)

/-- The program's sum of the elements g n at a list of numbers, from the first on; 0 at no
number. -/
def sumG (g : ℕ → Fmt.Ext3) : List ℕ → Fmt.Ext3
  | [] => Fmt.Fld.zeroE
  | n :: I => I.foldl (fun s m => Fmt.Fld.two.addE s (g m)) (g n)

/-- A fold that takes f i in at the members i that pass p: the fold over the passing members'
values. -/
theorem foldl_filter_map {α β : Type} (p : ℕ → Bool) (f : ℕ → β) (F : α → β → α) :
    ∀ (L : List ℕ) (s : α), L.foldl (fun s i => if p i then F s (f i) else s) s =
      ((L.filter p).map f).foldl F s
  | [], _ => rfl
  | i :: L, s => by
    rw [List.foldl_cons, foldl_filter_map p f F L]
    by_cases h : p i = true
    · simp [h]
    · simp [h]

/-- **The format's model prover's row at coefficients that are read off g by ixOf: the plan's
sums**, at the program's own elements. (Kin: row_eq, Johnson/SendSim/At/RideLay.lean: the like read
in the field, at coefficients made of the field's elements.) -/
theorem row_plan (k h b : ℕ) (g : ℕ → Fmt.Ext3) :
    freshRow .two k h ⟨fun l t => g (ixOf k l t), g (2 * (k - 1))⟩ b =
      (plan k h b).map (sumG g) := by
  unfold freshRow plan
  rw [List.map_append, List.map_cons, List.map_map, firstPlan_list]
  refine congrArg₂ (· ++ ·) (congrArg₂ List.cons ?_ ?_) ?_
  · show _ = (((List.range h).filter fun i => reaches h b (i + 1)).map
      fun i => ixOf k (i + 1) 1).foldl (fun s m => Fmt.Fld.two.addE s (g m))
        (g (if h < k then ixOf k (h + 1) 1 else 2 * (k - 1)))
    rw [foldl_filter_map (fun i => reaches h b (i + 1)) (fun i => g (ixOf k (i + 1) 1))
      (fun s x => Fmt.Fld.two.addE s x), List.foldl_map, List.foldl_map, apply_ite g]
  · refine List.map_congr_left fun i _ => ?_
    show (if _ then _ else _) = sumG g (if _ then _ else _)
    by_cases hr : reaches h b (i + 1) = true
    · rw [if_pos hr, if_pos hr]
      rfl
    · rw [if_neg hr, if_neg hr]
      rfl
  · by_cases hk : h < k
    · rw [if_pos hk, if_pos hk]
      simp only [List.map_cons, List.map_append, List.map_flatMap, List.map_nil, sumG,
        List.foldl_nil]
    · rw [if_neg hk, if_neg hk]
      rfl

/-- The sum reads g at the list's members alone. -/
theorem sumG_congr {g g' : ℕ → Fmt.Ext3} : ∀ {I : List ℕ}, (∀ n ∈ I, g n = g' n) →
    sumG g I = sumG g' I
  | [], _ => rfl
  | n :: I, h => by
    show I.foldl (fun s m => Fmt.Fld.two.addE s (g m)) (g n) =
      I.foldl (fun s m => Fmt.Fld.two.addE s (g' m)) (g' n)
    rw [h n List.mem_cons_self]
    have aux : ∀ (J : List ℕ) (s : Fmt.Ext3), (∀ m ∈ J, g m = g' m) →
        J.foldl (fun s m => Fmt.Fld.two.addE s (g m)) s =
          J.foldl (fun s m => Fmt.Fld.two.addE s (g' m)) s := by
      intro J
      induction J with
      | nil => intro _ _; rfl
      | cons m J ih =>
        intro s hJ
        rw [List.foldl_cons, List.foldl_cons, hJ m List.mem_cons_self]
        exact ih _ fun x hx => hJ x (List.mem_cons_of_mem _ hx)
    exact aux I _ fun m hm => h m (List.mem_cons_of_mem _ hm)

/-- The sum, read in the field: the field's sum of the elements, read. -/
theorem toE_sumG (g : ℕ → Fmt.Ext3) : ∀ I : List ℕ, toE (sumG g I) = sumAt (fun n => toE (g n)) I
  | [] => toE_zeroE
  | n :: I => by
    have aux : ∀ (J : List ℕ) (s : Fmt.Ext3),
        toE (J.foldl (fun s m => Fmt.Fld.two.addE s (g m)) s) =
          toE s + sumAt (fun n => toE (g n)) J := by
      intro J
      induction J with
      | nil => intro s; simp [sumAt]
      | cons m J ih =>
        intro s
        rw [List.foldl_cons, ih, toE_addE]
        simp [sumAt, add_assoc]
    show toE (I.foldl _ (g n)) = _
    rw [aux]
    simp [sumAt]

/-- K14's fresh table's entry, by the plan. -/
theorem fresh_mask_eq (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (k h r j : ℕ) :
    (laid codes s v cs (.fresh k h)).mask r j =
      E.ofTriple (sumG (fun n => (cs n).triple) ((plan k h r).getD j [])) := by
  show E.ofTriple ((freshRow .two k h
    ⟨fun l t => (fun n => (cs n).triple) (ixOf k l t), (fun n => (cs n).triple) (2 * (k - 1))⟩
      r).getD j Fmt.Fld.zeroE) = _
  rw [row_plan k h r fun n => (cs n).triple, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (plan k h r)[j]? <;> rfl

/-- AT MOST THESE: an entry of a fresh table reads the coins of the plan's list alone. -/
theorem fresh_mask_reads (codes : Codes) (s : OracleShape) (v cs cs' : ℕ → E) (k h r j : ℕ)
    (hc : ∀ n ∈ (plan k h r).getD j [], cs n = cs' n) :
    (laid codes s v cs (.fresh k h)).mask r j = (laid codes s v cs' (.fresh k h)).mask r j := by
  rw [fresh_mask_eq, fresh_mask_eq, sumG_congr fun n hn => by rw [hc n hn]]

/-- **JUST THESE**: an entry of a fresh table, read in the field, is the sum of the coins of the
plan's list, read: each as often as its number stands in the list: once where h ≤ k
(plan_entry_nodup). -/
theorem fresh_mask_sum (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (k h r j : ℕ) :
    readE ((laid codes s v cs (.fresh k h)).mask r j) =
      sumAt (fun n => readE (cs n)) ((plan k h r).getD j []) := by
  rw [fresh_mask_eq, readE_ofTriple, toE_sumG]
  rfl

/-- **A place of a message's rows in full**: of what the encoder is handed: not of a column. -/
inductive RowSpot where
  | main (r j : ℕ)
  | mainTail (r t : ℕ)
  | mask (r j : ℕ)
  | maskTail (r t : ℕ)

/-- What stands at a place. -/
def Laid.atSpot (L : Laid) : RowSpot → E
  | .main r j => L.main r j
  | .mainTail r t => L.mainTail r t
  | .mask r j => L.mask r j
  | .maskTail r t => L.maskTail r t

/-- A real row; a place below the code's message length; a tail's place below the code's tail. -/
def RowSpot.isReal (codes : Codes) (s : OracleShape) : RowSpot → Bool
  | .main r j => decide (r < s.mainRows) && decide (j < (codes.base.getD s.code default).ell)
  | .mainTail r t => decide (r < s.mainRows) && decide (t < (codes.base.getD s.code default).r)
  | .mask r j => decide (r < s.maskRows) && decide (j < (codes.mask.getD s.maskCode default).ell)
  | .maskTail r t => decide (r < s.maskRows) && decide (t < (codes.mask.getD s.maskCode default).r)

/-- The numbers, among the message's own coins, of the coins that a place is made of. -/
def spotCoins (codes : Codes) (s : OracleShape) : MsgSort → RowSpot → List ℕ
  | .plain _, .main r j =>
    if s.maskRows == 0 && r + 1 == s.mainRows &&
        decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
        decide (j < (codes.base.getD s.code default).ell) then
      [s.mainRows * (codes.base.getD s.code default).r +
        (j - ((codes.base.getD s.code default).ell - s.answers))]
    else []
  | .plain _, .mainTail r t => [r * (codes.base.getD s.code default).r + t]
  | .plain _, .mask r j =>
    [s.mainRows * (codes.base.getD s.code default).r +
      (if s.maskRows == 0 then s.answers else 0) + j * s.maskRows + r]
  | .plain _, .maskTail r t =>
    [s.mainRows * (codes.base.getD s.code default).r +
      (if s.maskRows == 0 then s.answers else 0) +
      s.maskRows * (codes.mask.getD s.maskCode default).ell +
      r * (codes.mask.getD s.maskCode default).r + t]
  | .fresh k h, .mask r j => (plan k h r).getD j []
  | .fresh k _, .maskTail r t => [2 * k + 1 + r * (codes.mask.getD s.maskCode default).r + t]
  | .fresh _ _, .main _ _ => []
  | .fresh _ _, .mainTail _ _ => []

/-- **Agreement at every real place is the form LaidAgree** (Honest/K14/SendingsWithin.lean),
through which alone the tables read the rows (tables_within) and, where the shapes fit, the answers
(answers_within). -/
theorem isReal_agree (codes : Codes) (s : OracleShape) (L L' : Laid) :
    (∀ p, RowSpot.isReal codes s p = true → Laid.atSpot L p = Laid.atSpot L' p) ↔
      LaidAgree codes s L L' := by
  constructor
  · intro h
    exact ⟨fun r hr j hj => h (.main r j)
        (Bool.and_eq_true_iff.2 ⟨decide_eq_true hr, decide_eq_true hj⟩),
      fun r hr t ht => h (.mainTail r t)
        (Bool.and_eq_true_iff.2 ⟨decide_eq_true hr, decide_eq_true ht⟩),
      fun r hr j hj => h (.mask r j)
        (Bool.and_eq_true_iff.2 ⟨decide_eq_true hr, decide_eq_true hj⟩),
      fun r hr t ht => h (.maskTail r t)
        (Bool.and_eq_true_iff.2 ⟨decide_eq_true hr, decide_eq_true ht⟩)⟩
  · intro h p hp
    cases p with
    | main r j =>
      simp only [RowSpot.isReal, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact h.main r hp.1 j hp.2
    | mainTail r t =>
      simp only [RowSpot.isReal, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact h.mainTail r hp.1 t hp.2
    | mask r j =>
      simp only [RowSpot.isReal, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact h.mask r hp.1 j hp.2
    | maskTail r t =>
      simp only [RowSpot.isReal, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact h.maskTail r hp.1 t hp.2

/-- **AT MOST THESE**: a place reads, of the message's coins, those of its list alone: at every
shape and every place. -/
theorem spot_reads (codes : Codes) (s : OracleShape) (v cs cs' : ℕ → E) (sort : MsgSort)
    (p : RowSpot) (h : ∀ n ∈ spotCoins codes s sort p, cs n = cs' n) :
    Laid.atSpot (laid codes s v cs sort) p = Laid.atSpot (laid codes s v cs' sort) p := by
  cases sort with
  | fresh k hh =>
    cases p with
    | main r j => rfl
    | mainTail r t => rfl
    | mask r j => exact fresh_mask_reads codes s v cs cs' k hh r j h
    | maskTail r t => exact h _ (List.mem_singleton.2 rfl)
  | plain high =>
    cases p with
    | main r j =>
      show (if _ then cs _ else v _) = (if _ then cs' _ else v _)
      by_cases c : (s.maskRows == 0 && r + 1 == s.mainRows &&
          decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
          decide (j < (codes.base.getD s.code default).ell)) = true
      · rw [if_pos c, if_pos c]
        refine h _ ?_
        show _ ∈ (if _ then _ else _)
        rw [if_pos c]
        exact List.mem_singleton.2 rfl
      · rw [if_neg c, if_neg c]
    | mainTail r t => exact h _ (List.mem_singleton.2 rfl)
    | mask r j => exact h _ (List.mem_singleton.2 rfl)
    | maskTail r t => exact h _ (List.mem_singleton.2 rfl)

/-- A fresh table's row's tail: the place t of the row r is the coin number 2 k + 1 + r z.r + t, z
the mask code. -/
theorem fresh_tail_coin (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (k h r t : ℕ) :
    (laid codes s v cs (.fresh k h)).maskTail r t =
      cs (2 * k + 1 + r * (codes.mask.getD s.maskCode default).r + t) := rfl

/-- **A PLACE WHOSE LIST IS ONE NUMBER IS THAT COIN**, at the program's own element: at every shape:
every tail that has a coin, the pad, a plain message's mask entries, and a fresh table's entries of
one coin. -/
theorem spot_coin (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (sort : MsgSort) (p : RowSpot)
    {n : ℕ} (h : spotCoins codes s sort p = [n]) :
    Laid.atSpot (laid codes s v cs sort) p = cs n := by
  cases sort with
  | fresh k hh =>
    cases p with
    | main r j => cases h
    | mainTail r t => cases h
    | mask r j =>
      show (laid codes s v cs (.fresh k hh)).mask r j = cs n
      rw [fresh_mask_eq, show (plan k hh r).getD j [] = [n] from h]
      exact E.ofTriple_triple _
    | maskTail r t =>
      obtain rfl := List.singleton_inj.1 h
      rfl
  | plain high =>
    cases p with
    | main r j =>
      have h' : (if _ then _ else _) = [n] := h
      show (if _ then cs _ else v _) = cs n
      split_ifs at h' with c
      obtain rfl := List.singleton_inj.1 h'
      rw [if_pos c]
    | mainTail r t =>
      obtain rfl := List.singleton_inj.1 h
      rfl
    | mask r j =>
      obtain rfl := List.singleton_inj.1 h
      rfl
    | maskTail r t =>
      obtain rfl := List.singleton_inj.1 h
      rfl

/-- A plain message's main place whose list is empty is the vector's entry. -/
theorem spot_vector (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (high : Bool) (r j : ℕ)
    (h : spotCoins codes s (.plain high) (.main r j) = []) :
    (laid codes s v cs (.plain high)).main r j =
      v ((OnBytes.vectorLay codes s high).entryAt
        (r + j * 2 ^ (OnBytes.vectorLay codes s high).rowBits)) := by
  have h' : (if _ then _ else _) = ([] : List ℕ) := h
  show (if _ then cs _ else v _) = _
  split_ifs at h' with c
  rw [if_neg c]

/-- **A PLACE OF A FRESH TABLE WHOSE LIST IS EMPTY HOLDS 0.** The main places and their tails have
the empty list by spotCoins' text; where h ≤ k so have, by plan's text and plan_places, the places 1
to h of a row that does not reach the variable and every place from 2 k - h + 1 on: no theorem here
says which. -/
theorem spot_zero (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (k h : ℕ) (p : RowSpot)
    (he : spotCoins codes s (.fresh k h) p = []) :
    Laid.atSpot (laid codes s v cs (.fresh k h)) p = zeroE := by
  cases p with
  | main r j => rfl
  | mainTail r t => rfl
  | mask r j =>
    show (laid codes s v cs (.fresh k h)).mask r j = zeroE
    rw [fresh_mask_eq, show (plan k h r).getD j [] = [] from he]
    rfl
  | maskTail r t => cases he

/-- **JUST THESE, AT EVERY PLACE BUT THE VECTOR's**: a place, read in the field, is the sum of the
coins of its list, read, each as often as its number stands in the list: at every shape; at a plain
message's main place where its list is not empty: the pad. EACH WITH THE COEFFICIENT 1 WHERE THE
SHAPE FITS: cite it with spot_once. Two elements of the program can read as one of the field: each
place also has its equation at the program's own element (spot_coin, fresh_mask_eq, spot_vector,
spot_zero). -/
theorem spot_sum (codes : Codes) (s : OracleShape) (v cs : ℕ → E) (sort : MsgSort) (p : RowSpot)
    (hp : ∀ high r j, sort = .plain high → p = .main r j → spotCoins codes s sort p ≠ []) :
    readE (Laid.atSpot (laid codes s v cs sort) p) =
      sumAt (fun n => readE (cs n)) (spotCoins codes s sort p) := by
  have one : ∀ n, spotCoins codes s sort p = [n] →
      readE (Laid.atSpot (laid codes s v cs sort) p) =
        sumAt (fun n => readE (cs n)) (spotCoins codes s sort p) := fun n h => by
    rw [spot_coin codes s v cs sort p h, h, OnBytes.SendSim.At.sumAt_one]
  cases sort with
  | fresh k h =>
    cases p with
    | main r j => exact toE_zeroE
    | mainTail r t => exact toE_zeroE
    | mask r j => exact fresh_mask_sum codes s v cs k h r j
    | maskTail r t => exact one _ rfl
  | plain high =>
    cases p with
    | main r j =>
      have hne := hp high r j rfl rfl
      by_cases c : (s.maskRows == 0 && r + 1 == s.mainRows &&
          decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
          decide (j < (codes.base.getD s.code default).ell)) = true
      · exact one _ (if_pos c)
      · exact absurd (if_neg c) hne
    | mainTail r t => exact one _ rfl
    | mask r j => exact one _ rfl
    | maskTail r t => exact one _ rfl

/-- The tables read the rows at their real places alone. -/
theorem tables_of_real (codes : Codes) (sent : Array OnBytes.OracleNotice) (L L' : ℕ → Laid)
    (h : ∀ k, k < sent.size → ∀ p, RowSpot.isReal codes (sent.getD k default).shape p = true →
      Laid.atSpot (L k) p = Laid.atSpot (L' k) p) :
    sentTables codes sent L = sentTables codes sent L' :=
  tables_within codes sent L L' fun k hk => (isReal_agree _ _ _ _).1 (h k hk)

/-- So do the answers, where the sending's shapes fit. -/
theorem answers_of_real (J : SendJob) (hfit : sendShapeFits J = true) (L L' : ℕ → Laid)
    (h : ∀ k, k < J.Q.sent.size →
      ∀ p, RowSpot.isReal J.Q.codes (J.Q.sent.getD k default).shape p = true →
        Laid.atSpot (L k) p = Laid.atSpot (L' k) p) (seeds : List (List E × E)) :
    answersOf J.Q L seeds = answersOf J.Q L' seeds :=
  answers_within J hfit L L' (fun k hk => (isReal_agree _ _ _ _).1 (h k hk)) seeds

/-- A real place of a main row. -/
theorem isReal_main {codes : Codes} {s : OracleShape} {r j : ℕ}
    (h : RowSpot.isReal codes s (.main r j) = true) :
    r < s.mainRows ∧ j < (codes.base.getD s.code default).ell := by
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨of_decide_eq_true a, of_decide_eq_true b⟩

/-- A real place of a main row's tail. -/
theorem isReal_mainTail {codes : Codes} {s : OracleShape} {r t : ℕ}
    (h : RowSpot.isReal codes s (.mainTail r t) = true) :
    r < s.mainRows ∧ t < (codes.base.getD s.code default).r := by
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨of_decide_eq_true a, of_decide_eq_true b⟩

/-- A real place of a mask row. -/
theorem isReal_mask {codes : Codes} {s : OracleShape} {r j : ℕ}
    (h : RowSpot.isReal codes s (.mask r j) = true) :
    r < s.maskRows ∧ j < (codes.mask.getD s.maskCode default).ell := by
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨of_decide_eq_true a, of_decide_eq_true b⟩

/-- A real place of a mask row's tail. -/
theorem isReal_maskTail {codes : Codes} {s : OracleShape} {r t : ℕ}
    (h : RowSpot.isReal codes s (.maskTail r t) = true) :
    r < s.maskRows ∧ t < (codes.mask.getD s.maskCode default).r := by
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨of_decide_eq_true a, of_decide_eq_true b⟩

/-- What the test on a fresh table's shape gives. -/
theorem freshShape_fits {codes : Codes} {s : OracleShape} {k h : ℕ}
    (hf : msgShapeFits codes s (.fresh k h) = true) :
    s.maskRows = 2 ^ h ∧ h ≤ k ∧ 2 * k - h + 1 ≤ (codes.mask.getD s.maskCode default).ell := by
  unfold msgShapeFits at hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  exact ⟨hf.1.1.1.2, hf.1.1.2, hf.2⟩

/-- The pad's condition, out of the Bool. -/
theorem pad_cond {codes : Codes} {s : OracleShape} {r j : ℕ}
    (c : (s.maskRows == 0 && r + 1 == s.mainRows &&
      decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
      decide (j < (codes.base.getD s.code default).ell)) = true) :
    s.maskRows = 0 ∧ r + 1 = s.mainRows ∧ (codes.base.getD s.code default).ell - s.answers ≤ j ∧
      j < (codes.base.getD s.code default).ell := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  exact ⟨c.1.1.1, c.1.1.2, c.1.2, c.2⟩

/-- A member of an entry is a member of the entries laid in a row. -/
theorem getD_mem_flatten {L : List (List ℕ)} {j n : ℕ} (h : n ∈ L.getD j []) : n ∈ L.flatten := by
  rw [List.getD_eq_getElem?_getD] at h
  cases e : L[j]? with
  | none => rw [e] at h; cases h
  | some I =>
    rw [e] at h
    exact List.mem_flatten.2 ⟨I, List.mem_of_getElem? e, h⟩

/-- Within the message's count. (Kin: laid_within, Honest/K14/SendingsWithin.lean: the same bound as
a congruence.) -/
theorem spot_below {codes : Codes} {s : OracleShape} {sort : MsgSort} {p : RowSpot}
    (hfit : msgShapeFits codes s sort = true) (hp : RowSpot.isReal codes s p = true) :
    ∀ n ∈ spotCoins codes s sort p, n < dueOf codes s sort := by
  intro n hn
  cases sort with
  | fresh k h =>
    obtain ⟨-, hh, -⟩ := freshShape_fits hfit
    cases p with
    | main r j => cases hn
    | mainTail r t => cases hn
    | mask r j =>
      have := plan_below hh n (getD_mem_flatten (show n ∈ (plan k h r).getD j [] from hn))
      show n < 2 * k + 1 + _
      omega
    | maskTail r t =>
      obtain rfl := List.mem_singleton.1 hn
      obtain ⟨a, b⟩ := isReal_maskTail hp
      have := cell_below a b
      show _ < 2 * k + 1 + s.maskRows * (codes.mask.getD s.maskCode default).r
      omega
  | plain high =>
    show n < s.mainRows * (codes.base.getD s.code default).r +
      (if s.maskRows == 0 then s.answers else 0) +
      s.maskRows * (codes.mask.getD s.maskCode default).ell +
      s.maskRows * (codes.mask.getD s.maskCode default).r
    cases p with
    | main r j =>
      have hn' : n ∈ (if _ then _ else _) := hn
      split_ifs at hn' with c
      · obtain rfl := List.mem_singleton.1 hn'
        obtain ⟨c1, -, c3, c4⟩ := pad_cond c
        rw [if_pos (by rw [c1]; rfl)]
        omega
      · cases hn'
    | mainTail r t =>
      obtain rfl := List.mem_singleton.1 hn
      obtain ⟨a, b⟩ := isReal_mainTail hp
      have := cell_below a b
      omega
    | mask r j =>
      obtain rfl := List.mem_singleton.1 hn
      obtain ⟨a, b⟩ := isReal_mask hp
      have := cell_below b a
      rw [Nat.mul_comm s.maskRows (codes.mask.getD s.maskCode default).ell]
      omega
    | maskTail r t =>
      obtain rfl := List.mem_singleton.1 hn
      obtain ⟨a, b⟩ := isReal_maskTail hp
      have := cell_below a b
      omega

/-- Once in a place: no list has a number twice. -/
theorem spot_once {codes : Codes} {s : OracleShape} {sort : MsgSort} (p : RowSpot)
    (hfit : msgShapeFits codes s sort = true) : (spotCoins codes s sort p).Nodup := by
  cases sort with
  | fresh k h =>
    obtain ⟨-, hh, -⟩ := freshShape_fits hfit
    cases p with
    | main r j => exact List.nodup_nil
    | mainTail r t => exact List.nodup_nil
    | mask r j =>
      show ((plan k h r).getD j []).Nodup
      rw [List.getD_eq_getElem?_getD]
      cases e : (plan k h r)[j]? with
      | none => exact List.nodup_nil
      | some I => exact plan_entry_nodup hh I (List.mem_of_getElem? e)
    | maskTail r t => exact List.nodup_singleton _
  | plain high =>
    cases p with
    | main r j =>
      show (if _ then _ else _ : List ℕ).Nodup
      split_ifs
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    | mainTail r t => exact List.nodup_singleton _
    | mask r j => exact List.nodup_singleton _
    | maskTail r t => exact List.nodup_singleton _

/-- What a number at a pad's place is. -/
theorem padSpot_mem {codes : Codes} {s : OracleShape} {high : Bool} {r j n : ℕ}
    (hn : n ∈ spotCoins codes s (.plain high) (.main r j)) :
    s.maskRows = 0 ∧ r + 1 = s.mainRows ∧ (codes.base.getD s.code default).ell - s.answers ≤ j ∧
      j < (codes.base.getD s.code default).ell ∧
      n = s.mainRows * (codes.base.getD s.code default).r +
        (j - ((codes.base.getD s.code default).ell - s.answers)) := by
  have hn' : n ∈ (if _ then _ else _) := hn
  split_ifs at hn' with c
  · obtain ⟨c1, c2, c3, c4⟩ := pad_cond c
    exact ⟨c1, c2, c3, c4, List.mem_singleton.1 hn'⟩
  · cases hn'

/-- Two real places of one message that share a coin are one place, or one place's number in two
rows of a fresh table: spot_apart in its positive form. -/
theorem spot_share {codes : Codes} {s : OracleShape} {sort : MsgSort} {p q : RowSpot} {n : ℕ}
    (hfit : msgShapeFits codes s sort = true) (hp : RowSpot.isReal codes s p = true)
    (hq : RowSpot.isReal codes s q = true) (hn : n ∈ spotCoins codes s sort p)
    (hn' : n ∈ spotCoins codes s sort q) :
    p = q ∨ ∃ k h r r' j, sort = .fresh k h ∧ p = .mask r j ∧ q = .mask r' j := by
  cases sort with
  | fresh k h =>
    obtain ⟨-, hh, -⟩ := freshShape_fits hfit
    cases p with
    | main r j => cases hn
    | mainTail r t => cases hn
    | mask r j =>
      cases q with
      | main r' j' => cases hn'
      | mainTail r' t' => cases hn'
      | mask r' j' =>
        obtain rfl := plan_one_place hh (show n ∈ (plan k h r).getD j [] from hn)
          (show n ∈ (plan k h r').getD j' [] from hn')
        exact .inr ⟨k, h, r, r', j, rfl, rfl, rfl⟩
      | maskTail r' t' =>
        have a := plan_below hh n (getD_mem_flatten (show n ∈ (plan k h r).getD j [] from hn))
        have b := List.mem_singleton.1 hn'
        omega
    | maskTail r t =>
      cases q with
      | main r' j' => cases hn'
      | mainTail r' t' => cases hn'
      | mask r' j' =>
        have a := plan_below hh n (getD_mem_flatten (show n ∈ (plan k h r').getD j' [] from hn'))
        have b := List.mem_singleton.1 hn
        omega
      | maskTail r' t' =>
        have a := List.mem_singleton.1 hn
        have b := List.mem_singleton.1 hn'
        obtain ⟨e1, e2⟩ := K1.mul_add_inj _ _ _ _ _ (isReal_maskTail hp).2 (isReal_maskTail hq).2
          (show r * (codes.mask.getD s.maskCode default).r + t =
            r' * (codes.mask.getD s.maskCode default).r + t' by omega)
        subst e1 e2
        exact .inl rfl
  | plain high =>
    left
    have hM : s.maskRows * (codes.mask.getD s.maskCode default).ell =
        (codes.mask.getD s.maskCode default).ell * s.maskRows := Nat.mul_comm _ _
    cases p with
    | main r j =>
      obtain ⟨c1, c2, c3, c4, e⟩ := padSpot_mem hn
      have hP : (if s.maskRows == 0 then s.answers else 0) = s.answers := by rw [c1]; rfl
      cases q with
      | main r' j' =>
        obtain ⟨-, d2, d3, d4, e'⟩ := padSpot_mem hn'
        obtain rfl : r = r' := by omega
        obtain rfl : j = j' := by omega
        rfl
      | mainTail r' t' =>
        have b := List.mem_singleton.1 hn'
        have := cell_below (isReal_mainTail hq).1 (isReal_mainTail hq).2
        omega
      | mask r' j' =>
        have := (isReal_mask hq).1
        omega
      | maskTail r' t' =>
        have := (isReal_maskTail hq).1
        omega
    | mainTail r t =>
      have a := List.mem_singleton.1 hn
      have ha := cell_below (isReal_mainTail hp).1 (isReal_mainTail hp).2
      cases q with
      | main r' j' =>
        obtain ⟨-, -, -, -, e'⟩ := padSpot_mem hn'
        omega
      | mainTail r' t' =>
        have b := List.mem_singleton.1 hn'
        obtain ⟨e1, e2⟩ := K1.mul_add_inj _ _ _ _ _ (isReal_mainTail hp).2 (isReal_mainTail hq).2
          (show r * (codes.base.getD s.code default).r + t =
            r' * (codes.base.getD s.code default).r + t' by omega)
        subst e1 e2
        rfl
      | mask r' j' =>
        have b := List.mem_singleton.1 hn'
        omega
      | maskTail r' t' =>
        have b := List.mem_singleton.1 hn'
        omega
    | mask r j =>
      have a := List.mem_singleton.1 hn
      have ha := cell_below (isReal_mask hp).2 (isReal_mask hp).1
      cases q with
      | main r' j' =>
        obtain ⟨d1, -, -, -, -⟩ := padSpot_mem hn'
        have := (isReal_mask hp).1
        omega
      | mainTail r' t' =>
        have b := List.mem_singleton.1 hn'
        have := cell_below (isReal_mainTail hq).1 (isReal_mainTail hq).2
        omega
      | mask r' j' =>
        have b := List.mem_singleton.1 hn'
        obtain ⟨e1, e2⟩ := K1.mul_add_inj _ _ _ _ _ (isReal_mask hp).1 (isReal_mask hq).1
          (show j * s.maskRows + r = j' * s.maskRows + r' by omega)
        subst e1 e2
        rfl
      | maskTail r' t' =>
        have b := List.mem_singleton.1 hn'
        omega
    | maskTail r t =>
      have a := List.mem_singleton.1 hn
      cases q with
      | main r' j' =>
        obtain ⟨d1, -, -, -, -⟩ := padSpot_mem hn'
        have := (isReal_maskTail hp).1
        omega
      | mainTail r' t' =>
        have b := List.mem_singleton.1 hn'
        have := cell_below (isReal_mainTail hq).1 (isReal_mainTail hq).2
        omega
      | mask r' j' =>
        have b := List.mem_singleton.1 hn'
        have := cell_below (isReal_mask hq).2 (isReal_mask hq).1
        omega
      | maskTail r' t' =>
        have b := List.mem_singleton.1 hn'
        obtain ⟨e1, e2⟩ := K1.mul_add_inj _ _ _ _ _ (isReal_maskTail hp).2 (isReal_maskTail hq).2
          (show r * (codes.mask.getD s.maskCode default).r + t =
            r' * (codes.mask.getD s.maskCode default).r + t' by omega)
        subst e1 e2
        rfl

/-- **TWO REAL PLACES OF ONE MESSAGE SHARE NO COIN, BUT FOR ONE CASE: ONE PLACE's NUMBER IN TWO ROWS
OF A FRESH TABLE.** The rows of a fresh table share their entries' coins BY DESIGN: 2 k + 1 coins in
all, not 2 ^ h rows' worth; no row's entries are independent of another's; each row's tail is its
own. What Lean has for these: plan_rows_high (any two rows share the constant's coin and every
coefficient above h), plan_below and plan_last_all (2 k + 1 in all), spot_share at two tails. -/
theorem spot_apart {codes : Codes} {s : OracleShape} {sort : MsgSort} {p q : RowSpot}
    (hfit : msgShapeFits codes s sort = true) (hp : RowSpot.isReal codes s p = true)
    (hq : RowSpot.isReal codes s q = true) (hne : p ≠ q)
    (hrow : ¬ ∃ k h r r' j, sort = .fresh k h ∧ p = .mask r j ∧ q = .mask r' j) :
    ∀ n ∈ spotCoins codes s sort p, n ∉ spotCoins codes s sort q := fun _ hn hn' =>
  (spot_share hfit hp hq hn hn').elim hne hrow

/-- **A MASK ROW's COIN REACHES NO TAIL**: no real place of a mask row's tail, of whichever row, and
none of a main row's. THE SECOND HALF IS EMPTY WHEREVER THE PREMISES ARE MET: where the shape fits,
a message with a mask row has no main row: there the test bars, not the numbers; the numbers' own
reason is spot_share's arm at a plain message, whose proof spends nothing of the test. -/
theorem mask_no_tail {codes : Codes} {s : OracleShape} {sort : MsgSort} {r j n : ℕ}
    (hfit : msgShapeFits codes s sort = true) (hp : RowSpot.isReal codes s (.mask r j) = true)
    (hn : n ∈ spotCoins codes s sort (.mask r j)) :
    (∀ r' t, RowSpot.isReal codes s (.maskTail r' t) = true →
        n ∉ spotCoins codes s sort (.maskTail r' t)) ∧
      ∀ r' t, RowSpot.isReal codes s (.mainTail r' t) = true →
        n ∉ spotCoins codes s sort (.mainTail r' t) :=
  ⟨fun _ _ hq => spot_apart hfit hp hq (fun e => nomatch e)
      (fun ⟨_, _, _, _, _, _, _, e⟩ => nomatch e) n hn,
    fun _ _ hq => spot_apart hfit hp hq (fun e => nomatch e)
      (fun ⟨_, _, _, _, _, _, _, e⟩ => nomatch e) n hn⟩

/-- **A MASK ROW's COIN REACHES NO SECOND PLACE OF ITS ROW**, nor another place's number in any
row. -/
theorem mask_one_place {codes : Codes} {s : OracleShape} {sort : MsgSort} {r j r' j' n : ℕ}
    (hfit : msgShapeFits codes s sort = true) (hp : RowSpot.isReal codes s (.mask r j) = true)
    (hq : RowSpot.isReal codes s (.mask r' j') = true) (hn : n ∈ spotCoins codes s sort (.mask r j))
    (hn' : n ∈ spotCoins codes s sort (.mask r' j')) : j = j' := by
  rcases spot_share hfit hp hq hn hn' with e | ⟨_, _, _, _, _, _, e1, e2⟩
  · injection e
  · injection e1 with _ a
    injection e2 with _ b
    rw [a, b]

/-- What the test on a plain message's shape gives: one of two arms. -/
theorem plainShape_fits {codes : Codes} {s : OracleShape} {high : Bool}
    (hf : msgShapeFits codes s (.plain high) = true) :
    (s.maskRows = 0 ∧ 0 < s.mainRows ∧ s.answers ≤ (codes.base.getD s.code default).ell) ∨
      (s.mainRows = 0 ∧ 0 < s.maskRows) := by
  unfold msgShapeFits at hf
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  rcases hf.2 with h | h
  · exact .inl ⟨h.1.1.1.1, h.1.1.1.2, h.1.2⟩
  · exact .inr h

/-- A number below n b is a b + c with a below n and c below b. (The same sentence: split_mul,
Honest/K1/SeatOnto.lean; it does not lie beneath this file.) -/
theorem cell_split {n b x : ℕ} (h : x < n * b) : ∃ a c, a < n ∧ c < b ∧ x = a * b + c := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with e | e
    · rw [e, Nat.mul_zero] at h; omega
    · exact e
  refine ⟨x / b, x % b, (Nat.div_lt_iff_lt_mul hb).2 h, Nat.mod_lt _ hb, ?_⟩
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod x b).symm

/-- **EVERY COIN BELOW THE MESSAGE's COUNT STANDS AT A REAL PLACE.** -/
theorem spot_all {codes : Codes} {s : OracleShape} {sort : MsgSort}
    (hfit : msgShapeFits codes s sort = true) : ∀ n, n < dueOf codes s sort →
    ∃ p, RowSpot.isReal codes s p = true ∧ n ∈ spotCoins codes s sort p := by
  intro n hn
  cases sort with
  | fresh k h =>
    obtain ⟨hm, hh, hl⟩ := freshShape_fits hfit
    replace hn : n < 2 * k + 1 + s.maskRows * (codes.mask.getD s.maskCode default).r := hn
    by_cases c : n < 2 * k + 1
    · obtain ⟨I, hI, hnI⟩ := List.mem_flatten.1 (plan_last_all hh n c)
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hI
      have hjl : j < (plan k h (2 ^ h - 1)).length := (List.getElem?_eq_some_iff.1 hj).1
      rw [plan_places hh] at hjl
      refine ⟨.mask (2 ^ h - 1) j,
        Bool.and_eq_true_iff.2 ⟨decide_eq_true ?_, decide_eq_true ?_⟩, ?_⟩
      · rw [hm]
        exact Nat.sub_lt (Nat.two_pow_pos h) Nat.one_pos
      · omega
      · show n ∈ (plan k h (2 ^ h - 1)).getD j []
        rw [List.getD_eq_getElem?_getD, hj]
        exact hnI
    · obtain ⟨a, t, ha, ht, e⟩ := cell_split (show n - (2 * k + 1) <
        s.maskRows * (codes.mask.getD s.maskCode default).r by omega)
      exact ⟨.maskTail a t, Bool.and_eq_true_iff.2 ⟨decide_eq_true ha, decide_eq_true ht⟩,
        List.mem_singleton.2 (by omega)⟩
  | plain high =>
    replace hn : n < s.mainRows * (codes.base.getD s.code default).r +
      (if s.maskRows == 0 then s.answers else 0) +
      s.maskRows * (codes.mask.getD s.maskCode default).ell +
      s.maskRows * (codes.mask.getD s.maskCode default).r := hn
    by_cases c1 : n < s.mainRows * (codes.base.getD s.code default).r
    · obtain ⟨a, t, ha, ht, e⟩ := cell_split c1
      exact ⟨.mainTail a t, Bool.and_eq_true_iff.2 ⟨decide_eq_true ha, decide_eq_true ht⟩,
        List.mem_singleton.2 e⟩
    · rcases plainShape_fits hfit with ⟨z, hm, ha⟩ | ⟨z, hm⟩
      · -- no mask row: the pad
        have hP : (if s.maskRows == 0 then s.answers else 0) = s.answers := by rw [z]; rfl
        rw [hP, z, Nat.zero_mul, Nat.zero_mul] at hn
        refine ⟨.main (s.mainRows - 1) ((codes.base.getD s.code default).ell - s.answers +
          (n - s.mainRows * (codes.base.getD s.code default).r)),
          Bool.and_eq_true_iff.2 ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩, ?_⟩
        show n ∈ (if _ then _ else _)
        rw [if_pos]
        · exact List.mem_singleton.2 (by omega)
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          exact ⟨⟨⟨z, by omega⟩, by omega⟩, by omega⟩
      · -- mask rows alone
        have hP : (if s.maskRows == 0 then s.answers else 0) = 0 := by
          rw [if_neg]
          simp only [beq_iff_eq]
          omega
        rw [hP] at hn
        by_cases c2 : n < s.mainRows * (codes.base.getD s.code default).r + 0 +
            s.maskRows * (codes.mask.getD s.maskCode default).ell
        · obtain ⟨j, r, hj, hr, e⟩ := cell_split (show n -
              (s.mainRows * (codes.base.getD s.code default).r + 0) <
              (codes.mask.getD s.maskCode default).ell * s.maskRows by
            rw [Nat.mul_comm (codes.mask.getD s.maskCode default).ell s.maskRows]; omega)
          refine ⟨.mask r j, Bool.and_eq_true_iff.2 ⟨decide_eq_true hr, decide_eq_true hj⟩,
            List.mem_singleton.2 ?_⟩
          rw [hP]
          omega
        · obtain ⟨a, t, ha, ht, e⟩ := cell_split (show n -
              (s.mainRows * (codes.base.getD s.code default).r + 0 +
                s.maskRows * (codes.mask.getD s.maskCode default).ell) <
              s.maskRows * (codes.mask.getD s.maskCode default).r by omega)
          refine ⟨.maskTail a t, Bool.and_eq_true_iff.2 ⟨decide_eq_true ha, decide_eq_true ht⟩,
            List.mem_singleton.2 ?_⟩
          rw [hP]
          omega

/-- **TWO MESSAGES OF A SENDING SHARE NO COIN**: among the part's coins the coin number n of the
message number k is the number offsetOf … k + n. -/
theorem messages_apart (J : SendJob) {k k' n n' : ℕ} (hk : k < J.Q.sent.size)
    (hk' : k' < J.Q.sent.size) (hne : k ≠ k')
    (hn : n < dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k))
    (hn' : n' < dueOf J.Q.codes (J.Q.sent.getD k' default).shape (J.sort k')) :
    offsetOf J.Q.codes J.Q.sent J.sort k + n ≠ offsetOf J.Q.codes J.Q.sent J.sort k' + n' := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have a := offset_step J.Q.codes J.Q.sent J.sort k hk
    have b := offset_le J.Q.codes J.Q.sent J.sort k' (k + 1) h (Nat.le_of_lt hk')
    omega
  · have a := offset_step J.Q.codes J.Q.sent J.sort k' hk'
    have b := offset_le J.Q.codes J.Q.sent J.sort k (k' + 1) h (Nat.le_of_lt hk)
    omega

/-- Where a place of message k turns under a change of the coin N alone, N is one of its coins. -/
theorem turn_reads (J : SendJob) (t : State Ask Unit) (cs cs' : Array E) (N k : ℕ) (p : RowSpot)
    (hoff : ∀ i, i ≠ N → cs.getD i zeroE = cs'.getD i zeroE)
    (h : Laid.atSpot (J.rows t cs k) p ≠ Laid.atSpot (J.rows t cs' k) p) :
    ∃ n ∈ spotCoins J.Q.codes (J.Q.sent.getD k default).shape (J.sort k) p,
      offsetOf J.Q.codes J.Q.sent J.sort k + n = N := by
  by_contra hc
  refine h (spot_reads _ _ _ _ _ _ p fun n hn => hoff _ fun e => hc ⟨n, hn, e⟩)

/-- **CHANGE ONE COIN OF THE PART AND LOOK AT WHAT TURNS**: two real places that turn lie in one
message, and are one place, or one place's number in two rows of a fresh table. At one state t on
both sides: one input, the same challenges heard. -/
theorem one_coin_turns (J : SendJob) (hfit : sendShapeFits J = true) (t : State Ask Unit)
    (cs cs' : Array E) (N : ℕ) (hoff : ∀ i, i ≠ N → cs.getD i zeroE = cs'.getD i zeroE)
    {k k' : ℕ} (hk : k < J.Q.sent.size) (hk' : k' < J.Q.sent.size) {p q : RowSpot}
    (hp : RowSpot.isReal J.Q.codes (J.Q.sent.getD k default).shape p = true)
    (hq : RowSpot.isReal J.Q.codes (J.Q.sent.getD k' default).shape q = true)
    (h1 : Laid.atSpot (J.rows t cs k) p ≠ Laid.atSpot (J.rows t cs' k) p)
    (h2 : Laid.atSpot (J.rows t cs k') q ≠ Laid.atSpot (J.rows t cs' k') q) :
    k = k' ∧ (p = q ∨ ∃ a b r r' j, J.sort k = .fresh a b ∧ p = .mask r j ∧ q = .mask r' j) := by
  obtain ⟨n, hn, e⟩ := turn_reads J t cs cs' N k p hoff h1
  obtain ⟨n', hn', e'⟩ := turn_reads J t cs cs' N k' q hoff h2
  have f := msgFits_at J hfit k hk
  have f' := msgFits_at J hfit k' hk'
  have hkk : k = k' := by
    by_contra hne
    exact messages_apart J hk hk' hne (spot_below f hp n hn) (spot_below f' hq n' hn')
      (e.trans e'.symm)
  subst hkk
  obtain rfl : n = n' := by omega
  exact ⟨rfl, spot_share f hp hq hn hn'⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.foldl_filter_map
#print axioms ProofFile.Honest.K14.row_plan
#print axioms ProofFile.Honest.K14.sumG_congr
#print axioms ProofFile.Honest.K14.toE_sumG
#print axioms ProofFile.Honest.K14.fresh_mask_eq
#print axioms ProofFile.Honest.K14.fresh_mask_reads
#print axioms ProofFile.Honest.K14.fresh_mask_sum
#print axioms ProofFile.Honest.K14.isReal_agree
#print axioms ProofFile.Honest.K14.spot_reads
#print axioms ProofFile.Honest.K14.fresh_tail_coin
#print axioms ProofFile.Honest.K14.spot_coin
#print axioms ProofFile.Honest.K14.spot_vector
#print axioms ProofFile.Honest.K14.spot_zero
#print axioms ProofFile.Honest.K14.spot_sum
#print axioms ProofFile.Honest.K14.tables_of_real
#print axioms ProofFile.Honest.K14.answers_of_real
#print axioms ProofFile.Honest.K14.isReal_main
#print axioms ProofFile.Honest.K14.isReal_mainTail
#print axioms ProofFile.Honest.K14.isReal_mask
#print axioms ProofFile.Honest.K14.isReal_maskTail
#print axioms ProofFile.Honest.K14.freshShape_fits
#print axioms ProofFile.Honest.K14.pad_cond
#print axioms ProofFile.Honest.K14.getD_mem_flatten
#print axioms ProofFile.Honest.K14.spot_below
#print axioms ProofFile.Honest.K14.spot_once
#print axioms ProofFile.Honest.K14.padSpot_mem
#print axioms ProofFile.Honest.K14.spot_share
#print axioms ProofFile.Honest.K14.spot_apart
#print axioms ProofFile.Honest.K14.mask_no_tail
#print axioms ProofFile.Honest.K14.mask_one_place
#print axioms ProofFile.Honest.K14.plainShape_fits
#print axioms ProofFile.Honest.K14.cell_split
#print axioms ProofFile.Honest.K14.spot_all
#print axioms ProofFile.Honest.K14.messages_apart
#print axioms ProofFile.Honest.K14.turn_reads
#print axioms ProofFile.Honest.K14.one_coin_turns
