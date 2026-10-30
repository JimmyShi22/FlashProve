-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/BookFromFits.lean: the kind "the code switch" (K2): THIS KIND's
OWN TEST ON THE TWO LISTS OF ENTRIES (`bookFits`, Honest/K2/Fresh.lean) GIVES ANOTHER WRITER's TWO
PREMISES ON THE BOOK AT ONE SPENDER (`WithinAt`, `SpenderClear`, Johnson/SendSim/At/Fresh.lean). SO
THE SECOND LAW ON THE SENDER (`SendFreshLaw`) HOLDS OF THE CORE's OWN SENDER AT A BOOK's TWO LISTS
WITH NO PREMISE ON THE BOOK BESIDE THE LAW's OWN HYPOTHESIS. Statements with their proofs; no
definition.

  1  runs and numbers: `mem_eAll_ex`, `apart_e`, `inside_e`, `inside_noF`, `unknown_of`, `apart_of`,
     and tools on numbers: `tail_lt`, `free_form`, `free_below`, `pad_bounds`
  2  the two writers' numbers are the same: `entriesFrom_shared` (where a sampled message's mask
     entries begin), `freshStart_shared` (a fresh mask's coefficients begin where its coins begin),
     `wholeEnd_shared` (a message's coins of the extension field end where its mask rows' tails
     end), `one_message` (a number in two messages' stretches names one message), `free_in` (a free
     mask entry's number lies in its message's stretch), and tools: `sendingPar_codes`,
     `main_sampled`, `main_none`, `dueMsg_e`, `maskStart_eq`, `dueBefore_succ_e`, `mask_plain`
  3  the test's two arms: `fold_of_arm`, `mask_of_arm`; the ends: `within_of_bookFits`,
     `clear_of_bookFits`, `sendFreshLaw_core_book`, and, wherever the proof file's description is
     returned, at every place of the kind's lot, at every book and order: `sendFresh_open`: the
     field `sendFresh` of `FreshAsks`

Limits. The converse is not claimed: `bookFits` asks more. The last two are as good as another
writer's theorem on the shared sending's rows that Honest/K2/Law/AtCore.lean calls. Inside the law
its own hypotheses stand as they were: the shared sending's public test, "the table that rides has
one row", `bookFits`, the seeds, the positions: none is shown here of a place or a book.
`sendFresh_open`: at the format's second hash function as the library's seats take it; idle where the lot
has no place; the book and the order are free letters there: whoever uses the sentence lays the
description's own. Nothing here says what the law would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.AtCore
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.SendSim.At.BookTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes.SendSim.At (eOf fOf eAll fAll freeNo padNo maskTailNo WithinAt MaskSpender FoldSpender
  SpenderClear)
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)

/-! ## 1 Runs and numbers -/

theorem mem_eAll_ex (l : List Ahead) (x : Nat) : x ∈ eAll l ↔ ∃ e ∈ l, x ∈ eOf e := by
  induction l with
  | nil =>
    constructor
    · intro h
      have h' : x ∈ (∅ : Finset ℕ) := h
      exact absurd h' (by simp)
    · rintro ⟨e, he, _⟩
      cases he
  | cons a l ih =>
    have h : eAll (a :: l) = eOf a ∪ eAll l := rfl
    rw [h, Finset.mem_union, ih]
    constructor
    · rintro (h1 | ⟨e, he, hx⟩)
      · exact ⟨a, List.mem_cons_self, h1⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, hx⟩
    · rintro ⟨e, he, hx⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact Or.inl hx
      · exact Or.inr ⟨e, he, hx⟩

/-- A run that an entry's run does not meet holds none of the entry's numbers. -/
theorem apart_e {a : Ahead} {R : Run} (h : (runOf a).meets R = false) {x : Nat}
    (hx : x ∈ eOf a) : ¬ (R.1.e ≤ x ∧ x < R.1.e + R.2.e) := by
  intro hR
  have hx' : a.start.e ≤ x ∧ x < a.start.e + a.count.e := Finset.mem_Ico.1 hx
  have h2 : (runOf a).meets R = true := by
    simp only [Run.meets, runOf, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]
    right
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega
  rw [h] at h2
  cases h2

/-- A run inside which an entry's run lies holds all the entry's numbers. -/
theorem inside_e {a : Ahead} {R : Run} (h : (runOf a).inside R = true) {x : Nat}
    (hx : x ∈ eOf a) : R.1.e ≤ x ∧ x < R.1.e + R.2.e := by
  have hx' : a.start.e ≤ x ∧ x < a.start.e + a.count.e := Finset.mem_Ico.1 hx
  simp only [Run.inside, runOf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  omega

theorem inside_noF {a : Ahead} {R : Run} (h : (runOf a).inside R = true) (h0 : R.2.f = 0) :
    a.count.f = 0 := by
  simp only [Run.inside, runOf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  omega

theorem unknown_of {es ks : List Ahead}
    (h : es.all (fun e => ks.all fun k => !(runOf e).meets (runOf k)) = true) :
    Disjoint (eAll es) (eAll ks) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨e, he, hxe⟩ := (mem_eAll_ex _ _).1 hx
  obtain ⟨k, hk, hxk⟩ := (mem_eAll_ex _ _).1 hy
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h e he) k hk
  have h2 : (runOf e).meets (runOf k) = false := by simpa using h1
  exact apart_e h2 hxe (Finset.mem_Ico.1 hxk)

theorem apart_of {es : List Ahead}
    (h : es.zipIdx.all (fun x => es.zipIdx.all fun y =>
      x.2 == y.2 || !(runOf x.1).meets (runOf y.1)) = true) :
    es.Pairwise fun e e' => Disjoint (eOf e) (eOf e') := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have mi : (es[i], i) ∈ es.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hi]
  have mj : (es[j], j) ∈ es.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hj]
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h _ mi) _ mj
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hy
    exact apart_e h1 hx (Finset.mem_Ico.1 hy)

/-- Entry q of row r of m rows of z entries. -/
theorem tail_lt {r q m z : Nat} (hr : r < m) (hq : q < z) : r * z + q < m * z := by
  have h : (r + 1) * z ≤ m * z := Nat.mul_le_mul_right z hr
  rw [Nat.add_one_mul] at h
  omega

/-- The free entries of m rows of ell places with a answers, where there is one. -/
theorem free_form {m ell a j : Nat} (hj : j < OnBytes.Send.freeMaskEntries m ell a) :
    OnBytes.Send.freeMaskEntries m ell a = m * (ell - a) + (m - 1) ∧ 0 < m ∧ a ≤ ell := by
  unfold OnBytes.Send.freeMaskEntries at hj ⊢
  split_ifs at hj ⊢ with hc
  · omega
  · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    exact ⟨rfl, Nat.pos_of_ne_zero hc.1, hc.2⟩

/-- They end below the rows' end. -/
theorem free_below {m ell a : Nat} (hm : 0 < m) (ha : a ≤ ell) (h0 : 0 < a) :
    m * (ell - a) + (m - 1) < m * ell := by
  have h2 : (ell - a + 1) * m ≤ ell * m := Nat.mul_le_mul_right m (by omega)
  rw [Nat.add_one_mul] at h2
  rw [Nat.mul_comm m (ell - a), Nat.mul_comm m ell]
  omega

/-- A pad's entry lies behind them and below the rows' end. -/
theorem pad_bounds {m ell a i : Nat} (hm : 0 < m) (ha : a ≤ ell) (hi : i < a) :
    m * (ell - a) + (m - 1) ≤ (ell - a + i) * m + (m - 1) ∧
      (ell - a + i) * m + (m - 1) < m * ell := by
  have h1 : (ell - a) * m ≤ (ell - a + i) * m := Nat.mul_le_mul_right m (Nat.le_add_right _ _)
  have h2 : (ell - a + i + 1) * m ≤ ell * m := Nat.mul_le_mul_right m (by omega)
  rw [Nat.add_one_mul] at h2
  rw [Nat.mul_comm m (ell - a), Nat.mul_comm m ell]
  constructor <;> omega

/-! ## 2 The two writers' numbers are the same -/

section
variable {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}

theorem sendingPar_codes (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    (sendingPar codes sent).codes = codes := rfl

/-- A sampled message's main rows' coins, over the extension field. -/
theorem main_sampled (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (R : Option K1.Ride)
    (ha : s.answers ≠ 0) (h3 : (s.mainDeg == 3) = true) :
    (K1.stepsOf codes s R).main =
      s.mainRows * (codes.base.getD s.code default).r +
        (if s.maskRows != 0 then 0 else s.answers) := by
  by_cases hm : s.maskRows = 0
  · simp [K1.Steps.main, K1.stepsOf, ha, h3, hm]
  · simp [K1.Steps.main, K1.stepsOf, ha, hm]

/-- A message without a main row and without a sample has none. -/
theorem main_none (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (R : Option K1.Ride)
    (hm : s.mainRows = 0) (ha : s.answers = 0) : (K1.stepsOf codes s R).main = 0 := by
  simp [K1.Steps.main, K1.stepsOf, hm, ha]

theorem dueMsg_e (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (R : Option K1.Ride) :
    (K1.dueMsg codes s R).e =
      (if s.mainDeg == 3 then (K1.stepsOf codes s R).main else 0) + (K1.stepsOf codes s R).mask +
        s.maskRows * (codes.mask.getD s.maskCode default).r := by
  by_cases h3 : (s.mainDeg == 3) = true
  · simp only [K1.dueMsg, h3, if_true]
    rfl
  · simp only [K1.dueMsg, h3, Bool.false_eq_true, if_false, Nat.zero_add]
    rfl

theorem maskStart_eq (n : Nat) :
    K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n =
      (K1.startR (sendingPar codes sent) (rideOf sent fresh) n).e +
        if (sent.getD n default).shape.mainDeg == 3 then
          (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).main else 0 := by
  unfold K1.maskStart
  rw [sendingPar_shape, sendingPar_codes]

/-- Where a sampled message's mask entries begin. -/
theorem entriesFrom_shared
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n : Nat} (hn : n < sent.size) (ha : (sent.getD n default).shape.answers ≠ 0) :
    entriesFrom codes sent fresh n =
      K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n := by
  rw [maskStart_eq]
  unfold entriesFrom
  rw [dueBefore_shared hf hw n (Nat.le_of_lt hn)]
  by_cases h3 : ((sent.getD n default).shape.mainDeg == 3) = true
  · simp only [h3, if_true]
    rw [main_sampled codes _ _ ha h3]
  · simp only [h3, Bool.false_eq_true, if_false]

/-- A fresh mask's coefficients begin where its coins begin. -/
theorem freshStart_shared
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n k : Nat} (hn : n < sent.size) (hr : foldAt fresh n = some k) :
    (dueBefore codes sent fresh n).e =
      K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n := by
  have H := (shapeFits_of hf hn).ride k hr
  simp only [K1.rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at H
  rw [maskStart_eq, dueBefore_shared hf hw n (Nat.le_of_lt hn),
    main_none codes _ _ H.1.1.1.1.2 H.1.1.1.1.1, ite_self, Nat.add_zero]

/-- A message's coins of the extension field end where its mask rows' tails end. -/
theorem wholeEnd_shared
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n : Nat} (hn : n < sent.size) :
    (dueBefore codes sent fresh n).e ≤
        K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n ∧
      (dueBefore codes sent fresh n).e +
          (messageDue codes (sent.getD n default).shape (foldAt fresh n)).e =
        K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n +
          (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).mask +
          (sent.getD n default).shape.maskRows *
            (codes.mask.getD (sent.getD n default).shape.maskCode default).r := by
  rw [maskStart_eq, dueBefore_shared hf hw n (Nat.le_of_lt hn),
    messageDue_shared (shapeFits_of hf hn) (hw n hn), dueMsg_e, ← rideOf_as]
  constructor <;> omega

/-- A number in two messages' stretches names one message. -/
theorem one_message {k n x : Nat} (hk : k < sent.size) (hn : n < sent.size)
    (h1 : (dueBefore codes sent fresh k).e ≤ x ∧ x < (dueBefore codes sent fresh (k + 1)).e)
    (h2 : (dueBefore codes sent fresh n).e ≤ x ∧ x < (dueBefore codes sent fresh (n + 1)).e) :
    k = n := by
  rcases Nat.lt_trichotomy k n with h | h | h
  · have h3 : (dueBefore codes sent fresh (k + 1)).e ≤ (dueBefore codes sent fresh n).e :=
      (dueBefore_le codes sent fresh n h (Nat.le_of_lt hn)).2
    omega
  · exact h
  · have h3 : (dueBefore codes sent fresh (n + 1)).e ≤ (dueBefore codes sent fresh k).e :=
      (dueBefore_le codes sent fresh k h (Nat.le_of_lt hk)).2
    omega

theorem dueBefore_succ_e {n : Nat} (hn : n < sent.size) :
    (dueBefore codes sent fresh (n + 1)).e = (dueBefore codes sent fresh n).e +
      (messageDue codes (sent.getD n default).shape (foldAt fresh n)).e := by
  rw [dueBefore_succ codes sent fresh hn]

/-- A message that does not ride has its mask rows' entries as coins. -/
theorem mask_plain {n : Nat} (hr : foldAt fresh n = none) :
    (K1.stepsOf codes (sent.getD n default).shape (rideOf sent fresh n)).mask =
      (sent.getD n default).shape.maskRows *
        (codes.mask.getD (sent.getD n default).shape.maskCode default).ell := by
  rw [rideOf_as, hr]
  rfl

/-- A free mask entry's number lies in its message's stretch. -/
theorem free_in
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n j : Nat} (hn : n < sent.size) (hr : foldAt fresh n = none)
    (ha : (sent.getD n default).shape.answers ≠ 0)
    (hj : j < OnBytes.Send.freeMaskEntries (sent.getD n default).shape.maskRows
      (codes.mask.getD (sent.getD n default).shape.maskCode default).ell
      (sent.getD n default).shape.answers) :
    (dueBefore codes sent fresh n).e ≤
        K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n + j ∧
      K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n + j <
        (dueBefore codes sent fresh (n + 1)).e := by
  obtain ⟨h1, h2⟩ := wholeEnd_shared hf hw hn
  rw [mask_plain hr] at h2
  have h3 := K1.free_lt _ _ _ j (Nat.pos_of_ne_zero ha) hj
  rw [dueBefore_succ_e hn]
  constructor <;> omega

end

/-! ## 3 The ends -/

section
variable {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
  {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

theorem within_of_bookFits
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    (hb : bookFits codes sent fresh (Bk.spentBy o p) (Bk.knownBy ord o p) = true) :
    WithinAt (sendingPar codes sent) (rideOf sent fresh) Bk ord o p := by
  unfold bookFits at hb
  simp only [Bool.and_eq_true] at hb
  intro e he
  have h := List.all_eq_true.1 hb.1.1.1 e (List.mem_append.2 he)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [sendingDue_shared hf hw] at h
  exact h

/-- The test's arm on a fold's fresh mask. -/
theorem fold_of_arm
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n k : Nat} (hone : (sent.getD n default).shape.maskRows = 1)
    (hfold : foldAt fresh n = some k)
    (hU : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)))
    (hl : (Bk.spentBy o p).length = 1)
    (hin : ∀ e ∈ Bk.spentBy o p,
      (runOf e).inside (coefficientsRun codes sent fresh n k) = true ∧
        (coefficientsRun codes sent fresh n k).inside (runOf e) = true)
    (hk : ∀ a ∈ Bk.knownBy ord o p,
      (runOf a).meets (freshTailsRun codes sent fresh n k) = false) :
    FoldSpender (sendingPar codes sent) (rideOf sent fresh) Bk ord o p := by
  obtain ⟨e, he⟩ := List.length_eq_one_iff.1 hl
  have hn : n < sent.size := by
    by_contra h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h),
      Option.getD_none] at hone
    exact absurd hone (by decide)
  have hride : rideOf sent fresh n =
      some ⟨k, OnBytes.ceilLog2 (sent.getD n default).shape.maskRows⟩ := by
    rw [rideOf_as, hfold]
    rfl
  obtain ⟨h1, h2⟩ := hin e (by rw [he]; exact List.mem_cons_self)
  simp only [Run.inside, runOf, coefficientsRun, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h1 h2
  have hcf : e.count.f = 0 := by omega
  have hce : e.count.e = 2 * k + 1 := by omega
  have hse : e.start.e = (dueBefore codes sent fresh n).e := by omega
  have hs := freshStart_shared hf hw hn hfold
  refine ⟨⟨n, ⟨k, OnBytes.ceilLog2 (sent.getD n default).shape.maskRows⟩, e, ?_, hride, ?_, he,
    ?_, ?_, ?_⟩, hU⟩
  · rw [sendingPar_sent]
    exact hn
  · show OnBytes.ceilLog2 (sent.getD n default).shape.maskRows = 0
    rw [hone]
    decide
  · have hc : e.count = ⟨e.count.f, e.count.e⟩ := rfl
    rw [hc, hcf, hce]
    rfl
  · rw [hse]
    exact hs
  · intro r hr q hq hmem
    obtain ⟨a, ha, hx⟩ := (mem_eAll_ex _ _).1 hmem
    rw [sendingPar_shape] at hr
    unfold OnBytes.SendSim.At.maskCodeAt at hq
    rw [sendingPar_shape, sendingPar_codes] at hq
    have hm := tail_lt hr hq
    have e1 : maskTailNo (sendingPar codes sent) (rideOf sent fresh) n r q =
        K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n + (2 * k + 1) +
          r * (codes.mask.getD (sent.getD n default).shape.maskCode default).r + q := by
      unfold OnBytes.SendSim.At.maskTailNo OnBytes.SendSim.At.maskCodeAt
      rw [sendingPar_shape, sendingPar_codes, hride]
      rfl
    rw [e1, ← hs] at hx
    have g1 : (dueBefore codes sent fresh n).e + (2 * k + 1) ≤
        (dueBefore codes sent fresh n).e + (2 * k + 1) +
          r * (codes.mask.getD (sent.getD n default).shape.maskCode default).r + q := by omega
    have g2 : (dueBefore codes sent fresh n).e + (2 * k + 1) +
          r * (codes.mask.getD (sent.getD n default).shape.maskCode default).r + q <
        (dueBefore codes sent fresh n).e + (2 * k + 1) +
          (sent.getD n default).shape.maskRows *
            (codes.mask.getD (sent.getD n default).shape.maskCode default).r := by omega
    exact apart_e (hk a ha) hx ⟨g1, g2⟩

/-- The test's arm on a sampled message's free mask entries. -/
theorem mask_of_arm
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    {n : Nat} (hn : n < sent.size) (hr : foldAt fresh n = none)
    (ha : (sent.getD n default).shape.answers ≠ 0)
    (hU : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)))
    (hA : (Bk.spentBy o p).Pairwise fun e e' => Disjoint (eOf e) (eOf e'))
    (hin : ∀ e ∈ Bk.spentBy o p, (runOf e).inside (freeRun codes sent fresh n) = true)
    (hk : ∀ a ∈ Bk.knownBy ord o p,
      (runOf a).meets (wholeRun codes sent fresh n) = false ∨
        (runOf a).inside (freeRun codes sent fresh n) = true) :
    MaskSpender (sendingPar codes sent) (rideOf sent fresh) Bk ord o p := by
  have hF := entriesFrom_shared hf hw hn ha
  obtain ⟨hW1, hW2⟩ := wholeEnd_shared hf hw hn
  rw [mask_plain hr] at hW2
  have hfree : ∀ x ∈ eAll (Bk.spentBy o p),
      K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n ≤ x ∧
        x < K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n +
          OnBytes.Send.freeMaskEntries (sent.getD n default).shape.maskRows
            (codes.mask.getD (sent.getD n default).shape.maskCode default).ell
            (sent.getD n default).shape.answers := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := (mem_eAll_ex _ _).1 hx
    have h : entriesFrom codes sent fresh n ≤ x ∧ x < entriesFrom codes sent fresh n +
        OnBytes.Send.freeMaskEntries (sent.getD n default).shape.maskRows
          (codes.mask.getD (sent.getD n default).shape.maskCode default).ell
          (sent.getD n default).shape.answers := inside_e (hin e he) hxe
    rwa [hF] at h
  have hoff : ∀ y, K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n +
        OnBytes.Send.freeMaskEntries (sent.getD n default).shape.maskRows
          (codes.mask.getD (sent.getD n default).shape.maskCode default).ell
          (sent.getD n default).shape.answers ≤ y →
      y < (dueBefore codes sent fresh n).e +
        (messageDue codes (sent.getD n default).shape (foldAt fresh n)).e →
      y ∉ eAll (Bk.knownBy ord o p) := by
    intro y h1 h2 hy
    obtain ⟨a, hak, hya⟩ := (mem_eAll_ex _ _).1 hy
    rcases hk a hak with h | h
    · have g1 : (dueBefore codes sent fresh n).e ≤ y := by omega
      exact apart_e h hya ⟨g1, h2⟩
    · have h' : entriesFrom codes sent fresh n ≤ y ∧ y < entriesFrom codes sent fresh n +
          OnBytes.Send.freeMaskEntries (sent.getD n default).shape.maskRows
            (codes.mask.getD (sent.getD n default).shape.maskCode default).ell
            (sent.getD n default).shape.answers := inside_e h hya
      rw [hF] at h'
      omega
  refine ⟨?_, ?_, hA, hU, ?_⟩
  · exact OnBytes.SendSim.At.fAll_of_test
      (List.all_eq_true.2 fun e he => beq_iff_eq.2 (inside_noF (hin e he) rfl))
  · intro x hx
    obtain ⟨h1, h2⟩ := hfree x hx
    refine ⟨n, by rw [sendingPar_sent]; exact hn, by rw [rideOf_as, hr]; rfl,
      by rw [sendingPar_shape]; exact ha, ?_⟩
    refine OnBytes.SendSim.At.mem_freeNo _ _ h1 ?_
    unfold OnBytes.SendSim.At.maskCodeAt
    rw [sendingPar_shape, sendingPar_codes]
    exact h2
  · intro k j hk' hrk hak hjf hjs
    rw [sendingPar_sent] at hk'
    rw [sendingPar_shape] at hak
    have hrk' : foldAt fresh k = none := by
      rw [rideOf_as] at hrk
      cases hfk : foldAt fresh k with
      | none => rfl
      | some v =>
        rw [hfk] at hrk
        cases hrk
    have hj := OnBytes.SendSim.At.lt_of_mem_freeNo _ _ hjf
    unfold OnBytes.SendSim.At.maskCodeAt at hj
    rw [sendingPar_shape, sendingPar_codes] at hj
    have hs1 := free_in hf hw hk' hrk' hak hj
    obtain ⟨g1, g2⟩ := hfree _ hjs
    have hs2 := free_in hf hw hn hr ha
      (j := K1.maskStart (sendingPar codes sent) (rideOf sent fresh) k + j -
        K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n) (by omega)
    rw [Nat.add_sub_cancel' g1] at hs2
    have hkn : k = n := one_message hk' hn hs1 hs2
    rw [hkn] at hj ⊢
    obtain ⟨hfe, hm0, hal⟩ := free_form hj
    rw [hfe] at hoff
    have hb0 := free_below hm0 hal (Nat.pos_of_ne_zero ha)
    have hTail : ∀ r q, r < (sent.getD n default).shape.maskRows →
        q < (codes.mask.getD (sent.getD n default).shape.maskCode default).r →
        maskTailNo (sendingPar codes sent) (rideOf sent fresh) n r q ∉
          eAll (Bk.knownBy ord o p) := by
      intro r q hr' hq'
      have hm := tail_lt hr' hq'
      have e1 : maskTailNo (sendingPar codes sent) (rideOf sent fresh) n r q =
          K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n +
            (sent.getD n default).shape.maskRows *
              (codes.mask.getD (sent.getD n default).shape.maskCode default).ell +
            r * (codes.mask.getD (sent.getD n default).shape.maskCode default).r + q := by
        unfold OnBytes.SendSim.At.maskTailNo OnBytes.SendSim.At.maskCodeAt
        rw [sendingPar_shape, sendingPar_codes, mask_plain hr]
      rw [e1]
      exact hoff _ (by omega) (by omega)
    constructor
    · intro i hi
      rw [sendingPar_shape] at hi
      obtain ⟨b1, b2⟩ := pad_bounds hm0 hal hi
      have e2 : padNo (sendingPar codes sent) (rideOf sent fresh) n i =
          K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n +
            (((codes.mask.getD (sent.getD n default).shape.maskCode default).ell -
              (sent.getD n default).shape.answers + i) *
                (sent.getD n default).shape.maskRows +
              ((sent.getD n default).shape.maskRows - 1)) := by
        unfold OnBytes.SendSim.At.padNo OnBytes.SendSim.At.maskCodeAt
        rw [sendingPar_shape, sendingPar_codes]
      rw [e2]
      exact hoff _ (by omega) (by omega)
    · intro q hq
      unfold OnBytes.SendSim.At.maskCodeAt at hq
      rw [sendingPar_shape, sendingPar_codes] at hq
      rw [sendingPar_shape]
      exact ⟨hTail _ q (Nat.mod_lt _ hm0) hq, hTail _ q (by omega) hq⟩

/-- **This kind's own test on the two lists gives the other writer's premise at one spender.** -/
theorem clear_of_bookFits
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent)
    (hone : ∀ x ∈ fresh, (sent.getD x.1 default).shape.maskRows = 1)
    (hb : bookFits codes sent fresh (Bk.spentBy o p) (Bk.knownBy ord o p) = true) :
    SpenderClear (sendingPar codes sent) (rideOf sent fresh) Bk ord o p := by
  unfold bookFits at hb
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hb
  obtain ⟨⟨⟨-, hU⟩, hA⟩, hC⟩ := hb
  have hU' := unknown_of hU
  rcases hC with (h0 | hF) | hM
  · exact Or.inl (List.isEmpty_iff.1 h0)
  · rcases fresh with _ | ⟨n, k⟩
    · exact absurd hF (by simp)
    · simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        Bool.not_eq_true'] at hF
      obtain ⟨⟨hl, hin⟩, hk⟩ := hF
      exact Or.inr (Or.inr (fold_of_arm hf hw (hone (n, k) rfl) (by simp [foldAt]) hU' hl hin hk))
  · obtain ⟨n, hn, h⟩ := List.any_eq_true.1 hM
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hr, ha⟩, hin⟩, hk⟩ := h
    exact Or.inr (Or.inl (mask_of_arm hf hw (List.mem_range.1 hn) hr ha hU' (apart_of hA) hin hk))

/-- **The second law on the sender, at the core's own sender, at a book's two lists**: no premise on
the book beside the law's own hypothesis. -/
theorem sendFreshLaw_core_book {table : FreshTable} (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j) :
    SendFreshLaw (coreSender table) codes sent fresh (Bk.spentBy o p) (Bk.knownBy ord o p) :=
  fun hf hone hb => sendFreshLaw_core hw htab (within_of_bookFits hf hw hb)
    (clear_of_bookFits hf hw hone hb) hf hone hb

end

/-- **Wherever the proof file's description is returned: the second law at every place of the lot,
at every book and order.** As good as another writer's theorem on the shared sending's rows, which
Honest/K2/Law/AtCore.lean calls. Inside the law its own hypotheses stand as they were: the shared
sending's public test, "the table that rides has one row", `bookFits`, the seeds, the positions:
none is shown here. Where the lot has no place the sentence is idle. -/
theorem sendFresh_open {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ p ∈ switchPlaces Z Bs.G₀, ∀ (Bk : ProverCoinCounts) (ord : List Place) (q : Addr),
      SendFreshLaw (coreSender freshTable) p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
        (Bk.knownBy ord ⟨p.place, 0⟩ q) :=
  fun p hp _ _ _ => sendFreshLaw_core_book (noWord_open O p hp) fun _ _ _ _ _ => rfl

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.mem_eAll_ex
#print axioms ProofFile.Honest.K2.apart_e
#print axioms ProofFile.Honest.K2.inside_e
#print axioms ProofFile.Honest.K2.inside_noF
#print axioms ProofFile.Honest.K2.unknown_of
#print axioms ProofFile.Honest.K2.apart_of
#print axioms ProofFile.Honest.K2.tail_lt
#print axioms ProofFile.Honest.K2.free_form
#print axioms ProofFile.Honest.K2.free_below
#print axioms ProofFile.Honest.K2.pad_bounds
#print axioms ProofFile.Honest.K2.sendingPar_codes
#print axioms ProofFile.Honest.K2.main_sampled
#print axioms ProofFile.Honest.K2.main_none
#print axioms ProofFile.Honest.K2.dueMsg_e
#print axioms ProofFile.Honest.K2.maskStart_eq
#print axioms ProofFile.Honest.K2.entriesFrom_shared
#print axioms ProofFile.Honest.K2.freshStart_shared
#print axioms ProofFile.Honest.K2.wholeEnd_shared
#print axioms ProofFile.Honest.K2.one_message
#print axioms ProofFile.Honest.K2.dueBefore_succ_e
#print axioms ProofFile.Honest.K2.mask_plain
#print axioms ProofFile.Honest.K2.free_in
#print axioms ProofFile.Honest.K2.within_of_bookFits
#print axioms ProofFile.Honest.K2.fold_of_arm
#print axioms ProofFile.Honest.K2.mask_of_arm
#print axioms ProofFile.Honest.K2.clear_of_bookFits
#print axioms ProofFile.Honest.K2.sendFreshLaw_core_book
#print axioms ProofFile.Honest.K2.sendFresh_open
