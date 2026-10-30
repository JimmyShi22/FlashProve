-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/LendsRow.lean: definitions with code, and statements with their
proofs. NO KIND IS NAMED. By the writers of the feed-forward layers' own rounds (sub-protocol K4).
It stands over Honest/Frame.lean alone.

What is here. WHETHER THE BOOK's LENDING RETURNS IS A FUNCTION OF PUBLIC DATA. The frame's
`lendRow` (Honest/Frame.lean) hands the parts of a row their coins off a run's coins, or refuses.
`lendsRow B ch a ps` is a Bool of the book, the chain's number, the place and the parts' stated
counts: `lendRow`'s own text at part number 0, with each cut of coins replaced by the test on
counts by which `Cs.cut` returns, and the count at an address read off the book alone. AT EVERY
RUN's COINS `lendRow` RETURNS JUST WHERE THAT BOOL IS true. So a text that answers JUST WHERE
`lendRow` returns, inside a fence of its own on public data, at parts whose three counts are made
of public data, answers or says «none» by that Bool and that fence.

  `cutFits`, `cutFits_is`   the test on counts; a cut returns just where it accepts.
  `findDue`, `lookDue`, `find_dueIs`, `look_dueIs`   the count at an address, off the book:
      `Coins.look`'s text without the coins; it is the count of what `Coins.look` hands, in all
      three chains.
  `lendsRuns`, `lendsPart`, `lendsRowAt`   the texts of `lend`, `lendPart`, `lendRow`, on counts.
      Their letter due is the count at an address.
  `lend_ok_iff`, `lendPart_ok_iff`, `lendRow_ok_iff`   each returns just where its Bool is true, AT
      ANY look, with due := the counts of that look.
  `lendsRow`   **the Bool**
  `lendsRow_iff`, `lendRow_isSome`   **`lendRow` returns at a run's coins ↔ the Bool is true; the
      same as an equation of Bools.**
  `lendRow_refuses`   a tooth: where the Bool is false `lendRow` refuses at every run's coins.
  `lendsRuns_short`, `lendsRuns_short_tail`, `lendsRuns_short_at`, `lendsPart_short`,
      `lendsPart_short_spends`, `lendsPart_short_carries`, `lendsRowAt_short`, `lendsRow_short`  
      what makes a Bool false: an entry anywhere in a list that reaches beyond its owner's count; a
      part that takes more than stands at its address, or whose runs are not lent; such a part
      anywhere in the row.
  `lendRow_refuses_short`   **these joined: a short book makes `lendRow` refuse, at every run's
      coins.** Two evaluations at a book of one row: it lends; with one coin fewer it does not.
  `lendsPart_counts`, `lendsRowAt_alike`, `lendsRow_alike`, `lendsRowAt_map`, `lendsRow_map`   the
      Bool reads of a part its takes, spends and carries alone: two rows whose parts agree one by
      one in these three lend alike; so a row whose parts are seated by a function that keeps them
      lends as the unseated row does.

The three proofs follow the case splits of `lend_any`, `lendPart_any`, `lendRow_any`
(Honest/Law/ReadyAny.lean, which is not imported), which have that a return at one look gives a
return at another look of the same counts. Two small laws on `Except` are typed here anew,
privately; their like stands in Honest/Law/Play.lean. Three more helpers are private.

`lendsPart` ASKS THE PART's COUNT AT TWO TABLES, as `lendPart` does: `dueAt rows a` looks the
address up in the CHAIN's own table; `due a` is the first row at that address among the tables that
the chain MAY BE HANDED (in the second chain: first, then shared, then second). The two agree where
the address stands in no table but the chain's own: that is the matter of the first and second test
of `ProverCoinCounts.clauses`, not of this file.

Not shown here. THAT ANY BOOK PASSES THE TEST. WHICH coins are lent. Whether two entries of the
book name one coin: the book's own tests speak of that (`ProverCoinCounts.clauses`). Anything on the further
tests that `chainSteps` asks of the book at a place (the cuts, the rounds, rows beyond the parts).
Nothing on what a text shows where it answers. Nothing on soundness, on completeness or on any
other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

variable {V W X V' W' X' : Type}

private theorem bindOk {ε α β : Type} {a : Except ε α} {f : α → Except ε β} {y : β}
    (h : a.bind f = .ok y) : ∃ x, a = .ok x ∧ f x = .ok y := by
  cases a with
  | error e => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem mapOk {ε α β : Type} {a : Except ε α} {f : α → β} {y : β}
    (h : a.map f = .ok y) : ∃ x, a = .ok x ∧ f x = y := by
  cases a with
  | error e => cases h
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

/-! ## 1 A cut, and the count at an address -/

/-- The test on counts by which `Cs.cut` returns: n coins from number a on are among d. -/
def cutFits (d a n : Due) : Bool := decide (a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e)

/-- A cut returns just where the test on counts accepts. -/
theorem cutFits_is {d : Due} (c : Cs d) (a n : Due) : (c.cut a n).isSome = cutFits d a n := by
  unfold Cs.cut cutFits
  by_cases g : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e
  · rw [dif_pos g, decide_eq_true g]
    rfl
  · rw [dif_neg g, decide_eq_false g]
    rfl

/-- The count in the first row at an address: `Purse.find?`'s text without the coins. -/
def findDue : List (Addr × Due) → Addr → Option Due
  | [], _ => none
  | r :: l, a => if r.1 == a then some r.2 else findDue l a

/-- The count of what `Purse.find?` finds is the table's. -/
theorem find_dueIs : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    (Purse.find? l c a).map (·.1) = findDue l a
  | [], _, _ => rfl
  | r :: l, c, a => by
    unfold Purse.find? findDue
    by_cases h : (r.1 == a) = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      exact find_dueIs l c.2 a

/-- **The count at an address that the chain number ch may be handed**: `Coins.look`'s text without
the coins. No coin where the address has no row there. -/
def lookDue (B : ProverCoinCounts) (ch : Nat) (a : Addr) : Due :=
  if ch == 0 then (findDue B.first a).getD ⟨0, 0⟩
  else if ch == 1 then (findDue B.shared a).getD ⟨0, 0⟩
  else (((findDue B.first a).or (findDue B.shared a)).or (findDue B.second a)).getD ⟨0, 0⟩

private theorem getD_dueIs {o : Option ((d : Due) × Cs d)} {o' : Option Due}
    (h : o.map (·.1) = o') :
    (o.getD ⟨⟨0, 0⟩, Cs.empty⟩).1 = o'.getD ⟨0, 0⟩ := by
  subst h
  cases o <;> rfl

private theorem or_dueIs {a b : Option ((d : Due) × Cs d)} {a' b' : Option Due}
    (h : a.map (·.1) = a') (g : b.map (·.1) = b') : (a.or b).map (·.1) = a'.or b' := by
  subst h
  subst g
  cases a <;> rfl

/-- **The count of what `Coins.look` hands is the book's**, at every run's coins. -/
theorem look_dueIs {B : ProverCoinCounts} (c : Coins B) (ch : Nat) (a : Addr) :
    (c.look ch a).1 = lookDue B ch a := by
  unfold Coins.look sharedLook lookDue
  simp only
  by_cases h0 : (ch == 0) = true
  · rw [if_pos h0, if_pos h0]
    exact getD_dueIs (find_dueIs _ _ a)
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : (ch == 1) = true
    · rw [if_pos h1, if_pos h1]
      exact getD_dueIs (find_dueIs _ _ a)
    · rw [if_neg h1, if_neg h1]
      exact getD_dueIs
        (or_dueIs (or_dueIs (find_dueIs _ _ a) (find_dueIs _ _ a)) (find_dueIs _ _ a))

/-- «Not equal», by the test of equality. -/
private theorem bne_iff_not {α : Type} [BEq α] (a b : α) : (a != b) = true ↔ ¬ (a == b) = true := by
  show (!(a == b)) = true ↔ _
  cases (a == b) <;> simp

/-! ## 2 The three texts, on counts -/

/-- `lend`'s text on counts. due: the count at an address. -/
def lendsRuns (due : Addr → Due) : List (String × Due) → List Ahead → Bool
  | [], [] => true
  | d :: ds, a :: l =>
    a.name == d.1 && a.count == d.2 && cutFits (due a.owner) a.start d.2 && lendsRuns due ds l
  | _, _ => false

/-- `lend` returns just where its text on counts accepts, at any look. -/
theorem lend_ok_iff (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (l : List Ahead), (∃ y, lend look ds l = .ok y) ↔ lendsRuns (fun o => (look o).1) ds l = true
  | [], [] => ⟨fun _ => rfl, fun _ => ⟨(), rfl⟩⟩
  | [], _ :: _ => ⟨fun ⟨_, h⟩ => by simp [lend] at h, fun h => by simp [lendsRuns] at h⟩
  | _ :: _, [] => ⟨fun ⟨_, h⟩ => by simp [lend] at h, fun h => by simp [lendsRuns] at h⟩
  | d :: ds, a :: l => by
    have ih := lend_ok_iff look ds l
    have ec := cutFits_is (look a.owner).2 a.start d.2
    unfold lend lendsRuns
    simp only [Bool.and_eq_true]
    by_cases h1 : (a.name == d.1) = true
    · rw [if_neg fun h => (bne_iff_not _ _).1 h h1]
      by_cases h2 : (a.count == d.2) = true
      · rw [if_neg fun h => (bne_iff_not _ _).1 h h2]
        cases hc : (look a.owner).2.cut a.start d.2 with
        | none =>
          rw [hc] at ec
          constructor
          · rintro ⟨_, h⟩
            cases h
          · rintro ⟨⟨_, g⟩, _⟩
            rw [← ec] at g
            cases g
        | some x =>
          rw [hc] at ec
          constructor
          · rintro ⟨y, h⟩
            obtain ⟨w, hw, -⟩ := mapOk h
            exact ⟨⟨⟨h1, h2⟩, ec.symm⟩, ih.1 ⟨w, hw⟩⟩
          · rintro ⟨_, g⟩
            obtain ⟨w, hw⟩ := ih.2 g
            show ∃ y, ((lend look ds l).map fun y => (x, y)) = .ok y
            rw [hw]
            exact ⟨_, rfl⟩
      · rw [if_pos ((bne_iff_not _ _).2 h2)]
        constructor
        · rintro ⟨_, h⟩
          cases h
        · rintro ⟨⟨⟨_, g⟩, _⟩, _⟩
          exact absurd g h2
    · rw [if_pos ((bne_iff_not _ _).2 h1)]
      constructor
      · rintro ⟨_, h⟩
        cases h
      · rintro ⟨⟨⟨g, _⟩, _⟩, _⟩
        exact absurd g h1

/-- `lendPart`'s text on counts. rows: the book's table for the chain; due: the count at an
address. -/
def lendsPart (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Addr)
    (p : Part V W X) : Bool :=
  p.takes == dueAt rows a && cutFits (due a) ⟨0, 0⟩ p.takes &&
    lendsRuns due p.spends ((B.ahead.filter fun e => e.spender == a).filter (·.once)) &&
    lendsRuns due p.carries ((B.ahead.filter fun e => e.spender == a).filter (!·.once))

/-- `lendPart` returns just where its text on counts accepts, at any look. -/
theorem lendPart_ok_iff (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) :
    (∃ y, lendPart B rows look a p = .ok y) ↔
      lendsPart B rows (fun o => (look o).1) a p = true := by
  have i1 := lend_ok_iff look p.spends ((B.ahead.filter fun e => e.spender == a).filter (·.once))
  have i2 := lend_ok_iff look p.carries
    ((B.ahead.filter fun e => e.spender == a).filter (!·.once))
  have ec := cutFits_is (look a).2 ⟨0, 0⟩ p.takes
  unfold lendPart lendsPart
  simp only [Bool.and_eq_true]
  by_cases h1 : (p.takes == dueAt rows a) = true
  · rw [if_neg fun h => (bne_iff_not _ _).1 h h1]
    cases hc : (look a).2.cut ⟨0, 0⟩ p.takes with
    | none =>
      rw [hc] at ec
      constructor
      · rintro ⟨_, h⟩
        cases h
      · rintro ⟨⟨⟨_, g⟩, _⟩, _⟩
        rw [← ec] at g
        cases g
    | some x =>
      rw [hc] at ec
      constructor
      · rintro ⟨y, h⟩
        obtain ⟨sp, hsp, h'⟩ := bindOk h
        obtain ⟨ca, hca, -⟩ := mapOk h'
        exact ⟨⟨⟨h1, ec.symm⟩, i1.1 ⟨sp, hsp⟩⟩, i2.1 ⟨ca, hca⟩⟩
      · rintro ⟨⟨_, g1⟩, g2⟩
        obtain ⟨sp, hsp⟩ := i1.2 g1
        obtain ⟨ca, hca⟩ := i2.2 g2
        show ∃ y, ((lend look p.spends _).bind fun sp =>
          (lend look p.carries _).map fun ca => (x, sp, ca)) = .ok y
        rw [hsp]
        show ∃ y, ((lend look p.carries _).map fun ca => (x, sp, ca)) = .ok y
        rw [hca]
        exact ⟨_, rfl⟩
  · rw [if_pos ((bne_iff_not _ _).2 h1)]
    constructor
    · rintro ⟨_, h⟩
      cases h
    · rintro ⟨⟨⟨g, _⟩, _⟩, _⟩
      exact absurd g h1

/-- `lendRow`'s text on counts, from the part number j on. -/
def lendsRowAt (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place) :
    List (Part V W X) → Nat → Bool
  | [], _ => true
  | p :: ps, j => lendsPart B rows due ⟨a, j⟩ p && lendsRowAt B rows due a ps (j + 1)

/-- `lendRow` returns just where its text on counts accepts, at any look. -/
theorem lendRow_ok_iff (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) : ∀ (ps : List (Part V W X)) (j : Nat),
    (∃ y, lendRow B rows look a ps j = .ok y) ↔
      lendsRowAt B rows (fun o => (look o).1) a ps j = true
  | [], _ => ⟨fun _ => rfl, fun _ => ⟨(), rfl⟩⟩
  | p :: ps, j => by
    have ip := lendPart_ok_iff B rows look ⟨a, j⟩ p
    have ih := lendRow_ok_iff B rows look a ps (j + 1)
    unfold lendRow lendsRowAt
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨y, h⟩
      obtain ⟨c, hc, h'⟩ := bindOk h
      obtain ⟨r, hr, -⟩ := mapOk h'
      cases hp : lendPart B rows look ⟨a, j⟩ p with
      | error e =>
        rw [hp] at hc
        cases hc
      | ok c₀ => exact ⟨ip.1 ⟨c₀, hp⟩, ih.1 ⟨r, hr⟩⟩
    · rintro ⟨g1, g2⟩
      obtain ⟨c, hc⟩ := ip.2 g1
      obtain ⟨r, hr⟩ := ih.2 g2
      rw [hc]
      show ∃ y, ((lendRow B rows look a ps (j + 1)).map fun r => (c, r)) = .ok y
      rw [hr]
      exact ⟨_, rfl⟩

/-! ## 3 The Bool, and the two forms of the law -/

/-- **WHETHER THE BOOK LENDS THE ROW OF PARTS ps AT THE PLACE a, IN THE CHAIN NUMBER ch.** A Bool of
the book, the chain's number, the place and the parts' stated counts: no coins, no input. This is a
definition; it claims nothing. -/
def lendsRow (B : ProverCoinCounts) (ch : Nat) (a : Place) (ps : List (Part V W X)) : Bool :=
  lendsRowAt B (B.rowsOf ch) (lookDue B ch) a ps 0

/-- **AT EVERY RUN's COINS `lendRow` RETURNS JUST WHERE THE BOOL IS true.** No hypothesis. -/
theorem lendsRow_iff {B : ProverCoinCounts} (k : Coins B) (ch : Nat) (a : Place) (ps : List (Part V W X)) :
    (∃ c, lendRow B (B.rowsOf ch) (k.look ch) a ps 0 = .ok c) ↔ lendsRow B ch a ps = true := by
  have e : (fun o => (k.look ch o).1) = lookDue B ch := funext (look_dueIs k ch)
  have i := lendRow_ok_iff B (B.rowsOf ch) (k.look ch) a ps 0
  rw [e] at i
  exact i

/-- **The same as an equation of Bools.** No hypothesis. -/
theorem lendRow_isSome {B : ProverCoinCounts} (k : Coins B) (ch : Nat) (a : Place)
    (ps : List (Part V W X)) :
    (lendRow B (B.rowsOf ch) (k.look ch) a ps 0).toOption.isSome = lendsRow B ch a ps := by
  cases h : lendRow B (B.rowsOf ch) (k.look ch) a ps 0 with
  | error e =>
    have n : ¬ lendsRow B ch a ps = true := fun g => by
      obtain ⟨c, hc⟩ := (lendsRow_iff k ch a ps).2 g
      rw [h] at hc
      cases hc
    show false = _
    exact (Bool.eq_false_iff.2 n).symm
  | ok c =>
    show true = _
    exact ((lendsRow_iff k ch a ps).1 ⟨c, h⟩).symm

/-! ## 4 Teeth -/

/-- **WHERE THE BOOL IS false `lendRow` REFUSES, AT EVERY RUN's COINS.** CONDITIONAL on h. -/
theorem lendRow_refuses {B : ProverCoinCounts} (k : Coins B) (ch : Nat) (a : Place) (ps : List (Part V W X))
    (h : lendsRow B ch a ps = false) :
    ∃ e, lendRow B (B.rowsOf ch) (k.look ch) a ps 0 = .error e := by
  cases hl : lendRow B (B.rowsOf ch) (k.look ch) a ps 0 with
  | error e => exact ⟨e, rfl⟩
  | ok c =>
    have g := (lendsRow_iff k ch a ps).1 ⟨c, hl⟩
    rw [h] at g
    cases g

/-- An entry that reaches beyond its owner's count is not lent. CONDITIONAL on h. -/
theorem lendsRuns_short (due : Addr → Due) (d : String × Due) (ds : List (String × Due))
    (a : Ahead) (l : List Ahead) (h : cutFits (due a.owner) a.start d.2 = false) :
    lendsRuns due (d :: ds) (a :: l) = false := by
  unfold lendsRuns
  rw [h, Bool.and_false, Bool.false_and]

/-- A part that takes more coins than stand at its address is not lent. CONDITIONAL on h. -/
theorem lendsPart_short (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Addr)
    (p : Part V W X) (h : cutFits (due a) ⟨0, 0⟩ p.takes = false) :
    lendsPart B rows due a p = false := by
  unfold lendsPart
  rw [h, Bool.and_false, Bool.false_and, Bool.false_and]

/-- Where the rest of the lists is not lent, the whole is not. CONDITIONAL on h. -/
theorem lendsRuns_short_tail (due : Addr → Due) (d : String × Due) (ds : List (String × Due))
    (a : Ahead) (l : List Ahead) (h : lendsRuns due ds l = false) :
    lendsRuns due (d :: ds) (a :: l) = false := by
  unfold lendsRuns
  rw [h, Bool.and_false]

/-- **An entry ANYWHERE in the list that reaches beyond its owner's count: the list is not lent.**
i: its number, from 0. CONDITIONAL on the three hypotheses. -/
theorem lendsRuns_short_at (due : Addr → Due) : ∀ (ds : List (String × Due)) (l : List Ahead)
    (i : Nat) (d : String × Due) (a : Ahead), ds[i]? = some d → l[i]? = some a →
    cutFits (due a.owner) a.start d.2 = false → lendsRuns due ds l = false
  | [], _, _, _, _, hd, _, _ => by simp at hd
  | _ :: _, [], _, _, _, _, ha, _ => by simp at ha
  | d0 :: ds, a0 :: l, 0, d, a, hd, ha, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hd ha
    subst hd
    subst ha
    exact lendsRuns_short due d0 ds a0 l h
  | d0 :: ds, a0 :: l, i + 1, d, a, hd, ha, h => by
    simp only [List.getElem?_cons_succ] at hd ha
    exact lendsRuns_short_tail due d0 ds a0 l (lendsRuns_short_at due ds l i d a hd ha h)

/-- A part whose spent runs are not lent is not lent. CONDITIONAL on h. -/
theorem lendsPart_short_spends (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due)
    (a : Addr) (p : Part V W X)
    (h : lendsRuns due p.spends ((B.ahead.filter fun x => x.spender == a).filter (·.once)) =
      false) :
    lendsPart B rows due a p = false := by
  unfold lendsPart
  rw [h, Bool.and_false, Bool.false_and]

/-- A part whose carried runs are not lent is not lent. CONDITIONAL on h. -/
theorem lendsPart_short_carries (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due)
    (a : Addr) (p : Part V W X)
    (h : lendsRuns due p.carries ((B.ahead.filter fun x => x.spender == a).filter (!·.once)) =
      false) :
    lendsPart B rows due a p = false := by
  unfold lendsPart
  rw [h, Bool.and_false]

/-- **A part ANYWHERE in the row that is not lent: the row is not lent.** i: its number in the list,
from 0. CONDITIONAL on the two hypotheses. -/
theorem lendsRowAt_short (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place) :
    ∀ (ps : List (Part V W X)) (j i : Nat) (p : Part V W X), ps[i]? = some p →
    lendsPart B rows due ⟨a, j + i⟩ p = false → lendsRowAt B rows due a ps j = false
  | [], _, _, _, hp, _ => by simp at hp
  | q :: ps, j, 0, p, hp, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    have h' : lendsPart B rows due ⟨a, j⟩ q = false := h
    show (lendsPart B rows due ⟨a, j⟩ q && lendsRowAt B rows due a ps (j + 1)) = false
    rw [h', Bool.false_and]
  | q :: ps, j, i + 1, p, hp, h => by
    simp only [List.getElem?_cons_succ] at hp
    have e : j + 1 + i = j + (i + 1) := by omega
    have h' : lendsPart B rows due ⟨a, j + 1 + i⟩ p = false := by
      rw [e]
      exact h
    show (lendsPart B rows due ⟨a, j⟩ q && lendsRowAt B rows due a ps (j + 1)) = false
    rw [lendsRowAt_short B rows due a ps (j + 1) i p hp h', Bool.and_false]

/-- The like for the Bool. CONDITIONAL on hp and h. -/
theorem lendsRow_short (B : ProverCoinCounts) (ch : Nat) (a : Place) {ps : List (Part V W X)} {i : Nat}
    {p : Part V W X} (hp : ps[i]? = some p)
    (h : lendsPart B (B.rowsOf ch) (lookDue B ch) ⟨a, i⟩ p = false) :
    lendsRow B ch a ps = false := by
  have h' : lendsPart B (B.rowsOf ch) (lookDue B ch) ⟨a, 0 + i⟩ p = false := by
    rw [Nat.zero_add]
    exact h
  exact lendsRowAt_short B (B.rowsOf ch) (lookDue B ch) a ps 0 i p hp h'

/-- **A SHORT BOOK MAKES `lendRow` REFUSE, AT EVERY RUN's COINS**: where run number n of what part
number i of the row spends is typed at a count d.2 that, from the entry's start on, reaches beyond
the count that the book has at the entry's owner. It is stated for the runs that are SPENT; the like
for the runs that are carried follows from `lendsPart_short_carries` by the same three steps and has
no name. CONDITIONAL on hp, hd, he and h. -/
theorem lendRow_refuses_short {B : ProverCoinCounts} (k : Coins B) (ch : Nat) (a : Place)
    (ps : List (Part V W X)) {i n : Nat} {p : Part V W X} {d : String × Due} {e : Ahead}
    (hp : ps[i]? = some p) (hd : p.spends[n]? = some d)
    (he : ((B.ahead.filter fun x => x.spender == ⟨a, i⟩).filter (·.once))[n]? = some e)
    (h : cutFits (lookDue B ch e.owner) e.start d.2 = false) :
    ∃ er, lendRow B (B.rowsOf ch) (k.look ch) a ps 0 = .error er :=
  lendRow_refuses k ch a ps (lendsRow_short B ch a hp
    (lendsPart_short_spends B (B.rowsOf ch) (lookDue B ch) ⟨a, i⟩ p
      (lendsRuns_short_at (lookDue B ch) _ _ n d e hd he h)))

/-- A part without moves that takes no coin and spends one run of two. For the two evaluations. -/
private def toyPart : Part Unit Unit Unit :=
  { takes := ⟨0, 0⟩, spends := [("run", ⟨0, 2⟩)], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩, moves := [] }

/-- A book of one row: the part number 1 of one place has n coins; one entry hands the part number
0 two of them, from coin number 1 on. For the two evaluations. -/
private def toyBook (n : Nat) : ProverCoinCounts :=
  { first := [(⟨default, 1⟩, ⟨0, n⟩)], shared := [], second := []
    ahead := [⟨"run", ⟨default, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨default, 0⟩, true⟩], cuts := [] }

/- With three coins the book lends; WITH ONE COIN FEWER IT DOES NOT. By Lean's evaluator: no
proof. -/
#guard lendsRow (toyBook 3) 0 default [toyPart]
#guard !lendsRow (toyBook 2) 0 default [toyPart]

/-! ## 5 It reads of a part its three counts alone -/

/-- Two parts of the same takes, spends and carries are lent alike. CONDITIONAL on h1, h2, h3. -/
theorem lendsPart_counts (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Addr)
    {p : Part V W X} {q : Part V' W' X'} (h1 : q.takes = p.takes) (h2 : q.spends = p.spends)
    (h3 : q.carries = p.carries) : lendsPart B rows due a q = lendsPart B rows due a p := by
  unfold lendsPart
  rw [h1, h2, h3]

/-- **Two rows whose parts agree one by one in the three counts lend alike**, from any part number
on. CONDITIONAL on that agreement. -/
theorem lendsRowAt_alike (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place) :
    ∀ (ps : List (Part V W X)) (qs : List (Part V' W' X')) (j : Nat),
    List.Forall₂ (fun p q => q.takes = p.takes ∧ q.spends = p.spends ∧ q.carries = p.carries)
      ps qs →
    lendsRowAt B rows due a qs j = lendsRowAt B rows due a ps j
  | [], [], _, _ => rfl
  | p :: ps, q :: qs, j, h => by
    obtain ⟨hpq, hr⟩ := List.forall₂_cons.1 h
    show (lendsPart B rows due ⟨a, j⟩ q && lendsRowAt B rows due a qs (j + 1)) =
      (lendsPart B rows due ⟨a, j⟩ p && lendsRowAt B rows due a ps (j + 1))
    rw [lendsRowAt_alike B rows due a ps qs (j + 1) hr,
      lendsPart_counts B rows due ⟨a, j⟩ hpq.1 hpq.2.1 hpq.2.2]
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- The like for the Bool. CONDITIONAL on h. -/
theorem lendsRow_alike (B : ProverCoinCounts) (ch : Nat) (a : Place) {ps : List (Part V W X)}
    {qs : List (Part V' W' X')}
    (h : List.Forall₂
      (fun p q => q.takes = p.takes ∧ q.spends = p.spends ∧ q.carries = p.carries) ps qs) :
    lendsRow B ch a qs = lendsRow B ch a ps :=
  lendsRowAt_alike B (B.rowsOf ch) (lookDue B ch) a ps qs 0 h

/-- A row whose parts are seated by a function that keeps the three counts lends as the unseated
row does. CONDITIONAL on hf. -/
theorem lendsRowAt_map (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Place)
    (f : Part V W X → Part V' W' X')
    (hf : ∀ p, (f p).takes = p.takes ∧ (f p).spends = p.spends ∧ (f p).carries = p.carries) :
    ∀ (ps : List (Part V W X)) (j : Nat),
    lendsRowAt B rows due a (ps.map f) j = lendsRowAt B rows due a ps j
  | [], _ => rfl
  | p :: ps, j => by
    show (lendsPart B rows due ⟨a, j⟩ (f p) && lendsRowAt B rows due a (ps.map f) (j + 1)) =
      (lendsPart B rows due ⟨a, j⟩ p && lendsRowAt B rows due a ps (j + 1))
    rw [lendsRowAt_map B rows due a f hf ps (j + 1),
      lendsPart_counts B rows due ⟨a, j⟩ (hf p).1 (hf p).2.1 (hf p).2.2]

/-- The like for the Bool. CONDITIONAL on hf. -/
theorem lendsRow_map (B : ProverCoinCounts) (ch : Nat) (a : Place) (f : Part V W X → Part V' W' X')
    (hf : ∀ p, (f p).takes = p.takes ∧ (f p).spends = p.spends ∧ (f p).carries = p.carries)
    (ps : List (Part V W X)) : lendsRow B ch a (ps.map f) = lendsRow B ch a ps :=
  lendsRowAt_map B (B.rowsOf ch) (lookDue B ch) a f hf ps 0

end ProofFile.Honest

#print axioms ProofFile.Honest.cutFits_is
#print axioms ProofFile.Honest.find_dueIs
#print axioms ProofFile.Honest.look_dueIs
#print axioms ProofFile.Honest.lend_ok_iff
#print axioms ProofFile.Honest.lendPart_ok_iff
#print axioms ProofFile.Honest.lendRow_ok_iff
#print axioms ProofFile.Honest.lendsRow_iff
#print axioms ProofFile.Honest.lendRow_isSome
#print axioms ProofFile.Honest.lendRow_refuses
#print axioms ProofFile.Honest.lendsRuns_short
#print axioms ProofFile.Honest.lendsPart_short
#print axioms ProofFile.Honest.lendsRuns_short_tail
#print axioms ProofFile.Honest.lendsRuns_short_at
#print axioms ProofFile.Honest.lendsPart_short_spends
#print axioms ProofFile.Honest.lendsPart_short_carries
#print axioms ProofFile.Honest.lendsRowAt_short
#print axioms ProofFile.Honest.lendsRow_short
#print axioms ProofFile.Honest.lendRow_refuses_short
#print axioms ProofFile.Honest.lendsPart_counts
#print axioms ProofFile.Honest.lendsRowAt_alike
#print axioms ProofFile.Honest.lendsRow_alike
#print axioms ProofFile.Honest.lendsRowAt_map
#print axioms ProofFile.Honest.lendsRow_map
