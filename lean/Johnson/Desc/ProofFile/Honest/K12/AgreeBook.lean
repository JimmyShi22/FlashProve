-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AgreeBook.lean: the two parts' readers agree (`Agree`,
CoinsAgree.lean in this folder) at the coins that the frame lends, from equations on the book's
entries, where the first fold's fresh table has come earlier. As theorems: `agree_came` takes the
equations as hypotheses, and `agree_of_ties` takes them as one test on the book (`tiesB`); both have
three more hypotheses, listed below. General in the book and in the run's coins, which are not
looked into. The frame hands a part each stretch as a cut of its entry's owner's coins from the
entry's start on (`lend`, Johnson/Desc/ProofFile/Honest/Frame.lean): so two entries with one owner
and one start hand over the same coins as far as both reach. Theorems and one definition.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Coins (`Cs d`, the frame) are
elements of the base field and of the extension field, as many as the count d states (`Due`: fields
`f` and `e`). A cut (`Cs.cut`) is the n coins from number a on, in each field; it is `none` if they
are not all there. A stretch (`Stretch`, Coins.lean in this folder) is a run of coins, read by
number: `stretchOf` makes one of a `Cs`, with 0 beyond the count, and `stretches ds y n` is stretch
number n of a list. A part (`Part`, the frame) is the prover's side of some rounds in a row; its
address (`Addr`) is a place (`Place`: where a sub-protocol is in a description) and the part's
number there, from 0. A book Bk (`ProverCoinCounts`) is public data. An entry of it (`Ahead`) is a block of its
owner's coins, from `start` on and `count` long, that one other part, its spender, is given too,
marked as spent or as carried. `spentE Bk a` and `carryE Bk a`
(Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean) list the entries whose spender is the part at the
address a, those marked as spent and those marked as carried, in the book's order. look gives the
coins at an address: the run's coins enter by this free parameter only. rows, a table of the parts'
own counts, is a free parameter too. A job J (`TestJob`, Test.lean in this folder) is what a caller
supplies for its proximity test. Here it is written out as ⟨p, ms, some f, r, ro, tr⟩: p has the
test's place `p.place`; ms lists the members, the group's oracle messages; `some f` is the field
`fresh` and says that the first fold's fresh table has come earlier, f being its sender's address
and the message's number there; r, ro and tr are the fields `rec₀`, `rows₀` and `trees₀`. All six
are free parameters. The first part is `firstPart J`, at part number 0 of the place, and the second
is `restPart J`, at part number 1, which the Lean text writes 0 + 1 (both Parts.lean in this
folder). The row of the two parts is the list of them, and c (`RowCoins`, the frame) is what
`lendRow` (the frame) returns for it. A part's reader makes a family of coins (`TestCoins`,
Test.lean) of what the part is given: `firstRd J` (HalfSteps.lean in this folder) and `restCoins J`
(Parts.lean). w is the prover's input, and a front fr (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean) is what the job's functions are given of the run before the
test. The first stage is `J.s₀`, the first of the list `J.p.nums.stages` (a stage of zeros where the
list is empty); k is its field, and h and g are those of `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean)
at it, where g is k - h. The coefficients are those of the first fold's hiding polynomial; `hideAt`,
by `byName` (both Coins.lean), indexes them by the library's type `HIdx`. The stretch that the first
part spends counts 2k + 1 coins of the extension field (`spentRun`, Parts.lean); the fresh table's
stretch, which the second part carries, counts `dueFresh` (Coins.lean) of them: 2k + 1 plus the
entries of the table's rows' tails (`freshRun`, Parts.lean). The first stage's message is `μOf`
(Johnson/Prover/Link/BodyState.lean) at the first stage's state.

  `agree_came`: the row of the two parts is lent its coins · the entry by which the first part
    spends the coefficients and the entry by which the second carries the fresh table's stretch have
    one owner and, among the coins of the extension field, one start · for each member the two
    parts' entries have one owner, one start and one count · the first stage's message reads of the
    members' stretches those of the job's members alone · k = h + g at the first stage ⟹ `Agree`.
    The conclusion is `Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1)`
  `agree_of_ties`: the same conclusion, with `tiesB Bk p.place ms.length = true` in place of the
    second and the third of these five hypotheses; the other three are the same
  `tiesB Bk pl n`: a definition: these equations on the book's entries as one test that returns a
    `Bool`, of the book, the place and the number of members. Four tests, all of which have to pass:
    `spentE Bk ⟨pl, 0⟩` has an entry number 0; its `owner` and `start.e` are those of entry number n
    of `carryE Bk ⟨pl, 1⟩`; `carryE Bk ⟨pl, 0⟩` has at least n entries; its first n entries and the
    first n of `carryE Bk ⟨pl, 1⟩` have, one by one, the same `owner`, `start` and `count`
  `lend_stretch`: what `lend` hands over for its entry number n: a cut at the entry's own count; and
    that count is the one that the part states there. Where `lend look ds l` returns y and entry
    number n of l is a: element number n of ds has the count `a.count`; the cut of the coins
    `(look a.owner).2` at `a.start` and `a.count` is there; and `stretches ds y n` is its stretch
  `cut_e`: a cut's coin number i is the owner's coin number start + i. Stated for the coins of the
    extension field only, at i below the cut's count, both sides read by `stretchOf`
  `stretch_tie`: one owner, one start, one count: one stretch. For two entries with the same
    `owner`, `start` and `count`, both of whose cuts are there, the two cuts have the same stretch
  `byName_congr`, `hideAt_congr`: the coefficients under the library's names read the coins 0 ... 2k
    alone. `hideAt_congr`: `hideAt k` is the same at two functions that agree at every number below
    2k + 1. `byName_congr`: `byName k` is the same at two constants that are equal and two functions
    that agree at every variable from 1 to k and at the degrees 1 and 2

By what. `lendRow_cons_ok` (Johnson/Desc/ProofFile/Honest/Law/Rule/RowModel.lean) and `lendPart_ok`
(Johnson/Desc/ProofFile/Honest/Law/Rule/PartCell.lean) take `lendRow` apart: what a part is given
under `spends` and under `carries` is what `lend` returns at `spentE` and at `carryE` of its
address. For the field `hide` of `Agree`, `agree_came` calls `lend_stretch` at the two entries,
`cut_e` at each and `hideAt_congr`. For the field `table` it calls `lend_stretch` and `stretch_tie`
at each member and then the hypothesis hrows; `μOf` reads the fields `tabM` and `tabZ` of the state,
which `TestJob.first` (Test.lean) takes from `rows₀`. `lend_stretch` unfolds `lend` and calls
`exMap_ok` (Johnson/Desc/ProofFile/Honest/Law/Play.lean). `agree_of_ties` unfolds `tiesB` and calls
`agree_came`.

Hypotheses of `agree_came`. h: `lendRow Bk rows look p.place` at the list of the two parts, from
part number 0 on, returns c. hs, hf: e₁ is entry number 0 of `spentE Bk ⟨p.place, 0⟩`, and e₂ is
entry number `ms.length` of `carryE Bk ⟨p.place, 1⟩`. ho, hst: `e₁.owner = e₂.owner` and
`e₁.start.e = e₂.start.e`. hm: for every t below `ms.length`, `carryE Bk ⟨p.place, 0⟩` and
`carryE Bk ⟨p.place, 1⟩` each have an entry number t, and the two have the same `owner`, `start` and
`count`. hk: k = h + g at `J.s₀`; since g is k - h, this says that h is at most k. hrows: at this w
and fr, for any two functions mem and mem' that agree at every number below `ms.length`, `μOf` of
`ro w fr mem` is `μOf` of `ro w fr mem'`.

Why the first pair's starts are held among the extension field's coins alone. Both stretches hold
coins of that field alone, and a book may begin a spent stretch at no coin of the base field while
it begins a carried one behind all coins of the messages in front, of both fields. In the Lean text:
hst compares `e₁.start.e` with `e₂.start.e`, and the second test of `tiesB` does the same; neither
reads `start.f` of these two entries.

Limits.
- The equations on the book's entries and the clause on the job's rows are hypotheses. That
  `lendRow` returns is a hypothesis too, and so is k = h + g at the first stage. No book and no job
  is shown here to meet them. `agree_of_ties` is called in AgreeToy.lean [not in this library; so
  here read: not proved in this library] (`agree_toy`: at one small made-up book, at every value of
  its coins at which `lendRow` returns) and in Sim/OnFromLent.lean; no other file calls
  `agree_came`. `tiesB` is evaluated in AgreeToy.lean [not in this library; so here read: not tested
  in this library] and, at the key file's book, in TiesAtKey.lean; TiesAtKey.lean has a negative
  test by `#guard`.
- The case in which the first fold sends its own table is not treated. Both theorems are stated at
  `fresh := some f` only, and there the field `tails` of `Agree` is vacuous.
- `Agree` does not state that the two readers give the same family of coins: its fields compare
  `hideAt` at h + g, `μOf` at the first stage's state and, where `fresh` is `none`, the tails. See
  the limits of CoinsAgree.lean.
- The field `hide` is proved from this: under h, hs, hf, ho and hst, for every i below 2k + 1, coin
  number i of the stretch that the first part spends is coin number i of the fresh table's stretch,
  which the second part carries. So under these hypotheses the same coins of one owner are given to
  both parts.
- No hypothesis says that the owner of e₁ and e₂ is the sender that f names, or that a member's
  entries have that member's sender as their owner.
- Only the direction from `tiesB` to `Agree` is proved.
- Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.CoinsAgree
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

/-- A cut's coin number i is the owner's coin number start + i. c: the owner's coins. a: the start.
n: the cut's count. Stated for the coins of the extension field only, at i below `n.e`; both sides
are read by `stretchOf`. -/
theorem cut_e {d : Due} (c : Cs d) (a n : Due) (x : Cs n) (h : c.cut a n = some x) (i : ℕ)
    (hi : i < n.e) : (stretchOf x).e i = (stretchOf c).e (a.e + i) := by
  unfold Cs.cut at h
  split at h
  · rename_i hb
    cases h
    have h2 : a.e + i < d.e := by
      have := hb.2
      omega
    simp only [stretchOf, dif_pos hi, dif_pos h2]
  · cases h

/-- What `lend` hands over for its entry number n. Where `lend look ds l` returns y and entry number
n of l is a: element number n of ds has the count `a.count`, the cut of the coins `(look a.owner).2`
at `a.start` and `a.count` is there, and `stretches ds y n` is its stretch. -/
theorem lend_stretch (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y → ∀ (n : ℕ) (a : Ahead),
    l[n]? = some a → (ds[n]?).map (·.2) = some a.count ∧
      ∃ x : Cs a.count, (look a.owner).2.cut a.start a.count = some x ∧
        stretches ds y n = stretchOf x
  | [], [], _, _, n, a, hn => by simp at hn
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h
  | d :: ds, e :: l, y, h, n, a, hn => by
    simp only [lend] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hcount
    split at h
    · cases h
    rename_i x hx
    obtain ⟨y', hy, rfl⟩ := exMap_ok h
    cases n with
    | zero =>
      obtain rfl : e = a := Option.some.inj hn
      have hc : e.count = d.2 := by simpa using hcount
      obtain ⟨dn, dd⟩ := d
      obtain ⟨en, eo, es, ec, ep, eb⟩ := e
      obtain rfl : ec = dd := hc
      exact ⟨rfl, x, hx, rfl⟩
    | succ m => exact lend_stretch look ds l y' hy m a hn

/-- One owner, one start, one count: one stretch. For two entries a and a' with the same `owner`,
`start` and `count`, whose cuts x and x' are both there, `stretchOf x` is `stretchOf x'`. -/
theorem stretch_tie (look : Addr → (d : Due) × Cs d) (a a' : Ahead) (x : Cs a.count)
    (x' : Cs a'.count) (h : (look a.owner).2.cut a.start a.count = some x)
    (h' : (look a'.owner).2.cut a'.start a'.count = some x') (ho : a.owner = a'.owner)
    (hs : a.start = a'.start) (hc : a.count = a'.count) : stretchOf x = stretchOf x' := by
  obtain ⟨n, o, s, c, p, b⟩ := a
  obtain ⟨n', o', s', c', p', b'⟩ := a'
  obtain rfl : o = o' := ho
  obtain rfl : s = s' := hs
  obtain rfl : c = c' := hc
  rw [Option.some.inj (h.symm.trans h')]

theorem byName_congr : ∀ (k : ℕ) (u u' : ℕ → ℕ → GE) (u0 u0' : GE), u0 = u0' →
    (∀ l t, 1 ≤ l → l ≤ k → 1 ≤ t → t ≤ 2 → u l t = u' l t) → byName k u u0 = byName k u' u0'
  | 0, _, _, _, _, h0, _ => by
    funext _
    exact h0
  | k + 1, u, u', u0, u0', h0, h => by
    funext i
    cases i with
    | inl t =>
      have ht : t.val < 2 := t.isLt
      exact h 1 (t.val + 1) (le_refl _) (by omega) (by omega) (by omega)
    | inr i =>
      exact congrFun (byName_congr k (fun l t => u (l + 1) t) (fun l t => u' (l + 1) t) u0 u0' h0
        fun l t h1 h2 h3 h4 => h (l + 1) t (by omega) (by omega) h3 h4) i

/-- The coefficients under the library's names read the coins 0 ... 2k alone. `hideAt k` is the same
at two functions c and c' that agree at every number below 2k + 1. -/
theorem hideAt_congr (k : ℕ) (c c' : ℕ → GE) (h : ∀ i, i < 2 * k + 1 → c i = c' i) :
    hideAt k c = hideAt k c' := by
  unfold hideAt
  refine byName_congr k _ _ _ _ (h _ (by omega)) fun l t h1 h2 h3 h4 => ?_
  show c (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t) =
    c' (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)
  split <;> exact h _ (by omega)

/-- **The two readers agree at the coins that the frame lends.** Under hypotheses, which the file's
head lists one by one: that `lendRow` returns c (h), on the book's entries (hs, hf, ho, hst, hm), on
the first stage (hk) and on the job's rows (hrows). Stated only where the job's field `fresh` is
`some f`. -/
theorem agree_came (p : P12) (ms : List (Addr × ℕ × Due)) (f : Addr × ℕ) (r : W → Front X → T12)
    (ro : W → Front X → (ℕ → Stretch) → PS)
    (tr : W → Front X → (ℕ → Stretch) → PS → List Tree) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩])
    (h : lendRow Bk rows look p.place [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩] 0 = .ok c)
    (w : W) (fr : Front X) (e₁ e₂ : Ahead) (hs : (spentE Bk ⟨p.place, 0⟩)[0]? = some e₁)
    (hf : (carryE Bk ⟨p.place, 0 + 1⟩)[ms.length]? = some e₂) (ho : e₁.owner = e₂.owner)
    (hst : e₁.start.e = e₂.start.e)
    (hm : ∀ t, t < ms.length → ∃ a a', (carryE Bk ⟨p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (hk : (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩).k =
      (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)).h +
        (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)) (ro w fr mem) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)) (ro w fr mem')) :
    Agree ⟨p, ms, some f, r, ro, tr⟩ w fr (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)
      (firstRd ⟨p, ms, some f, r, ro, tr⟩ c.1) (restCoins ⟨p, ms, some f, r, ro, tr⟩ c.2.1) := by
  obtain ⟨l1, l2'⟩ := lendRow_cons_ok h
  obtain ⟨l2, -⟩ := lendRow_cons_ok l2'
  obtain ⟨-, s1, c1⟩ := lendPart_ok l1
  obtain ⟨-, -, c2⟩ := lendPart_ok l2
  refine ⟨?_, ?_, fun hn => by cases hn⟩
  · -- the coefficients
    obtain ⟨q1, x1, k1, z1⟩ := lend_stretch look _ _ _ s1 0 e₁ hs
    obtain ⟨q2, x2, k2, z2⟩ := lend_stretch look _ _ _ c2 ms.length e₂ hf
    have n1 : e₁.count = ⟨0, 2 * (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩).k + 1⟩ :=
      (Option.some.inj q1).symm
    have n2 : e₂.count = ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)⟩ := by
      have e : ((memberRuns (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) ⟨p.place, 1⟩ ++
          [freshRun ⟨p, ms, some f, r, ro, tr⟩])[ms.length]?).map (·.2) = some e₂.count := q2
      rw [List.getElem?_append_right (by simp [memberRuns])] at e
      simp only [memberRuns, List.length_map, Nat.sub_self, List.getElem?_cons_zero,
        Option.map_some] at e
      exact (Option.some.inj e).symm
    refine hideAt_congr _ _ _ fun i hi => ?_
    rw [← hk] at hi
    show (stretchOf c.1.2.1.1).e i = (stretches _ c.2.1.2.2 ms.length).e i
    have z1' : stretchOf c.1.2.1.1 = stretchOf x1 := z1
    rw [z1', z2, cut_e _ _ _ x1 k1 i (by rw [n1]; exact hi),
      cut_e _ _ _ x2 k2 i (by
        rw [n2]
        show i < 2 * _ + 1 + _
        omega), ho, hst]
  · -- the first stage's message
    have e : ∀ K : TestCoins, μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩))
        (TestJob.first ⟨p, ms, some f, r, ro, tr⟩ w fr K) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)) (ro w fr K.mem) := fun K => by
      funext x
      cases x <;> rfl
    rw [e, e]
    refine hrows _ _ fun t ht => ?_
    obtain ⟨a, a', ha, ha', o1, o2, o3⟩ := hm t ht
    obtain ⟨-, x1, k1, z1⟩ := lend_stretch look _ _ _ c1 t a ha
    obtain ⟨-, x2, k2, z2⟩ := lend_stretch look _ _ _ c2 t a' ha'
    show stretches _ c.1.2.2 t = stretches _ c.2.1.2.2 t
    rw [z1, z2]
    exact stretch_tie look a a' x1 x2 k1 k2 o1 o2 o3

/-- The equations on the book's entries, as a test that returns a `Bool`. pl: the test's place. n:
the number of the job's members. -/
def tiesB (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (n : ℕ) : Bool :=
  ((spentE Bk ⟨pl, 0⟩)[0]?).isSome &&
  (((spentE Bk ⟨pl, 0⟩)[0]?).map fun e => (e.owner, e.start.e)) ==
    (((carryE Bk ⟨pl, 0 + 1⟩)[n]?).map fun e => (e.owner, e.start.e)) &&
  decide (n ≤ (carryE Bk ⟨pl, 0⟩).length) &&
  ((carryE Bk ⟨pl, 0⟩).take n).map (fun e => (e.owner, e.start, e.count)) ==
    ((carryE Bk ⟨pl, 0 + 1⟩).take n).map fun e => (e.owner, e.start, e.count)

/-- **The conclusion of `agree_came` where the test on the book returns true.** hT takes the place
of hs, hf, ho, hst and hm; h, hk and hrows are the same. -/
theorem agree_of_ties (p : P12) (ms : List (Addr × ℕ × Due)) (f : Addr × ℕ)
    (r : W → Front X → T12) (ro : W → Front X → (ℕ → Stretch) → PS)
    (tr : W → Front X → (ℕ → Stretch) → PS → List Tree) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩])
    (h : lendRow Bk rows look p.place [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩] 0 = .ok c)
    (w : W) (fr : Front X) (hT : tiesB Bk p.place ms.length = true)
    (hk : (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩).k =
      (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)).h +
        (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)) (ro w fr mem) =
        μOf (sgOf (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)) (ro w fr mem')) :
    Agree ⟨p, ms, some f, r, ro, tr⟩ w fr (TestJob.s₀ ⟨p, ms, some f, r, ro, tr⟩)
      (firstRd ⟨p, ms, some f, r, ro, tr⟩ c.1) (restCoins ⟨p, ms, some f, r, ro, tr⟩ c.2.1) := by
  unfold tiesB at hT
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := hT
  obtain ⟨e₁, he₁⟩ := Option.isSome_iff_exists.1 t1
  rw [he₁, Option.map_some] at t2
  obtain ⟨e₂, he₂, k2⟩ := Option.map_eq_some_iff.1 t2.symm
  refine agree_came p ms f r ro tr Bk rows look c h w fr e₁ e₂ he₁ he₂
    (congrArg (·.1) k2).symm (congrArg (·.2) k2).symm (fun t ht => ?_) hk hrows
  have e := congrArg (·[t]?) t4
  simp only [List.getElem?_map, List.getElem?_take, if_pos ht] at e
  obtain ⟨a, ha⟩ : ∃ a, (carryE Bk ⟨p.place, 0⟩)[t]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [ha, Option.map_some] at e
  obtain ⟨a', ha', k3⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨a, a', ha, ha', (congrArg (·.1) k3).symm, (congrArg (·.2.1) k3).symm,
    (congrArg (·.2.2) k3).symm⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.agree_of_ties
#print axioms ProofFile.Honest.K12.cut_e
#print axioms ProofFile.Honest.K12.lend_stretch
#print axioms ProofFile.Honest.K12.stretch_tie
#print axioms ProofFile.Honest.K12.byName_congr
#print axioms ProofFile.Honest.K12.hideAt_congr
#print axioms ProofFile.Honest.K12.agree_came
#print axioms ProofFile.Honest.K12.tiesB
