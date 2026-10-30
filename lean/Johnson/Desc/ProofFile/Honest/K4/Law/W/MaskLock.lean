-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskLock.lean: CONDITIONAL. One definition of a hypothesis's
form, and six statements with their proofs.

What is here. THE LOCK OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) FOR
ITS SEGMENT's MASK ROW: `K4MaskLock`, A PUBLIC TEST ON THE BOOK OF COINS (`ProverCoinCounts`,
Honest/Frame.lean), with no coin in any field: `K4LastEntry` (Law/W/LastEntry.lean, of another
writer: the book lends K4's row; the spending entries for the row's parts are a list es₁ and then
one entry eL; eL hands one coin), and of es₁: they are ONE STRETCH of one owner o's coins, from
number base + e on, cnt coins long (`oneStretch`, Honest/BookStretch.lean, of other writers). No
test is typed anew: the fields are calls of `lendsRow`, `rowEntries` and `oneStretch`. THAT THE
STRETCH LIES INSIDE o's COUNT IS NO FIELD: `K4MaskLock.room` has it from the two. Under it: (1)
`k4RowBegins_of_lock`: what the row's parts spend is that stretch and one coin more, at every run's
coins (`RowBeginsBy`, Honest/Law/Rule/TiesLen.lean). (2) `k4Cnt_of_lock`: cnt + 1 is the number of
slots that the hearing takes (`k4Takes`). (3) `k4Lock_member`: **WHOSE THE MEMBERS ARE**: at every
run's coins and every j below cnt, member number j of `rowSpentGl` … (Honest/Law/Rule/CoinBack.lean)
IS THERE, AND IT IS o's ELEMENT NUMBER base + e + j of the extension field (`Cs.eAt`,
Honest/Frame.lean). TWO STATEMENTS THAT THE LOCK BITES: (4) `k4Lock_owners`: every entry of es₁
names the one owner o. (5) `k4Lock_fixed`: THE BOOK FIXES THE LETTERS: two locks at one book and one
Qp have the same es₁, eL and o, the same start base + e and the same cnt: so the lock cannot be met
at two owners, two starts or two counts; base and e are fixed in their sum alone.

How. (1): one call of `rowBeginsBy_one` (Honest/Law/Rule/TiesLen.lean), whose hypothesis on the last
entry's room is `K4LastEntry.fits` (Law/W/LastEntry.lean), by `look_dueIs`
(Honest/Small/LendsRow.lean). `K4MaskLock.room`: each entry of a row that the book lends fits its
owner's count (`lendsRow_fit`, Law/W/LastEntry.lean), and the walk of `oneStretch` ends where its
last entry ends. (2): `rowSpent_length` (Honest/Law/Rule/TiesLen.lean) against `spentOf_length`
(Law/RowKit.lean), `k4_coins_total` (Law/W/MaskBelowHead.lean) and `spentOf_row`
(Honest/Law/Rule/Spent.lean), at a lending that `lendsRow_iff` hands. (3): (1) under `val_rowSpent`
and `val_coinsE` (Honest/Law/Rule/CoinBack.lean). (4): the text of `oneStretch`'s walk. (5): the two
fields ents and stretch are equations with one left side.

Not shown here. THAT ANY BOOK OF THE FULL SIZE PASSES THE LOCK: `k4Names_at_head_elems`
(Law/W/LockAtHeadElems.lean) has the lock, in the form `K4MaskLockAt` (Law/W/MaskLockAt.lean), at e
:= the number of scalars that the lookup's declared rounds count, under the library's head, at a
book that the maker `bookWhole` returns, AT THE MAKER's OWN OWNER AND START, WHICH ARE NOT SHOWN TO
BE THE SENDER's; that the maker returns a book there is a hypothesis of it; at the book of what
`onlineProverFromPublicFiles` returns, under the head: `k4Book_at_atPure` (Law/W/BookAtPure.lean). THE FIELD last.lends
COMPARES THE BOOK WITH WHAT K4's OWN PARTS STATE (names, counts, order and lengths): no fact on the
book alone gives it; it is a field of the lock, and is had where the lock is. THE ONE EQUATION THAT
JOINS LOCK AND KEY: THE STRETCH BEGINS AT base + e WITH THE SENDER's OWN base: the field stretch has
the book's start for K4's row as base + e, and the sender's sentence (hE,
Law/W/MaskOfSenderLot.lean) has its mask row's entry number ν at its coin number base + ν: that the
maker's start and the place where the sender's mask row begins among its coins are one number plus e
is shown nowhere here; AND THAT THE STRETCH's OWNER o IS THE SENDER's OWN ADDRESS IS AS UNSHOWN AS
THE START: it is what makes the coins the sender's. THE FIELD last.lends STANDS AT THE FIRST CHAIN
AND READS THE BOOK's FIRST TABLE ALONE (`lookDue`, Honest/Small/LendsRow.lean): at a book that keeps
the row of the stretch's owner, or of the last entry's, in another table it is false, and every
statement here is empty. OTHER KINDS' PARTS SPEND OF THE SAME MASK ROW: that the book's entries hand
out each coin of the owner's once is a matter of all its entries together: nothing on it here; the
frame's writers' law on it: `ProverCoinCounts.spentApart_parts` (Honest/BookApart.lean). Nothing on the row's
last coin but that it is one (`K4LastEntry`). Nothing on what any message holds. A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/,
at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `K4MaskLock`   the lock. A definition: a hypothesis's form
  `K4MaskLock.room`   the stretch lies inside the owner's count
  `k4RowBegins_of_lock`, `k4Cnt_of_lock`   one stretch and one coin more; how long
  `k4Lock_member`   **member j is the owner's element number base + e + j**
  `k4Lock_owners`, `k4Lock_fixed`   one owner; the book fixes the letters
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LastEntry
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTxtGPub
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open VerifiableInference.Desc (Place)

/-- **THE LOCK: a public test on the book, at K4's row.** e: the first entry that K4's text reads.
es₁, eL: the book's spending entries for the row's parts, all but the last, and the last. o: the
owner of the stretch. base: where the owner's mask row begins among its coins. cnt: how many coins
the stretch has. No coin stands in any field. This defines a hypothesis's form; the definition
claims nothing. -/
structure K4MaskLock (Bk : ProverCoinCounts) (Qp : K4Pub) (e : ℕ) (es₁ : List Ahead) (eL : Ahead) (o : Addr)
    (base cnt : ℕ) : Prop where
  /-- the book lends the row; its entries are es₁ and then eL; eL has one coin -/
  last : K4LastEntry Bk Qp es₁ eL
  /-- all entries but the last are one stretch of o's coins, from number base + e on -/
  stretch : oneStretch es₁ = some (o, base + e, cnt)

variable {Bk : ProverCoinCounts} {Qp : K4Pub} {e : ℕ} {es₁ : List Ahead} {eL : Ahead} {o : Addr}
  {base cnt : ℕ}

private theorem runOn_owner {o : Addr} {s : ℕ} : ∀ (fs : List Ahead) (c c' : ℕ),
    runOn o s c fs = some c' → ∀ f ∈ fs, f.owner = o
  | [], _, _, _, _, hf => by cases hf
  | g :: fs, c, c', h, f, hf => by
    unfold runOn at h
    split at h
    · rename_i hc
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact hc.1
      · exact runOn_owner fs _ _ h f hf'
    · cases h

/-- CONDITIONAL on K. **Every entry in front of the last names the one owner.** -/
theorem k4Lock_owners (K : K4MaskLock Bk Qp e es₁ eL o base cnt) : ∀ f ∈ es₁, f.owner = o := by
  have h := K.stretch
  cases es₁ with
  | nil => cases h
  | cons a es =>
    have h' : (runOn a.owner a.start.e a.count.e es).map (fun c => (a.owner, a.start.e, c)) =
        some (o, base + e, cnt) := h
    cases hr : runOn a.owner a.start.e a.count.e es with
    | none =>
      rw [hr] at h'
      cases h'
    | some c =>
      rw [hr] at h'
      have e' : (a.owner, a.start.e, c) = (o, base + e, cnt) := Option.some.inj h'
      have ho : a.owner = o := congrArg Prod.fst e'
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact ho
      · rw [← ho]
        exact runOn_owner es _ _ hr f hf'

private theorem runOn_room {o : Addr} {s D : ℕ} : ∀ (fs : List Ahead) (c c' : ℕ),
    runOn o s c fs = some c' → s + c ≤ D → (∀ f ∈ fs, f.start.e + f.count.e ≤ D) → s + c' ≤ D
  | [], c, c', h, h0, _ => by
    have e : c = c' := Option.some.inj h
    omega
  | g :: fs, c, c', h, _, hf => by
    unfold runOn at h
    split at h
    · rename_i hc
      have hg := hf g List.mem_cons_self
      have hs := hc.2
      exact runOn_room fs _ _ h (by omega) (fun f hm => hf f (List.mem_cons_of_mem _ hm))
    · cases h

/-- CONDITIONAL on K. **The stretch lies inside the owner's count**: each entry of a row that the
book lends fits its owner's count. -/
theorem K4MaskLock.room (K : K4MaskLock Bk Qp e es₁ eL o base cnt) :
    base + e + cnt ≤ (lookDue Bk 0 o).e := by
  have ow := k4Lock_owners K
  have fit : ∀ f ∈ es₁, f.start.e + f.count.e ≤ (lookDue Bk 0 o).e := by
    intro f hf
    have hm : f ∈ rowEntries Bk (k4Place Qp) (k4RowIn Qp).length 0 := by
      rw [K.last.ents]
      exact List.mem_append.2 (Or.inl hf)
    have h1 := lendsRow_fit Bk 0 (k4Place Qp) (k4RowIn Qp) K.last.lends f hm
    unfold cutFits at h1
    have h2 := (of_decide_eq_true h1).2
    rw [ow f hf] at h2
    exact h2
  have h := K.stretch
  cases es₁ with
  | nil => cases h
  | cons a es =>
    have h' : (runOn a.owner a.start.e a.count.e es).map (fun c => (a.owner, a.start.e, c)) =
        some (o, base + e, cnt) := h
    cases hr : runOn a.owner a.start.e a.count.e es with
    | none =>
      rw [hr] at h'
      cases h'
    | some c =>
      rw [hr] at h'
      have e' : (a.owner, a.start.e, c) = (o, base + e, cnt) := Option.some.inj h'
      have hs : a.start.e = base + e := congrArg (fun x => x.2.1) e'
      have hcn : c = cnt := congrArg (fun x => x.2.2) e'
      have r := runOn_room es _ _ hr (fit a List.mem_cons_self)
        (fun f hm => fit f (List.mem_cons_of_mem _ hm))
      rw [hs, hcn] at r
      exact r

/-- CONDITIONAL on K. What the row's parts spend is one stretch of o's coins and one coin more. -/
theorem k4RowBegins_of_lock (K : K4MaskLock Bk Qp e es₁ eL o base cnt) :
    RowBeginsBy Bk 0 (k4Place Qp) (k4RowIn Qp).length o (base + e) cnt 1 := by
  have h := rowBeginsBy_one (ch := 0) K.last.ents K.stretch (fun k => by
    rw [look_dueIs, K.last.one]
    exact K.last.fits)
  rw [K.last.one] at h
  exact h

/-- CONDITIONAL on K. The stretch is one shorter than the number of slots that the hearing takes. -/
theorem k4Cnt_of_lock (K : K4MaskLock Bk Qp e es₁ eL o base cnt) :
    cnt + 1 = k4Takes Qp.P Qp.hp Qp.g := by
  obtain ⟨cr, hl⟩ := (lendsRow_iff (default : Coins Bk) 0 (k4Place Qp) (k4RowIn Qp)).2 K.last.lends
  have e1 : (spentOf (k4RowIn Qp) cr).length = k4Takes Qp.P Qp.hp Qp.g := by
    rw [spentOf_length]
    exact k4_coins_total Qp
  rw [spent_same, spentOf_row Bk _ _ _ _ 0 cr hl] at e1
  have e2 := rowSpent_length (k4RowBegins_of_lock K) default (by
    rw [look_dueIs]
    exact K.room)
  rw [e2] at e1
  exact e1

/-- CONDITIONAL on K and hj. **WHOSE THE MEMBERS ARE**: member number j of what the row spends is
there, and it is o's element number base + e + j, at every run's coins. -/
theorem k4Lock_member (K : K4MaskLock Bk Qp e es₁ eL o base cnt) (k : Coins Bk) {j : ℕ}
    (hj : j < cnt) :
    ∃ y, (rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[j]? = some y ∧
      (k.look 0 o).2.eAt (base + e + j) = .ok y := by
  obtain ⟨rest, -, eq⟩ := k4RowBegins_of_lock K k
  have hroom : base + e + cnt ≤ (k.look 0 o).1.e := by
    rw [look_dueIs]
    exact K.room
  have hr : base + e + j < (k.look 0 o).1.e := by omega
  refine ⟨(k.look 0 o).2.e ⟨base + e + j, hr⟩, ?_, ?_⟩
  · rw [← val_rowSpent, eq, List.map_append, List.map_take, List.map_drop,
      val_coinsE, List.getElem?_append_left (by
        rw [List.length_take, List.length_drop, List.length_ofFn]
        omega),
      List.getElem?_take_of_lt hj, List.getElem?_drop, List.getElem?_ofFn, dif_pos hr]
  · unfold Cs.eAt
    rw [dif_pos hr]

/-- CONDITIONAL on K and K'. **THE BOOK FIXES THE LETTERS**: two locks at one book and one Qp have
the same entries, the same owner, the same start and the same count. -/
theorem k4Lock_fixed {e' : ℕ} {es₁' : List Ahead} {eL' : Ahead} {o' : Addr} {base' cnt' : ℕ}
    (K : K4MaskLock Bk Qp e es₁ eL o base cnt) (K' : K4MaskLock Bk Qp e' es₁' eL' o' base' cnt') :
    es₁' = es₁ ∧ eL' = eL ∧ o' = o ∧ base' + e' = base + e ∧ cnt' = cnt := by
  have h0 : es₁' ++ [eL'] = es₁ ++ [eL] := K'.last.ents.symm.trans K.last.ents
  obtain ⟨h1, h2⟩ := List.append_inj' h0 rfl
  have h3 : eL' = eL := List.head_eq_of_cons_eq h2
  have s' := K'.stretch
  rw [h1, K.stretch] at s'
  have h4 : (o, base + e, cnt) = (o', base' + e', cnt') := Option.some.inj s'
  exact ⟨h1, h3, (congrArg Prod.fst h4).symm, (congrArg (fun x => x.2.1) h4).symm,
    (congrArg (fun x => x.2.2) h4).symm⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.K4MaskLock.room
#print axioms ProofFile.Honest.K4.W.k4RowBegins_of_lock
#print axioms ProofFile.Honest.K4.W.k4Cnt_of_lock
#print axioms ProofFile.Honest.K4.W.k4Lock_member
#print axioms ProofFile.Honest.K4.W.k4Lock_owners
#print axioms ProofFile.Honest.K4.W.k4Lock_fixed
