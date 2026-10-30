-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/SpentOfWants.lean: one definition with code, and statements
with their proofs. No kind is named in the code. By the writers of the feed-forward layers' own
rounds (sub-protocol K4). It stands over Honest/BookRowKit.lean.

What is here. WHERE A ROW's SPENDING ENTRIES ARE THE LIST `partsWants`, WHAT THE BOOK OF COINS HAS
FOR ONE PART TO SPEND, AS NAMES AND COUNTS, IS A FUNCTION OF THAT PART's ADDRESS AND ROUNDS, OF
WHETHER IT IS LISTED AS A MERGE, AND OF THE TWO OWNERS' NAMES. For the parts of a segment the
book's maker lays the entries that spend the mask row and the index-mask message as one list
(`partsWants`, Honest/BookEntries.lean). A part states what it spends as names and counts
(`Part.spends`, Honest/Frame.lean), and the lending compares these with the book's entries for that
part (`spentE`, Honest/Law/Rule/Cell.lean). Two facts carry it. Every entry bears its spender
(`BookRow.partWants_spender`, Honest/BookRowKit.lean, called here), and part number i of the row
stands at the address (place, i) (the premise had; `planParts_addr` has it at `planParts`): so
picking by spender cuts the maker's list part by part. And an entry's name and count hang neither
on the maker's two running numbers nor on where the owners' coins begin: of the two owners the name
alone is read.

  `partStates rowN idxN merge q`   **A SECOND TEXT OF `partWants`' FIVE ARMS**, as names and counts:
      nothing for a part without a scalar of its own; one run "scalars"; one run "sum"; or "sum" and
      "ends", the second under the index-mask message's name where the part is a merge.
  `partWants_named`   **what ties the second text to the first, with no hypothesis**: the names and
      counts of `partWants`' entries, at any two numbers, are `partStates` at the two owners' names.
  `pick_rowEntries`, `pick_rowEntries_at`   no hypothesis but that the row has a part number i: of
      a row's spending entries (`rowEntries`, Honest/BookStretch.lean) those that name part number i
      as their spender are that part's.
  `partsWants_pick`   of the maker's list for parts that stand at (place, k), (place, k + 1), …
      those that name one part are `partWants` of that part, at some two numbers.
  `spent_named_of_wants`   **THE STEP FROM A ROW TO A PART**: where a row's spending entries are the
      list `partsWants` (hE) and its parts stand at (place, i) (had), each part's entries have the
      names and counts of `partStates`.
  `ownerOf_name`, `planParts_addr`   `ownerOf` hands its first argument back as the name;
      `planParts` numbers its parts from 0.

Not shown here. THAT ANY BOOK's ROW IS THE LIST `partsWants`: that is the premise hE. `partsWants`
IS ONE OF THE MAKER's LISTS OF SPENDING ENTRIES: a fold's, the shared split's and those of a
sumcheck outside a segment come from others (Honest/BookFolds.lean, Honest/BookAll.lean): of a row
that holds such a part nothing is said here. THAT ANY PART OF THE PROTOCOL STATES WHAT `partStates`
SAYS. WHERE A PART HAS NO SCALAR OF ITS OWN `partWants` LAYS NO ENTRY: a part that states a run
of count 0 there does not meet it. Which coins the entries name: starts and owners are not spoken
of. Only the runs that are spent, not those that are carried. Which parts are merges is a free
parameter. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {S Cl : Type}

/-! ## 1 The second text, and what ties it -/

/-- **What `partWants` lays for one part, as names and counts**: its five arms. rowN, idxN: the
names of the segment's mask row and of the index-mask message. This is a definition; it claims
nothing. -/
def partStates (rowN idxN : String) (merge : Bool) (q : PartAt) : List (String × Due) :=
  let s := q.ownScalars
  let n := q.endScalars
  if s == 0 then []
  else if !q.isSum then [(runName rowN q.addr "scalars", ⟨0, s⟩)]
  else if n == 0 then [(runName rowN q.addr "sum", ⟨0, s⟩)]
  else [(runName rowN q.addr "sum", ⟨0, s - n⟩),
    (runName (if merge then idxN else rowN) q.addr "ends", ⟨0, n⟩)]

/-- No hypothesis. **The names and counts of `partWants`' entries are `partStates`**, whatever the
two numbers. -/
theorem partWants_named (row idx : MsgAt) (merge : Bool) (q : PartAt) (j t : Nat) :
    ((partWants row idx merge q j t).1.map (·.entry)).map Ahead.named =
      partStates row.name idx.name merge q := by
  unfold partWants partStates
  dsimp only
  by_cases h0 : (q.ownScalars == 0) = true
  · simp only [if_pos h0]
    rfl
  · by_cases h1 : (!q.isSum) = true
    · simp only [if_neg h0, if_pos h1]
      rfl
    · by_cases h2 : (q.endScalars == 0) = true
      · simp only [if_neg h0, if_neg h1, if_pos h2]
        rfl
      · cases merge <;> simp only [if_neg h0, if_neg h1, if_neg h2] <;> rfl

/-! ## 2 Picking by spender -/

private theorem pick_spent_self (B : ProverCoinCounts) (a : Addr) :
    BookRow.pick a (spentE B a) = spentE B a := by
  have h1 : ∀ e ∈ spentE B a, (e.spender == a) = true := fun e he => by
    have he' : e ∈ (B.ahead.filter fun e => e.spender == a).filter fun e => e.once := he
    exact (List.mem_filter.1 (List.mem_filter.1 he').1).2
  have h2 : ∀ e ∈ spentE B a, e.once = true := fun e he => by
    have he' : e ∈ (B.ahead.filter fun e => e.spender == a).filter fun e => e.once := he
    exact (List.mem_filter.1 he').2
  show ((spentE B a).filter fun e => e.spender == a).filter (fun e => e.once) = spentE B a
  rw [List.filter_eq_self.2 h1, List.filter_eq_self.2 h2]

private theorem pick_spent_other (B : ProverCoinCounts) {a a' : Addr} (hne : a' ≠ a) :
    BookRow.pick a (spentE B a') = [] :=
  BookRow.pick_other fun e he hh => by
    have he' : e ∈ (B.ahead.filter fun e => e.spender == a').filter fun e => e.once := he
    have h1 : (e.spender == a') = true := (List.mem_filter.1 (List.mem_filter.1 he').1).2
    exact hne ((beq_iff_eq.1 h1).symm.trans hh)

private theorem pick_rowEntries_front (B : ProverCoinCounts) (p : Place) {i : Nat} : ∀ n j, i < j →
    BookRow.pick ⟨p, i⟩ (rowEntries B p n j) = []
  | 0, _, _ => rfl
  | n + 1, j, h => by
    show BookRow.pick ⟨p, i⟩ (spentE B ⟨p, j⟩ ++ rowEntries B p n (j + 1)) = []
    have hne : (⟨p, j⟩ : Addr) ≠ ⟨p, i⟩ := fun e => by
      have e' : j = i := congrArg Addr.part e
      omega
    rw [BookRow.pick_append, pick_spent_other B hne, pick_rowEntries_front B p n (j + 1) (by omega)]
    rfl

/-- Of a row's spending entries from part number j on, those that name part number i are that
part's. -/
theorem pick_rowEntries_at (B : ProverCoinCounts) (p : Place) {i : Nat} : ∀ n j, j ≤ i → i < j + n →
    BookRow.pick ⟨p, i⟩ (rowEntries B p n j) = spentE B ⟨p, i⟩
  | 0, j, h1, h2 => by omega
  | n + 1, j, h1, h2 => by
    show BookRow.pick ⟨p, i⟩ (spentE B ⟨p, j⟩ ++ rowEntries B p n (j + 1)) = spentE B ⟨p, i⟩
    rw [BookRow.pick_append]
    by_cases e : j = i
    · subst e
      rw [pick_spent_self, pick_rowEntries_front B p n (j + 1) (by omega), List.append_nil]
    · have hne : (⟨p, j⟩ : Addr) ≠ ⟨p, i⟩ := fun h => e (congrArg Addr.part h)
      rw [pick_spent_other B hne, pick_rowEntries_at B p n (j + 1) (by omega) (by omega)]
      rfl

/-- No hypothesis but i < n. **Of a row's spending entries those that name part number i are that
part's.** -/
theorem pick_rowEntries (B : ProverCoinCounts) (p : Place) {n i : Nat} (hi : i < n) :
    BookRow.pick ⟨p, i⟩ (rowEntries B p n 0) = spentE B ⟨p, i⟩ :=
  pick_rowEntries_at B p n 0 (Nat.zero_le i) (by omega)

/-- CONDITIONAL on the parts' addresses. **Of the maker's list those that name one part are
`partWants` of that part**, at some two numbers. -/
theorem partsWants_pick (row idx : MsgAt) (ms : List Addr) (p : Place) :
    ∀ (ps : List PartAt) (k j t : Nat),
      (∀ (i : Nat) (q : PartAt), ps[i]? = some q → q.addr = ⟨p, k + i⟩) →
      ∀ (i : Nat) (q : PartAt), ps[i]? = some q → ∃ j' t',
        (partsWants row idx ms ps j t).1.filter (fun w => w.spender == (⟨p, k + i⟩ : Addr)) =
          (partWants row idx (ms.contains q.addr) q j' t').1
  | [], _, _, _, _, _, _, hq => by simp at hq
  | r :: ps, k, j, t, had, 0, q, hq => by
    have hr : r = q := Option.some.inj hq
    subst hr
    have ha : r.addr = ⟨p, k + 0⟩ := had 0 r rfl
    refine ⟨j, t, ?_⟩
    rw [partsWants]
    dsimp only
    rw [List.filter_append,
      wants_all (fun w hw => (BookRow.partWants_spender _ _ _ _ _ _ w hw).trans ha), wants_other ?_,
      List.append_nil]
    intro w hw e
    obtain ⟨q', hq', e'⟩ := partsWants_spender row idx ms ps _ _ w hw
    obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.1 hq'
    have h2 : q'.addr = ⟨p, k + (i' + 1)⟩ := had (i' + 1) q' hi'
    have h4 : k + (i' + 1) = k + 0 := congrArg Addr.part (h2.symm.trans (e'.symm.trans e))
    omega
  | r :: ps, k, j, t, had, i + 1, q, hq => by
    have ha : r.addr = ⟨p, k + 0⟩ := had 0 r rfl
    have hq' : ps[i]? = some q := hq
    obtain ⟨j', t', e⟩ := partsWants_pick row idx ms p ps (k + 1) (j + r.ownScalars)
      (partWants row idx (ms.contains r.addr) r j t).2
      (fun i' q' h' => by
        have e1 : k + (i' + 1) = k + 1 + i' := by omega
        rw [had (i' + 1) q' h', e1]) i q hq'
    refine ⟨j', t', ?_⟩
    rw [partsWants]
    dsimp only
    have ek : k + (i + 1) = k + 1 + i := by omega
    rw [List.filter_append, ek, e, wants_other ?_, List.nil_append]
    intro w hw e2
    have h3 : r.addr = ⟨p, k + 1 + i⟩ :=
      (BookRow.partWants_spender _ _ _ _ _ _ w hw).symm.trans e2
    have h4 : k + 0 = k + 1 + i := congrArg Addr.part (ha.symm.trans h3)
    omega

/-! ## 3 From a row to a part -/

/-- CONDITIONAL on hE and had. **WHERE A ROW's SPENDING ENTRIES ARE THE MAKER's LIST, EACH PART's
ENTRIES HAVE THE NAMES AND COUNTS OF `partStates`.** -/
theorem spent_named_of_wants {B : ProverCoinCounts} {p : Place} {ps : List PartAt} {row idx : MsgAt}
    {ms : List Addr} {j t : Nat}
    (hE : rowEntries B p ps.length 0 = (partsWants row idx ms ps j t).1.map (·.entry))
    (had : ∀ (i : Nat) (q : PartAt), ps[i]? = some q → q.addr = ⟨p, i⟩) :
    ∀ (i : Nat) (q : PartAt), ps[i]? = some q →
      (spentE B ⟨p, i⟩).map Ahead.named =
        partStates row.name idx.name (ms.contains q.addr) q := by
  intro i q hq
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hq
  obtain ⟨j', t', e⟩ := partsWants_pick row idx ms p ps 0 j t
    (fun i' q' h' => by rw [had i' q' h', Nat.zero_add]) i q hq
  rw [Nat.zero_add] at e
  have e1 : spentE B ⟨p, i⟩ =
      (partWants row idx (ms.contains q.addr) q j' t').1.map (·.entry) := by
    rw [← pick_rowEntries B p hi, hE, pick_entries, e]
  rw [e1, partWants_named]

/-! ## 4 Two small ones -/

/-- CONDITIONAL on h. `ownerOf` hands its first argument back as the name. -/
theorem ownerOf_name {name : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {label : String} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pick = some m) : m.name = name := by
  unfold ownerOf at h
  obtain ⟨x, -, h⟩ := opt_bind h
  obtain ⟨a, -, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨fr, -, h⟩ := opt_map h
  rw [← h]

private theorem numbered_at (p : Place) : ∀ (L : List (List (String × Nat))) (k i : Nat)
    (q : PartAt), ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))[i]? = some q →
      q.addr = ⟨p, k + i⟩
  | [], _, _, _, h => by simp at h
  | r :: L, k, 0, q, h => by
    rw [List.zipIdx_cons, List.map_cons] at h
    rw [← Option.some.inj h]
    rfl
  | r :: L, k, i + 1, q, h => by
    rw [List.zipIdx_cons, List.map_cons] at h
    have e1 : k + 1 + i = k + (i + 1) := by omega
    rw [numbered_at p L (k + 1) i q h, e1]

/-- No hypothesis but that the part is there. `planParts` numbers its parts from 0. -/
theorem planParts_addr (b : Block S Cl) : ∀ (i : Nat) (q : PartAt),
    (planParts b)[i]? = some q → q.addr = ⟨b.place, i⟩ := by
  intro i q h
  unfold planParts at h
  rw [numbered_at b.place _ 0 i q h, Nat.zero_add]

end ProofFile.Honest

#print axioms ProofFile.Honest.partWants_named
#print axioms ProofFile.Honest.pick_rowEntries_at
#print axioms ProofFile.Honest.pick_rowEntries
#print axioms ProofFile.Honest.partsWants_pick
#print axioms ProofFile.Honest.spent_named_of_wants
#print axioms ProofFile.Honest.ownerOf_name
#print axioms ProofFile.Honest.planParts_addr
