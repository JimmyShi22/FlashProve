-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/OwnedHomes.lean: the honest side of the kind "lookup" (K3):
THE
TABLE OF STARTS AND THE FUNCTION FROM SLOTS TO MASK ENTRIES, LAID FOR EVERY LETTER OF OWNERS: each
owner's
coins are taken in the order of sending, each owner in its own count. So the premise `ReadsBy` of
Honest/K3/Parts/OwnedMasks.lean's law is paid, at every letter. Definitions with code and theorems.

  `unroll`              a letter unrolled, hidden value by hidden value in the order of sending:
  whose
                        the value's coin is
  `secondOf_unroll`, `unroll_key`   Honest/K3/RowOwned.lean's unrolled marks are this list's; at the
  key file's
                        letter a value's coin is the index-mask message's just where the verifier's
                        own
                        list `K3.fromKeys` marks it
  `unroll_split`        the list, cut at a stage: in front of the stage's two stretches stand as
  many
                        members as hidden values of the lookup stand in front of the stage
  `startsOf`, `maskOf`   the table; the function. home: where each owner's coins lie: its address,
  and
                        where its entries begin among its coins
  `readsBy_owners`      **`ReadsBy` holds of them**
  `startsOf_one`        at one owner, with home laid at base and the ledger's count in front of the
                        lookup, the table is Honest/K3/Parts/OwnedMasks.lean's `oneStarts`
  `masksOwners`         so: Honest/K3/Parts/OwnedMasks.lean's law with that premise paid

WHAT home IS. An owner's address, and where its entries FOR THIS LOOKUP begin among its coins: the
owner's first free entry in front of the lookup. `startsOf` adds no count of the ledger's. At one
owner
and a proof file's link, where the mask row's entries begin at base and the ledger's count in front
of
the lookup is first, home's start is base.plus ⟨0, first⟩, not base (`startsOf_one`).

Limits. What stays of `masksOwners`' premises: `bookFitsOwned` AND `startsFitBy` at `startsOf`:
PREMISES (the first: see `keyBookFitsTheOwnedRow`) ON A BOOK
THAT ANOTHER HAND MAKES, NOT SEEN HERE TO ACCEPT AT A REAL BOOK OF THE KEY FILE. Whether a real
book
counts each owner's coins in the order of sending is just what `startsFitBy` would test. Members of
the
counts: Honest/K3/Parts/OwnedHomesGuards.lean [not in this library]. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.OwnedMasks
import Johnson.Desc.ProofFile.Honest.K3.RowOwnedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.K3 (fromKeys)
open ProofFile.Honest.K3.Law

/-! ## 1 The letter unrolled -/

/-- **A letter unrolled**, hidden value by hidden value in the order of sending: whose the value's
coin
is. -/
def unroll (o : Owners) (f : LFace) : List String :=
  (stages f).flatMap fun s =>
    List.replicate (s.own f) (o s).1 ++ List.replicate (s.tail f) (o s).2

/-- Honest/K3/RowOwned.lean's unrolled marks are this list's. -/
theorem secondOf_unroll (o : Owners) (f : LFace) (w : String) :
    secondOf o f w = (unroll o f).map (· == w) := by
  unfold secondOf unroll
  rw [List.map_flatMap]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.map_append, List.map_replicate, List.map_replicate]

/-- **At the key file's letter a value's coin is the index-mask message's just where the verifier's
own
list marks it.** CONDITIONAL ON two planes or more. -/
theorem unroll_key (f : LFace) (h : 2 ≤ f.planes) :
    (unroll (keyOwners f) f).map (· == indexMaskRun) = fromKeys f := by
  rw [← secondOf_unroll, fromKeys_eq f h]

/-- A list of stages' stretches is as long as the stages have hidden values. -/
theorem unroll_length (o : Owners) (f : LFace) : ∀ l : List Stage,
    (l.flatMap fun s =>
      List.replicate (s.own f) (o s).1 ++ List.replicate (s.tail f) (o s).2).length =
      (l.map (Stage.slots f)).sum
  | [] => rfl
  | s :: l => by
    rw [List.flatMap_cons, List.length_append, unroll_length o f l, List.map_cons, List.sum_cons,
      List.length_append, List.length_replicate, List.length_replicate]
    rfl

/-- **The list, cut at a stage.** CONDITIONAL ON the stage standing in the row. -/
theorem unroll_split (o : Owners) (f : LFace) (s : Stage) (hs : s ∈ stages f) :
    ∃ pre post, unroll o f = pre ++ (List.replicate (s.own f) (o s).1 ++
        (List.replicate (s.tail f) (o s).2 ++ post)) ∧ pre.length = firstSlot f s := by
  have hi : indexOf f s < (stages f).length := List.idxOf_lt_length_iff.2 hs
  have hg : (stages f)[indexOf f s] = s := List.getElem_idxOf hi
  have e : stages f = (stages f).take (indexOf f s) ++ s :: (stages f).drop (indexOf f s + 1) := by
    conv_lhs => rw [← List.take_append_drop (indexOf f s) (stages f), List.drop_eq_getElem_cons hi,
      hg]
  refine ⟨((stages f).take (indexOf f s)).flatMap fun s =>
      List.replicate (s.own f) (o s).1 ++ List.replicate (s.tail f) (o s).2,
    ((stages f).drop (indexOf f s + 1)).flatMap fun s =>
      List.replicate (s.own f) (o s).1 ++ List.replicate (s.tail f) (o s).2, ?_,
    unroll_length o f _⟩
  unfold unroll
  conv_lhs => rw [e]
  rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-! ## 2 Lists -/

theorem getD_mid {α : Type} (pre rest : List α) (n i : Nat) (a d : α) (h : i < n) :
    (pre ++ (List.replicate n a ++ rest)).getD (pre.length + i) d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [List.length_replicate]; exact h),
    List.getElem?_replicate, if_pos h]
  rfl

theorem count_mid (pre rest : List String) (n i : Nat) (a : String) (h : i ≤ n) :
    ((pre ++ (List.replicate n a ++ rest)).take (pre.length + i)).count a = pre.count a + i := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.take_append, List.take_replicate, List.length_replicate, Nat.min_eq_left h,
    show i - n = 0 by omega, List.take_zero, List.append_nil, List.count_append,
    List.count_replicate_self]

/-! ## 3 The table and the function -/

/-- **The table of starts**: each stretch begins, among its owner's coins, behind as many of that
owner's entries as the lookup has taken of them in front of the stretch. home: an owner's address,
and
where its entries for the lookup begin among its coins. -/
def startsOf (o : Owners) (f : LFace) (home : String → Addr × Due) : Starts := fun s =>
  (((home (o s).1).1,
      (home (o s).1).2.plus ⟨0, ((unroll o f).take (firstSlot f s)).count (o s).1⟩),
    ((home (o s).2).1,
      (home (o s).2).2.plus ⟨0, ((unroll o f).take (firstSlot f s + s.own f)).count (o s).2⟩))

/-- **The mask entry under a slot**: the coin of the slot's owner, in that owner's own count. first:
the ledger's count in front of the lookup. -/
def maskOf (o : Owners) (f : LFace) (home : String → Addr × Due)
    (look : Addr → (d : Due) × Cs d) (first j : Nat) : GE :=
  rd ((coinsE (look (home ((unroll o f).getD (j - first) "")).1).2).getD
    ((home ((unroll o f).getD (j - first) "")).2.e +
      ((unroll o f).take (j - first)).count ((unroll o f).getD (j - first) "")) zeroE)

/-- **`ReadsBy` holds of the table and the function**, at every letter. No premise. -/
theorem readsBy_owners {W : Type} (R : Course W) (o : Owners) (home : String → Addr × Due)
    (look : Addr → (d : Due) × Cs d) :
    ReadsBy R look (startsOf o R.f home) (maskOf o R.f home look R.first) := by
  refine ⟨fun s hs i hi => ?_, fun s hs j hj => ?_⟩
  · obtain ⟨pre, post, e, hl⟩ := unroll_split o R.f s hs
    have k : R.first + firstSlot R.f s + i - R.first = pre.length + i := by omega
    have g1 : (unroll o R.f).getD (pre.length + i) "" = (o s).1 := by
      rw [e]
      exact getD_mid _ _ _ _ _ _ hi
    have g2 : ((unroll o R.f).take (pre.length + i)).count (o s).1 = pre.count (o s).1 + i := by
      rw [e]
      exact count_mid _ _ _ _ _ (Nat.le_of_lt hi)
    have g3 : ((unroll o R.f).take (firstSlot R.f s)).count (o s).1 = pre.count (o s).1 := by
      rw [← hl, e]
      exact count_mid _ _ _ 0 _ (Nat.zero_le _)
    unfold maskOf startsOf
    rw [k, g1, g2]
    show rd _ = rd ((coinsE _).getD ((home (o s).1).2.e + _ + i) zeroE)
    rw [g3, Nat.add_assoc]
  · obtain ⟨pre, post, e, hl⟩ := unroll_split o R.f s hs
    have e' : unroll o R.f = (pre ++ List.replicate (s.own R.f) (o s).1) ++
        (List.replicate (s.tail R.f) (o s).2 ++ post) := by rw [e, List.append_assoc]
    have hl' : (pre ++ List.replicate (s.own R.f) (o s).1).length =
        firstSlot R.f s + s.own R.f := by rw [List.length_append, List.length_replicate, hl]
    have k : R.endSlot s + j - R.first =
        (pre ++ List.replicate (s.own R.f) (o s).1).length + j := by
      rw [hl']
      show R.first + firstSlot R.f s + s.own R.f + j - R.first = _
      omega
    have g1 : (unroll o R.f).getD ((pre ++ List.replicate (s.own R.f) (o s).1).length + j) "" =
        (o s).2 := by
      rw [e']
      exact getD_mid _ _ _ _ _ _ hj
    have g2 : ((unroll o R.f).take ((pre ++ List.replicate (s.own R.f) (o s).1).length + j)).count
        (o s).2 = (pre ++ List.replicate (s.own R.f) (o s).1).count (o s).2 + j := by
      rw [e']
      exact count_mid _ _ _ _ _ (Nat.le_of_lt hj)
    have g3 : ((unroll o R.f).take (firstSlot R.f s + s.own R.f)).count (o s).2 =
        (pre ++ List.replicate (s.own R.f) (o s).1).count (o s).2 := by
      rw [← hl', e']
      exact count_mid _ _ _ 0 _ (Nat.zero_le _)
    unfold maskOf startsOf
    rw [k, g1, g2]
    show rd _ = rd ((coinsE _).getD ((home (o s).2).2.e + _ + j) zeroE)
    rw [g3, Nat.add_assoc]

/-- At one owner every member of the unrolled letter is that owner. -/
theorem unroll_one (f : LFace) : ∀ w ∈ unroll oneOwner f, w = maskRowRun := by
  intro w hw
  unfold unroll at hw
  obtain ⟨s, _, hw⟩ := List.mem_flatMap.1 hw
  rcases List.mem_append.1 hw with h | h
  · exact (List.mem_replicate.1 h).2
  · exact (List.mem_replicate.1 h).2

/-- A list all of whose members are a holds a as often as it is long. CONDITIONAL ON that. -/
theorem count_all (l : List String) (a : String) (h : ∀ w ∈ l, w = a) : l.count a = l.length := by
  rw [List.count_eq_length]
  exact fun w hw => (h w hw).symm

/-- **At one owner the table is Honest/K3/Parts/OwnedMasks.lean's**, with home laid at base and the
ledger's count in front of the lookup. CONDITIONAL ON the stage standing in the row. -/
theorem startsOf_one (a : At) (first : Nat) (o : Addr) (base : Due) (s : Stage)
    (hs : s ∈ stages a.face) :
    startsOf oneOwner a.face (fun _ => (o, base.plus ⟨0, first⟩)) s =
      oneStarts a first o base s := by
  obtain ⟨pre, post, e, hl⟩ := unroll_split oneOwner a.face s hs
  have hall := unroll_one a.face
  have g1 : ((unroll oneOwner a.face).take (firstSlot a.face s)).count maskRowRun =
      firstSlot a.face s := by
    rw [count_all _ _ fun w hw => hall w (List.mem_of_mem_take hw), List.length_take, e]
    simp only [List.length_append, hl]
    omega
  have g2 : ((unroll oneOwner a.face).take (firstSlot a.face s + s.own a.face)).count maskRowRun =
      firstSlot a.face s + s.own a.face := by
    rw [count_all _ _ fun w hw => hall w (List.mem_of_mem_take hw), List.length_take, e]
    simp only [List.length_append, List.length_replicate, hl]
    omega
  unfold startsOf oneStarts
  rw [show (oneOwner s).1 = maskRowRun from rfl, show (oneOwner s).2 = maskRowRun from rfl, g1, g2]
  show ((o, (⟨base.f + 0 + 0, base.e + first + firstSlot a.face s⟩ : Due)),
    (o, (⟨base.f + 0 + 0, base.e + first + (firstSlot a.face s + s.own a.face)⟩ : Due))) =
    ((o, (⟨base.f + 0, base.e + (first + firstSlot a.face s + 0)⟩ : Due)),
      (o, (⟨base.f + 0, base.e + (first + firstSlot a.face s + s.own a.face)⟩ : Due)))
  simp only [Nat.add_zero, Nat.add_assoc]

/-- **THE MASK ENTRIES UNDER THE LOOKUP'S SLOTS ARE THE OWNERS' COINS, EACH OWNER IN ITS OWN
COUNT.**
CONDITIONAL ON `bookFitsOwned` and on `startsFitBy` at `startsOf` (premises on a book that another
hand makes;
seen to accept at no real book of the key file); on what the row's parts spend being what the book's
entries name; and on the course's coins being the row's. No member is typed. -/
theorem masksOwners {W : Type} (R : Course W) (o : Owners) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (home : String → Addr × Due)
    (c : RowCoins (lookRow (V := Unit) ⟨ptsOf, pointsAt⟩ R.J R.a))
    (hb : bookFitsOwned o B rows (fun x => (look x).1) R.a = true)
    (hst : startsFitBy o B R.a (startsOf o R.f home) = true)
    (hsp : rowSpent _ c = ((List.range (stages R.f).length).map fun i =>
      (entriesAt B R.a.place i).map (lentE look)))
    (hca : CoinsAre R c) : MasksAre R (maskOf o R.f home look R.first) :=
  masksBy R o B rows look _ _ c hb hst hsp hca (readsBy_owners R o home look)

#print axioms ProofFile.Honest.K3.Parts.secondOf_unroll
#print axioms ProofFile.Honest.K3.Parts.unroll_key
#print axioms ProofFile.Honest.K3.Parts.unroll_length
#print axioms ProofFile.Honest.K3.Parts.unroll_split
#print axioms ProofFile.Honest.K3.Parts.getD_mid
#print axioms ProofFile.Honest.K3.Parts.count_mid
#print axioms ProofFile.Honest.K3.Parts.readsBy_owners
#print axioms ProofFile.Honest.K3.Parts.unroll_one
#print axioms ProofFile.Honest.K3.Parts.count_all
#print axioms ProofFile.Honest.K3.Parts.startsOf_one
#print axioms ProofFile.Honest.K3.Parts.masksOwners

end ProofFile.Honest.K3.Parts
