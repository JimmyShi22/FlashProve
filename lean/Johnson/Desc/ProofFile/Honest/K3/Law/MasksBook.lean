-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MasksBook.lean: from the book's entries to the hypothesis
`MasksAre` (Honest/K3/Law/Statements.lean). Conditional on two tests on the book. A definition with
code, a statement and theorems.

Terms. Honest/K3/GLOSSARY.md ("book, coins", "mask, mask row", "slot").

What is shown.
  `startsFit`: a clause more than `bookFits` (Honest/K3/Law/RowLends.lean), as a test with code:
    which of the owner's coins each entry names.
  `MasksFromBook`, `masksFromBook`: the statement and its proof: the mask entries under the lookup's
    slots are the owner's coins, by number.
  Helpers: `getD_drop_take` (`h`: j < n), `stage_lead` (`h`: the stage's call is k), `map_pair_zip`,
    `lent_of_lists`.

Hypotheses that remain, in `MasksFromBook`.
  `bookFits` and `startsFit` accept.
  What the row's parts spend is what the book's entries name (as `RowLends` gives it,
  RowLends.lean).
  The course's coins are the row's (`CoinsAre`; as `RowPlaysSeated` gives them,
  Honest/K3/Law/RowSeated.lean).

Users. `masksWorldBook` (Honest/K3/Law/MasksWorld.lean) calls `masksFromBook`.

Limits. Conditional on the two tests; no theorem of this file shows them. By evaluation they were
seen to accept at all ten sites of the shipped small example, at the real small book of the frame's
files (Honest/K3/Law/BookAtSites.lean [not in this library] takes them there; in a printed run, not
in
this tree; five negative tests rejected as due). At the full size no printed run in which they
accept was known to this file's writers when this was written (searched: their own two folders of
printed runs and papers, for the test's own headline; no other writers').
Honest/K3/Law/MasksBookToy.lean [not in this library] evaluates them at synthetic books.
"The mask entry under slot j" is here a function of the owner's coins. That the world in which the
verifier's claims are read has just these values under the segment's mask row is for the theorems on
the part that sends that row to show, and is not spoken of here.
One owner, and an offset: an owner whose coins for the row's entries do not lie in a row is not
covered. (By a text on the order of an owner's coins, not in this tree,
all entries of a message's mask rows stand in a row, by the format's own number, behind the main
rows' tails: so that "what one spender takes is one stretch"; in a segment the number is the
scalar's.)
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.RowLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open ProofFile.Honest.SumLaw (firstRun endRun hidingCoin)

/-- **A clause more than `bookFits`, as a test with code: which of the owner's coins each entry
names.** first: the number, in the segment's own count of scalars, of the lookup's first scalar: the
ledger's next slot in front of the lookup (`Course.first`; `First.Look.P.first`; the library's jLK).
o: the one owner. base: where the mask row's entries begin among the owner's coins, in both fields'
counts (a start names a coin of each field, though no coin of the base field is lent): the owner's
coin number base.e + j of the extension field is the one for the segment's scalar number j. At each
part of the row: its entries' owner is o; the first entry starts at the coin for the stage's first
hidden value, the second at the coin for its first end value. -/
def startsFit (B : ProverCoinCounts) (a : At) (first : Nat) (o : Addr) (base : Due) : Bool :=
  (stages a.face).zipIdx.all fun x =>
    (entriesAt B a.place x.2).map (fun e => (e.owner, e.start)) ==
      (runsAt a x.1 x.2).zipIdx.map fun r =>
        (o, base.plus ⟨0, first + firstSlot a.face x.1 +
          (if r.2 == 0 then 0 else x.1.own a.face)⟩)

/-- **Conditional on `bookFits` and `startsFit`: the mask entries under the lookup's slots are the
owner's coins**: if what the row's parts spend is what the book's entries name (as `RowLends` gives
it) and the course's coins are the row's (as `RowPlaysSeated` gives them), then `MasksAre` holds of
the course at the function that reads, under slot j, the owner's coin number base.e + j. Both tests
are hypotheses on a book that other files make; no theorem of this file shows them.
Honest/K3/Law/BookAtSites.lean [not in this library] takes them at a book that a maker in other
files makes of a description, for a program to
evaluate. A coin is read by `getD … zeroE`, in the end: up to the lookup's last slot the default is
never taken where `bookFits` (each entry inside its owner's coins) and `startsFit` (owner and start)
hold: both are premises here; `tests_fence` (Honest/K3/Law/BookFence.lean), which shows it, asks
besides that the face has at least two planes: no premise here. This is the statement of a lemma,
none of the library's goals. -/
def MasksFromBook : Prop :=
  ∀ (W : Type) (R : Course W) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (o : Addr) (base : Due)
    (c : RowCoins (lookRow (V := Unit) ⟨ptsOf, pointsAt⟩ R.J R.a)),
    bookFits B rows (fun x => (look x).1) R.a = true → startsFit B R.a R.first o base = true →
    rowSpent _ c = ((List.range (stages R.f).length).map fun i =>
      (entriesAt B R.a.place i).map (lentE look)) →
    CoinsAre R c →
    MasksAre R fun j => rd ((coinsE (look o).2).getD (base.e + j) zeroE)

theorem getD_drop_take (u : List E) (a n j : Nat) (h : j < n) :
    ((u.drop a).take n).getD j zeroE = u.getD (a + j) zeroE := by
  simp [List.getD_eq_getElem?_getD, h, List.getElem?_drop]

theorem stage_lead (f : LFace) (s : Stage) (k : Call) (h : s.call f = some k) : k.lead = 0 := by
  cases s with
  | tie n =>
    cases n with
    | zero => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
    | succ n => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | split i => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | key i m => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | tab l => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | leaves => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | bits => simp only [Stage.call, Option.some.injEq] at h; subst h; rfl
  | shift => simp [Stage.call] at h
  | alpha => simp [Stage.call] at h
  | join => simp [Stage.call] at h
  | keyLine i m => simp [Stage.call] at h
  | tabLine l => simp [Stage.call] at h
  | zero => simp [Stage.call] at h

theorem map_pair_zip {α β γ : Type} (f : α → β) (g : α → γ) : ∀ l : List α,
    l.map (fun e => (f e, g e)) = (l.map f).zip (l.map g)
  | [] => rfl
  | _ :: l => by simp [map_pair_zip f g l]

/-- What the entries of a part lend, of their owners, starts and counts alone. -/
theorem lent_of_lists (look : Addr → (d : Due) × Cs d) (es : List Ahead) :
    es.map (lentE look) = (((es.map fun e => (e.owner, e.start)).zip
      ((es.map Ahead.named).map (·.2))).map fun t =>
        ((coinsE (look t.1.1).2).drop t.1.2.e).take t.2.e) := by
  rw [List.map_map, ← map_pair_zip, List.map_map]
  rfl

/-- **The proof of `MasksFromBook`.** -/
theorem masksFromBook : MasksFromBook := by
  intro W R B rows look o base c hb hst hsp hca s hs
  have hj : indexOf R.a.face s < (stages R.a.face).length := List.idxOf_lt_length_iff.2 hs
  have hj' : indexOf R.a.face s < ((stages R.a.face).zipIdx).length := by simpa using hj
  have hmem : (s, indexOf R.a.face s) ∈ (stages R.a.face).zipIdx := by
    have e : ((stages R.a.face).zipIdx)[indexOf R.a.face s]'hj' = (s, indexOf R.a.face s) := by
      simp [List.getElem_zipIdx, indexOf]
    rw [← e]
    exact List.getElem_mem hj'
  cases hk : s.call R.a.face with
  | none =>
    have h1 : s.own R.a.face = 0 := by simp [Stage.own, hk]
    have h2 : s.tail R.a.face = 0 := by simp [Stage.tail, hk]
    exact ⟨fun i hi => by rw [h1] at hi; omega, fun j hj => by rw [h2] at hj; omega⟩
  | some k =>
    have g1 := List.all_eq_true.1 hb _ hmem
    have g2 := List.all_eq_true.1 hst _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at g1 g2
    have hnamed := g1.1.2
    have hlent := lent_of_lists look (entriesAt B R.a.place (indexOf R.a.face s))
    rw [g2, hnamed] at hlent
    have hspent : (rowSpent _ c).getD (indexOf R.a.face s) [] =
        (entriesAt B R.a.place (indexOf R.a.face s)).map (lentE look) := by
      rw [hsp]
      simp [List.getD_eq_getElem?_getD, hj]
    have hco := hca s hs (by simp [hk])
    rw [hspent, hlent] at hco
    have hown : s.own R.a.face = ownRun k := by simp [Stage.own, hk]
    have hlead : (R.job s).shape.lead = 0 := by
      show (shapeAt R.a s).lead = 0
      rw [shapeAt_some R.a s k hk]
      exact stage_lead R.a.face s k hk
    have hne := stage_ends_ne R.a.face s k hk
    have htail : s.tail R.a.face = ((k.ends).map (·.n)).getD 0 := by simp [Stage.tail, hk]
    simp only [runsAt, hk] at hco
    obtain ⟨lead, vs, ends⟩ := k
    cases ends with
    | none =>
      have ht : s.tail R.a.face = 0 := by rw [htail]; rfl
      have hco' : [((coinsE (look o).2).drop (base.e + (R.first + firstSlot R.a.face s + 0))).take
          (ownRun ⟨lead, vs, none⟩)] =
          firstRun (J := R.job s) (R.c s) :: (if s.tail R.f = 0 then [] else [R.masks s]) := hco
      simp only [List.cons.injEq] at hco'
      refine ⟨fun i hi => ?_, fun j hj => by rw [ht] at hj; omega⟩
      show rd _ = rd ((firstRun (J := R.job s) (R.c s)).getD ((R.job s).shape.lead + i) zeroE)
      rw [← hco'.1, hlead, Nat.zero_add, getD_drop_take _ _ _ _ (by rw [← hown]; exact hi)]
      congr 2
      show base.e + (R.first + firstSlot R.a.face s + i) = _
      omega
    | some en =>
      have ht : s.tail R.a.face = en.n := by rw [htail]; rfl
      have hn0 : s.tail R.f ≠ 0 := by
        show s.tail R.a.face ≠ 0
        rw [ht]
        exact hne en rfl
      have hco' : [((coinsE (look o).2).drop (base.e + (R.first + firstSlot R.a.face s + 0))).take
          (ownRun ⟨lead, vs, some en⟩),
          ((coinsE (look o).2).drop
            (base.e + (R.first + firstSlot R.a.face s + s.own R.a.face))).take en.n] =
          firstRun (J := R.job s) (R.c s) :: (if s.tail R.f = 0 then [] else [R.masks s]) := hco
      rw [if_neg hn0] at hco'
      simp only [List.cons.injEq, and_true] at hco'
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · show rd _ = rd ((firstRun (J := R.job s) (R.c s)).getD ((R.job s).shape.lead + i) zeroE)
        rw [← hco'.1, hlead, Nat.zero_add, getD_drop_take _ _ _ _ (by rw [← hown]; exact hi)]
        congr 2
        show base.e + (R.first + firstSlot R.a.face s + i) = _
        omega
      · show rd _ = rd ((R.masks s).getD j zeroE)
        rw [← hco'.2, getD_drop_take _ _ _ _ (by rw [← ht]; exact hj)]
        congr 2
        show base.e + (R.first + firstSlot R.a.face s + s.own R.a.face + j) = _
        omega

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.masksFromBook
#print axioms ProofFile.Honest.K3.Law.getD_drop_take
#print axioms ProofFile.Honest.K3.Law.stage_lead
#print axioms ProofFile.Honest.K3.Law.map_pair_zip
#print axioms ProofFile.Honest.K3.Law.lent_of_lists
