-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/OwnedMasks.lean: the honest side of the kind "lookup" (K3):
WHICH
COIN LIES UNDER WHICH HIDDEN VALUE, WITH AN OWNER AND A START FOR EACH STRETCH: the law of
Honest/K3/Law/MasksBook.lean, which knows one owner, general in a table that gives each of a stage's
two
stretches its owner and where it begins among that owner's coins. Definitions with code and
theorems.

  `Starts`              the table: a stage's first stretch's owner and start; its second's
  `startsFitBy`         THE PREMISE ON THE BOOK, as a test with code: the entries' owners and starts
  are
                        the table's
  `ReadsBy`             a function from slots to mask entries reads, under each stretch's slots, the
                        owner's coins from the start on
  `masksBy`             **the mask entries under the lookup's slots are the owners' coins**
  `oneStarts`, `startsFit_by`, `readsBy_one`, `masksFromBook_by`   at one owner the test is
                        Honest/K3/Law/MasksBook.lean's, and that file's law follows from this one

Limits. CONDITIONAL ON `bookFitsOwned` AND `startsFitBy`: PREMISES ON A BOOK THAT ANOTHER HAND
MAKES (the first: see `keyBookFitsTheOwnedRow`). HERE THEY ARE
NOT SEEN TO ACCEPT AT A REAL BOOK OF THE KEY FILE: no book that a maker makes of that chain is at
hand
here. `ReadsBy` is a premise on the function: no function is laid here for the key file's letter.
No member is typed. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.OwnedLends
import Johnson.Desc.ProofFile.Honest.K3.Law.MasksBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (firstRun)
open ProofFile.Honest.K3.Law

/-! ## 1 The premises -/

/-- **Whose coins each of a stage's two stretches are, and where it begins among them**, in both
fields' counts. -/
abbrev Starts : Type := Stage → (Addr × Due) × (Addr × Due)

/-- **THE PREMISE ON THE BOOK, as a test with code**: at each part of the row its entries' owners
and
starts are the table's: the first entry's the first pair, the second's the second. -/
def startsFitBy (o : Owners) (B : ProverCoinCounts) (a : At) (σ : Starts) : Bool :=
  (stages a.face).zipIdx.all fun x =>
    (entriesAt B a.place x.2).map (fun e => (e.owner, e.start)) ==
      (runsAtOwned o a x.1 x.2).zipIdx.map fun r => if r.2 == 0 then (σ x.1).1 else (σ x.1).2

/-- **The function μ reads, under each stretch's slots, its owner's coins from its start on.** -/
structure ReadsBy {W : Type} (R : Course W) (look : Addr → (d : Due) × Cs d) (σ : Starts)
    (μ : Nat → GE) : Prop where
  own : ∀ s ∈ stages R.f, ∀ i, i < s.own R.f → μ (R.first + firstSlot R.f s + i) =
    rd ((coinsE (look (σ s).1.1).2).getD ((σ s).1.2.e + i) zeroE)
  ends : ∀ s ∈ stages R.f, ∀ j, j < s.tail R.f → μ (R.endSlot s + j) =
    rd ((coinsE (look (σ s).2.1).2).getD ((σ s).2.2.e + j) zeroE)

/-! ## 2 The law -/

/-- **THE MASK ENTRIES UNDER THE LOOKUP'S SLOTS ARE THE OWNERS' COINS.** c: the row's coins, as
coins of
Honest/K3/Row.lean's row. CONDITIONAL ON `bookFitsOwned` and `startsFitBy` (premises on a book that
another hand
makes; seen to accept at no real book of the key file); on what the row's parts spend being what the
book's entries name; on the course's coins being the row's; and on `ReadsBy`. No member is typed. -/
theorem masksBy {W : Type} (R : Course W) (o : Owners) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (σ : Starts) (μ : Nat → GE)
    (c : RowCoins (lookRow (V := Unit) ⟨ptsOf, pointsAt⟩ R.J R.a))
    (hb : bookFitsOwned o B rows (fun x => (look x).1) R.a = true)
    (hst : startsFitBy o B R.a σ = true)
    (hsp : rowSpent _ c = ((List.range (stages R.f).length).map fun i =>
      (entriesAt B R.a.place i).map (lentE look)))
    (hca : CoinsAre R c) (hμ : ReadsBy R look σ μ) : MasksAre R μ := by
  intro s hs
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
    simp only [runsAtOwned, hk] at hco
    obtain ⟨lead, vs, ends⟩ := k
    cases ends with
    | none =>
      have ht : s.tail R.a.face = 0 := by rw [htail]; rfl
      have hco' : [((coinsE (look (σ s).1.1).2).drop (σ s).1.2.e).take
          (ownRun ⟨lead, vs, none⟩)] =
          firstRun (J := R.job s) (R.c s) :: (if s.tail R.f = 0 then [] else [R.masks s]) := hco
      simp only [List.cons.injEq] at hco'
      refine ⟨fun i hi => ?_, fun j hj => by rw [ht] at hj; omega⟩
      rw [hμ.own s hs i hi]
      show rd _ = rd ((firstRun (J := R.job s) (R.c s)).getD ((R.job s).shape.lead + i) zeroE)
      rw [← hco'.1, hlead, Nat.zero_add, getD_drop_take _ _ _ _ (by rw [← hown]; exact hi)]
    | some en =>
      have ht : s.tail R.a.face = en.n := by rw [htail]; rfl
      have hn0 : s.tail R.f ≠ 0 := by
        show s.tail R.a.face ≠ 0
        rw [ht]
        exact hne en rfl
      have hco' : [((coinsE (look (σ s).1.1).2).drop (σ s).1.2.e).take
          (ownRun ⟨lead, vs, some en⟩),
          ((coinsE (look (σ s).2.1).2).drop (σ s).2.2.e).take en.n] =
          firstRun (J := R.job s) (R.c s) :: (if s.tail R.f = 0 then [] else [R.masks s]) := hco
      rw [if_neg hn0] at hco'
      simp only [List.cons.injEq, and_true] at hco'
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [hμ.own s hs i hi]
        show rd _ = rd ((firstRun (J := R.job s) (R.c s)).getD ((R.job s).shape.lead + i) zeroE)
        rw [← hco'.1, hlead, Nat.zero_add, getD_drop_take _ _ _ _ (by rw [← hown]; exact hi)]
      · rw [hμ.ends s hs j hj]
        show rd _ = rd ((R.masks s).getD j zeroE)
        rw [← hco'.2, getD_drop_take _ _ _ _ (by rw [← ht]; exact hj)]

/-! ## 3 At one owner -/

/-- The table at one owner: the mask row's entries begin at base among the owner's coins; first: the
ledger's count in front of the lookup. -/
def oneStarts (a : At) (first : Nat) (o : Addr) (base : Due) : Starts := fun s =>
  ((o, base.plus ⟨0, first + firstSlot a.face s + 0⟩),
    (o, base.plus ⟨0, first + firstSlot a.face s + s.own a.face⟩))

/-- **At one owner the test is Honest/K3/Law/MasksBook.lean's.** -/
theorem startsFit_by (B : ProverCoinCounts) (a : At) (first : Nat) (o : Addr) (base : Due) :
    startsFit B a first o base = startsFitBy oneOwner B a (oneStarts a first o base) := by
  unfold startsFit startsFitBy
  congr 1
  funext x
  congr 1
  show (runsAt a x.1 x.2).zipIdx.map _ = (runsAt a x.1 x.2).zipIdx.map _
  congr 1
  funext r
  unfold oneStarts
  split <;> rfl

/-- The one owner's function reads as the table says. -/
theorem readsBy_one {W : Type} (R : Course W) (look : Addr → (d : Due) × Cs d) (o : Addr)
    (base : Due) :
    ReadsBy R look (oneStarts R.a R.first o base)
      fun j => rd ((coinsE (look o).2).getD (base.e + j) zeroE) := by
  refine ⟨fun s _ i _ => ?_, fun s _ j _ => ?_⟩
  · show rd _ = rd ((coinsE (look o).2).getD (base.e + (R.first + firstSlot R.a.face s + 0) + i) _)
    congr 2
    show base.e + (R.first + firstSlot R.a.face s + i) = _
    omega
  · show rd _ = rd ((coinsE (look o).2).getD
      (base.e + (R.first + firstSlot R.a.face s + s.own R.a.face) + j) _)
    congr 2
    show base.e + (R.first + firstSlot R.a.face s + s.own R.a.face + j) = _
    omega

/-- **Honest/K3/Law/MasksBook.lean's statement follows from `masksBy`**: so the two cannot part. -/
theorem masksFromBook_by : MasksFromBook := by
  intro W R B rows look o base c hb hst hsp hca
  rw [startsFit_by] at hst
  exact masksBy R oneOwner B rows look _ _ c hb hst hsp hca (readsBy_one R look o base)

#print axioms ProofFile.Honest.K3.Parts.masksBy
#print axioms ProofFile.Honest.K3.Parts.startsFit_by
#print axioms ProofFile.Honest.K3.Parts.readsBy_one
#print axioms ProofFile.Honest.K3.Parts.masksFromBook_by

end ProofFile.Honest.K3.Parts
