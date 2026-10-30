-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PlanPartsAtM3.lean: kind K13, the members' batching: WHAT THE
MAKER OF THE BOOK OF COINS READS OFF THE PLAN AT A SUB-PROTOCOL THAT HAS THE KIND's ROUNDS AND
STANDS AT THE KIND's PLACE: TWO PARTS; THE SECOND ALONE IS A MASKED SUMCHECK; ITS OWN SCALARS ARE 2
kCol + 1. Two definitions with code, and statements with their proofs. General in the kind's numbers
p and in the sub-protocol: no hypothesis on a proof file, no closed fact.

Main names: `k13QuietPartAt`, `k13SumPartAt`: the two parts as lists of (a round's name, its number
of scalars). `k13_partsCut_of`: the maker's cut (`partsCut`, Honest/BookOf.lean) is [1, 1 + kCol].
`k13_planParts_of`: **`planParts` (Honest/BookEntries.lean) yields just these two**;
`k13_planParts_atM3`: at the kind's own sub-protocol `atM3`; `k13_planParts_length`: they are two.
`k13_quietPart_not_sum`, `k13_sumPart_isSum`, `k13_sumPart_ownScalars`: which is a masked sumcheck,
and its count. `k13_no_fold_epsilon`: no round is named "FOLD epsilon". `k13_listed_scalars`:
**where the second part's address is listed, the listed sumchecks' own scalars at this sub-protocol
add up to 2 kCol + 1.**

Why. The premise on the book in CoinsTieAtHead.lean of this folder (hS) has four written terms: the
number of the row's parts, 2; the owner; the first entry; the count 2 kCol + 1. The frame's law on
which entries a sub-protocol outside a segment spends (`bookWhole_lone_stretch`,
Honest/BookLoneStretch.lean; this file does not import it) speaks in the maker's terms: the number
of `planParts`, and a fold over them that adds the own scalars of the parts that are listed and are
sumchecks (`loneScalarsOf`). `k13_listed_scalars` has that fold written out on its left side: that
the two are one is held by Lean in PlanPartsListed.lean of this folder (`k13_lone_scalars`). These
statements reach the first and the last of the four terms, the last where the part is listed; the
owner and the first entry are not touched.

How. The rounds' names are "BAT-sigma", "PSC epsilon" and kCol times "PSC round" (`battRounds`,
Johnson/Desc/K13/Kind.lean). The maker cuts a list of names unit by unit: "BAT-sigma" is a unit of
one round; "PSC epsilon" takes the run of "PSC round" behind it. A round's scalars are its message's
bytes, here without roots or sample answers, by 24: 0, 1 and 2. None of the three names is among the
frame's names (`frameNames`).

Limits. THAT THE SECOND PART's ADDRESS IS LISTED IS A PREMISE of `k13_listed_scalars`: it is shown
at the list `mergesByName` in PlanPartsListed.lean of this folder, and nowhere else. Nothing but
that file calls these statements yet. It says what functions of the plan return: nothing on any
book, on which entries are lent, or on what a part does. That the sub-protocol number 355 of a proof
file's first chain has these rounds and this place is not shown here (FromThreadAt.lean of this
folder has both, under the library's hypothesis).

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookEntries
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.K13.Law.Tile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K13 (Where atM3 battRounds)
open VerifiableInference.Desc.K13.Law (atM3_rounds)

variable {S Cl : Type}

/-- The part number 0 as the maker reads it off the plan: one round, no scalar. -/
def k13QuietPartAt (p : Where) : PartAt := ⟨⟨k13Place p, 0⟩, [("BAT-sigma", 0)]⟩

/-- The part number 1: "PSC epsilon" with one scalar, then kCol rounds "PSC round" with two each. -/
def k13SumPartAt (p : Where) : PartAt :=
  ⟨⟨k13Place p, 1⟩, ("PSC epsilon", 1) :: List.replicate p.lin.kCol ("PSC round", 2)⟩

/-- The run of a name at the head of so many copies of it. -/
theorem headRun_replicate (s : String) (n : ℕ) : headRun s (List.replicate n s) = n := by
  simp [headRun]

/-- The names of the kind's rounds. -/
theorem k13_names (p : Where) :
    (battRounds p).map (·.entry.name) =
      "BAT-sigma" :: "PSC epsilon" :: List.replicate p.lin.kCol "PSC round" := by
  simp [battRounds, VerifiableInference.Desc.K13.sigmaEntry, VerifiableInference.Desc.K13.epsEntry,
    VerifiableInference.Desc.K13.roundEntry]

/-- **The maker's cut**: one round; then "PSC epsilon" with its kCol rounds. -/
theorem k13_partsCut_of {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p)
    (hp : b.place = k13Place p) : partsCut b = [1, 1 + p.lin.kCol] := by
  unfold partsCut
  rw [hr, hp, k13_names]
  have hs : sumTail (List.replicate p.lin.kCol "PSC round") = p.lin.kCol := by
    simp [sumTail, headRun_replicate, headOne]
  have h2 : unitLen ("PSC epsilon" :: List.replicate p.lin.kCol "PSC round") =
      1 + p.lin.kCol := by
    simp [unitLen, hs]
  have h1 : unitLen ("BAT-sigma" :: "PSC epsilon" :: List.replicate p.lin.kCol "PSC round") =
      1 := by
    simp [unitLen]
  have u (k : ℕ) (a : String) (l : List String) : unitsOf (k + 1) (a :: l) =
      unitLen (a :: l) :: unitsOf k ((a :: l).drop (unitLen (a :: l))) := rfl
  have u0 (k : ℕ) : unitsOf k [] = [] := by cases k <;> rfl
  have hd : ("PSC epsilon" :: List.replicate p.lin.kCol "PSC round").drop (1 + p.lin.kCol) =
      [] := List.drop_eq_nil_of_le (by simp [Nat.add_comm])
  have hU : unitsOf ("BAT-sigma" :: "PSC epsilon" :: List.replicate p.lin.kCol "PSC round").length
      ("BAT-sigma" :: "PSC epsilon" :: List.replicate p.lin.kCol "PSC round") =
      [1, 1 + p.lin.kCol] := by
    rw [show ("BAT-sigma" :: "PSC epsilon" :: List.replicate p.lin.kCol "PSC round").length =
      (p.lin.kCol + 1) + 1 from by simp, u, h1]
    show 1 :: unitsOf (p.lin.kCol + 1) ("PSC epsilon" :: List.replicate p.lin.kCol "PSC round") = _
    rw [u, h2, hd, u0]
  unfold cutOfNames
  rw [hU]
  rfl

/-- **What the maker reads off the plan: just these two parts.** -/
theorem k13_planParts_of {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p)
    (hp : b.place = k13Place p) : planParts b = [k13QuietPartAt p, k13SumPartAt p] := by
  unfold planParts
  rw [k13_partsCut_of hr hp, hr, hp]
  simp [battRounds, stretchesBy, scalarsIn, k13QuietPartAt, k13SumPartAt, List.zipIdx,
    VerifiableInference.Desc.K13.sigmaEntry, VerifiableInference.Desc.K13.epsEntry,
    VerifiableInference.Desc.K13.roundEntry]

/-- At the kind's own sub-protocol: so the two premises hr and hp can be met together. -/
theorem k13_planParts_atM3 (p : Where) :
    planParts (atM3 (Cl := Cl) p) = [k13QuietPartAt p, k13SumPartAt p] :=
  k13_planParts_of (atM3_rounds p) rfl

/-- They are two. -/
theorem k13_planParts_length {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p)
    (hp : b.place = k13Place p) : (planParts b).length = 2 := by
  rw [k13_planParts_of hr hp]
  rfl

/-- The first is no masked sumcheck. -/
theorem k13_quietPart_not_sum (p : Where) : (k13QuietPartAt p).isSum = false := by
  simp [k13QuietPartAt, PartAt.isSum]

/-- The second is one. -/
theorem k13_sumPart_isSum (p : Where) : (k13SumPartAt p).isSum = true := by
  simp [k13SumPartAt, PartAt.isSum]

/-- The fold of `PartAt.ownScalars`, over n copies of ("PSC round", 2), from m: it adds 2 for
each. -/
theorem foldl_rounds (n m : ℕ) :
    (List.replicate n ("PSC round", 2)).foldl
      (fun k (r : String × ℕ) => if frameNames.contains r.1 then k else k + r.2) m = m + 2 * n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, show (if frameNames.contains ("PSC round", 2).1 then m
      else m + ("PSC round", 2).2) = m + 2 from if_neg (by decide), ih]
    omega

/-- **Its own scalars are 2 kCol + 1.** -/
theorem k13_sumPart_ownScalars (p : Where) : (k13SumPartAt p).ownScalars = 2 * p.lin.kCol + 1 := by
  unfold PartAt.ownScalars k13SumPartAt
  rw [List.foldl_cons, show (if frameNames.contains ("PSC epsilon", 1).1 then 0
    else 0 + ("PSC epsilon", 1).2) = 1 from by decide, foldl_rounds]
  omega

/-- **No round is named "FOLD epsilon".** -/
theorem k13_no_fold_epsilon {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p) :
    ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon" := by
  intro r hm
  have hn : r.entry.name ∈ (battRounds p).map (·.entry.name) :=
    List.mem_map.2 ⟨r, hr ▸ hm, rfl⟩
  rw [k13_names] at hn
  rcases List.mem_cons.1 hn with e | hn
  · rw [e]
    decide
  · rcases List.mem_cons.1 hn with e | hn
    · rw [e]
      decide
    · rw [List.eq_of_mem_replicate hn]
      decide

/-- **WHERE THE SECOND PART's ADDRESS IS LISTED, THE LISTED SUMCHECKS' OWN SCALARS AT THIS
SUB-PROTOCOL ADD UP TO 2 kCol + 1.** Whether the first part's address is listed does not matter: it
is no sumcheck. -/
theorem k13_listed_scalars {b : Block S Cl} {p : Where} (hr : b.rounds = battRounds p)
    (hp : b.place = k13Place p) (lone : List Addr) (hl : lone.contains ⟨k13Place p, 1⟩ = true) :
    (planParts b).foldl
      (fun n q => if lone.contains q.addr && q.isSum then n + q.ownScalars else n) 0 =
      2 * p.lin.kCol + 1 := by
  rw [k13_planParts_of hr hp, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    k13_quietPart_not_sum, k13_sumPart_isSum, k13_sumPart_ownScalars]
  have ha : (k13SumPartAt p).addr = ⟨k13Place p, 1⟩ := rfl
  rw [ha, hl]
  simp

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.headRun_replicate
#print axioms ProofFile.Honest.K13.k13_names
#print axioms ProofFile.Honest.K13.k13_partsCut_of
#print axioms ProofFile.Honest.K13.k13_planParts_of
#print axioms ProofFile.Honest.K13.k13_planParts_atM3
#print axioms ProofFile.Honest.K13.k13_planParts_length
#print axioms ProofFile.Honest.K13.k13_quietPart_not_sum
#print axioms ProofFile.Honest.K13.k13_sumPart_isSum
#print axioms ProofFile.Honest.K13.foldl_rounds
#print axioms ProofFile.Honest.K13.k13_sumPart_ownScalars
#print axioms ProofFile.Honest.K13.k13_no_fold_epsilon
#print axioms ProofFile.Honest.K13.k13_listed_scalars
