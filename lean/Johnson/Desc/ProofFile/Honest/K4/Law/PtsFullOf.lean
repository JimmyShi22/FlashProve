-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsFullOf.lean: CONDITIONAL: on `DrawnSkel`, `LookSkel`,
`InSkel`.

What is here. THE LENGTHS OF THE SAMPLED VALUES OF THE FEED-FORWARD LAYERS' ROUNDS (`ptsOf`,
Johnson/Desc/K4/Honest/Front.lean) HANG ON HOW MANY CHALLENGES HAVE BEEN HEARD BEHIND THE ROUNDS IN
FRONT OF THE PLACE AND ON HOW MANY ELEMENTS EACH OF THESE HOLDS, and on nothing else of these
challenges. One definition, thirteen statements with their proofs, and two examples.

  `DrawnSkel`   two lists of challenges: as many, each with as many elements.
  `all2_drop`, `all2_take`, `all2_get`, `drop_take_rep`   through List.drop, List.take and a member
      by its number.
  `elems_skel`, `pw_skel`, `onesFrom_skel`, `whole_skel`, `inner_skel`, `levelR_skel`   the ways in
      which a field is made.
  `ptsOf_full`   **the sampled values of two such lists are in PtsFull.**
  `ptsOf_zero`, `k4Makers_run`   against the zero challenges in front of a part; **the clause on the
      makers at a run's own challenges.**
  The examples at the end: a member of the premise; two lists that are not in it.

Debts and ends. `DrawnSkel` IS A DEBT: a hypothesis of seven statements here: four inner ones
(`elems_skel`, `pw_skel`, `onesFrom_skel`, `inner_skel`) and `ptsOf_full`, `ptsOf_zero`,
`k4Makers_run`; a file outside this family of congruences calls `ptsOf_zero` (Law/SumAtRun.lean).
ITS PAYER, THE ONE THAT ITS WRITERS KNOW OF: `drawnSkel_of_ownFits` (Law/SumAtRun.lean), against the
first n zero challenges, from `OwnFits` (the sub-protocol's own challenges have the table's shape)
and two counts: that n of them have been heard, and that the table has as many rounds; `OwnFits` is
had where a thread stands (`k4_own_fits`, Law/OwnFits.lean). IT READS NO ELEMENT: how many
challenges, and how many elements each holds. `PtsFull` (Law/MakersAt.lean) IS A DEBT OF THE LAWS
THERE, AND TWO OF ITS THREE PAYERS ARE HERE: `ptsOf_full` and `ptsOf_zero`, from `DrawnSkel` and
`LookSkel`. `LookSkel` IS A DEBT: see Law/LookSkel.lean: a hypothesis of `ptsOf_full`, `ptsOf_zero`
and `k4Makers_run`. `InSkel` (Law/MakersAt.lean) IS A DEBT: see there: the hypothesis I of
`k4Makers_run`.

Not shown here. THAT THE CHALLENGES OF A RUN HOLD AS MANY ELEMENTS AS THE VERIFIER's TABLE SAYS
(`DrawnSkel` against the zero challenges) IS A PREMISE HERE. THAT hs k IS THE LIST WHICH THE PART OF
MASKED SUMCHECK NUMBER k SEES IN A RUN IS NOT SHOWN: no statement here ties `(starts Q).getD k 0` to
the part's place in the row. OF hb NOTHING IS ASKED BUT WHAT `look` RETURNS AT hb 1: the two long
lists' lengths hang on nothing else. `LookSkel` of what `look` returns is a premise: WHERE THE
TEST's YES STANDS AT WHAT `look` RETURNS OF THE RUN's OWN CHALLENGES IN FRONT OF THE PLACE, AS IN
`K4Seated` (Law/Seated.lean), IT HOLDS OF A THING AND ITSELF (`lookSkel_refl`, Law/LookSkel.lean).
WHERE THE TEST IS ASKED ONCE, AT A LIST LAID BEFORE ANY CHALLENGE (`k4Side`, Honest/K4/Part.lean),
Lb AND Ls STAY OWED: no law that its writers know of has `LookSkel` between what `look` returns at
two lists. `k4MakersAt`'s clauses count a job's end values at challenges 0: for the batched sumcheck
`stack_ends_len` (Law/AtEnds.lean) carries the number to a run's. Nothing on the values.

Kin. `all2_get` IS THE LIBRARY's `all2_getElem?` (OnBytes/Flat/LinksFreeHeadB.lean) WITH THE NUMBER
IN FRONT OF THE TWO LISTS; this file does not import that one. `drop_take_rep` stands beside two
theorems named `drop_take_mid` (OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean,
Honest/Law/Rule/Stands.lean): the middle of three lists laid end to end. `pw_skel` calls
`powers_size` (OnBytes/Desc/First/P1/BatchPoint.lean; two more theorems of the library have that
name and sentence). `levelR_skel` calls `foldl_size` (Law/SkelLists.lean). The head of
Honest/K4/Part.lean names `k4Makers_run`; `k4_makers_seated_all` (Law/SeatedRun.lean (no part of the
library yet)) calls it, and no other file of its writers; `makersAt_one` (Law/SumAtRun.lean) does
not call it: it goes from `k4MakersAt_skel` and `ptsOf_zero` themselves, one sumcheck at a time. The
library has another definition under the short name PtsFull (Johnson/LinkSim/AtText/ShortTail.lean),
in another namespace, on another thing; none under DrawnSkel was found.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersAt
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard powers)
open OnBytes.Flat (All2 OptRel)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-- Two lists of challenges: as many, each with as many elements of the extension field. -/
def DrawnSkel (l l₀ : List Fmt.Drawn) : Prop :=
  All2 (fun d d₀ : Fmt.Drawn => d.elems.length = d₀.elems.length) l l₀

/-- Two lists in R member by member stay so behind their first n members. -/
theorem all2_drop {α β : Type} {R : α → β → Prop} : ∀ (n : Nat) {l : List α} {l' : List β},
    All2 R l l' → All2 R (l.drop n) (l'.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ h => all2_drop n h

/-- And in their first n members. -/
theorem all2_take {α β : Type} {R : α → β → Prop} : ∀ (n : Nat) {l : List α} {l' : List β},
    All2 R l l' → All2 R (l.take n) (l'.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h0 h => .cons h0 (all2_take n h)

/-- The members of one number: both are missing, or both are there and in R. -/
theorem all2_get {α : Type} {R : α → α → Prop} : ∀ (j : Nat) {l l' : List α},
    All2 R l l' → OptRel R l[j]? l'[j]?
  | _, _, _, .nil => trivial
  | 0, _, _, .cons h0 _ => h0
  | j + 1, _, _, .cons _ h => all2_get j h

variable {own own₀ : List Fmt.Drawn}

/-- The elements that the challenge of a given number holds. -/
theorem elems_skel (h : DrawnSkel own own₀) (i : Option Nat) :
    (((i.bind fun j => own[j]?).map elemsOf).getD #[]).size =
      (((i.bind fun j => own₀[j]?).map elemsOf).getD #[]).size := by
  cases i with
  | none => rfl
  | some j =>
    have r := all2_get j h
    show ((own[j]?.map elemsOf).getD #[]).size = ((own₀[j]?.map elemsOf).getD #[]).size
    revert r
    cases own[j]? <;> cases own₀[j]? <;> intro r
    · rfl
    · exact False.elim r
    · exact False.elim r
    · show (elemsOf _).size = (elemsOf _).size
      unfold elemsOf
      rw [List.size_toArray, List.size_toArray, List.length_map, List.length_map]
      exact r

/-- The powers of its first element. -/
theorem pw_skel (h : DrawnSkel own own₀) (i : Option Nat) (n : Nat) :
    ((((((i.bind fun j => own[j]?).map elemsOf).getD #[])[0]?).map fun x => powers x n).getD
        #[]).size =
      ((((((i.bind fun j => own₀[j]?).map elemsOf).getD #[])[0]?).map fun x => powers x n).getD
        #[]).size := by
  have e := elems_skel h i
  generalize ((i.bind fun j => own[j]?).map elemsOf).getD #[] = a at e ⊢
  generalize ((i.bind fun j => own₀[j]?).map elemsOf).getD #[] = a₀ at e ⊢
  by_cases hp : 0 < a.size
  · have hp₀ : 0 < a₀.size := e ▸ hp
    rw [Array.getElem?_eq_getElem hp, Array.getElem?_eq_getElem hp₀]
    show (powers _ n).size = (powers _ n).size
    rw [OnBytes.Desc.First.P1.powers_size, OnBytes.Desc.First.P1.powers_size]
  · have hp₀ : ¬ 0 < a₀.size := e ▸ hp
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hp), Array.getElem?_eq_none (Nat.le_of_not_lt hp₀)]

/-- The first elements of n challenges from number i on: as many. -/
theorem onesFrom_skel (h : DrawnSkel own own₀) (i n : Nat) :
    (onesFrom own i n).size = (onesFrom own₀ i n).size := by
  unfold onesFrom
  rw [List.size_toArray, List.size_toArray, List.length_map, List.length_map]
  exact (all2_take n (all2_drop i h)).length

/-- `whole n` at two arrays of one size: of one size. -/
theorem whole_skel (n : Nat) {a a₀ : Array E} (h : a.size = a₀.size) :
    (whole n a).size = (whole n a₀).size := by
  unfold whole
  rw [h]
  split
  · exact h
  · rfl

/-- The challenges of the n rounds behind a masked sumcheck's first. -/
theorem inner_skel (h : DrawnSkel own own₀) (o : Option Nat) (n : Nat) :
    ((o.map fun s => whole n (onesFrom own (s + 1) n)).getD #[]).size =
      ((o.map fun s => whole n (onesFrom own₀ (s + 1) n)).getD #[]).size := by
  cases o with
  | none => rfl
  | some s => exact whole_skel n (onesFrom_skel h (s + 1) n)

/-- A level's point, made of two arrays of one size: of one size. -/
theorem levelR_skel (mu : Nat) (order : List Nat) {xs xs₀ : Array E} (h : xs.size = xs₀.size) :
    (levelR mu order xs).size = (levelR mu order xs₀).size := by
  unfold levelR
  rw [h]
  split
  · rfl
  · rw [foldl_size (f := fun (r : Array E) (x : Nat × E) => r.set! (mu - 1 - x.1) x.2)
        (fun _ _ => Array.size_setIfInBounds ..),
      foldl_size (f := fun (r : Array E) (x : Nat × E) => r.set! (mu - 1 - x.1) x.2)
        (fun _ _ => Array.size_setIfInBounds ..)]

/-- **The sampled values of two lists of challenges are in PtsFull where K4's OWN challenges in them
are as many, each with as many elements**, and what `look` returns of those in front is in LookSkel.
Of the challenges in front of the place nothing else is asked. -/
theorem ptsOf_full (Q : K4Pub) (w w₀ : K4In) {heard heard₀ : List Fmt.Drawn}
    (o : DrawnSkel (heard.drop Q.r0) (heard₀.drop Q.r0))
    (L : LookSkel (w.look (heard.take Q.r0)) (w₀.look (heard₀.take Q.r0))) :
    PtsFull (ptsOf Q w heard) (ptsOf Q w₀ heard₀) := by
  have ite_sz : ∀ (c : Bool) {a a₀ : Array E}, a.size = a₀.size →
      (if c = true then a else #[]).size = (if c = true then a₀ else #[]).size := by
    intro c a a₀ e
    cases c
    · rfl
    · exact e
  have hPV : (ptsOf Q w heard).PV.size = (ptsOf Q w₀ heard₀).PV.size := by
    unfold ptsOf
    dsimp only
    exact elems_skel o _
  have hZE : (ptsOf Q w heard).ZE.size = (ptsOf Q w₀ heard₀).ZE.size := by
    unfold ptsOf
    dsimp only
    exact ite_sz _ (elems_skel o _)
  have htkh : (ptsOf Q w heard).tkh.size = (ptsOf Q w₀ heard₀).tkh.size := by
    unfold ptsOf
    dsimp only
    exact ite_sz _ (elems_skel o _)
  have hgp : (ptsOf Q w heard).gp.size = (ptsOf Q w₀ heard₀).gp.size := by
    unfold ptsOf
    dsimp only
    exact pw_skel o _ _
  have hrhoI : (ptsOf Q w heard).rhoI.size = (ptsOf Q w₀ heard₀).rhoI.size := by
    unfold ptsOf
    dsimp only
    exact elems_skel o _
  have hr6 : (ptsOf Q w heard).r6.size = (ptsOf Q w₀ heard₀).r6.size := by
    unfold ptsOf
    dsimp only
    exact levelR_skel _ _ (inner_skel o _ _)
  have homV : (ptsOf Q w heard).omV.size = (ptsOf Q w₀ heard₀).omV.size := by
    unfold ptsOf
    dsimp only
    exact pw_skel o _ _
  have hrtV : (ptsOf Q w heard).rtV.size = (ptsOf Q w₀ heard₀).rtV.size := by
    unfold ptsOf
    dsimp only
    exact inner_skel o _ _
  have hrt : (ptsOf Q w heard).rt.size = (ptsOf Q w₀ heard₀).rt.size := by
    unfold ptsOf
    dsimp only
    exact inner_skel o _ _
  have hom : (ptsOf Q w heard).om.size = (ptsOf Q w₀ heard₀).om.size := by
    unfold ptsOf
    dsimp only
    exact pw_skel o _ _
  have hrs : (ptsOf Q w heard).rs.size = (ptsOf Q w₀ heard₀).rs.size := by
    unfold ptsOf
    dsimp only
    rw [Array.size_reverse, Array.size_reverse]
    exact inner_skel o _ _
  have hr12 : (ptsOf Q w heard).r12.size = (ptsOf Q w₀ heard₀).r12.size := by
    unfold ptsOf
    dsimp only
    exact levelR_skel _ _ (inner_skel o _ _)
  have hrhoM : (ptsOf Q w heard).rhoM.size = (ptsOf Q w₀ heard₀).rhoM.size := by
    unfold ptsOf
    dsimp only
    exact elems_skel o _
  have hr14 : (ptsOf Q w heard).r14.size = (ptsOf Q w₀ heard₀).r14.size := by
    unfold ptsOf
    dsimp only
    exact levelR_skel _ _ (inner_skel o _ _)
  have hrhoW : (ptsOf Q w heard).rhoW.size = (ptsOf Q w₀ heard₀).rhoW.size := by
    unfold ptsOf
    dsimp only
    exact pw_skel o _ _
  exact ⟨⟨L, hPV, hZE, hr6, hrtV, hrt, hr12, hr14⟩, htkh, hgp, hrhoI, homV, hom, hrs, hrhoM, hrhoW⟩

/-- Behind r copies of x in front of l: the first r + n members less the first r are l's first n. -/
theorem drop_take_rep {α : Type} (x : α) (l : List α) : ∀ r n : Nat,
    ((List.replicate r x ++ l).take (r + n)).drop r = l.take n
  | 0, n => by simp
  | r + 1, n => by
    rw [List.replicate_succ, List.cons_append, Nat.add_right_comm r 1 n, List.take_succ_cons,
      List.drop_succ_cons]
    exact drop_take_rep x l r n

/-- Against the zero challenges of which the first n of K4's own rounds have been heard. -/
theorem ptsOf_zero (Q : K4Pub) (w : K4In) {heard : List Fmt.Drawn} {fo₀ : Forest.Heard} (n : Nat)
    (h : DrawnSkel (heard.drop Q.r0) ((k4ZeroOwn Q).take n))
    (L : LookSkel (w.look (heard.take Q.r0)) fo₀) :
    PtsFull (ptsOf Q w heard) (k4ZeroPts Q fo₀ n) := by
  refine ptsOf_full Q w (k4ZeroIn Q fo₀) ?_ L
  unfold k4ZeroHeard
  rw [drop_take_rep]
  exact h

/-- **A yes of the test's clause on the makers is a yes at a run's own challenges**: hs k: the
challenges in front of masked sumcheck number k; hb k: those in front of the round number k that
batches rows. Premises: the tokens fit as the zero input's do; behind the rounds in front of the
place each list hs k has as many challenges as K4's table has rounds in front of that part, each
with as many elements as its round samples; what `look` returns of each list hs k, and of hb 1 (of
the other hb k nothing is asked), is in LookSkel with the list at which the test was asked. All of
Hs is met in one stroke by hs k := the run's challenges cut behind Q.r0 + (starts Q).getD k 0 of
them, where these have the table's shape. -/
theorem k4Makers_run {Q : K4Pub} {fo₀ : Forest.Heard} (h : k4MakersFit Q fo₀ = true) {w : K4In}
    (I : InSkel Q w (k4ZeroIn Q fo₀)) (hb hs : Nat → List Fmt.Drawn)
    (Lb : LookSkel (w.look ((hb 1).take Q.r0)) fo₀)
    (Hs : ∀ k, DrawnSkel ((hs k).drop Q.r0) ((k4ZeroOwn Q).take ((starts Q).getD k 0)))
    (Ls : ∀ k, LookSkel (w.look ((hs k).take Q.r0)) fo₀) (sh : Array E) :
    k4MakersAt Q w (fun k => ptsOf Q w (hb k)) (fun k => ptsOf Q w (hs k)) sh = true :=
  k4Makers_everywhere h I Lb (fun k => ptsOf_zero Q w _ (Hs k) (Ls k)) sh

/-- A member of the premise: the same challenges with other elements. -/
example (l : List Fmt.Drawn) (f : UInt64 × UInt64 × UInt64 → UInt64 × UInt64 × UInt64) :
    DrawnSkel (l.map fun d => { d with elems := d.elems.map f }) l := by
  induction l with
  | nil => exact .nil
  | cons d l ih => exact .cons (List.length_map ..) ih

/-- Negative test: a list with one challenge more is not in the relation. -/
example (l : List Fmt.Drawn) (d : Fmt.Drawn) : ¬ DrawnSkel (d :: l) l := fun h => by
  have e := All2.length h
  rw [List.length_cons] at e
  omega

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.DrawnSkel
#print axioms ProofFile.Honest.K4.all2_drop
#print axioms ProofFile.Honest.K4.all2_take
#print axioms ProofFile.Honest.K4.all2_get
#print axioms ProofFile.Honest.K4.elems_skel
#print axioms ProofFile.Honest.K4.pw_skel
#print axioms ProofFile.Honest.K4.onesFrom_skel
#print axioms ProofFile.Honest.K4.whole_skel
#print axioms ProofFile.Honest.K4.inner_skel
#print axioms ProofFile.Honest.K4.levelR_skel
#print axioms ProofFile.Honest.K4.ptsOf_full
#print axioms ProofFile.Honest.K4.drop_take_rep
#print axioms ProofFile.Honest.K4.ptsOf_zero
#print axioms ProofFile.Honest.K4.k4Makers_run
