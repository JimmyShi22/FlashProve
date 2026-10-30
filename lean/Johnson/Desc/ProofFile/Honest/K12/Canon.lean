-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Canon.lean: what a view shows of a message of a proximity test's
move is the term's own round. The term is `testAll J w fr C D` (Test.lean in this folder). Its
rounds are its field `rs`, a list of `Fmt.RoundView`, and a round's items (`vals`) have the type `Fmt.ItemValue`:
words, triples of words, or roots. The message of a move (`moveAt`, Parts.lean in this folder) is a
value of `msgAt J w fr C D i` (Parts.lean), the message of round number i. `msgAt` reads each item
of the term's round number i by `saidOf` (Parts.lean): an item of the sort `.f`, `.e` or `.answer`
is read as an element of the base field or of the extension field, a `.word` passes unchanged, and a
root is left out. The frame (Johnson/Desc/ProofFile/Honest/Frame.lean) writes each item as words
again (`Said.got`). Reading and then writing gives back a triple of words that was written from an
element (`ofE`, OnBytes/Slice/Field.lean), and every item of the term's rounds is given back in this
way. General: at every job J (`TestJob`, Test.lean: what a caller supplies for its test), input w,
front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), coins C
(`TestCoins`, Test.lean), sampled challenges D and number i. Definitions and theorems.

  `msgAt_vals`: the items of round number i's message, as a view shows them, are the term's own. As
    Lean has it: where r is round number i of the term's `rs`,
    `(msgAt J w fr C D i).vals.map Said.got` is `r.vals`
  `canon_test`, `canon_stages`: every item of every round of `testAll`, and of `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean), meets `Canon`, at all arguments. No hypothesis
  `Canon g`: a definition, of an item g: `saidOf g` returns an item, and `Said.got` of that item is
    g. So g is the written form of what it is read as, and is no root: at a root `saidOf` returns
    `none`
  `CanonR rs`: a definition, of a list of rounds: every item of every round of rs meets `Canon`
  `canon_e`, `canon_answer`: for every element x of the extension field, the items `.e (ofE x)` and
    `.answer (ofE x)` meet `Canon`
  `back_of_canon`: for a list l of items that all meet `Canon`, `(l.filterMap saidOf).map Said.got`
    is l
  `CanonR.append`: if two lists of rounds meet `CanonR`, so does the first followed by the second
  `canon_showRV`, `canon_fold`, `canon_switch`, `canon_last`: `CanonR` holds of the rounds of
    `showRV` (Johnson/Prover/Link/FoldSay.lean), of a fold (`foldShown`,
    Johnson/Desc/K12/Honest/Fold.lean), of a switch (`aSwitch`, Stages.lean) and of the base case
    (`lastOut`, Johnson/Prover/Link/BodyAll.lean), at all arguments
  `canon_wr`: for every triple x in `wr n f` (Johnson/Prover/Link/Base.lean: the first n values of
    f, written by `ofE`), the item `.e x` meets `Canon`

By what. `canon_e` and `canon_answer` rewrite by `toE_ofE` (OnBytes/Slice/Field.lean): an element of
the extension field is read back from its triple. The theorems on rounds unfold the definitions that
the list names and go through each round's items; each item is closed by `canon_e` or
`canon_answer`. `canon_last` also unfolds `shownAll` (Base.lean), which is four lists of `wr`, and
calls `canon_wr`. `canon_showRV` goes by recursion on the number of rounds, `canon_stages` on the
list of stages. `msgAt_vals` unfolds `msgAt` and calls `back_of_canon` and `canon_test`.

Limits. On the items in the clear alone: nothing on a table. Of a round of the term, `msgAt_vals`
compares the field `vals` only, not the field `drawn`; where the term has no round number i, its
hypothesis holds of no r. Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- The item g is the written form of what it is read as: `saidOf g` returns an item, and `Said.got`
of that item is g. No root meets this: at a root `saidOf` returns `none`. -/
def Canon (g : Fmt.ItemValue) : Prop := (saidOf g).map Said.got = some g

/-- Every item of every round of the list rs meets `Canon`. -/
def CanonR (rs : List Fmt.RoundView) : Prop := ∀ r ∈ rs, ∀ g ∈ r.vals, Canon g

theorem canon_e (x : GE) : Canon (.e (ofE x)) := by
  show some (Fmt.ItemValue.e (ofE (toE (ofE x)))) = _
  rw [toE_ofE]

theorem canon_answer (x : GE) : Canon (.answer (ofE x)) := by
  show some (Fmt.ItemValue.answer (ofE (toE (ofE x)))) = _
  rw [toE_ofE]

/-- Reading each item of a list by `saidOf` and writing it again by `Said.got` gives the list back,
where every item of the list meets `Canon`. -/
theorem back_of_canon : ∀ l : List Fmt.ItemValue, (∀ g ∈ l, Canon g) →
    (l.filterMap saidOf).map Said.got = l
  | [], _ => rfl
  | g :: l, h => by
    have hg : (saidOf g).map Said.got = some g := h g (by simp)
    obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 hg
    rw [List.filterMap_cons_some hs, List.map_cons, e,
      back_of_canon l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem CanonR.append {a b : List Fmt.RoundView} (ha : CanonR a) (hb : CanonR b) : CanonR (a ++ b) :=
  fun r hr => (List.mem_append.1 hr).elim (ha r) (hb r)

theorem canon_showRV : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    CanonR (showRV k q D)
  | 0, _, _ => fun _ h => by cases h
  | k + 1, q, D => fun r hr g hg => by
    rcases List.mem_cons.1 hr with rfl | hr
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact canon_e _
      · rcases List.mem_cons.1 hg with rfl | hg
        · exact canon_e _
        · cases hg
    · exact canon_showRV k _ _ r hr g hg

theorem canon_fold (s : Sg) (v μ : s.cIn.J → GE) (Wc : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : CanonR (foldShown s v μ Wc D) := fun r hr g hg => by
  rcases List.mem_cons.1 hr with rfl | hr
  · rcases List.mem_cons.1 hg with rfl | hg
    · exact canon_e _
    · cases hg
  · exact canon_showRV _ _ _ r hr g hg

theorem canon_switch (cur : Fmt.M1.Stage) (o : ℕ) (D : ℕ → Fmt.Drawn) (a : GE) :
    CanonR (aSwitch cur o D a) := fun r hr g hg => by
  rcases List.mem_cons.1 hr with rfl | hr
  · cases hg
  · rcases List.mem_cons.1 hr with rfl | hr
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact canon_answer _
      · cases hg
    · cases hr

theorem canon_wr (n : ℕ) (f : ℕ → GE) : ∀ x ∈ wr n f, Canon (.e x) := fun x hx => by
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  exact canon_e _

theorem canon_last (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    CanonR (lastOut p j cur o t P col row D).rs := fun r hr g hg => by
  rcases List.mem_cons.1 hr with rfl | hr
  · rcases List.mem_cons.1 hg with rfl | hg
    · exact canon_e _
    · cases hg
  · rcases List.mem_cons.1 hr with rfl | hr
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
      unfold shownAll at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx | hx | hx <;> exact canon_wr _ _ x hx
    · cases hr

/-- **Every item of every round of `stagesAll` meets `Canon`**, at all arguments. -/
theorem canon_stages (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), CanonR (stagesAll p K rest j cur l o t P trees D).rs
  | [], j, cur, _, o, t, P, _, D => canon_last p j cur o t P (fun _ => []) (rowOf t) D
  | next :: rest, j, cur, l, o, t, P, trees, D =>
    ((canon_fold _ _ _ _ _).append (canon_switch cur o D _)).append
      (canon_stages p K rest (j + 1) next _ _ _ _ _ D)

/-- **Every item of every round of `testAll` meets `Canon`**, at all arguments. -/
theorem canon_test (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    CanonR (testAll J w fr C D).rs := by
  unfold testAll
  split
  · exact fun _ h => by cases h
  · intro r hr g hg
    rcases List.mem_cons.1 hr with rfl | hr
    · cases hg
    · exact canon_stages _ _ _ _ _ _ _ _ _ _ _ r hr g hg

/-- **The items of a message, as a view shows them, are the term's own.** The term is
`testAll J w fr C D`. Hypothesis: r is round number i of its `rs`. -/
theorem msgAt_vals (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) (r : Fmt.RoundView) (hr : (testAll J w fr C D).rs[i]? = some r) :
    (msgAt J w fr C D i).vals.map Said.got = r.vals := by
  show ((((testAll J w fr C D).rs[i]?).map fun r => r.vals.filterMap saidOf).getD []).map
    Said.got = r.vals
  rw [hr]
  exact back_of_canon _ (canon_test J w fr C D r (List.mem_of_getElem? hr))

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.canon_e
#print axioms ProofFile.Honest.K12.canon_answer
#print axioms ProofFile.Honest.K12.back_of_canon
#print axioms ProofFile.Honest.K12.CanonR.append
#print axioms ProofFile.Honest.K12.canon_showRV
#print axioms ProofFile.Honest.K12.canon_fold
#print axioms ProofFile.Honest.K12.canon_switch
#print axioms ProofFile.Honest.K12.canon_wr
#print axioms ProofFile.Honest.K12.canon_last
#print axioms ProofFile.Honest.K12.canon_stages
#print axioms ProofFile.Honest.K12.canon_test
#print axioms ProofFile.Honest.K12.msgAt_vals
#print axioms ProofFile.Honest.K12.Canon
#print axioms ProofFile.Honest.K12.CanonR
