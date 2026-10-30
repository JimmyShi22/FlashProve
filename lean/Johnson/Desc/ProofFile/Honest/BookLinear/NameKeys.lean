-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/NameKeys.lean: WHERE THE NAMES OF A LIST OF ENTRIES ARE THE
NAMES OF A LIST K OF KEYS (hK), THE TWO TABLES OF STRINGS PASS tablesOk, EVERY KEY LIES IN THE
TABLES, AND NO TWO KEYS HAVE ONE CODE (nodupN), THE ELEVENTH TEST OF ProverCoinCounts.clauses
(Honest/Frame.lean: "two entries bear one name") ACCEPTS THE LIST (clause11_of_keys). NO NAME IS
OPENED BY THE THREE TESTS (together: "the twin" below): they read numbers and two short tables. THE
LAW HOLDS WHATEVER K IS: THAT K IS THE LIST's IS hK, AN EQUATION OF TWO LISTS OF STRINGS: THE ONE
PREMISE THAT SPEAKS OF THE NAMES THEMSELVES: IT IS SHOWN AT NO BOOK, AND WHAT IT COSTS IS NOT KNOWN.
ONE DIRECTION ALONE. Definitions with code; statements with their proofs; closed facts. Written by
the authors of the honest side of the linear claim's shared rounds (K14), in the frame's folder, not
by the frame's authors; Ahead, Addr and the test are the frame's (Honest/Frame.lean); runName and
carriedName too (Honest/ForKinds.lean).

  NameKey         what a name is made of: of a spent run: the owner's string and the use, each by
                  its number in a table, and the address that is handed the run; of a carried run:
                  the sender's address, the message's number, the address that is handed it
  NameKey.name owners uses k   the name: runName or carriedName (Honest/ForKinds.lean) at what k
                  holds; a number beyond a table reads ""
  NameKey.code k  the key as one number, by Addr.code (Honest/BookLinear/Tool.lean); even for a
                  spent run, odd for a carried one
  tablesOk owners uses   no string twice in either table; no use holds a colon; no use is "carried"
  NameKey.inTables no nu k   a spent run's two numbers lie below the tables' lengths
  code_of_name    **where the tables pass and both keys lie in them: one name → one code**: by
                  runName_inj, carriedName_inj, runName_ne_carried (Honest/BookLinear/Names.lean);
                  equal spots have equal codes (code_of_spot); a table without a string twice is
                  one-to-one on its numbers (atTable_inj)
  clause11_of_keys   **the statement of the title**: THE CONCLUSION IS THE TEST's Bool AS IT STANDS
                  IN ProverCoinCounts.clauses, with the list as a letter: at l := B.ahead it is the eleventh
                  premise of clauses_all_of_each (Honest/BookWordOf.lean), to the letter. By
                  nodup_map_of (different codes, and one name → one code: so different names) and
                  clause11_of_nodup (Honest/BookLinear/Eleventh.lean)

THAT NameKey.code OR Addr.code IS ONE-TO-ONE IS NOT ASKED: where two keys with different names share
a code, the twin rejects. What the law leans on is the other direction, at this one code: keys in
the tables with one name have one code (code_of_name). THE PLACE's KIND: a name does not print it
and the codes leave it out: two keys that differ in a kind alone bear one name (Names.lean:
kind_not_read) and have one code: there the twin rejects, AND SO DOES THE TEST. That two places of a
description differ in more than the kind is not shown here. Where a description passes the library's
test FileDescription.placesOk (Johnson/Desc/Block.lean) it is so by that test's text: it counts each
(chain, link, piece) once; the frame's orderOf_nodup (Honest/Law/Rule/Tests.lean) has this inside
its proof and concludes less; no law states it.

THE FOUR PREMISES HOLD TOGETHER at a small list (clause11_keys_small: the law is spent there). BOTH
PREMISES ON THE TABLES ARE NEEDED (closed facts): tables_needed: with one string twice in the
owners' table two keys with different codes bear one name; inTables_needed: so do two keys whose
owner's number lies beyond the table.

Kin. VerifiableInference.Desc.K13.Honest.getD_mem (Johnson/Desc/K13/Honest/WithTaken.lean): "A
list's member by its number is in the list": atTable_mem is that at strings and "": it is not
called: its file's imports; here it is two calls of the core library. Mathlib's List.Nodup.map_on:
from "f is one-to-one on l" and l.Nodup; nodup_map_of starts from another function's values. No law
on names' keys, and none that concludes the eleventh test, was found in the frame's files or this
kind's beside Eleventh.lean.

Limits. WHERE K COMES FROM IS NOT SAID: no maker of keys stands here; hK is shown at no book. THE
TWIN REJECTS LISTS THAT THE TEST ACCEPTS: where two keys share a code though their names differ (a
number from 2 ^ 8, 2 ^ 20 or 2 ^ 80 on can run into the next field); where the sort has too few
rounds. The tables at which tables_small accepts are four strings and the five uses of
Honest/ForKinds.lean: that a book's makers pass no other owner's string or use is not shown: one of
them passes a message's own name. The closed facts are evaluations in Lean's kernel (decide
+kernel); clause11_keys_small is a call of the law over three such and a rfl. Nothing on what an
evaluation costs. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookLinear.Names
import Johnson.Desc.ProofFile.Honest.BookLinear.Eleventh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- What an entry's name is made of. -/
inductive NameKey
  /-- a spent run: the owner's string and the use, by their numbers in two tables; its address -/
  | spent (owner : Nat) (dest : Addr) (use : Nat)
  /-- a carried run: the sender; the message's number; who is handed it -/
  | carried (sender : Addr) (msg : Nat) (dest : Addr)

/-- The name that a key stands for, at two tables of strings. -/
def NameKey.name (owners uses : List String) : NameKey → String
  | .spent o d u => runName (owners.getD o "") d (uses.getD u "")
  | .carried s m d => carriedName s m d

/-- A key as one number: even for a spent run, odd for a carried one. -/
def NameKey.code : NameKey → Nat
  | .spent o d u => ((o * 2 ^ 8 + u) * 2 ^ 80 + d.code) * 2
  | .carried s m d => ((s.code * 2 ^ 20 + m) * 2 ^ 80 + d.code) * 2 + 1

/-- The test on the two tables: no string twice; no use holds a colon or is "carried". -/
def tablesOk (owners uses : List String) : Bool :=
  decide owners.Nodup && decide uses.Nodup &&
    uses.all fun u => !u.toList.contains ':' && u != "carried"

/-- A spent run's two numbers lie below the tables' lengths. -/
def NameKey.inTables (no nu : Nat) : NameKey → Bool
  | .spent o _ u => decide (o < no) && decide (u < nu)
  | .carried _ _ _ => true

/-- Equal spots have equal codes: `Addr.code` reads what `Addr.spot` holds. -/
theorem code_of_spot {a b : Addr} (h : a.spot = b.spot) : a.code = b.code := by
  simp only [Addr.spot, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Addr.code
  rw [h1, h2, h3, h4]

/-- A table without a string twice is one-to-one on its numbers. -/
theorem atTable_inj {l : List String} (hn : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i "" = l.getD j "") : i = j := by
  rw [List.getD_eq_getElem l "" hi, List.getD_eq_getElem l "" hj] at h
  exact (List.Nodup.getElem_inj_iff hn).1 h

/-- A table's string by its number is in the table. -/
theorem atTable_mem {l : List String} {i : Nat} (hi : i < l.length) : l.getD i "" ∈ l := by
  rw [List.getD_eq_getElem l "" hi]
  exact List.getElem_mem hi

/-- Where the values of c are all different, and one value of f gives one value of c, the values of
f are all different. -/
theorem nodup_map_of {α β γ : Type} (f : α → β) (c : α → γ) (l : List α) (hc : (l.map c).Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, f a = f b → c a = c b) : (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map] at hc ⊢
  exact hc.imp_of_mem fun {a b} ha hb hab e => hab (h a ha b hb e)

/-- **ONE NAME → ONE CODE**, where the tables pass and both keys lie in them. -/
theorem code_of_name {owners uses : List String} (hT : tablesOk owners uses = true) {k k' : NameKey}
    (hk : k.inTables owners.length uses.length = true)
    (hk' : k'.inTables owners.length uses.length = true)
    (h : k.name owners uses = k'.name owners uses) : k.code = k'.code := by
  unfold tablesOk at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hT
  obtain ⟨⟨hO, hU⟩, hA⟩ := hT
  have nc : ∀ u ∈ uses, ':' ∉ u.toList := fun u hu hm => by
    have := (hA u hu).1
    rw [List.contains_iff_mem.2 hm] at this
    cases this
  cases k with
  | spent o d u =>
    simp only [NameKey.inTables, Bool.and_eq_true, decide_eq_true_eq] at hk
    cases k' with
    | spent o' d' u' =>
      simp only [NameKey.inTables, Bool.and_eq_true, decide_eq_true_eq] at hk'
      obtain ⟨e1, e2, e3⟩ := runName_inj (nc _ (atTable_mem hk.2)) (nc _ (atTable_mem hk'.2)) h
      show ((o * 2 ^ 8 + u) * 2 ^ 80 + d.code) * 2 = ((o' * 2 ^ 8 + u') * 2 ^ 80 + d'.code) * 2
      rw [atTable_inj hO hk.1 hk'.1 e1, code_of_spot e2, atTable_inj hU hk.2 hk'.2 e3]
    | carried s m d' =>
      exact absurd h (runName_ne_carried (nc _ (atTable_mem hk.2)) (hA _ (atTable_mem hk.2)).2)
  | carried s m d =>
    cases k' with
    | spent o' d' u' =>
      simp only [NameKey.inTables, Bool.and_eq_true, decide_eq_true_eq] at hk'
      exact absurd h.symm
        (runName_ne_carried (nc _ (atTable_mem hk'.2)) (hA _ (atTable_mem hk'.2)).2)
    | carried s' m' d' =>
      obtain ⟨e1, e2, e3⟩ := carriedName_inj h
      show ((s.code * 2 ^ 20 + m) * 2 ^ 80 + d.code) * 2 + 1 =
        ((s'.code * 2 ^ 20 + m') * 2 ^ 80 + d'.code) * 2 + 1
      rw [code_of_spot e1, e2, code_of_spot e3]

/-- **TWIN → ELEVENTH, BY KEYS**: the law holds whatever K is; that K is the list's is hK. -/
theorem clause11_of_keys {owners uses : List String} {K : List NameKey} {d : Nat} {l : List Ahead}
    (hT : tablesOk owners uses = true)
    (hI : K.all (NameKey.inTables owners.length uses.length) = true)
    (hC : nodupN d (K.map NameKey.code) = true)
    (hK : l.map (·.name) = K.map (NameKey.name owners uses)) :
    (l.all fun a => (l.filter fun b => b.name == a.name).length == 1) = true := by
  refine clause11_of_nodup ?_
  rw [hK]
  exact nodup_map_of _ NameKey.code K (nodupN_nodup hC) fun a ha b hb e =>
    code_of_name hT (List.all_eq_true.1 hI a ha) (List.all_eq_true.1 hI b hb) e

/-! ## what the tests accept and reject; that both premises on the tables are needed -/

/-- tablesOk: four of the frame's strings and its five uses: accepted. Rejected: a use with a colon;
the use "carried"; an owner's string twice. -/
theorem tables_small :
    tablesOk [maskRowRun, indexMaskRun, foldMaskRun, splitMaskRun]
      ["sum", "ends", "fold", "split", "scalars"] = true ∧
    tablesOk [maskRowRun] ["a: b"] = false ∧
    tablesOk [maskRowRun] ["carried"] = false ∧
    tablesOk [maskRowRun, maskRowRun] ["sum"] = false := by
  decide +kernel

/-- The names that two keys stand for, written out. -/
theorem name_small :
    NameKey.name [maskRowRun, indexMaskRun, foldMaskRun, splitMaskRun]
      ["sum", "ends", "fold", "split", "scalars"] (.spent 2 (toyTo 0) 2) =
      "the fold's fresh mask to 1.2.3.0: fold" ∧
    NameKey.name [] [] (.carried (toyTo 0) 7 ⟨⟨2, none, 5, .K1⟩, 1⟩) =
      "message 7 of 1.2.3.0 to 2.-.5.1: carried" := by
  decide +kernel

/-- The keys' two tests: accepted: a spent and a carried key. Rejected: a key beyond a table; two
keys that differ in a place's kind alone (one code). -/
theorem nameKeys_small :
    [NameKey.spent 0 (toyTo 0) 1, .carried (toyTo 0) 0 (toyTo 0)].all
      (NameKey.inTables 4 5) = true ∧
    nodupN 20 ([NameKey.spent 0 (toyTo 0) 1, .carried (toyTo 0) 0 (toyTo 0)].map
      NameKey.code) = true ∧
    [NameKey.spent 4 (toyTo 0) 1].all (NameKey.inTables 4 5) = false ∧
    nodupN 20 ([NameKey.spent 0 (toyTo 0) 1, .spent 0 ⟨⟨1, some 2, 3, .K5⟩, 0⟩ 1].map
      NameKey.code) = false := by
  decide +kernel

/-- **tablesOk is needed**: with one string twice in the owners' table two keys in the tables, with
different codes, bear one name. -/
theorem tables_needed :
    NameKey.name ["a", "a"] ["sum"] (.spent 0 (toyTo 0) 0) =
      NameKey.name ["a", "a"] ["sum"] (.spent 1 (toyTo 0) 0) ∧
    NameKey.code (.spent 0 (toyTo 0) 0) ≠ NameKey.code (.spent 1 (toyTo 0) 0) := by
  decide +kernel

/-- **inTables is needed**: two keys whose owner's number lies beyond the table, with different
codes, bear one name. -/
theorem inTables_needed :
    NameKey.name ["a"] ["sum"] (.spent 1 (toyTo 0) 0) =
      NameKey.name ["a"] ["sum"] (.spent 2 (toyTo 0) 0) ∧
    NameKey.code (.spent 1 (toyTo 0) 0) ≠ NameKey.code (.spent 2 (toyTo 0) 0) := by
  decide +kernel

/-- **The four premises hold together**: at a list of two entries, a spent run's and a carried
one's, named by the frame's own makers: clause11_of_keys is spent: three premises by an evaluation
each, hK by rfl. -/
theorem clause11_keys_small :
    ([⟨runName maskRowRun (toyTo 1) "sum", toyTo 0, ⟨0, 0⟩, ⟨0, 1⟩, toyTo 1, true⟩,
      ⟨carriedName (toyTo 0) 3 (toyTo 2), toyTo 0, ⟨0, 0⟩, ⟨0, 1⟩, toyTo 2, false⟩].all
        fun (a : Ahead) =>
      ([⟨runName maskRowRun (toyTo 1) "sum", toyTo 0, ⟨0, 0⟩, ⟨0, 1⟩, toyTo 1, true⟩,
        ⟨carriedName (toyTo 0) 3 (toyTo 2), toyTo 0, ⟨0, 0⟩, ⟨0, 1⟩, toyTo 2, false⟩].filter
          fun (b : Ahead) => b.name == a.name).length == 1) = true :=
  clause11_of_keys (owners := [maskRowRun]) (uses := ["sum"])
    (K := [.spent 0 (toyTo 1) 0, .carried (toyTo 0) 3 (toyTo 2)]) (d := 20)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.code_of_spot
#print axioms ProofFile.Honest.atTable_inj
#print axioms ProofFile.Honest.atTable_mem
#print axioms ProofFile.Honest.nodup_map_of
#print axioms ProofFile.Honest.code_of_name
#print axioms ProofFile.Honest.clause11_of_keys
#print axioms ProofFile.Honest.tables_small
#print axioms ProofFile.Honest.name_small
#print axioms ProofFile.Honest.nameKeys_small
#print axioms ProofFile.Honest.tables_needed
#print axioms ProofFile.Honest.inTables_needed
#print axioms ProofFile.Honest.clause11_keys_small
