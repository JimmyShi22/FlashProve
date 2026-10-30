-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelLists.lean: SMALL GENERAL LAWS.

What is here. Laws on two lists that are related member by member (`All2`,
OnBytes/Flat/DryRel.lean), on values that may be missing (`OptRel`,
OnBytes/Flat/LinksFreeLayer.lean) and on folds that keep an array's size. No definition; eleven
statements with their proofs.

  `all2_filter`, `aall2_filter`   two filters whose tests agree on related members.
  `find_all2`, `afind_all2`   two searches whose tests agree on related members.
  `length_flatMap_all2`, `size_flatMap_all2`   two lists of arrays of the same sizes, joined.
  `agetD_all2`   a member by its number.
  `optRel_bind_eq`   a first step with its two equations handed on.
  `amapM_mem`   each member of what a map returns is a value of the function.
  `foldl_size`, `afoldl_size`   a fold whose step keeps the size.

Debts and ends. NONE: the file defines no relation, and names none of this family of congruences:
`All2` and `OptRel` are the library's.

Not shown here. Lemmas on List, Array and Option: the statements say nothing on the sub-protocol.
THE FILE's IMPORTS ARE NOT GENERAL: it imports Law/SkelEnv.lean and
Johnson/Road/K4/Reads/TermsEnts.lean for two helpers: `all2_getD`
(Johnson/Desc/First/K4/Returns/Pub/Panels.lean, beneath the first) and `all_mapM` (in the second).

Kin. `all2_filter` HAS A TWIN IN A SISTER FILE: `filter_both` (Law/SkelWeights.lean): one statement,
one proof; neither file imports the other; both stay.
`agetD_all2` is the array's form of `all2_getD`, which it calls; `all2_getElem?`
(OnBytes/Flat/LinksFreeHeadB.lean) says the like with `OptRel`. `optRel_bind_eq` is `optRel_bind`
(OnBytes/Flat/LinksFreeLayer.lean) with the two equations handed on. `amapM_mem` is the array's form
of `mapM_mem` (Johnson/Desc/First/K4/RunsLength.lean; the library has more theorems of that name).
`length_flatMap_all2` stands beside the private `All2.flatMap_eq` (OnBytes/Flat/MemberFree.lean:
equal lists where the functions agree). `foldl_size` stands beside `foldlM_size`
(OnBytes/Params/Fit/LayPasses.lean), `foldl_modify_size`
(Johnson/Desc/K12/Honest/Shape/TestKeeps.lean) and `foldl_keeps` (Law/SkelGen.lean: each step yields
n members). Sisters in its writers' own files, both in Law/SkelReads.lean: `find_pt` says the like
of `find_all2` of two lists of named points, with a weaker end; `length_flatMap_every` counts where
every image has one length n, where `length_flatMap_all2` compares two lists. No twin in the library
is known to its writers.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelEnv
import Johnson.Road.K4.Reads.TermsEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Flat (All2 OptRel)
open OnBytes.Desc.First.K4.RtPub

/-- Two lists in R member by member stay so under two tests that give one answer on members in R. -/
theorem all2_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h : ∀ a b, R a b → p a = q b) {l : List α} {l' : List β} (hl : All2 R l l') :
    All2 R (l.filter p) (l'.filter q) := by
  induction hl with
  | nil => exact .nil
  | @cons a b l l' h0 _ ih =>
    rw [List.filter_cons, List.filter_cons, h a b h0]
    cases q b
    · exact ih
    · exact .cons h0 ih

/-- The same over two arrays. -/
theorem aall2_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (h : ∀ a b, R a b → p a = q b) {l : Array α} {l' : Array β}
    (hl : All2 R l.toList l'.toList) : All2 R (l.filter p).toList (l'.filter q).toList := by
  rw [Array.toList_filter, Array.toList_filter]
  exact all2_filter h hl

/-- Two searches by such tests: both find nothing, or what they find is in R. -/
theorem find_all2 {α : Type} {R : α → α → Prop} {p q : α → Bool}
    (h : ∀ a b, R a b → p a = q b) {l l' : List α} (hl : All2 R l l') :
    OptRel R (l.find? p) (l'.find? q) := by
  induction hl with
  | nil => trivial
  | @cons a b l l' h0 _ ih =>
    rw [List.find?_cons, List.find?_cons, h a b h0]
    cases q b
    · exact ih
    · exact h0

/-- The same over two arrays. -/
theorem afind_all2 {α : Type} {R : α → α → Prop} {p q : α → Bool}
    (h : ∀ a b, R a b → p a = q b) {l l' : Array α} (hl : All2 R l.toList l'.toList) :
    OptRel R (l.find? p) (l'.find? q) := by
  rw [← Array.find?_toList, ← Array.find?_toList]
  exact find_all2 h hl

/-- Two lists whose members' images are as long, member by member: laid end to end, as long. -/
theorem length_flatMap_all2 {α β γ δ : Type} {f : α → List γ} {g : β → List δ} {l : List α}
    {l' : List β} (hl : All2 (fun a b => (f a).length = (g b).length) l l') :
    (l.flatMap f).length = (l'.flatMap g).length := by
  induction hl with
  | nil => rfl
  | cons h0 _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append, h0, ih]

/-- Two arrays of arrays of the same sizes, member by member: joined, of one size. -/
theorem size_flatMap_all2 {γ δ : Type} {l : Array (Array γ)} {l' : Array (Array δ)}
    (hl : All2 (fun a b => a.size = b.size) l.toList l'.toList) :
    (l.flatMap id).size = (l'.flatMap id).size := by
  rw [← Array.length_toList, ← Array.length_toList, Array.toList_flatMap, Array.toList_flatMap]
  exact length_flatMap_all2 hl

/-- The members of one number, with defaults in R, are in R. -/
theorem agetD_all2 {α β : Type} {R : α → β → Prop} {d : α} {d' : β} (hd : R d d') {l : Array α}
    {l' : Array β} (hl : All2 R l.toList l'.toList) (i : Nat) : R (l.getD i d) (l'.getD i d') := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact all2_getD hd hl i

/-- Two binds: the second step may use that both first values are there, by their two equations. -/
theorem optRel_bind_eq {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : Option α}
    {f f' : α → Option β} (hx : OptRel S x x')
    (hf : ∀ a a', x = some a → x' = some a' → S a a' → OptRel R (f a) (f' a')) :
    OptRel R (x >>= f) (x' >>= f') := by
  cases x <;> cases x'
  · trivial
  · exact False.elim hx
  · exact False.elim hx
  · exact hf _ _ rfl rfl hx

/-- Each member of what a map that may yield nothing returns is a value of the function. -/
theorem amapM_mem {α β : Type} {f : α → Option β} {xs : Array α} {ys : Array β}
    (h : xs.mapM f = some ys) : ∀ y ∈ ys.toList, ∃ x, f x = some y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | none =>
    rw [hl] at h
    cases h
  | some zs =>
    rw [hl] at h
    obtain rfl : zs.toArray = ys := Option.some.inj h
    exact OnBytes.Desc.First.K4.Reads.all_mapM (Pr := fun y => ∃ x, f x = some y)
      (fun a b e => ⟨a, e⟩) _ zs hl

/-- A fold over a list whose step keeps the array's size keeps it. -/
theorem foldl_size {α β : Type} {f : Array β → α → Array β} (h : ∀ t x, (f t x).size = t.size) :
    ∀ (l : List α) (t : Array β), (l.foldl f t).size = t.size
  | [], _ => rfl
  | x :: l, t => by rw [List.foldl_cons, foldl_size h l, h]

/-- The same over an array. -/
theorem afoldl_size {α β : Type} {f : Array β → α → Array β} (h : ∀ t x, (f t x).size = t.size)
    (l : Array α) (t : Array β) : (l.foldl f t).size = t.size := by
  rw [← Array.foldl_toList]
  exact foldl_size h _ t

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.all2_filter
#print axioms ProofFile.Honest.K4.aall2_filter
#print axioms ProofFile.Honest.K4.find_all2
#print axioms ProofFile.Honest.K4.afind_all2
#print axioms ProofFile.Honest.K4.length_flatMap_all2
#print axioms ProofFile.Honest.K4.size_flatMap_all2
#print axioms ProofFile.Honest.K4.agetD_all2
#print axioms ProofFile.Honest.K4.optRel_bind_eq
#print axioms ProofFile.Honest.K4.amapM_mem
#print axioms ProofFile.Honest.K4.foldl_size
#print axioms ProofFile.Honest.K4.afoldl_size
