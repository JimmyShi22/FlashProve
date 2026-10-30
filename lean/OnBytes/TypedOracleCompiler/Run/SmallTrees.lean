-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SmallTrees.lean: WITHIN THE SIBLING's LIMITS THE TREES OF A DESCRIPTION's ROUNDS'
DATA ARE SMALL (a number below 2^16, fewer than 2^24 words in a column, a depth of at most 63), AND
THE SALT IS SHORT. After the library's Run/OneIsTypedLeaf.lean:126-128 (SmallTrees) and
Run/OneIsTypedTop.lean:286-362 (treeSh_of_mem, own_shape, specOk_of, and the fields small | salt of
fitsS_of). WHY: the reader of string bodies gives pi_after's | forests_ind's hypothesis on bodies
under just these bounds (rdOk_embTail_of_small). SmallL (rds S) follows from ok S = true, its one
hypothesis: smallL_of_ok (OnBytes/TypedOracleCompiler/StringsMeet.lean), by small_of of this file.
  AS TEXT        own_shape, specOk_of
  TURNED         SmallTrees (∀ sh ∈ d.trees), treeSh_of_mem (written anew: a tree of a round has a
                 number in the whole)
  NEW            small_of, salt_of: the two fields of the library's fitsS_of, as lemmas of their own
                 (their proofs are its text)
  LEFT TO THE LIBRARY   roundsOk_mem, round_facts, tab_ownNo; Fmt.ok_count | ok_small | ok_salt

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs
import Run.OneIsTypedTop

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-- the trees are small: a number below 2^16, fewer than 2^24 words in a column, a depth of at most
63 -/
def SmallTrees (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ sh ∈ d.trees, (sh.tree < 2 ^ 16 ∧ sh.W < 2 ^ 24) ∧ sh.a ≤ 63

theorem treeSh_of_mem :
    ∀ (ds : List RD) (d : RD), d ∈ ds → ∀ sh ∈ d.trees, ∃ n, treeSh ds n = some sh
  | [], _, hd, _, _ => by cases hd
  | d0 :: ds, d, hd, sh, ht => by
      rcases List.mem_cons.1 hd with rfl | hd
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ht
        refine ⟨k, ?_⟩
        show (if k < d.trees.length then d.trees[k]? else _) = some sh
        rw [if_pos (List.getElem?_eq_some_iff.1 hk).1, hk]
      · obtain ⟨n, hn⟩ := treeSh_of_mem ds d hd sh ht
        refine ⟨d0.trees.length + n, ?_⟩
        show (if d0.trees.length + n < d0.trees.length then _
          else treeSh ds (d0.trees.length + n - d0.trees.length)) = some sh
        rw [if_neg (by omega), Nat.add_sub_cancel_left, hn]

/-- the n-th tree of a description within the limits -/
theorem own_shape (S : _root_.Fmt.Spec) (hok : ok S = true) (n : ℕ)
    (sh : _root_.Fmt.Shape) (h : treeSh (rds S) n = some sh) :
    n < nRoots S ∧
    sh.tree = S.firstTree + n ∧
    sh.a ≤ 63 ∧
    ((∃ r ∈ S.rounds, ∃ x ∈ r.opens, x.1 = sh) ∨
      (shapeOfOwn S n = none ∧ sh = bareShape S.firstTree n)) := by
  have t := tab_limits S hok
  rw [tab_tree S t n] at h
  by_cases hn : n < nRoots S
  · rw [if_pos hn] at h
    rcases hs : shapeOfOwn S n with _ | s
    · rw [hs] at h
      obtain rfl : bareShape S.firstTree n = sh := Option.some.inj h
      exact ⟨hn, rfl, Nat.zero_le _, Or.inr ⟨rfl, rfl⟩⟩
    rw [hs] at h
    obtain rfl : s = sh := Option.some.inj h
    unfold shapeOfOwn at hs
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hs
    have hm : x ∈ allOpens S := List.mem_of_find?_eq_some hx
    have hp : (ownNo x == some n) = true :=
      List.find?_some (p := fun o : _root_.Fmt.Shape × _root_.Fmt.Src => ownNo o == some n) hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hm
    obtain ⟨n', g⟩ := tab_good S t r hr x hxr
    have e1 : x.2 = _root_.Fmt.Src.own n := (tab_ownNo x n).1 (beq_iff_eq.1 hp)
    have e2 : n' = n := by
      have := g.src.symm.trans e1
      injection this
    obtain ⟨af, se, hro⟩ := roundsOk_mem _ _ _ S.rounds _ _ t.rok r hr
    exact ⟨hn, e2 ▸ g.tree, (round_facts _ _ _ _ _ r hro).2 x hxr, Or.inl ⟨r, hr, x, hxr, rfl⟩⟩
  · rw [if_neg hn] at h
    cases h

/-- the format's own conditions, out of the road's limits -/
theorem specOk_of (S : _root_.Fmt.Spec) (hok : ok S = true) : S.ok = true := by
  simp only [ok, Bool.and_eq_true] at hok
  exact hok.1.1.1.1

/-- Within the limits the trees are small. -/
theorem small_of (S : _root_.Fmt.Spec) (hok : ok S = true) : SmallTrees (rds S) :=
  fun d hd sh ht => by
    obtain ⟨n, hn⟩ := treeSh_of_mem (rds S) d hd sh ht
    obtain ⟨h1, h2, h3, hopen⟩ := own_shape S hok n sh hn
    have hc := _root_.Fmt.ok_count (specOk_of S hok)
    have hs := _root_.Fmt.ok_small (specOk_of S hok)
    simp only [_root_.Fmt.Spec.small, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    have hn' : n < (S.rounds.map (·.entry.roots)).sum := h1
    rcases hopen with ⟨r, hr, x, hx, e⟩ | ⟨-, e⟩
    · exact ⟨⟨by omega, e ▸ (hs.1.2 r hr x hx).2⟩, h3⟩
    · exact ⟨⟨by omega, by rw [e]; exact (by decide : (1 : ℕ) < 2 ^ 24)⟩, h3⟩

/-- and the salt has fewer than 2^8 words -/
theorem salt_of (S : _root_.Fmt.Spec) (hok : ok S = true) : S.plan.salt / 8 < 2 ^ 8 := by
  have := _root_.Fmt.ok_salt (specOk_of S hok)
  simp only [_root_.Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

end TypedOracleCompiler.Run.PQ
