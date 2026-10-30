-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/InsideLaw.lean: how `Inside` (Honest/Thread/Pays.lean) begins
and goes on: the state of a run after the first n rounds of a sub-protocol. Lemmas on this folder's
own functions and definitions, general in the `Thread`'s parameters: no kind is named.

  `inside_zero`   at the border before the sub-protocol: from the invariant there
  `inside_more`   from after n rounds to after n + j: by `play` over the sub-protocol's next j
     `Step`s

What they are for. A list of several parts: before part number i, `Inside T b n` holds, with n the
rounds of the parts before it. So a condition at every part's entry is obtained from the invariant
at the border before the sub-protocol and from the parts' own play, with no clause and no hypothesis
of its own.

Limits.
  * They are none of the library's goals.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `inside_more`.
  * `inside_zero` and `inside_more` also take "`chainSteps` … [blk] T.hs = .ok l": the book gives
    the sub-protocol's `Step`s their coins.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- At the border before the sub-protocol. -/
theorem inside_zero {b : Nat} {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {l : List (Step W X)} (hblk : T.bs[b]? = some blk) (hA : Thr T b k s m E)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l) : Inside T b 0 k m E := by
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA'
  unfold Thread.Made at hM
  obtain ⟨-, -, -, hTi, -⟩ := hM
  unfold Inside
  exact ⟨blk, s, m, E, l, [], ([], m), hblk, hA, hl, rfl, rfl, rfl, (Env.add_nil E hTi).symm⟩

/-- From after n rounds of the sub-protocol to after n + j. -/
theorem inside_more {b n j : Nat} {blk : Block S Cl} {k : Coins Bk} {m : Mid W X} {E : Env}
    {l : List (Step W X)} {ds' : List Fmt.Drawn} {y' : List Played × Mid W X}
    (hI : Inside T b n k m E) (hblk : T.bs[b]? = some blk)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l)
    (hd : drawsFit ((blk.rounds.drop n).take j) ds' = true)
    (hy : play ((l.drop n).take j) ds' [] m = .ok y') :
    Inside T b (n + j) k y'.2 (E.add y'.1) := by
  unfold Inside at hI ⊢
  obtain ⟨blk₀, s, m₀, E₀, l₀, ds, y, hb₀, hA, hl₀, hd₀, hy₀, rfl, rfl⟩ := hI
  rw [hblk] at hb₀
  cases hb₀
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy₀
  rw [ei, hl₀] at hl
  cases hl
  have hnl : l.length = blk.rounds.length := by
    have e := congrArg List.length (steps_decl hl₀)
    rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  have hL : ds.length = (blk.rounds.take n).length := drawsFit_length _ _ hd₀
  have hlen : ds.length = (l.take n).length := by
    rw [hL, List.length_take, List.length_take, hnl]
  refine ⟨blk, s, m₀, E₀, l, ds ++ ds', (y.1 ++ y'.1, y'.2), hblk, hA, hl₀, ?_, ?_, rfl,
    Env.add_add E₀ y.1 y'.1⟩
  · rw [List.take_add, drawsFit_append, List.take_left' hL, List.drop_left' hL, Bool.and_eq_true]
    exact ⟨hd₀, hd⟩
  · rw [List.take_add, play_append _ _ _ _ _ _ hlen, hy₀]
    show (play ((l.drop n).take j) ds' (([] : List Fmt.RoundView).drop _) y.2).map _ = _
    rw [List.drop_nil, hy]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.inside_zero
#print axioms ProofFile.Honest.inside_more
