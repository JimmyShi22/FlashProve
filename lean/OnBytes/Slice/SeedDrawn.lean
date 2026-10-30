-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedDrawn.lean: the seeds of a stored table's record as what a ROUND of the kind
"seeds" draws: the format's list of that round's draws, the seeds off the format's record of what
was drawn, and the probability over the round's uniform verifier's message at the library's kit
"challenges as hash blocks", as an equation with the probability of OnBytes/Slice/SeedBias.lean.

WHY. A compiled part that has the seeds' chain among its typed oracles has a protocol with one round
of the kind "seeds". At the library's kit `ckP f` (Run/PlanPull.lean) that round's verifier's
message is the blocks of the round's own sampler, `bsOf f (Fmt.dsOf e k)`, and what is handed on is
the format's record `Fmt.collect` of the sampler's values. OnBytes/Slice/SeedBias.lean speaks of
`seedBS lg s`, the sampler of the list `seedDraws lg s`. The two lists differ: the format closes
every round's draws with a draw of the entry's number of matrix entries, here none, which reads no
word.

Main definitions.
 `roundDraws lg s`      the seeds' draws, and that closing draw.
 `seedEntry lg s`       an entry whose round of the kind "seeds" draws these (`dsOf_seedEntry`, for
                        0 < s).
 `seedOfDrawn lg s l`   s seeds off the elements of the first of the format's records l (`readFlat`,
                        OnBytes/Slice/SeedTie.lean).
Main theorems.
 `dsSeeds_eq`, `dsOf_seeds`   a round of the kind "seeds" whose entry names s (lg + 1) elements, s
                        of them not 0, no position and no matrix entry draws `roundDraws lg s`, for
                        0 < s.
 `roundDraws_b`         both samplers read the same number of blocks: an equation between two
                        expressions, not an unfolding.
 `drawn_seed`, `drawn_seed_of`   THE SEEDS OFF THE RECORD OF WHAT THE ROUND'S SAMPLER DRAWS ARE
                        `toSeed` OF WHAT THE SEEDS' SAMPLER DRAWS, on the same blocks. With
                        `collect_ext`, `flat_eq_map`, `row_cast`.
 `pr_drawn`, `pr_ckP`   AN EQUATION between the two probabilities, for every property of seeds. With
                        `pr_cast`.
 `chalP_unif_seeds`     that verifier's message is exactly uniform under the library's wire `chalP
                        .two K`, if K is at least the number of blocks.
 `seedUnder_of_blocks`  FROM K BLOCKS THAT ARE g'S ANSWERS AT THE STRINGS OF THE BLOCKS 1, .., K OF
                        THE SEEDS' ROUND TO THE SEED UNDER g (`seedUnder_eq`,
                        OnBytes/Slice/SeedRow.lean).
 `collRaw_pr_ckP`       the bound of `collRaw_pr` over that verifier's message, for ONE raw string
                        fixed before it.

What is not claimed. The field is the second. lg and s are arguments. ONE raw string, fixed before
the message: nothing for a maker that picks its table after questions. That a typed answer's K
blocks ARE g's answers at the strings of the blocks 1, .., K of the byte format's round (block 0 is
the chain's next value: `seedRound_HO`, OnBytes/Slice/SeedRow.lean) is a hypothesis of
`seedUnder_of_blocks`: a page's to meet. No protocol, no wiring, no part. No number is evaluated.
Nothing on proof of work. Nothing on any hash function.

-/
import OnBytes.Slice.SeedRow
import Run.PlanPull

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood _root_.Iop _root_.Run Rom
open OnBytes.Tie (IdKey)
open scoped ENNReal

/-! ## The draws of a round of the kind "seeds" -/

/-- The format's list of the draws of s seeds of lg coordinates is `seedDraws lg s`. -/
theorem dsSeeds_eq (lg : ℕ) : ∀ s : ℕ, Fmt.dsSeeds s lg = seedDraws lg s
  | 0 => rfl
  | s + 1 => by
    have ih := dsSeeds_eq lg s
    unfold Fmt.dsSeeds at ih ⊢
    rw [List.replicate_succ, List.flatten_cons, ih]
    rfl

/-- The draws of a round that draws s seeds and nothing else: the seeds' draws, and the format's
closing draw of no matrix entry. -/
def roundDraws (lg s : ℕ) : List Fmt.Draw := seedDraws lg s ++ [.trits 0]

/-- **A round of the kind "seeds" whose entry names s (lg + 1) elements, s of them not 0, no
position and no matrix entry draws these**, for 0 < s. -/
theorem dsOf_seeds (e : Fmt.Entry) (lg s : ℕ) (hs : 0 < s) (h1 : e.poss = 0) (h2 : e.trits = 0)
    (h3 : e.drawNZ = s) (h4 : e.drawE = s * (lg + 1)) : Fmt.dsOf e .seeds = roundDraws lg s := by
  have a : s * (lg + 1) - s = s * lg := by
    rw [Nat.mul_succ]
    omega
  unfold Fmt.dsOf Fmt.dsElems roundDraws
  rw [if_pos rfl, if_neg (by decide), h1, h2, h3, h4, a, Nat.mul_div_cancel_left lg hs,
    Nat.mul_mod_right, dsSeeds_eq, List.replicate_zero, List.replicate_zero, List.nil_append,
    List.append_nil]

/-- An entry whose round of the kind "seeds" draws s seeds of lg coordinates and nothing else: no
work, no message, s (lg + 1) elements, s of them not 0. -/
def seedEntry (lg s : ℕ) : Fmt.Entry := { name := "", drawE := s * (lg + 1), drawNZ := s }

/-- Its round draws `roundDraws lg s`, for 0 < s. -/
theorem dsOf_seedEntry (lg s : ℕ) (hs : 0 < s) :
    Fmt.dsOf (seedEntry lg s) .seeds = roundDraws lg s :=
  dsOf_seeds _ lg s hs rfl rfl rfl rfl

/-- The sampler of these draws reads as many blocks as the sampler of the seeds' draws. -/
theorem roundDraws_b (lg s : ℕ) : (seedBS lg s).b = (bsOf .two (roundDraws lg s)).b := by
  show (Fmt.mostAll (seedDraws lg s) + 3) / 4 = (Fmt.mostAll (seedDraws lg s ++ [.trits 0]) + 3) / 4
  rw [mostAll_append]
  rfl

/-! ## The seeds off the format's record of what a round draws -/

/-- **s seeds off the format's records of what was drawn**: off the elements of the first record. -/
noncomputable def seedOfDrawn (lg s : ℕ) (l : List Fmt.Drawn) : Fin s → (Fin lg → GE) × NZ :=
  readFlat lg s ((l.headD ⟨[], [], [], none⟩).elems.map Fmt.Val.ext)

/-- The elements of the record of a list of values that begins with elements. -/
theorem collect_ext (rest : List Fmt.Val) : ∀ xs : List Fmt.Ext,
    (Fmt.collect (xs.map Fmt.Val.ext ++ rest)).elems = xs ++ (Fmt.collect rest).elems
  | [] => rfl
  | x :: xs => by
    show x :: (Fmt.collect (xs.map Fmt.Val.ext ++ rest)).elems = _
    rw [collect_ext rest xs]
    rfl

/-- The flat list of a list of seeds holds elements alone. -/
theorem flat_eq_map : ∀ l : List (List Fmt.Ext × Fmt.Ext),
    flat l = (l.flatMap fun y => y.1 ++ [y.2]).map Fmt.Val.ext
  | [] => rfl
  | y :: l => by
    have ih := flat_eq_map l
    unfold flat at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, ih]
    rfl

/-- The rows of words of the same blocks, where the number of blocks is written in two ways. -/
theorem row_cast {b b' : ℕ} (h : b = b') (u : Fin b' → Dig 256) :
    rowFn (0 : UInt64) (rowOf e64 b' u) =
      rowFn 0 (rowOf e64 b fun i => u (Fin.cast h i)) := by
  subst h
  rfl

/-- **THE SEEDS OFF THE RECORD OF WHAT THE ROUND'S SAMPLER DRAWS ARE `toSeed` OF WHAT THE SEEDS'
SAMPLER DRAWS**, on the same blocks. -/
theorem drawn_seed (lg s : ℕ) (u : Fin (bsOf .two (roundDraws lg s)).b → Dig 256) :
    seedOfDrawn lg s
        [Fmt.collect (outAll .two (roundDraws lg s) ((bsOf .two (roundDraws lg s)).φ u))] =
      toSeed lg s ((seedBS lg s).φ fun i => u (Fin.cast (roundDraws_b lg s) i)) := by
  rw [toSeed_eq]
  have h1 := drawTie_bs .two (roundDraws lg s) u
  have h2 := drawTie_bs .two (seedDraws lg s) fun i => u (Fin.cast (roundDraws_b lg s) i)
  have h2' : outAll .two (seedDraws lg s)
      ((seedBS lg s).φ fun i => u (Fin.cast (roundDraws_b lg s) i)) = _ := h2
  have hr : rowFn (0 : UInt64) (rowOf e64 (bsOf .two (seedDraws lg s)).b fun i =>
      u (Fin.cast (roundDraws_b lg s) i)) =
      rowFn 0 (rowOf e64 (bsOf .two (roundDraws lg s)).b u) :=
    (row_cast (roundDraws_b lg s) u).symm
  rw [h2', h1, hr]
  unfold roundDraws
  rw [readAll_append, readAll_seeds]
  unfold seedOfDrawn
  show readFlat lg s ((Fmt.collect (flat _ ++ [Fmt.Val.trits _])).elems.map Fmt.Val.ext) = _
  rw [flat_eq_map, collect_ext]
  show readFlat lg s ((_ ++ []).map Fmt.Val.ext) = _
  rw [List.append_nil]

/-- The same where the round's draws are given by an equation. -/
theorem drawn_seed_of (lg s : ℕ) (ds : List Fmt.Draw) (h : ds = roundDraws lg s)
    (u : Fin (bsOf .two ds).b → Dig 256) :
    seedOfDrawn lg s [Fmt.collect (outAll .two ds ((bsOf .two ds).φ u))] =
      toSeed lg s ((seedBS lg s).φ fun i => u (Fin.cast
        ((roundDraws_b lg s).trans (congrArg (fun d => (bsOf .two d).b) h.symm)) i)) := by
  subst h
  exact drawn_seed lg s u

/-! ## The probability -/

/-- Uniform blocks, where their number is written in two ways. -/
theorem pr_cast {b b' : ℕ} (h : b = b') (Q : (Fin b → Dig 256) → Prop) :
    pr (unif (Fin b' → Dig 256)) {u | Q fun i => u (Fin.cast h i)} =
      pr (unif (Fin b → Dig 256)) {u | Q u} := by
  subst h
  rfl

/-- **AN EQUATION: over the round's uniform blocks, the seeds off the record of what is drawn have a
property with the probability with which `toSeed` of the seeds' sampler has it over ITS uniform
blocks.** -/
theorem pr_drawn (lg s : ℕ) (ds : List Fmt.Draw) (h : ds = roundDraws lg s)
    (P : (Fin s → (Fin lg → GE) × NZ) → Prop) :
    pr (unif (Fin (bsOf .two ds).b → Dig 256))
        {u | P (seedOfDrawn lg s [Fmt.collect (outAll .two ds ((bsOf .two ds).φ u))])} =
      pr (unif (Fin (seedBS lg s).b → Dig 256)) {u | P (toSeed lg s ((seedBS lg s).φ u))} := by
  simp only [drawn_seed_of lg s ds h]
  exact pr_cast _ fun u => P (toSeed lg s ((seedBS lg s).φ u))

/-! ## At the library's kit "challenges as hash blocks" -/

/-- **At the kit `ckP .two` the equation reads**: over a uniform verifier's message of a round of
the kind "seeds" that draws s seeds and nothing else, the seeds off the record of what is drawn have
a property with the probability with which `toSeed` of the seeds' sampler has it over uniform
blocks. -/
theorem pr_ckP (lg s : ℕ) (e : Fmt.Entry) (h : Fmt.dsOf e .seeds = roundDraws lg s)
    (P : (Fin s → (Fin lg → GE) × NZ) → Prop) :
    pr (unif ((ckP .two).Ch e .seeds)) {c | P (seedOfDrawn lg s [(ckP .two).dr e .seeds c])} =
      pr (unif (Fin (seedBS lg s).b → Dig 256)) {u | P (toSeed lg s ((seedBS lg s).φ u))} :=
  pr_drawn lg s (Fmt.dsOf e .seeds) h P

/-- **That verifier's message is exactly uniform under the library's wire `chalP .two K`** (the
first blocks of K), if K is at least the number of blocks of the seeds' sampler. -/
theorem chalP_unif_seeds (lg s K : ℕ) (e : Fmt.Entry) (h : Fmt.dsOf e .seeds = roundDraws lg s)
    (hK : (seedBS lg s).b ≤ K) :
    (unif (Fin K → Dig 256)).map (chalP .two K e .seeds) = unif ((ckP .two).Ch e .seeds) := by
  have hb : (bsRound .two e .seeds).b ≤ K := by
    have e1 : (bsRound .two e .seeds).b = (bsOf .two (roundDraws lg s)).b :=
      congrArg (fun d => (bsOf .two d).b) h
    rw [e1, ← roundDraws_b]
    exact hK
  exact map_firstBlocks_unif (Dig 256) (fun _ => false) (bsRound .two e .seeds).b K hb

/-- **FROM K BLOCKS THAT ARE g'S ANSWERS AT THE STRINGS OF THE BLOCKS 1, .., K OF THE SEEDS' ROUND
TO THE SEED UNDER g**: the seeds off the record of what the library's wire and kit make of these
blocks are the seed of the key's table under g. Asked: K is at least the number of blocks of the
seeds' sampler. The hypothesis on the blocks is asked of all K; the first `(seedBS lg s).b` are
read. -/
theorem seedUnder_of_blocks (lg s K : ℕ) (e : Fmt.Entry) (h : Fmt.dsOf e .seeds = roundDraws lg s)
    (hK : (seedBS lg s).b ≤ K) (k : IdKey) (g : Fam (rom 256)) (B : Fin K → Dig 256)
    (hB : ∀ i : Fin K, B i = g () (bytesToBits (blockStr
      (oB (g ()) (seedFirst (Key.nameOf k.1 k.2.1 k.2.2))) (i.val + 1)))) :
    seedUnder lg s k g =
      some (seedOfDrawn lg s [(ckP .two).dr e .seeds (chalP .two K e .seeds B)]) := by
  have e1 : seedOfDrawn lg s [(ckP .two).dr e .seeds (chalP .two K e .seeds B)] = _ :=
    drawn_seed_of lg s (Fmt.dsOf e .seeds) h (chalP .two K e .seeds B)
  rw [seedUnder_eq, e1]
  refine congrArg (fun u => some (toSeed lg s ((seedBS lg s).φ u))) (funext fun i => ?_)
  have hi : i.val < K := lt_of_lt_of_le i.isLt hK
  show g () _ = firstBlocks 256 K _ B _
  unfold firstBlocks
  split
  · rw [hB]
    rfl
  · rename_i hn
    exact absurd hi hn

/-- **THE BOUND OF `collRaw_pr` OVER THAT VERIFIER'S MESSAGE**: for ONE raw string F, fixed before
the message, within the Johnson bound. -/
theorem collRaw_pr_ckP (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (e : Fmt.Entry) (h : Fmt.dsOf e .seeds = roundDraws lg s)
    (F : Raw Run.PQ.SgX) :
    pr (unif ((ckP .two).Ch e .seeds))
        {c | (decRec T v eM lg s).collRaw F (seedOfDrawn lg s [(ckP .two).dr e .seeds c])} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) :=
  (pr_ckP lg s e h fun ρ => (decRec T v eM lg s).collRaw F ρ).le.trans
    (collRaw_pr T v eM lg s ha hk he hJ h3 hl F)

end OnBytes.Slice
