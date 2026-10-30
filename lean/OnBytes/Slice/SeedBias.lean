-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedBias.lean: from a count of seeds to a probability over uniform hash blocks, for
the draws of a record's seeds; and with it the count of OnBytes/Slice/RecordColl.lean as a
probability, for one table.

The library has the format's draws as readers of a row of machine words, a round's draws as one
block sampler (`bsOf`, Run/DrawPage.lean), and its bias as a theorem (`drawPage_bs`,
Run/DrawPageProofs.lean): every value has at most w preimages, with w times the number of values at
most (1 + 2^-128)^b times the number of tuples of b blocks. Its readers are "at most six tries, a
word each; then 0" for an element of the base field and "at most two triples; the first that is not
0; then (1, 0, 0)" for a factor. So a set of values has, over uniform blocks, at most (1 + 2^-128)^b
times its share (`pr_preimage_le_mul`, Prob/Bias.lean): A FACTOR, NO SUMMAND.

Main definitions.
 `seedDraws lg s`, `seedBS lg s`   the draws of s seeds as a list of the format's draws; the
                        library's block sampler of that list, in the programs' field.
 `eF`, `eE`, `eNZ`, `consE`, `eElems`, `toSeed lg s`   the sampler's values as seeds of `recZ`:
                        numbers below p as elements of the base field, triples as elements of the
                        extension field, in the order of the draws. A one-to-one correspondence.
Main theorems.
 `seedDraws_most`, `seedBS_b`, `seedBS_b_full`   s (18 lg + 36) words at most; so as many blocks as
                        the program's `recordSeeds` hands to its draw; 140 at the sizes of
                        OnBytes/Slice/RecordFull.lean.
 `pr_bs_le`, `pr_seed_le`   from a count to a probability; for every one-to-one correspondence
                        between the sampler's values and a type of seeds.
 `coll_pr`, `coll_pr_toSeed`, `collRaw_pr`, `coll_pr_full`   for ONE stored table, within the
                        Johnson bound: over uniform blocks the record does not single one table out
                        with probability at most (1 + 2^-128)^b (`listMax` choose 2) `err` / the
                        number of seeds.

WHAT IS NOT SHOWN. (1) That `toSeed` of the sampler's value is the program's seed is not shown HERE:
OnBytes/Slice/SeedTie.lean (`seedTie`), on the row of the blocks' words. (2) The words of a block
(that the words of a block of 256 bits are those that the format reads off 32 bytes): not HERE:
OnBytes/Slice/SeedRow.lean (`rowOf_blocks`, `seedUnder_eq`). (3) FROM UNIFORM BLOCKS TO THE ORACLE.
The blocks are the oracle's answers at the strings of the seeds' round: at the sizes, blocks 1 to
140 of the 142 asked (71 calls, two strings and two blocks a call; block 0 is the chain's next
value, block 141 is dropped; which strings and blocks the draw reads: `seedRound_HO`,
`seedUnder_eq`, OnBytes/Slice/SeedRow.lean); that the strings are pairwise different, and different
from the name's string, is shown in OnBytes/Slice/SeedStrings.lean, and used in
OnBytes/Slice/SeedOracle.lean: for one table and one name fixed before the oracle is drawn the
blocks are uniform. They are uniform and independent of the table only if these strings were not
asked before the table stood. THE SEED HANGS ON TWO STEPS OF CALLS: the strings of the round hold
the ANSWER of the call on the table's name, and can be asked before that call, at starts of a
committer's choice; it can then fit a table to one of those seeds and hope that the name's call
answers that start: an event of about (starts asked) (names asked) / 2^256, bounded by nothing here.
(4) ONE TABLE: a committer that tries many roots has one try for each. (5) No number is evaluated:
the radius is an argument; `listMax`, `err` and the number of seeds stand as expressions. Nothing on
proof of work: the seeds' calls are written with work 0. It is laid into no join in this file:
`coll_pr_bytes` (OnBytes/Slice/SeedRow.lean) calls `coll_pr_toSeed`, and `RecFits.seedLawB`
(OnBytes/Flat/EntryRecord.lean) calls that. That `recZ` is the programs' sample map is a reading of
their text. (Of the Lean port one part is shown: the coefficients of its row of a record's answer
are `recZ`'s matrix: `coefAt_recRow`, OnBytes/Slice/BlkRecRow.lean. Of the C++ programs nothing is
shown.) Nothing on any hash function.

-/
import OnBytes.Slice.RecordColl
import Run.DrawPageProofs
import Run.PlanDraws

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood Blocks _root_.Iop _root_.Run
open scoped ENNReal

/-! ## The draws of a record's seeds, as a round's draws -/

/-- One seed's draws: lg elements of the extension field, then one that is not 0. -/
def seedDraws1 (lg : ℕ) : List Fmt.Draw := List.replicate lg .elem ++ [.elemNZ]

/-- **The draws of s seeds**, one seed behind the other (`Fmt.drawSeed`, s times). -/
def seedDraws (lg : ℕ) : ℕ → List Fmt.Draw
  | 0 => []
  | s + 1 => seedDraws1 lg ++ seedDraws lg s

/-- None of them is a draw of positions. -/
theorem seedDraws_lawful (lg : ℕ) : ∀ (s : ℕ), ∀ d ∈ seedDraws lg s, Lawful d
  | 0, d, h => absurd h List.not_mem_nil
  | s + 1, d, h => by
    rcases List.mem_append.1 h with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · rw [List.eq_of_mem_replicate h2]
        trivial
      · rw [List.mem_singleton.1 h2]
        trivial
    · exact seedDraws_lawful lg s d h1

/-- The most words of two lists of draws, one behind the other. -/
theorem mostAll_append : ∀ a b : List Fmt.Draw,
    Fmt.mostAll (a ++ b) = Fmt.mostAll a + Fmt.mostAll b
  | [], b => (Nat.zero_add _).symm
  | d :: a, b => by
    show d.most + Fmt.mostAll (a ++ b) = d.most + Fmt.mostAll a + Fmt.mostAll b
    rw [mostAll_append a b, Nat.add_assoc]

/-- The most words of n elements. -/
theorem mostAll_elems : ∀ n : ℕ, Fmt.mostAll (List.replicate n .elem) = n * 18
  | 0 => (Nat.zero_mul _).symm
  | n + 1 => by
    show 18 + Fmt.mostAll (List.replicate n .elem) = (n + 1) * 18
    rw [mostAll_elems n]
    omega

/-- **The most words of s seeds: s (18 lg + 36)**: the number from which the program's `recordSeeds`
takes its number of blocks. -/
theorem seedDraws_most (lg : ℕ) : ∀ s : ℕ, Fmt.mostAll (seedDraws lg s) = s * (lg * 18 + 36)
  | 0 => (Nat.zero_mul _).symm
  | s + 1 => by
    show Fmt.mostAll (seedDraws1 lg ++ seedDraws lg s) = _
    unfold seedDraws1
    rw [mostAll_append, mostAll_append, mostAll_elems, seedDraws_most lg s]
    show lg * 18 + (36 + 0) + s * (lg * 18 + 36) = (s + 1) * (lg * 18 + 36)
    rw [Nat.succ_mul]
    omega

/-- **The library's block sampler of these draws**, in the field of the programs. -/
def seedBS (lg s : ℕ) : BS 256 (Vals .two (seedDraws lg s)) :=
  bsOf .two (seedDraws lg s)

/-- It reads as many blocks as the program's `recordSeeds` hands to its draw. -/
theorem seedBS_b (lg s : ℕ) : (seedBS lg s).b = Fmt.blocksFor (s * (lg * 18 + 36)) := by
  rw [← seedDraws_most lg s]
  exact (drawPage_bs .two (seedDraws lg s) (seedDraws_lawful lg s)).2

/-! ## From a count of values to a probability over uniform blocks -/

/-- A block sampler that obeys the library's law with κ: a set of values has, over uniform blocks,
at most κ times its share of the values. -/
theorem pr_bs_le {C : Type} [Fintype C] [Nonempty C] (B : BS 256 C) (κ : ℝ≥0∞) (hB : B.Good κ)
    (P : C → Prop) :
    pr (unif (Fin B.b → Dig 256)) {u | P (B.φ u)} ≤ κ * ((cnt P : ℝ≥0∞) / Fintype.card C) := by
  have h := pr_preimage_le_mul B.φ hB.fib (κ := κ)
    (by have := hB.ratio; rwa [Nat.card_eq_fintype_card] at this) {c | P c}
  rw [pr_unif_eq P] at h
  exact h

/-- **FROM A COUNT OF SEEDS TO A PROBABILITY OVER UNIFORM BLOCKS.** For EVERY one-to-one
correspondence e between the values of the library's sampler and a type D of seeds, and every set
Bad of seeds: over uniform blocks the seed is in Bad with at most (1 + 2^-128)^b times the share of
Bad among all seeds; b is the number of blocks. A FACTOR, no summand. -/
theorem pr_seed_le (lg s : ℕ) {D : Type} [Fintype D] (e : Vals .two (seedDraws lg s) ≃ D)
    (Bad : D → Prop) :
    pr (unif (Fin (seedBS lg s).b → Dig 256)) {u | Bad (e ((seedBS lg s).φ u))} ≤
      kapSl 128 ^ (seedBS lg s).b * ((cnt Bad : ℝ≥0∞) / Fintype.card D) := by
  have h := pr_bs_le (seedBS lg s) _
    (drawPage_bs .two (seedDraws lg s) (seedDraws_lawful lg s)).1 fun c => Bad (e c)
  rwa [cnt_equiv e Bad, Fintype.card_congr e] at h

/-! ## A correspondence between the sampler's values and the seeds -/

/-- A number below p as an element of the base field. -/
noncomputable def eF : FV .two ≃ GF where
  toFun x := (x.val : GF)
  invFun y := ⟨y.val, (ZMod.val_lt y).trans_eq Code.pGold_eq⟩
  left_inv x := Fin.ext (by
    show ((x.val : GF)).val = x.val
    exact ZMod.val_natCast_of_lt (by rw [Code.pGold_eq]; exact x.isLt))
  right_inv y := ZMod.natCast_zmod_val y

/-- Three numbers below p as an element of the extension field. -/
noncomputable def eE : EV .two ≃ GE :=
  (Equiv.prodCongr eF (Equiv.prodCongr eF eF)).trans Code.Cubic.equivProd.symm

/-- The triple of zeros is 0. -/
theorem eE_zero : eE (zF .two, zF .two, zF .two) = 0 := by
  show (⟨((0 : ℕ) : GF), ((0 : ℕ) : GF), ((0 : ℕ) : GF)⟩ : GE) = 0
  rw [Nat.cast_zero]
  rfl

/-- The triples other than zeros as the factors. -/
noncomputable def eNZ : Run.NZ .two ≃ NZ :=
  Equiv.subtypeEquiv eE fun a => by
    rw [← eE_zero]
    exact (eE.injective.ne_iff).symm

/-- A first member and n further members as n + 1 members. -/
def consE (n : ℕ) (β : Type) : β × (Fin n → β) ≃ (Fin (n + 1) → β) where
  toFun x := Fin.cons x.1 x.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv _ := rfl
  right_inv f := funext fun i => by
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The values of n elements and further draws. -/
noncomputable def eElems (rest : List Fmt.Draw) : (n : ℕ) →
    Vals .two (List.replicate n .elem ++ rest) ≃ (Fin n → GE) × Vals .two rest
  | 0 => (Equiv.uniqueProd _ _).symm
  | n + 1 =>
    ((Equiv.prodCongr eE (eElems rest n)).trans (Equiv.prodAssoc _ _ _).symm).trans
      (Equiv.prodCongr (consE n GE) (Equiv.refl _))

/-- **The values of the draws of s seeds as s seeds**: numbers below p are read as elements of the
base field, triples as elements of the extension field, in the order of the draws. -/
noncomputable def toSeed (lg : ℕ) : (s : ℕ) →
    Vals .two (seedDraws lg s) ≃ (Fin s → (Fin lg → GE) × NZ)
  | 0 =>
    { toFun := fun _ i => i.elim0, invFun := fun _ => (), left_inv := fun _ => rfl,
      right_inv := fun _ => funext fun i => i.elim0 }
  | s + 1 =>
    (((Equiv.cast (congrArg (Vals .two) (List.append_assoc _ _ _))).trans
      (eElems (.elemNZ :: seedDraws lg s) lg)).trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr eNZ (toSeed lg s)))).trans
      ((Equiv.prodAssoc _ _ _).symm.trans (consE s ((Fin lg → GE) × NZ)))

/-- **A BOUND ON THE PROBABILITY, OVER UNIFORM BLOCKS, THAT THE RECORD DOES NOT SINGLE ONE OUT**:
`coll_count` behind `pr_seed_le`. For ONE stored table f, within the Johnson bound, and every
one-to-one correspondence e between the sampler's values and the seeds. -/
theorem coll_pr (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (f : Fin (2 ^ T.a) → Run.PQ.SgX)
    (e : Vals .two (seedDraws lg s) ≃ (recZ T.l lg s).D) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll f (e ((seedBS lg s).φ u))} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) := by
  refine (pr_seed_le lg s e ((decRec T v eM lg s).coll f)).trans ?_
  gcongr
  exact_mod_cast coll_count T v eM lg s ha hk he hJ h3 hl f

/-- **The same at `toSeed`**: the theorem is not empty. -/
theorem coll_pr_toSeed (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll f (toSeed lg s ((seedBS lg s).φ u))} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) :=
  coll_pr T v eM lg s ha hk he hJ h3 hl f (toSeed lg s)

/-- **The same on raw strings** (`DecR.collRaw`, which the way out of the three languages reads):
for ONE raw string F, fixed before the blocks. -/
theorem collRaw_pr (T : Fmt.M1.Code) (v eM lg s : ℕ) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (F : Raw Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).collRaw F (toSeed lg s ((seedBS lg s).φ u))} ≤
      kapSl 128 ^ (seedBS lg s).b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) := by
  refine (pr_seed_le lg s (toSeed lg s) ((decRec T v eM lg s).collRaw F)).trans ?_
  gcongr
  exact_mod_cast collRaw_count T v eM lg s ha hk he hJ h3 hl F

/-- At the sizes of OnBytes/Slice/RecordFull.lean the sampler reads 140 blocks. -/
theorem seedBS_b_full : (seedBS recLg recS).b = 140 := by
  rw [seedBS_b]
  decide

/-- **At the sizes of the parameter file with a record**; the radius eM is an argument, within the
Johnson bound. ONE table f, fixed before the blocks. Uniform blocks, not an oracle's answers. That
`toSeed` of the sampler's value is the program's seed: OnBytes/Slice/SeedTie.lean. No number on the
right is evaluated. -/
theorem coll_pr_full (eM : ℕ) (he : eM < 3848273922) (hJ : InJohnson (2 ^ 32) 3848273922 eM)
    (f : Fin (2 ^ recT.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS recLg recS).b → Dig 256))
        {u | (decRecFull eM).coll f (toSeed recLg recS ((seedBS recLg recS).φ u))} ≤
      kapSl 128 ^ 140 *
        ((((listMax (2 ^ 32) 3848273922 eM).choose 2 * (recZ recT.l recLg recS).err : ℕ) : ℝ≥0∞) /
          Fintype.card (recZ recT.l recLg recS).D) := by
  have h := coll_pr_toSeed recT recV eM recLg recS (by decide) (by decide) he hJ recT_room.1
    recT_room.2 f
  have e : kapSl 128 ^ (seedBS recLg recS).b = kapSl 128 ^ 140 := by rw [seedBS_b_full]
  rwa [e] at h

end OnBytes.Slice
