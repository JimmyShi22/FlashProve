-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryRecord.lean: at the configuration over which the entry file's protocol is shown
sound (`DecR.configurationOfStoredTable A R` at the written link's own decoder, OnBytes/Flat/EntryValue.lean), at both
sizes, nothing assumed: THE RECORD BINDS, and THE SEED's LAW; and the link's list of errors in the
form in which a description with bits of work asks it.

Main names (general in the sizes T, v, eM, lg, s of `decRec`).
 `RecFits` six conditions on the sizes: the tree's depth is at most 32; message and random tail fit
     into a word; the radius is below the code's distance and within the Johnson bound; the message
     has room for its pads; the entries before the pads are at most 2^lg.
 `recER`          the number (`listMax` choose 2) times the sample map's `err`.
 `RecFits.record` every word has a collision at no more than `recER` seeds.
 `recSeedB`, `recSeedAt` the seed of b blocks, b the number of blocks that the seeds' draws need:
     the expression of the programs' `recordSeeds` behind its round's query, on the blocks' bytes;
     the seed of b + c blocks: that of the first b; the other c are not read.
 `recBound`       the samplers' bias to the power b, times `recER` over the number of seeds.
 `RecFits.seedLaw`  for every word, fixed before the blocks: the seed of b + c uniform blocks is a
                  seed with a collision with probability at most `recBound`.
At the sizes.
 `fr_dec`, `sr_dec`   the written link's decoder IS `decRec` at the typed sizes (by unfolding).
 `fr_fits`, `sr_fits`, `fr_bound`, `sr_bound` (at most 2^-128).
 `entryFull_record`, `entrySmall_record`; `entryFull_seedLaw`, `entrySmall_seedLaw` (b = 140 | 95).
 `entryFull_belowG`, `entrySmall_belowG`   each count of the link's list is at most 2^-128 of its
                  round's written verifier messages, at zero further bits of work.

What must be said beside them. THE COUNT `recER` IS NOT EVALUATED, and no bound of a compiled
verifier reads it: what carries the record's binding there is the seed's law. The word is fixed
before the blocks are drawn. Which of a wire's blocks a seed reads is set here: the first b. That a
program's query gives these blocks is not shown here: the programs ask at a table's name (root, the
public files' digest, the shape). ZERO FURTHER BITS DOES NOT MEAN NO WORK: 32 of the 128 bits are
proof of work at six rounds (full size) and four (small), which stands inside the written verifier
messages as test bits. No other clause of `ConfigurationWithOutOfDomainSample.Props`. Nothing on hiding.

-/
import OnBytes.Slice.LinkHoleAt
import Prob.LensLaw
import OnBytes.Join1.LinkHoles
import OnBytes.Slice.RecordColl
import OnBytes.Slice.RecordPriceGlue
import OnBytes.Slice.LinkAtRec
import OnBytes.Params.RecordBelow
import OnBytes.Params.RecordRoundSmall
import OnBytes.Params.EntryBlocksRecord

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood Hiop _root_.Iop _root_.Run Rom
open scoped ENNReal

/-- The first b of b + c uniform values are uniform. -/
theorem map_unif_take {α : Type} [Fintype α] [Nonempty α] (b c : ℕ) :
    (unif (Fin (b + c) → α)).map (fun a (i : Fin b) => a (Fin.castAdd c i)) =
      unif (Fin b → α) := by
  have e : (fun a : Fin (b + c) → α => fun i : Fin b => a (Fin.castAdd c i)) =
      Prod.fst ∘ (Fin.appendEquiv b c).symm := by
    funext a
    rfl
  rw [e, ← PMF.map_comp, map_unif_equiv]
  exact Prob.Lens.map_fst

/-- An event on the first b of b + c uniform values. -/
theorem pr_unif_take {α : Type} [Fintype α] [Nonempty α] (b c : ℕ) (P : Set (Fin b → α)) :
    pr (unif (Fin (b + c) → α)) {a | (fun i : Fin b => a (Fin.castAdd c i)) ∈ P} =
      pr (unif (Fin b → α)) P := by
  rw [← map_unif_take b c, pr_map]
  rfl

section Sizes
variable (T : Fmt.M1.Code) (v eM lg s : ℕ)

/-- Six conditions on the sizes. -/
structure RecFits : Prop where
  /-- the tree's depth is at most 32 -/
  depth : T.a ≤ 32
  /-- message and random tail fit into a word -/
  dim : T.r + T.l ≤ 2 ^ T.a
  /-- the radius is below the code's distance -/
  radius : eM < 2 ^ T.a - (T.r + T.l) + 1
  /-- the radius is within the Johnson bound -/
  johnson : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM
  /-- the message has room for its pads -/
  pads : 3 * s ≤ T.l
  /-- the entries before the pads are at most 2^lg -/
  cube : T.l - 3 * s ≤ 2 ^ lg

/-- The number of seeds at which a word may have a collision. -/
noncomputable def recER : ℕ :=
  (listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err

/-- The seed of b blocks: the programs' own expression, on the blocks' bytes. -/
def recSeedB (u : Fin (seedBS lg s).b → Dig 256) : (recZ T.l lg s).D :=
  seedOf lg s
    ((timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf (blockBytes u)) 0).1.map
      fun x => (x.1.map E.ofTriple, E.ofTriple x.2))

/-- The record's bound. -/
noncomputable def recBound : ℝ≥0∞ :=
  kapSl 128 ^ (seedBS lg s).b *
    ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 *
      (recZ T.l lg s).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ T.l lg s).D)

variable {T v eM lg s}

/-- **The record binds.** -/
theorem RecFits.record (h : RecFits T eM lg s) {X : Type} (A : (decRec T v eM lg s).Claims X)
    (R : (decRec T v eM lg s).RelationsAndEncoding A) (y : Fin (2 ^ T.a) → Run.PQ.SgX) :
    cnt (fun σ => (DecR.configurationOfStoredTable A R).coll y σ) ≤ recER T eM lg s :=
  coll_count T v eM lg s h.depth h.dim h.radius h.johnson h.pads h.cube y

/-- The seed's law on b blocks. -/
theorem RecFits.seedLawB (h : RecFits T eM lg s) (y : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll y (recSeedB T lg s u)} ≤ recBound T eM lg s :=
  coll_pr_bytes T v eM lg s h.depth h.dim h.radius h.johnson h.pads h.cube y

attribute [irreducible] recSeedB recBound

variable (T lg s) in
/-- **The seed of b + c blocks**: that of the first b. -/
noncomputable def recSeedAt (c : ℕ) (a : Fin ((seedBS lg s).b + c) → Dig 256) : (recZ T.l lg s).D :=
  recSeedB T lg s fun i => a (Fin.castAdd c i)

/-- **The seed's law.** -/
theorem RecFits.seedLaw (h : RecFits T eM lg s) {X : Type} (A : (decRec T v eM lg s).Claims X)
    (R : (decRec T v eM lg s).RelationsAndEncoding A) (c : ℕ) (y : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin ((seedBS lg s).b + c) → Dig 256))
        {a | (DecR.configurationOfStoredTable A R).coll y (recSeedAt T lg s c a)} ≤ recBound T eM lg s :=
  le_of_eq_of_le
    (pr_unif_take (seedBS lg s).b c {u | (decRec T v eM lg s).coll y (recSeedB T lg s u)})
    (h.seedLawB y)

end Sizes

/-- A negative power of 2 beyond 128, as a real number, is at most 2^-128 in the extended reals. -/
theorem ofReal_two_neg (n : ℕ) (hn : 128 ≤ n) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  have hr : (2 : ℝ) ^ (-(n : ℤ)) ≤ ((2 : ℝ)⁻¹) ^ 128 := by
    have e : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [e, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hn)
  have he : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ 128) = ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [← he]
  exact ENNReal.ofReal_le_ofReal hr

/-! ## The full size -/

/-- The written link's decoder at the full size is `decRec` at the typed sizes. -/
theorem fr_dec :
    frS.toDecR frZ 402653181 = decRec recT recV Params.recordRadius recLg recS := rfl

/-- The full size's numbers fit. -/
theorem fr_fits : RecFits recT Params.recordRadius recLg recS where
  depth := by decide
  dim := by decide
  radius := Params.record_radius_inJohnson.2
  johnson := Params.record_radius_inJohnson.1
  pads := recT_room.1
  cube := recT_room.2

/-- The record's bound at the full size is at most 2^-128. -/
theorem fr_bound : recBound recT Params.recordRadius recLg recS ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  unfold recBound
  exact (record_bound_full_letters.trans
    (ENNReal.ofReal_le_ofReal Params.recordPrice_below)).trans (ofReal_two_neg 178 (by norm_num))

/-! ## The small example -/

/-- The code of a table's row at the small example. -/
def srT : Fmt.M1.Code := ⟨23, 524288, 65535⟩

/-- The written link's decoder at the small example is `decRec` at the typed sizes. -/
theorem sr_dec : srS.toDecR srZ 524285 = decRec srT 8 Params.smallRecordRadius 19 1 := rfl

/-- The small example's numbers fit. -/
theorem sr_fits : RecFits srT Params.smallRecordRadius 19 1 where
  depth := by decide
  dim := by decide
  radius := Params.small_record_radius_inJohnson.2
  johnson := Params.small_record_radius_inJohnson.1
  pads := by decide
  cube := by decide

/-- The setting of the small lines with a record has the extension field's number of elements. -/
theorem srSet_card : Params.smallRecordSet.cardE = Fintype.card GE :=
  cardE_card_GE Params.smallRecordSet (by decide +kernel) (by decide +kernel)

/-- The seeds' sampler at the small example reads 95 blocks. -/
theorem sr_seed_blocks : (seedBS 19 1).b = 95 := by
  rw [seedBS_b]
  exact Params.record_seed_blocks.2

/-- The record's bound at the small example is at most 2^-128. -/
theorem sr_bound : recBound srT Params.smallRecordRadius 19 1 ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  unfold recBound
  have e1 : (2 : ℕ) ^ srT.a = 2 ^ 23 := rfl
  have e2 : 2 ^ 23 - (srT.r + srT.l) + 1 = 7798786 := by decide
  have hpos : 0 < Fintype.card (recZ srT.l 19 1).D := Fintype.card_pos
  have h : kapSl 128 ^ (seedBS 19 1).b *
      ((((listMax (2 ^ srT.a) (2 ^ srT.a - (srT.r + srT.l) + 1) Params.smallRecordRadius).choose
        2 * (recZ srT.l 19 1).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ srT.l 19 1).D) ≤
        ENNReal.ofReal ((Params.smallRecordPrice.val : ℚ) : ℝ) := by
    rw [e1, e2, sr_seed_blocks, bound_ofReal 95 _ _ hpos, recZ_err_clash, recZ_card_all,
      ← srSet_card]
    exact ENNReal.ofReal_le_ofReal
      (Params.small_record_covers_at (b := 95) (by positivity) (by norm_num))
  exact (h.trans (ENNReal.ofReal_le_ofReal Params.smallRecordPrice_below)).trans
    (ofReal_two_neg 175 (by norm_num))

end OnBytes.Slice

namespace OnBytes.Flat
open Prob Cb Hiop _root_.Iop _root_.Run OnBytes.Slice OnBytes.Join1
open scoped ENNReal

/-- **The record binds, at the full size.** -/
theorem entryFull_record {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    cnt (fun σ => (DecR.configurationOfStoredTable A R).coll y σ) ≤ recER recT Params.recordRadius recLg recS :=
  fr_fits.record (v := recV) A R y

/-- **The record binds, at the small example.** -/
theorem entrySmall_record {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
    (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    cnt (fun σ => (DecR.configurationOfStoredTable A R).coll y σ) ≤ recER srT Params.smallRecordRadius 19 1 :=
  sr_fits.record (v := 8) A R y

/-- **The seed's law, at the full size: at most 2^-128.** -/
theorem entryFull_seedLaw {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (c : ℕ)
    (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    pr (unif (Fin ((seedBS recLg recS).b + c) → Dig 256))
        {a | (DecR.configurationOfStoredTable A R).coll y (recSeedAt recT recLg recS c a)} ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 :=
  (fr_fits.seedLaw (v := recV) A R c y).trans fr_bound

/-- **The seed's law, at the small example: at most 2^-128.** -/
theorem entrySmall_seedLaw {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
    (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (c : ℕ)
    (y : Fin (DecR.configurationOfStoredTable A R).n → (DecR.configurationOfStoredTable A R).Sg) :
    pr (unif (Fin ((seedBS 19 1).b + c) → Dig 256))
        {a | (DecR.configurationOfStoredTable A R).coll y (recSeedAt srT 19 1 c a)} ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 :=
  (sr_fits.seedLaw (v := 8) A R c y).trans sr_bound

/-- **The link's list, at zero further bits of work, at the full size.** -/
theorem entryFull_belowG :
    Err.BelowG (GBits.zero frShape) frErr (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  belowG_zero_of_below _ _ frErr_below

/-- **The link's list, at zero further bits of work, at the small example.** -/
theorem entrySmall_belowG :
    Err.BelowG (GBits.zero srShape) srErr (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  belowG_zero_of_below _ _ srErr_below

end OnBytes.Flat

#print axioms OnBytes.Flat.entryFull_record
#print axioms OnBytes.Flat.entrySmall_record
#print axioms OnBytes.Flat.entryFull_seedLaw
#print axioms OnBytes.Flat.entrySmall_seedLaw
#print axioms OnBytes.Flat.entryFull_belowG
#print axioms OnBytes.Flat.entrySmall_belowG
