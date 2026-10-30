-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/SeedBack.lean: a seed of the out-of-domain (OOD) sample whose points'
coordinates are numbered below a plain number lg, TYPED AT A SHAPE with that many coordinates; and
small laws on the builder of the explicit input `xiAt` (Johnson/Bind/ForProver/XiAt.lean).

Why. The library's typed OOD sample at the full size numbers a seed's coordinates below the numeral
29; this folder's typed seed (`Seed sh`, Johnson/Bind/ForProver/Seeds.lean) numbers them below
`sh.cube`. At the full size's shape the two numbers are equal by a reckoning (`cube_full`,
Johnson/Bind/ForProver/KeyOfRecAt.lean), not by the form of the two texts.
Johnson/Bind/ForProver/SeedAtFull.lean has the way from a `Seed sh`; here is the way back. That the
two undo each other, both ways, is not shown here: `seedAs_back`, E2E/KeyOodTie.lean,
says that `seedAs` undoes that file's own `seedBack` at the full size. The proof of
`key_is_committers` (AtFullSide/Honest/InstanceIsCommitters.lean) calls `oodAt_atFull` at
`cube_full` and a letter s; this file does not import that one. `Seed sh` is the type of
the seed in the input of this folder's builder `xiAt` (`ProofFile.Honest.Isk`,
Johnson/Desc/ProofFile/Honest/Committer.lean): a private input by its type alone: the seed is
written into the key (seeds_eq_keyOf), so it is public once the key is. (`seeds_eq_keyOf`:
Johnson/Bind/ForProver/OodIsKeyOf.lean.)

Main names (namespace `Bind.ForProver`).
  **`seedBack h e`**   the seed e, typed at sh, where (h) `sh.cube = lg`: each coordinate is read at
    the same number; the factors stay. A DEFINITION: section 1. `spell_seedBack`: spelled, it is the
    same list.
  `entryOfPub_atFull`   under `ShapeAtFull Z` (Johnson/Bind/ForProver/LawsSizes.lean) the packing
    off Z is the packing at the full size's numbers.
  `xiAt_of_key`   an explicit input whose key is `oodAt` at k's letters is `xiAt` at k: by
    unfolding. `inst_eq_xiAt`   the same of an explicit input that is told by its three parts.
    `xiIdxAt_of_reader`   `xiAt` at an index's own reader is `xiIdxAt` at the index.
    `oodAt_atFull`   `entryOfPub_atFull` and `spell_seedBack` in one, at the full size's shape.

Limits. Bookkeeping on types and terms: `spell_seedBack`, `xiAt_of_key`, `inst_eq_xiAt` and
`xiIdxAt_of_reader` hold by unfolding. `xiAt_of_key` and `inst_eq_xiAt`:
NOT IN FRONT OF A LAW OVER COINS: a rule of use, told whole in the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean ("A limit on the coins"). THE GROUND HERE: hK and hρ are of
that rule's first kind; ha and hc name no coin and tie nothing: in the first the key K is a letter
under hK, which ties it to the index, the coins of the item 0 and the seed; in the second the
explicit input ξ is a letter whose key hK ties in the same way, and ρ is a letter under hρ. σ is a
letter beside rc in both: that rule's clause on the seed binds whoever states a law. WHICH MADE TERM
AND WHICH LEMMA LIFT THE BAR: none: the bar is flat: no lemma is named here. The made terms are
`oodSh sh Z ⟨w₀, rc, (σ, n)⟩` for K (unfolded, it is hK's right side) and
`xiAt sh Z ⟨w₀, rc, (σ, n)⟩ (a, c)` for ξ: there the premises hold by unfolding, at every value of
the coins, AND BOTH STATEMENTS ARE IDLE: each says that the term is itself. Nothing says that a seed
is sampled, or of what. `ShapeAtFull Z` is a premise. One committed table; which of the protocol's
tables it is, the first or a copy, is not said here. Nothing runs. This file writes no honest
prover. No correctness of extraction, no binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index privacy; nothing
on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.LawsSizes
import Johnson.Bind.ForProver.XiAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes.Slice (GE NZ frS)
open VerifiableInference.OnPublicFiles (numsRef)
open ProofFile.Honest (TableRand Weights Isk)
open Bind.Twin (Shape)
open Bind.Column (shFull)

/-! ## 1 A definition: a seed of the library's typed form, typed at a shape

It proves nothing. Whoever lays it into a private input takes it as part of how the honest side's
input is read. -/

/-- **A seed whose points' coordinates are numbered below lg, typed at a shape with lg
coordinates**: each coordinate is read at the same number; the factors stay. The way back of
`seedAs` (Johnson/Bind/ForProver/SeedAtFull.lean): that the two undo each other, both ways, is not
shown here: `seedAs_back`, E2E/KeyOodTie.lean, says that `seedAs` undoes that file's `seedBack`. -/
def seedBack {sh : Shape} {lg : ℕ} (h : sh.cube = lg) (e : Fin sh.s → (Fin lg → GE) × NZ) :
    Seed sh :=
  fun a => (fun t => (e a).1 (Fin.cast h t), (e a).2)

/-! ## 2 Small laws -/

/-- Spelled, it is the same list. -/
theorem spell_seedBack (sh : Shape) (lg : ℕ) (h : sh.cube = lg)
    (e : Fin sh.s → (Fin lg → GE) × NZ) :
    spell sh (seedBack h e) =
      (OnBytes.K.IdTable.spellSeedL lg sh.s e).map fun y => ⟨y.1, y.2⟩ := by
  subst h
  rfl

/-- Under `ShapeAtFull` the packing off Z is the packing at the full size's numbers. -/
theorem entryOfPub_atFull (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) (w : Weights) :
    entryOfPub Z w = entryAtF numsRef.kLo numsRef.rows frS.P.v w.entry := by
  have h1 : (linOf Z).kLo = numsRef.kLo := congrArg OnBytes.Flat.MatrixNums.kLo hZ.2
  have h2 : (linOf Z).matrixRows = numsRef.rows := congrArg OnBytes.Flat.MatrixNums.rows hZ.2
  have h3 : (shapeOf Z).v = frS.P.v := congrArg Bind.Twin.Shape.v hZ.1
  unfold entryOfPub
  rw [h1, h2, h3]

/-- An explicit input whose key is `oodAt` at k's letters is the builder's at k: by unfolding. The
number n is read by nothing, and of rc the item 0 alone: the equation holds at every n and at every
rc with that `rc 0`. NOT IN FRONT OF A LAW OVER COINS: of the first kind, tied to the coins: the key
K is a letter under hK; σ is a letter beside rc; which made term and lemma lift it: none: the bar is
flat; at the made key hK is `rfl` and the statement is idle (this file's head, Limits). -/
theorem xiAt_of_key (sh : Shape) (Z : ProofFile.Pub) (w₀ : Weights) (rc : ℕ → TableRand) (σ : Seed sh)
    (n : ℕ) (a c : ByteArray) (K : OnBytes.TableKey)
    (hK : K = oodAt sh (entryOfPub Z w₀) (rc 0) (spell sh σ)) :
    (⟨⟨a, K⟩, c⟩ : ProofFile.Inst) = xiAt sh Z ⟨w₀, rc, (σ, n)⟩ (a, c) := by
  subst hK
  rfl

/-- **An explicit input, told by its three parts, is the builder's at k**: its request's bytes, its
key and its reply's bytes are those that the builder lays; ρ is the coins of item 0. By unfolding.
The number n is read by nothing: the equation holds at every n. NOT IN FRONT OF A LAW OVER COINS: of
the first kind, tied to the coins: the explicit input ξ is a letter whose key stands under hK, ρ a
letter under hρ; σ is a letter beside rc; which made term and lemma lift it: none: the bar is flat;
at the made input the premises hold by unfolding and the statement is idle (this file's head,
Limits). -/
theorem inst_eq_xiAt (sh : Shape) (Z : ProofFile.Pub) (w₀ : Weights) (rc : ℕ → TableRand)
    (ρ : TableRand) (σ : Seed sh) (n : ℕ) (ξ : ProofFile.Inst) {a c : ByteArray} (hρ : rc 0 = ρ)
    (ha : ξ.pub.request = a) (hK : ξ.pub.key = oodAt sh (entryOfPub Z w₀) ρ (spell sh σ))
    (hc : ξ.y = c) : ξ = xiAt sh Z ⟨w₀, rc, (σ, n)⟩ (a, c) := by
  subst hρ ha hc
  obtain ⟨⟨q, K⟩, y⟩ := ξ
  exact xiAt_of_key sh Z w₀ rc σ n q y K hK

/-- The builder at a plain reader that is an index's own reader is the builder at the index type
`Cm.Idx`: by unfolding. -/
theorem xiIdxAt_of_reader (sh : Shape) (Z : ProofFile.Pub) (i : Cm.Idx) (f : ℕ → ℕ → Cb.Gl.F)
    (hf : f = OnBytes.HonestTrace.entryOf i) (rc : ℕ → TableRand) (sd : Seed sh × ℕ)
    (y : ByteArray × ByteArray) :
    xiAt sh Z ⟨⟨f⟩, rc, sd⟩ y = xiIdxAt sh Z ⟨i, rc, sd⟩ y := by
  subst hf
  rfl

/-- Under `ShapeAtFull`, at the full size's shape: the key at the packing off Z and at a seed that
is typed back is the key at the full size's numbers and at the seed's own spelling:
`entryOfPub_atFull` and `spell_seedBack` in one. (h) is a theorem: `cube_full`
(Johnson/Bind/ForProver/KeyOfRecAt.lean), which this file does not import. -/
theorem oodAt_atFull (Z : ProofFile.Pub) (hZ : ShapeAtFull Z) (f : ℕ → ℕ → Cb.Gl.F) (ρ : TableRand)
    (h : shFull.cube = 29) (e : Fin shFull.s → (Fin 29 → GE) × NZ) :
    oodAt shFull (entryOfPub Z ⟨f⟩) ρ (spell shFull (seedBack h e)) =
      oodAt shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v f) ρ
        ((OnBytes.K.IdTable.spellSeedL 29 1 e).map fun y => ⟨y.1, y.2⟩) :=
  (congrArg (fun en => oodAt shFull en ρ (spell shFull (seedBack h e)))
      (entryOfPub_atFull Z hZ ⟨f⟩)).trans
    (congrArg (fun l => oodAt shFull (entryAtF numsRef.kLo numsRef.rows frS.P.v f) ρ l)
      (spell_seedBack shFull 29 h e))

end Bind.ForProver

#print axioms Bind.ForProver.seedBack
#print axioms Bind.ForProver.spell_seedBack
#print axioms Bind.ForProver.entryOfPub_atFull
#print axioms Bind.ForProver.xiAt_of_key
#print axioms Bind.ForProver.inst_eq_xiAt
#print axioms Bind.ForProver.xiIdxAt_of_reader
#print axioms Bind.ForProver.oodAt_atFull
