-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/BzTie.lean: the honest side of the kind "lookup" (K3): what the row
of the lookup on the digits reads is what the two fillings of the oracle message set. Theorems, and
tests with code on public data.

Terms. Honest/K3/GLOSSARY.md. In this file: two arrays are sent behind the round of the smallness
test: the digits ZZ, and the bits BZ of the multiplicities of the lookup on them. Their values, as
fillings of `RowData` (Honest/RowData.lean), are defined in other files: ZZ by
`zzVals` (Honest/K8/ZzData.lean), BZ by `bzValsAt` (Johnson/HonestTrace/BZRows.lean). The lookup's
row makes its keys and bits by `lookZ` (Honest/K3/WitFill.lean) at `zzOf` (Honest/K8/Digits.lean).
This file defines no value.

What is shown.
  `bzValsAt_val`, `zzVals_val`: at a segment with its public data, whose round has been heard, the
    values are the field bz of `digitsOf` (Johnson/HonestTrace/DigitsAtTrace.lean) and `zzOf`.
  `bit_is_bzValsAt`: a bit of the lookup's structure on the digits is the value that `bzValsAt` sets
    at BZ's own address of that bit.
  `key_is_zzVals`: its keys are the joint key vector of the values that `zzVals` sets.
  `drawn_of_sampled`: where the two fillings name one round they read one list of sampled entries.
  `row_is_sent`, `seated_row_is_sent`: both ties at one structure, where the two fillings name one
    structure of the smallness test, one list and one round; and the same of the structure that the
    seated filling gives at a link's digits, where these are `tlOf` (Honest/K3/WitPlan.lean) and
    `matsOwn` (Honest/K3/WitOwner.lean).
  `sameTlB`, `sameGroundB`: tests on public data: the structures of the smallness test that the
    ground has built are, in eleven fields, those at which the lookups' rows stand (`tlOf`); the
    rounds named "RNG" are the sites' rounds.
  `oneRoundB`: a test on public data: three ways to one number. At every site of a lookup on digits
    the round that samples the matrix is the same by the site (Honest/K3/Lot.lean), by the rounds'
    names (`roundNumbers`, Honest/K2/Rounds.lean) and by the first round of the segment's place of
    the smallness test (`rngAt`, Johnson/HonestTrace/BZVals.lean); and the number of entries that
    this round is declared to sample is `tritsDue` (Honest/K3/WitFits.lean).
  `sameGroundB` and `oneRoundB` are definitions alone: they stand in no theorem and are run by no
    test (Honest/K3/BzTieGuards.lean [not in this library], under Limits, says why); no lemma says
    what an acceptance by either gives.
  Helper: `inBoth`.

Hypotheses that remain.
  `h1`, `h2`: the segment has its public data (b, or the structure tl); its round has been heard and
    has sampled t.
  `hZ`, `hm`, `hr`: (in `row_is_sent`, `seated_row_is_sent`) ZZ's public data name the same
    structure, the same list and the same round as BZ's.
  `hb`, `hl`: (in `seated_row_is_sent`) the structure of b is `tlOf X l`; its list is `matsOwn X l`.
  `h`: (in `drawn_of_sampled`) ZZ's list of rounds names, at the segment, the round of b.

Imported: Honest/RowData.lean, Honest/K8/ZzData.lean, Honest/K8/Digits.lean, Honest/K2/Rounds.lean,
Johnson/HonestTrace/BZRows.lean, Johnson/HonestTrace/BZVals.lean and
Johnson/HonestTrace/DigitsAtTrace.lean.

Users. `sameTlB` stands in statements of Honest/K3/BzTieCore.lean [not in this library] and is
evaluated in Honest/K3/BzTieGuards.lean [not in this library].

Limits. The digits that are looked up are the digits that are sent only where the two fillings and
the lookups' rows are given one list of where the matrices are read, one structure of the smallness
test and one round. The tests of this file compare eleven fields of the structure, and the round;
the list is a letter at both fillings, and the lookups' rows read `matsOwn`. The theorems are
conditional on the segment's public data and on the round's having been heard. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.HonestTrace.BZRows
import Johnson.Desc.ProofFile.Honest.K8.ZzData
import Johnson.Desc.ProofFile.Honest.K3.WitArrays
import Johnson.Desc.ProofFile.Honest.K3.WitFits
import Johnson.Desc.ProofFile.Honest.K3.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Slice (toF)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (digitsOf kvZ BzAt bzValsAt rngAt)
open ProofFile.Honest.K2 (drawnAt roundNumbers)
open ProofFile.Honest.K8 (ZzPub zzVals zzOf)
open VerifiableInference.Desc.K3 (sameShapeAll)

/-! ## 1 The values are the lookup's own -/

/-- At a segment with its public data whose round has been heard, BZ's value is the field bz of
`digitsOf`. -/
theorem bzValsAt_val (at_ : Nat → Option BzAt) (R : Readers) (heard : List Fmt.Drawn) (seg : Nat)
    (b : BzAt) (t : List Int) (h1 : at_ seg = some b) (h2 : b.sampled heard = some t)
    (name : String) (i c : Nat) :
    (bzValsAt at_).val R heard seg name i c = .inl ((digitsOf b.tl b.mats R.cells t).bz i c) := by
  show (match at_ seg with
    | some b => (let v := b.entry R.cells heard; fun i c => .inl (v i c) :
        Nat → Nat → Cb.Gl.F ⊕ Cb.Gl.E)
    | none => fun _ _ => .inl (toF 0)) i c = _
  rw [h1]
  show Sum.inl (b.entry R.cells heard i c) = _
  unfold BzAt.entry
  rw [h2]
  rfl

/-- The like of ZZ's values. -/
theorem zzVals_val (Z : ZzPub) (R : Readers) (heard : List Fmt.Drawn) (l : Nat) (tl : HTailF2)
    (t : List Int) (h1 : Z.tl l = some tl) (h2 : drawnAt Z.rng heard l = .ok t) (i c : Nat) :
    (zzVals Z).val R heard l "ZZ" i c = .inl (zzOf tl (Z.mats l) R.cells t i c) := by
  show (match ("ZZ" == "ZZ"), Z.tl l, (drawnAt Z.rng heard l).toOption with
    | true, some tl, some t => (.inl (zzOf tl (Z.mats l) R.cells t i c) : Cb.Gl.F ⊕ Cb.Gl.E)
    | _, _, _ => .inl (toF 0)) = _
  rw [h1, h2]
  rfl

/-- An element of the base field, or of the extension field, read in the extension field. -/
def inBoth : Cb.Gl.F ⊕ Cb.Gl.E → Cb.Gl.E
  | .inl x => algebraMap Cb.Gl.F Cb.Gl.E x
  | .inr x => x

/-- **A bit of the lookup's structure on the digits is the value that `bzValsAt` sets at BZ's own
address of that bit.** Conditional on: the segment has the public data b; its round has been heard
and has sampled t. No instance of these hypotheses is exhibited in this file. -/
theorem bit_is_bzValsAt (at_ : Nat → Option BzAt) (R : Readers) (heard : List Fmt.Drawn)
    (seg : Nat) (b : BzAt) (t : List Int) (h1 : at_ seg = some b)
    (h2 : b.sampled heard = some t) (u j : ℕ) :
    (lookZ b.tl (zzOf b.tl b.mats R.cells t)).bit u j =
      inBoth ((bzValsAt at_).val R heard seg "BZ" ((OnBytes.DgP.portQ b.tl).bAt u j).2.1
        ((OnBytes.DgP.portQ b.tl).bAt u j).2.2) := by
  rw [bzValsAt_val at_ R heard seg b t h1 h2]
  exact lookZ_bit_digitsOf b.tl b.mats R.cells t u j

/-- **The keys of the lookup's structure on the digits are the joint key vector of the values that
`zzVals` sets.** Conditional on: the segment has the structure tl; its round has been heard and has
sampled t. No instance of these hypotheses is exhibited in this file. -/
theorem key_is_zzVals (Z : ZzPub) (R : Readers) (heard : List Fmt.Drawn) (l : Nat) (tl : HTailF2)
    (t : List Int) (h1 : Z.tl l = some tl) (h2 : drawnAt Z.rng heard l = .ok t) (theta : Cb.Gl.E)
    (n : ℕ) :
    (lookZ tl (zzOf tl (Z.mats l) R.cells t)).key theta n =
      OnBytes.Ends.jointKey tl.f9
        (kvZ tl fun i c => inBoth ((zzVals Z).val R heard l "ZZ" i c)) theta n := by
  have e : (fun i c => inBoth ((zzVals Z).val R heard l "ZZ" i c)) =
      inExt (digitsOf tl (Z.mats l) R.cells t).zz := by
    funext i c
    rw [zzVals_val Z R heard l tl t h1 h2]
    rfl
  rw [e]
  exact lookZ_key_digitsOf tl (Z.mats l) R.cells t theta n

/-- Where the two fillings name one round they read one list of sampled entries. -/
theorem drawn_of_sampled (rng : List Nat) (b : BzAt) (heard : List Fmt.Drawn) (seg : Nat)
    (t : List Int) (h : rng[seg]? = some b.rng) (h2 : b.sampled heard = some t) :
    drawnAt rng heard seg = .ok t := by
  unfold BzAt.sampled at h2
  unfold drawnAt
  rw [h]
  show (match heard[b.rng]? with
    | some d => (.ok d.trits : Except String (List Int))
    | none => .error "a segment's matrix has not been drawn") = _
  cases hd : heard[b.rng]? with
  | none => rw [hd] at h2; exact absurd h2 (by simp)
  | some d =>
    rw [hd] at h2
    exact congrArg Except.ok (Option.some.inj h2)

/-- **Both ties at one structure.** Conditional on: the segment has BZ's public data b; its round
has been heard and has sampled t; ZZ's public data name the same structure of the smallness test,
the same list and the same round. No instance of these hypotheses is exhibited in this file. -/
theorem row_is_sent (at_ : Nat → Option BzAt) (Z : ZzPub) (R : Readers) (heard : List Fmt.Drawn)
    (l : Nat) (b : BzAt) (t : List Int) (h1 : at_ l = some b) (h2 : b.sampled heard = some t)
    (hZ : Z.tl l = some b.tl) (hm : Z.mats l = b.mats) (hr : Z.rng[l]? = some b.rng) :
    (∀ u j : ℕ, (lookZ b.tl (zzOf b.tl b.mats R.cells t)).bit u j =
      inBoth ((bzValsAt at_).val R heard l "BZ" ((OnBytes.DgP.portQ b.tl).bAt u j).2.1
        ((OnBytes.DgP.portQ b.tl).bAt u j).2.2)) ∧
    ∀ (theta : Cb.Gl.E) (n : ℕ), (lookZ b.tl (zzOf b.tl b.mats R.cells t)).key theta n =
      OnBytes.Ends.jointKey b.tl.f9
        (kvZ b.tl fun i c => inBoth ((zzVals Z).val R heard l "ZZ" i c)) theta n := by
  refine ⟨fun u j => bit_is_bzValsAt at_ R heard l b t h1 h2 u j, fun theta n => ?_⟩
  have k := key_is_zzVals Z R heard l b.tl t hZ (drawn_of_sampled Z.rng b heard l t hr h2) theta n
  rw [hm] at k
  exact k

/-- **The same of the structure that the seated filling gives at a link's digits** (`ownSources`,
Honest/K3/WitOwner.lean, at the entries that round number b.rng sampled). Conditional on the same,
and on: the structure of b is the one at which the lookups' rows stand, and the list of b is
`matsOwn`. No instance of these hypotheses is exhibited in this file. -/
theorem seated_row_is_sent {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH)
    (at_ : Nat → Option BzAt) (Z : ZzPub) (R : Readers) (heard : List Fmt.Drawn) (l : Nat)
    (b : BzAt) (t : List Int) (h1 : at_ l = some b) (h2 : b.sampled heard = some t)
    (hZ : Z.tl l = some b.tl) (hm : Z.mats l = b.mats) (hr : Z.rng[l]? = some b.rng)
    (hb : b.tl = tlOf X l) (hl : b.mats = matsOwn X l) :
    (∀ u j : ℕ,
      ((ownSources X cells weights pubH).digits l R.cells (tritsAt heard b.rng)).bit u j =
        inBoth ((bzValsAt at_).val R heard l "BZ" ((OnBytes.DgP.portQ b.tl).bAt u j).2.1
          ((OnBytes.DgP.portQ b.tl).bAt u j).2.2)) ∧
    ∀ (theta : Cb.Gl.E) (n : ℕ),
      ((ownSources X cells weights pubH).digits l R.cells (tritsAt heard b.rng)).key theta n =
        OnBytes.Ends.jointKey b.tl.f9
          (kvZ b.tl fun i c => inBoth ((zzVals Z).val R heard l "ZZ" i c)) theta n := by
  have ht : tritsAt heard b.rng = t := by
    unfold BzAt.sampled at h2
    unfold tritsAt
    rw [h2]
    rfl
  have e : (ownSources X cells weights pubH).digits l R.cells (tritsAt heard b.rng) =
      lookZ b.tl (zzOf b.tl b.mats R.cells t) := by
    show lookZ (tlOf X l) (zzOf (tlOf X l) (matsOwn X l) R.cells (tritsAt heard b.rng)) = _
    rw [ht, ← hb, ← hl]
  rw [e]
  exact row_is_sent at_ Z R heard l b t h1 h2 hZ hm hr

/-! ## 2 One structure, one round -/

/-- Two structures of a smallness test are the same in eleven fields: tau, mz, the number and the
list of the matrices, their first rows, the two calls with their pieces, the lookup's numbers, the
arrays' numbers. The structure has more fields, which are not compared. That `zzOf`, `digitsOf`,
`lookZ` and BZ's address read none of them is `sameTl_reads` (Honest/K3/BzTieCore.lean
[not in this library]). -/
def sameTlB (a b : HTailF2) : Bool :=
  a.tau == b.tau && a.mz == b.mz && a.NM == b.NM && decide (a.mats = b.mats) && a.off == b.off &&
    a.lidb == b.lidb && decide (a.blocks = b.blocks) && decide (a.ix = b.ix) &&
    sameCallZ a.z1 b.z1 && sameCallZ a.z2 b.z2 && sameShapeAll a.f9 b.f9

/-- **One structure and one round everywhere.** Every segment's structure that the ground has built
is, by `sameTlB`, the one at which the lookups' rows stand; there is one for every link with a plan
up to the head's; and at every site of a lookup on digits the site's number of the round that
samples the matrix, which is found by the table of places, is the number of the segment's round of
the name "RNG". -/
def sameGroundB (Z : Pub) (G : Ground) : Bool :=
  G.built.size == linkH Z.p.X + 1 &&
    (G.built.toList.zipIdx.all fun y => sameTlB y.1.tl (tlOf Z.p.X y.2)) &&
    (lookSites Z).all fun s => !s.digits || (roundNumbers Z.D.1 "RNG")[s.link]? == s.rng

/-- **Three ways to one number.** At every site of a lookup on digits: the site's round, the
segment's round of the name "RNG", and the first round of the segment's place of the smallness test
are one; and that round is declared to sample `tritsDue` entries. -/
def oneRoundB (Z : Pub) : Bool :=
  match spotsOf Z.cuts with
  | some sps =>
    (lookSites Z).all fun s => !s.digits ||
      ((roundNumbers Z.D.1 "RNG")[s.link]? == s.rng &&
        (rngAt Z sps s.link).map (·.1) == s.rng &&
        (rngAt Z sps s.link).map (·.2) == some (tritsDue Z.p.X s.link))
  | none => false

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.bzValsAt_val
#print axioms ProofFile.Honest.K3.zzVals_val
#print axioms ProofFile.Honest.K3.bit_is_bzValsAt
#print axioms ProofFile.Honest.K3.key_is_zzVals
#print axioms ProofFile.Honest.K3.drawn_of_sampled
#print axioms ProofFile.Honest.K3.row_is_sent
#print axioms ProofFile.Honest.K3.seated_row_is_sent
