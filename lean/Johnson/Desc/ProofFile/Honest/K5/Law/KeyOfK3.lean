-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeyOfK3.lean: THE READER OF THE KEY POINTS OF THE KIND "an
attention segment's own rounds" (K5), LAID AT THE TEXT OF THE LOOKUP's HONEST SIDE: each call's key
point, made of the challenges heard in the rounds of the segment's lookup on the calls (`keyPtsAt`,
Honest/K3/Heard.lean). A definition, and what it gives for nothing: the key points' lengths hang on
the lookup's shape alone, whatever was heard.

Why. The lot's honest side takes the reader as a letter, keyOf (Honest/K5/Row.lean), and this
folder's laws take two premises on lengths of it: `KeySizes` (Honest/K5/Law/Fits.lean) and `KeyWide`
(Honest/K5/Law/FitsRun.lean). At this text both hold with no premise: a key point is one sample in
front of `layBack m …`, whose size is m by the library's `layBack_size`; a round that is not heard
counts as zeros.

  `keyOfK3`            THE READER: at the segment number l: the shape of the plan of group l / 2;
                       base: the rounds in front of the table's step "A‹l / 2›.1.call"
  `keyPt_size`         a point in front of a level with n variables has n coordinates. No premise
  `keyPtsOf_sizes`     the cut's lengths hang on the point's length alone. CONDITIONAL: two points
                       of one length
  `keyOfK3_sizes`      **at any two lists of challenges the key points are as many and as long.** No
                       premise
  `keySizes_K3`, `keyWide_K3`   **`KeySizes` and `KeyWide` at a place whose reader is `keyOfK3`.**
                       CONDITIONAL: that equation on the place's letter keyAt. By `sameSizes_of_map`
                       (Honest/K5/Law/FitsRun.lean)

Limits. Lengths alone. That the key points have the calls' numbers of bits (the test
`Seat5.keysFit`) is not here: it wants facts on the plan. That the base is the number of the chain's
rounds in front of the lookup's member, that the reader reads nothing from the kind's own rounds on,
and that its value is what the verifier's state holds, are not here. Where the public files have no
plan of the group, or the table no such step, the reader returns no key point: the test
`Seat5.keysFit` then says no wherever the place has a call, the maker of the public data yields
nothing, AND NO HALF IS LAID AT THAT PLACE, WITHOUT A WORD: a wrong name of the step would make
nothing false: it would empty the lot. l / 2 is the group of an attention segment, whose number is
odd; at an even l the reader reads a plan that is not the segment's: no place of the kind has such a
number.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.K5.Law.FitsRun
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open ProofFile.Honest.K3 (LFace ptsOf keyPtsOf keyPtsAt)

/-- **THE READER OF THE KEY POINTS AT THE TEXT OF THE LOOKUP's HONEST SIDE.** Z: the public part; G:
the ground; l: the segment's number. It is a definition. -/
def keyOfK3 (Z : Pub) (G : Ground) (l : Nat) (heard : List Fmt.Drawn) : Array (Array E) :=
  match G.W.A[l / 2]?, Z.roundsBefore? ("A" ++ toString (l / 2) ++ ".1.call") with
  | some A, some base => (keyPtsAt A.fs base heard).zk
  | _, _ => #[]

/-- A point in front of a level with n variables has n coordinates. No premise. -/
theorem keyPt_size (f : LFace) (base : Nat) (heard : List Fmt.Drawn) (i n : Nat) :
    ((ptsOf f base heard).keyPt i n).size = n := by
  cases n with
  | zero => rfl
  | succ m =>
    show (#[_] ++ VerifiableInference.Desc.First.ProdV.layBack m _ _).size = m + 1
    rw [Array.size_append, VerifiableInference.Desc.First.ProdV.layBack_size]
    exact Nat.add_comm 1 m

/-- The cut's lengths hang on the point's length alone. CONDITIONAL: two points of one length. -/
theorem keyPtsOf_sizes (h : OnBytes.Model.Forest.Shape) {p p' : Array E} (hs : p.size = p'.size) :
    (keyPtsOf h p).zk.map (·.size) = (keyPtsOf h p').zk.map (·.size) := by
  unfold keyPtsOf
  simp only [Array.map_map]
  congr 1
  funext c
  simp [Function.comp, Array.size_append, Array.size_extract, hs]

/-- **At any two lists of challenges the key points are as many and as long.** No premise. -/
theorem keyOfK3_sizes (Z : Pub) (G : Ground) (l : Nat) (hd hd' : List Fmt.Drawn) :
    (keyOfK3 Z G l hd).map (·.size) = (keyOfK3 Z G l hd').map (·.size) := by
  unfold keyOfK3
  split
  · exact keyPtsOf_sizes _ (by rw [keyPt_size, keyPt_size])
  · rfl

/-- **`KeySizes` at a place whose reader is `keyOfK3`.** CONDITIONAL: hZ: that equation on the
place's letter keyAt. -/
theorem keySizes_K3 {Z5 : Seat5} {Z : Pub} {G : Ground} {l : Nat} (hZ : Z5.keyAt = keyOfK3 Z G l) :
    KeySizes Z5 := by
  intro f f' _
  rw [hZ]
  exact sameSizes_of_map (keyOfK3_sizes Z G l f f')

/-- **`KeyWide` at a place whose reader is `keyOfK3`**, at every list of declared rounds.
CONDITIONAL: hZ. -/
theorem keyWide_K3 {Z5 : Seat5} {Z : Pub} {G : Ground} {l : Nat} (hZ : Z5.keyAt = keyOfK3 Z G l)
    (ds : List Fmt.DeclaredRound) : KeyWide Z5 ds := by
  intro front more _
  rw [hZ]
  exact keyOfK3_sizes Z G l _ _

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.keyPt_size
#print axioms ProofFile.Honest.K5.keyPtsOf_sizes
#print axioms ProofFile.Honest.K5.keyOfK3_sizes
#print axioms ProofFile.Honest.K5.keySizes_K3
#print axioms ProofFile.Honest.K5.keyWide_K3
