-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Flat/CodingHonest.lean: A WRITTEN HONEST SIDE OF THE CONFIGURATION OF A STORED TABLE WITH A
RECORD (`Coding A`, OnBytes/Flat/FilesAt.lean), AND THE DECODER'S LAW AT IT: from the honest word
and the honest record of a matrix in range the index decoder gives that matrix back. Definitions,
statements and proofs.

Why. Binding of a commitment to "what the extractor gives" spends one law of the object: the decoder
gives back the index from its honest encoding and record (`HolographicProtocol.WiredR.dec_enc`,
Hiop/RecInterface.lean). At the objects of the two sizes (`Files.withProvers`, OnBytes/Flat/Object.lean,
over `DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)`) the encoder, the holding of a matrix and the answers are fields of
the letter E. Constants are values of that type, at
which the law fails as soon as two matrices are in range (`same_of_decodes` below says why). Here E
is written.

Main names (namespace `OnBytes.Flat`).
  `rowWordsAt`, `rowWords S m`: the words of a table of messages, row by row: of each entry its
    first coordinate. By the print at the foot of this file `rowWordsAt` (all of the text but that
    projection, over the base field) and `tailWords` are on [propext] alone; `rowWords` shows
    `Classical.choice`: its type names the extension field and the decoder's data.
  `tailWords S ρ`: the words of the rows' random tails.
  `codingHonest S Z cut A Pad holdW`: the value of `Coding A`. Its encoder is the format's own
    (`honestTab`, OnBytes/Slice/Honest.lean, made with `Fmt.M1.symF`) at these words; its answers
    are the sample map's own values (`LdIx.ZR`); the message that holds a matrix is `honestMsgs` of
    the words that holdW gives. Pad and holdW are letters.
  `honestMsgs_rowWords`: read back, the words of messages that were read off words are the same
    messages.
  **`conf_D_codingHonest`**: the law, at the configuration.
  **`obj_decodes`**: the same in the words of `HolographicProtocol`, at `F.withProvers P` for every F and P.
  `obj_decodes_full`, `obj_decodes_small`: at the two sizes' decoders: no premise on numbers.
  `same_of_decodes`: general in the object: where the law holds at two indices with one word and one
    record, the two are one index. So a constant encoder fails the law at two indices.
  `words_differ`: so at `codingHonest` two different matrices in range never have the same honest
    word and record.

WHO READS EACH LETTER (D: the index decoder `ConfigurationWithOutOfDomainSample.D`; E: the honest side; -: nobody here).
- S (the code, the number of row variables, the radius): D and E. Z (the sample map): D (which
  tables have the record's answers; collisions) and E (the answers). cut: D, through `A.mat_cut`
  alone; no proof here reads it.
- A.mat, A.inRange: D (`held`). A.Rel, X: -.
- Pad, holdW: E alone. Under "for all". hmat ties holdW to A.mat, at the one matrix and pad of which
  the statement speaks.
- d, hd, he: the code has distance d and the radius is below it. At the two sizes they are proved
  (`full_dist`, `small_dist`, OnBytes/K/Oracle/DecodesAt.lean).
- F, P (the three protocols, their honest provers): -: `withProvers` lays them beside what is read here.
- η, ρ, s (pads, tails, seed): under "for all".
NOTHING THAT A VERIFIER READS STANDS UNDER "THERE IS": no statement here has one.

Limits.
- hmat IS A PREMISE: that the words which holdW gives hold the matrix. No holdW is written here, and
  that some matrix is in range is not shown here: where none is, the law says nothing.
- The law is asked and shown at matrices IN RANGE alone. At a matrix out of range it is false at
  every E: the decoder never gives one (said here without a theorem).
- The radius is below the code's DISTANCE, not below half of it. Within it of a table of code words
  lies that table alone; of other tables nothing is said.
- That a program writes its tables with `Fmt.M1.symF`, draws its tails so, or stores these answers
  is not said: no file of a program is compared here. The type of the tails (a field element for
  each row and each place of a tail) is this file's choice.
- `rowWords` drops the second and third coordinate of an entry: at a message with an entry outside
  the base field the encoder encodes another message. `hold` gives no such message.
- Nothing on hiding: that the tails and pads hide anything is not treated. Nothing on a verifier, on
  soundness or on completeness. No commitment, no hash function.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.DecodesAt
import OnBytes.Flat.FilesAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice

/-! ## General in the object: what the law forces -/

/-- Where the decoder gives back two indices from one word and one record, they are one index. -/
theorem same_of_decodes {I X : Type} (L : HolographicProtocol I X) (i i' : I) (r r' : L.EncodingRandomness) (s s' : L.OutOfDomainSeed)
    (h : L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i)
    (h' : L.decodeIndex (L.encodeIndex i' r') (L.recOf i' r' s') = some i')
    (hw : L.encodeIndex i r = L.encodeIndex i' r') (hr : L.recOf i r s = L.recOf i' r' s') : i = i' := by
  rw [hw, hr, h'] at h
  exact (Option.some.inj h).symm

/-! ## The words -/

/-- The words of a table of messages over the base field: v row variables, l entries in a row's
message. -/
def rowWordsAt (v l : ℕ) (m : (Fin v → Bool) × Fin l → GF) (b : ℕ) : List UInt64 :=
  List.ofFn fun j : Fin l => OnBytes.Slice.ofF (m (fun t => b.testBit t.val, j))

section
variable (S : Sz)

/-- The words of a table of messages: row number b, entry j: the first coordinate of the entry at
the vertex of b's lowest bits, written as a word below the prime. -/
def rowWords (m : S.ix.Row × S.En → GE) (b : ℕ) : List UInt64 :=
  rowWordsAt S.P.v S.P.T.l (fun n => (m n).c0) b

/-- The words of the rows' tails; beyond the last row: none. -/
def tailWords (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) (b : ℕ) : List UInt64 :=
  if h : b < 2 ^ S.P.v then List.ofFn fun q => OnBytes.Slice.ofF (ρ ⟨b, h⟩ q) else []

/-- A word of `rowWords`, at the number of a vertex. -/
theorem rowWords_getD (m : S.ix.Row × S.En → GE) (r : S.ix.Row) (j : S.En) :
    (rowWords S m (Sz.rowNo r)).getD j.val 0 = OnBytes.Slice.ofF (m (r, j)).c0 := by
  have hl : j.val < (rowWords S m (Sz.rowNo r)).length := by
    unfold rowWords rowWordsAt
    rw [List.length_ofFn]
    exact j.isLt
  have hv : (fun t : Fin S.P.v => (Sz.rowNo r).testBit t.val) = r := funext (testBit_rowNo r)
  rw [List.getD_eq_getElem _ _ hl]
  unfold rowWords rowWordsAt
  rw [List.getElem_ofFn]
  exact congrArg (fun q : S.ix.Row => OnBytes.Slice.ofF (m (q, j)).c0) hv

/-- Read in the field, the words of a table of messages give each entry's first coordinate. -/
theorem honestMsgs_rowWords_apply (m : S.ix.Row × S.En → GE) (n : S.ix.Row × S.En) :
    honestMsgs S (rowWords S m) n = algebraMap GF GE (m n).c0 := by
  show algebraMap GF GE (OnBytes.Slice.toF ((rowWords S m (Sz.rowNo n.1)).getD n.2.val 0)) = _
  rw [rowWords_getD, toF_ofF]

/-- **Messages that were read off words come back.** -/
theorem honestMsgs_rowWords (msg : ℕ → List UInt64) :
    honestMsgs S (rowWords S (honestMsgs S msg)) = honestMsgs S msg := by
  funext n
  rw [honestMsgs_rowWords_apply]
  rfl

end

/-! ## The honest side, written -/

section
variable (S : Sz) (Z : Sample GE S.En) (cut : ℕ) {X : Type} (A : (S.toDecR Z cut).Claims X)
  (Pad : Type) [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- **The honest side of the configuration of a stored table with a record**: the format's own
encoder at the messages' words and the tails' words; the sample map's own answers; a matrix is held
by the messages that are read off the words which holdW gives. -/
def codingHonest : Coding A where
  Rnd := Fin (2 ^ S.P.v) → Fin S.P.T.r → GF
  enc := fun m ρ => honestTab S (rowWords S m) (tailWords S ρ)
  Pad := Pad
  hold := fun M η => honestMsgs S (holdW M η)
  smp := fun s m => (S.toDecR Z cut).ix.ZR.val s m

variable {d : ℕ}

/-- **The decoder's law at the written honest side.** The code has distance d, and the radius is
below it (hd, he). M is in range (hM), and the words that holdW gives at M and η hold M (hmat).
Then from the honest word of M, at the pads η and any tails ρ, and its honest record at any seed s,
the index decoder gives M. -/
theorem conf_D_codingHonest (hd : HasDist S.ix.G d) (he : S.eM < d) (M : A.Mat)
    (hM : A.inRange M) (η : Pad) (hmat : A.mat (honestMsgs S (holdW M η)) = M)
    (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) (s : Z.D) :
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW))).D
      (honestTab S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ))
      (s, (S.toDecR Z cut).ix.ZR.val s (honestMsgs S (holdW M η))) = some M := by
  classical
  have e := honestMsgs_rowWords S (holdW M η)
  have hv := view_honestPolys S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ)
  have hc : ¬ (S.toDecR Z cut).coll
      (honestTab S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ)) s :=
    OnBytes.K.Oracle.not_coll_words (S.toDecR Z cut) hd he _
      (honestPolys S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ))
      (tab_honestTab S _ _) s
  have hk : (S.toDecR Z cut).dcd
      (honestTab S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ))
      (s, (S.toDecR Z cut).ix.ZR.val s (honestMsgs S (holdW M η))) =
      some (honestMsgs S (holdW M η)) := by
    have h0 := OnBytes.K.Oracle.dcd_words (S.toDecR Z cut) hd he _
      (honestPolys S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ))
      (tab_honestTab S _ _) s
    have hv' : (S.toDecR Z cut).ix.view
        (honestPolys S (rowWords S (honestMsgs S (holdW M η))) (tailWords S ρ)) =
        honestMsgs S (holdW M η) := hv.trans e
    rw [hv'] at h0
    exact h0
  rw [DecR.conf_D, if_neg hc]
  refine (congrArg (fun o => Option.bind o
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW))).held) hk).trans ?_
  show (if A.inRange (A.mat (honestMsgs S (holdW M η))) then
    some (A.mat (honestMsgs S (holdW M η))) else none) = some M
  rw [hmat, if_pos hM]

/-- **The same in the words of an object with records**, at every three protocols F over that
configuration and all their honest provers P: the clause `dec_enc` of `HolographicProtocol.WiredR`
(Hiop/RecInterface.lean) at the index M. -/
theorem obj_decodes (hd : HasDist S.ix.G d) (he : S.eM < d)
    (F : Files (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW)))) (P : F.Provers)
    (M : A.Mat) (hM : A.inRange M) (hmat : ∀ η, A.mat (honestMsgs S (holdW M η)) = M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  conf_D_codingHonest S Z cut A Pad holdW hd he M hM r.1 (hmat r.1) r.2 s

/-- **Two different matrices in range never have the same honest word and record.** -/
theorem words_differ (hd : HasDist S.ix.G d) (he : S.eM < d)
    (F : Files (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW)))) (P : F.Provers)
    (M M' : A.Mat) (hM : A.inRange M) (hM' : A.inRange M')
    (hmat : ∀ η, A.mat (honestMsgs S (holdW M η)) = M)
    (hmat' : ∀ η, A.mat (honestMsgs S (holdW M' η)) = M') (hne : M ≠ M')
    (r r' : (F.withProvers P).EncodingRandomness) (s s' : (F.withProvers P).OutOfDomainSeed) :
    ¬ ((F.withProvers P).encodeIndex M r = (F.withProvers P).encodeIndex M' r' ∧
      (F.withProvers P).recOf M r s = (F.withProvers P).recOf M' r' s') :=
  fun h => hne (same_of_decodes (F.withProvers P) M M' r r' s s'
    (obj_decodes S Z cut A Pad holdW hd he F P M hM hmat r s)
    (obj_decodes S Z cut A Pad holdW hd he F P M' hM' hmat' r' s') h.1 h.2)

end

/-! ## At the two sizes: no premise on numbers is left -/

/-- **At the full size's decoder.** -/
theorem obj_decodes_full {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (Pad : Type)
    [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)
    (F : Files (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW))))
    (P : F.Provers) (M : A.Mat) (hM : A.inRange M)
    (hmat : ∀ η, A.mat (honestMsgs frS (holdW M η)) = M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  obj_decodes frS frZ 402653181 A Pad holdW OnBytes.K.Oracle.full_dist.1
    OnBytes.K.Oracle.full_dist.2 F P M hM hmat r s

/-- **At the small example's decoder.** -/
theorem obj_decodes_small {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (Pad : Type)
    [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)
    (F : Files (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest srS srZ 524285 A Pad holdW))))
    (P : F.Provers) (M : A.Mat) (hM : A.inRange M)
    (hmat : ∀ η, A.mat (honestMsgs srS (holdW M η)) = M)
    (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex M r) ((F.withProvers P).recOf M r s) = some M :=
  obj_decodes srS srZ 524285 A Pad holdW OnBytes.K.Oracle.small_dist.1
    OnBytes.K.Oracle.small_dist.2 F P M hM hmat r s

end OnBytes.Flat

#print axioms OnBytes.Flat.rowWordsAt
#print axioms OnBytes.Flat.rowWords
#print axioms OnBytes.Flat.tailWords
#print axioms OnBytes.Flat.same_of_decodes
#print axioms OnBytes.Flat.honestMsgs_rowWords
#print axioms OnBytes.Flat.conf_D_codingHonest
#print axioms OnBytes.Flat.obj_decodes
#print axioms OnBytes.Flat.words_differ
#print axioms OnBytes.Flat.obj_decodes_full
#print axioms OnBytes.Flat.obj_decodes_small
