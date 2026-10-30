-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/WalkOff.lean: what is read off a log under a root does not change when the entries at
a finite set of strings are left out, if these strings are read neither as vertices nor as leaves;
and the strings of the call number 169, at which a verifier would ask for the digests of the
configuration's files and of the parameter bytes, are such strings.

Why. OnBytes/Slice/AtSet.lean leads a bound for every table of values of the random oracle at a
finite set S of strings to a bound for the random oracle. It asks that the event does not get lost
when the entries at the strings of S are left out of the logs (`offSet`). The events of the join
read the logs through walks (OnBytes/Slice/Look.lean). A walk does not see these entries if its look
reads no string of S as a vertex or as a leaf (OnBytes/Slice/WalksO.lean). This file carries that to
the raw string of a part with an interface (`Part`, OnBytes/Slice/JoinThree.lean), and proves the
condition at the encodings `Tie.theImplX` for every string of a call with the number 169. With that
number the format hashes the parameter bytes (index 1: `Tie.digestStr`) and the configuration's
files (index 2: `Fmt.configDigestW`). These digests stand as constants in the checkers of
OnBytes/Slice/OneWorldChain.lean and in the encodings; a verifier that hashes by the oracle would
ask for them at such strings.

Main definition.
 `IsCall169 s`         s is the bits of the string of a call with the number 169: either half, any
                       tree number, any index, any start of 32 bytes, any bytes.
Main theorems.
 (`firstAt_offSet`, `walk_offSet`, `noClash_offSet`: a walk does not see the entries at strings that
 its look does not read: they stand in OnBytes/Slice/WalksO.lean.)
 `Part.raw_offSet`     the same for the raw string that a part reads under a root, if its
                       implementation has one block for a leaf's and a vertex's answer.
 `look_other`          through an encoding `Tie.theImplX`, a string with none of the format's five
                       tags and with neither escape byte in front is read neither as a vertex nor as
                       a leaf: it is a point of the spare oracle.
 `look_call169`        every string with `IsCall169` is such a string, for all data of the encoding.
 `look_digestStr`, `look_configStr`   its cases at the call on the parameter bytes and at the call
                       on the configuration's files.




What is not claimed. That an event of the join does not get lost when the entries at S are left out:
here only what the parts READ off the logs is shown not to change; a checker's value, the roots that
are read off the maker's output, and a reading of the published digest off the log are other
matters. No family of parts over the oracle's values at S is made here.
Which strings a verifier asks, how many,
and which of them are fixed before the oracle is drawn, is not said. Of calls with other numbers
(the commitment ID has 179) nothing is said. No probability. Nothing on any language, on the program
(the Lean port built from OnBytes/), on the C++ verifier or on BLAKE2b.

-/
import OnBytes.Slice.WalksO
import OnBytes.Slice.JudgeLink
import OnBytes.Slice.OneWorldTop
import OnBytes.Slice.RootsInAt
import Fmt.M1SpecKnownProofs
import Run.PlanPullM1
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions
import OnBytes.Tie.SpecXBase
import OnBytes.Slice.TopAny
import OnBytes.Slice.BaseAt
import OnBytes.Slice.BatAt
import OnBytes.Slice.CornersAt
import OnBytes.Slice.CsMet
import OnBytes.Slice.LinkSound
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.MembFacts
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.RoundsLink
import OnBytes.Entry.File
import Fmt.M3Items
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BatSem
import OnBytes.Slice.ManyClosesStd
import OnBytes.Slice.ManyHolds
import OnBytes.Params.EntryCheckIff
import OnBytes.Slice.ManyBlkWritten
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.BlkHead
import OnBytes.Slice.BlkHeadTie
import OnBytes.Slice.BlkTieFold
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyView
import OnBytes.Slice.ChainErrAny
import OnBytes.Slice.CsErr
import OnBytes.Slice.NoWorkRatesNum
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Slice.NoWorkRatesTail
import OnBytes.Slice.NoWorkRatesLink
import OnBytes.Slice.SemLib
import OnBytes.Slice.FoldAt
import OnBytes.Slice.ManyNumLink
import OnBytes.Tie.EntryPre
import OnBytes.Slice.FitsReadAt
import Fmt.M3ParOfLaws
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M1SpecKnown
import Fmt.M3ParOfLawsProofs
import OnBytes.Slice.BlkSem
import OnBytes.Slice.BlkSwitches
import OnBytes.Slice.SameStoredAt
import OnBytes.Slice.SameAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

/-! ## Walks -/

section
variable {lam : ℕ}

/-- **The raw string that a part reads under a root does not see the entries at the strings of S**,
if the part's implementation reads none of them as a vertex or as a leaf, and has one block for a
leaf's and a vertex's answer, taken as it is. No condition on the log. -/
theorem Part.raw_offSet {γ Sg : Type} (s : Part lam γ Sg) (hm : OneBlock s.m)
    (S : Finset (List Bool)) (hn : ∀ x ∈ S, (lookOf s.m).node x = none)
    (hl : ∀ x ∈ S, (lookOf s.m).leaf x = none) (σ : Trace (rom lam)) (cm : Dig lam) :
    s.raw (offSet S σ) cm = s.raw σ cm := by
  refine congrArg (rawOf s.u) (s.J.R.at_congr fun j => ?_)
  rw [extLeaf_eq_walk s.m hm, extLeaf_eq_walk s.m hm, walk_offSet _ S hn hl]

end

/-! ## The encodings, and the strings of the call number 169 -/

section
open _root_.Run
open OnBytes.Tie (PageCX theImplX theImplX_other Tag5 t174 tag_low digestStr)

/-- The 16 bits of the number 169, as they stand in the first word of a call's label. -/
def t169 : List Bool := (bytesToBits (Fmt.u64n 169)).take 16

/-- They are none of the format's five tags. -/
theorem t169_differs : t169 ≠ t160 ∧ t169 ≠ t162 ∧ t169 ≠ t164 ∧ t169 ≠ t166 ∧ t169 ≠ t174 := by
  decide +kernel

/-- The bit string s is the string of a call with the number 169: either half, any tree number t,
any index i, any start of 32 bytes, any bytes. The 32 bytes are asked by the library's lemma on the
tag. -/
def IsCall169 (s : List Bool) : Prop :=
  ∃ (half : UInt8) (t i : ℕ) (st bs : ByteArray), (half = 0 ∨ half = 1) ∧ st.size = 32 ∧
    s = bytesToBits (Fmt.oStr half 169 t i st bs)

variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageCX L K tg)

/-- **Through the encoding, a string with none of the format's five tags and with neither escape
byte in front is read neither as a vertex nor as a leaf.** It is a point of the spare oracle,
written as itself (`Tie.theImplX_other`). -/
theorem look_other (s : List Bool) (ht : ¬ Tag5 s) (h2 : ¬ bitsOfByte 2 <+: s)
    (h3 : ¬ bitsOfByte 3 <+: s) :
    (lookOf (theImplX C)).node s = none ∧ (lookOf (theImplX C)).leaf s = none := by
  have hi : (theImplX C).inv s = ⟨Batch.OracleName.other, (s, (0 : Fin 1))⟩ := by
    have h := (theImplX C).inv_code ⟨Batch.OracleName.other, (s, (0 : Fin 1))⟩
    rw [theImplX_other C s 0 ht h2 h3] at h
    exact h
  constructor
  · show nodeOf ((theImplX C).inv s).1 ((theImplX C).inv s).2.1 = none
    rw [hi]
    rfl
  · show leafOf ((theImplX C).inv s).1 ((theImplX C).inv s).2.1 = none
    rw [hi]
    rfl

/-- **The string of a call with the number 169 is read neither as a vertex nor as a leaf**, through
the encoding at any data. Its tag is none of the five (160, 162, 164, 166, 174), and its first byte
is 0 or 1. -/
theorem look_call169 (s : List Bool) (hs : IsCall169 s) :
    (lookOf (theImplX C)).node s = none ∧ (lookOf (theImplX C)).leaf s = none := by
  obtain ⟨half, t, i, st, bs, hh, hst, rfl⟩ := hs
  rw [oStr_bits half 169 t i st bs]
  have n2 : (2 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  have n3 : (3 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  refine look_other C _ ?_ (hdr_not_prefix 2 half n2 _ _ _ _ _) (hdr_not_prefix 3 half n3 _ _ _ _ _)
  have ht : tag16 (hdr half 169 t i st ++ bytesToBits bs) = t169 :=
    (tag16_hdr half 169 t i st hst (bytesToBits bs)).trans (tag_low 169 t)
  unfold Tag5
  rw [ht]
  obtain ⟨d0, d2, d4, d6, d7⟩ := t169_differs
  rintro (h | h | h | h | h)
  · exact d0 h
  · exact d2 h
  · exact d4 h
  · exact d6 h
  · exact d7 h

/-- The string of the call on the parameter bytes is the string of a call with the number 169. -/
theorem isCall169_digestStr (params : ByteArray) : IsCall169 (bytesToBits (digestStr params)) :=
  ⟨0, 0, 1, Fmt.zero32, params, Or.inl rfl, by decide, rfl⟩

/-- So is the string of the call on the configuration's files (`Fmt.configDigestW`). -/
theorem isCall169_configStr (files : List ByteArray) :
    IsCall169 (bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes files))) :=
  ⟨0, 0, 2, Fmt.zero32, Fmt.configBytes files, Or.inl rfl, by decide, rfl⟩

/-- The string at which a reader would ask for the digest of the parameter bytes is read neither as
a vertex nor as a leaf, through the encoding at any data and for any bytes `params`. -/
theorem look_digestStr (params : ByteArray) :
    (lookOf (theImplX C)).node (bytesToBits (digestStr params)) = none ∧
      (lookOf (theImplX C)).leaf (bytesToBits (digestStr params)) = none :=
  look_call169 C _ (isCall169_digestStr params)

/-- The string at which a verifier would ask for the configuration's digest is read neither as a
vertex nor as a leaf, through the encoding at any data and for any files. -/
theorem look_configStr (files : List ByteArray) :
    (lookOf (theImplX C)).node
        (bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes files))) = none ∧
      (lookOf (theImplX C)).leaf
        (bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes files))) = none :=
  look_call169 C _ (isCall169_configStr files)

end

end OnBytes.Slice
