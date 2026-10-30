-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsAt.lean: bodies that are strings of bits as the instance of the sibling's general
form of a page at a description; and the readers of a body joined.

The sibling's general form (OnBytes/TypedOracleCompiler/Run/PlanQXRun.lean, PageXFit.lean) takes the type of bodies
as a parameter, with data: how a stored table's symbol lies among the bodies, with a reading back
and both laws, and how any other body is spelled (`BodyD`); and one code of bodies with three
conditions and a serialiser (`LeafD`).
 - `okRd_of_ok2`, `ok2_of_okRd`: a body passes `okRd` (OnBytes/TypedOracleCompiler/StringsRead.lean: 164 alone)
   exactly if it passes `ok2` (OnBytes/TypedOracleCompiler/StringsBoth.lean: both numbers) with the number 164, and
   then the two readers read the same; `ok2_tag164`;
 - `call2_of_okRd`: there the map `call2` gives the sibling's `leafCall` at any spellings whose
   spelling of a leaf is `rdOk`;
 - `cX`: a total code of all stored symbols, from the library's serialisers: so `embX a salt cX` has
   no free datum but the depth and the salt's length;
 - `okA`: the narrower test: `ok2`, and the number is 164 or the body is read as a stored symbol.
   `ok2` alone passes every label under 174, also one that is no string of the stored symbols' code;
   the general form spells a body that is no stored symbol under 164, so its condition on such
   bodies fails at `pBody ok2`;
 - `ownB`: the spelling of a prover's own leaf's body; `ownB_eq_rdOk`: it is `rdOk`;
 - `pBodyA_tag`, `pBodyA_stored`, `pBodyA_own`: the three conditions of `LeafD` in its own letters;
 - `bodyS a salt`, `leafS D`: the sibling's `BodyD` and `LeafD` at strings of bits;
 - `okA_ownB_embTail`, `Stretches.okA_ownB_embS`: a prover's symbol's body passes `okA`, and `ownB`
   gives its leaf's spelling, under the conditions on the trees and the salt of
   OnBytes/TypedOracleCompiler/StringsBounds.lean; `embTail_take164`, `Stretches.embS_take164`: it begins with the
   16 bits of 164; `leafOK2_embTail`: for a page made by hand over `pBody ok2`.

Main definitions: `cX`, `okA`, `ownB`, `bodyS`, `leafS`.
Main theorems: `ok2_tag164`, `okRd_of_ok2`, `ok2_of_okRd`, `call2_of_okRd`, `ownB_eq_rdOk`,
`pBodyA_tag`, `pBodyA_stored`, `pBodyA_own`, `okA_ownB_of`, `okA_ownB_embTail`, `embTail_take164`,
`leafOK2_embTail`, `Stretches.okA_ownB_embS`, `Stretches.embS_take164`.

Not claimed. Nothing of what the general form does with these data is said here: no page, no family
of oracle functions, no fit is stated at strings; OnBytes/TypedOracleCompiler/StringsOwn.lean shows what the general
form asks besides of the bodies of the chain's own symbols (`OwnFits`). The general form's page
takes its own test on body and salt (`leafOKX`: by `getE`) and its own map of leaves (`leafX`), NOT
`leafOK2` and `call2`: `leafOK2_embTail`, like `storedIn` and `fitX_leaf`, is for a page made by
hand over `pBody ok2`. By hand, no statement: `leafOK2` and `leafOKX` at `bodyS` agree on every body
that passes `okA`, and differ on a body that begins with the 16 bits of 174 or the escape and is
read as no stored symbol (the start is asked; nothing is asked); `call2` and `leafX` at `bodyS` give
one call at every query that the page writes, and differ elsewhere: at a wrong start, at a body
behind the escape, at a label under 174 that is no stored symbol's. At a body under 174 `call2` and
`leafCall` at `rdOk` differ (a call; none): `call2_of_okRd` is for bodies under 164 alone. That the
description's depth and salt are those of a key's or an entry's stored table is the description's
matter. In `okA_ownB_embTail` the prover's salt and the stored table's depth and salt are
independent parameters. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsStoredAt
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.TypedOracleCompiler.Run.SerTie

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open Rom
open _root_.Iop (Ser)
open _root_.Run (t164 bytesToBits PCode)
open TypedOracleCompiler.Run (t174 pStored)

/-! ## The two readers agree under 164 -/

/-- A body that passes `ok2` with the number 164 begins with the 16 bits of 164. -/
theorem ok2_tag164 {b : List Bool} (h : ok2 b = true) (hn : (rd2 b).1 = 164) :
    16 ≤ b.length ∧ b.take 16 = t164 := by
  obtain ⟨-, -, he⟩ := (ok2_iff b).1 h
  have ht := spell2_take (rd2 b).1 (rd2 b).2
  rw [← he] at ht
  exact ⟨ht.1, by rw [ht.2, hn]; rfl⟩

/-- A body that passes `ok2` with the number 164 passes `okRd`, and the reader behind that test
reads from it what `rd2` reads behind the number. -/
theorem okRd_of_ok2 {b : List Bool} (h : ok2 b = true) (hn : (rd2 b).1 = 164) :
    okRd b = true ∧ rdOk b = some (rd2 b).2 := by
  obtain ⟨-, -, he⟩ := (ok2_iff b).1 h
  rw [hn] at he
  have hb : b = spell ((rd2 b).2.1, (rd2 b).2.2.1, (rd2 b).2.2.2) := he
  have hw : (_root_.Fmt.wordAt (_root_.Run.bitsToBytes (b.take 64)) 0).toNat < 2 ^ 64 :=
    UInt64.toNat_lt _
  have hn' : (_root_.Fmt.wordAt (_root_.Run.bitsToBytes (b.take 64)) 0).toNat % 65536 = 164 := hn
  have ht : 164 + 65536 * (rd2 b).2.1 < 2 ^ 64 := by
    show 164 + 65536 *
      ((_root_.Fmt.wordAt (_root_.Run.bitsToBytes (b.take 64)) 0).toNat / 65536) < 2 ^ 64
    omega
  have hi : (rd2 b).2.2.1 < 2 ^ 64 := UInt64.toNat_lt _
  have hk : ok164 b = true := by
    unfold ok164
    simp [(ok2_tag164 h hn).1, (ok2_tag164 h hn).2]
  have ho := okRd_of_fit _ _ _ hb hk ht hi
  refine ⟨ho, ?_⟩
  rw [rdOk_of ho]
  conv_lhs => rw [hb]
  exact rd_spell _ _ _ ht hi

/-- A body that passes `okRd` passes `ok2` with the number 164. -/
theorem ok2_of_okRd {b : List Bool} (h : okRd b = true) : ok2 b = true ∧ (rd2 b).1 = 164 := by
  obtain ⟨z, hz, hm⟩ := pBodyR_fit b b (if_pos h)
  rw [rdOk_of h] at hz
  have hw : (_root_.Fmt.wordAt (_root_.Run.bitsToBytes (b.take 64)) 0).toNat < 2 ^ 64 :=
    UInt64.toNat_lt _
  have e1 : z.1 =
      ((_root_.Fmt.wordAt (_root_.Run.bitsToBytes (b.take 64)) 0).toNat - 164) / 65536 :=
    (congrArg (·.1) (Option.some.inj hz)).symm
  have e2 : z.2.1 =
      (_root_.Fmt.wordAt (_root_.Run.bitsToBytes ((b.drop 64).take 64)) 0).toNat :=
    (congrArg (·.2.1) (Option.some.inj hz)).symm
  have ht : 164 + 65536 * z.1 < 2 ^ 64 := by rw [e1]; omega
  have hi : z.2.1 < 2 ^ 64 := by rw [e2]; exact UInt64.toNat_lt _
  have hr := ok2_rd2_of_spell z.1 z.2.1 z.2.2 (show b = spell (z.1, z.2.1, z.2.2) from hm) ht hi
  exact ⟨hr.1, congrArg (·.1) hr.2⟩

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X)

/-- Where the body passes `okRd`, the map `call2` gives the sibling's `leafCall`, at any
spellings whose spelling of a leaf is `rdOk`. (A prover's symbol's body passes `okRd` under the
conditions of OnBytes/TypedOracleCompiler/StringsBounds.lean.) -/
theorem call2_of_okRd {tg : _root_.Compile.Tag} (D : TypedOracleCompiler.Run.PageD (strung L) tg)
    (hD : D.leaf = rdOk) (q : Compile.Batch.LeafIn (strung L)) (h : okRd q.body = true) :
    call2 L q = TypedOracleCompiler.Run.leafCall D q := by
  obtain ⟨h2, hn⟩ := ok2_of_okRd h
  have hr := (okRd_of_ok2 h2 hn).2
  unfold call2 TypedOracleCompiler.Run.leafCall
  rw [if_pos h2, hD, hr, hn]
  rfl

/-! ## The total code behind the escape, closed -/

/-- A total code of all stored symbols (position, column), from the library's serialisers; the
position by the library's code of large numbers (`Ser.natG`), not in unary. -/
def cX : StrCode (ℕ × List UInt64) := (Ser.prod Ser.natG (Ser.list _root_.Run.PQ.serW)).toStrCode

/-! ## The narrower test: under 174 only what is a stored symbol's body -/

/- a: the stored table's depth; salt: the length of a file's salt, in bytes -/
variable (a salt : ℕ)

/-- The test: `ok2`, and the number is 164 or the body is read as a stored symbol. -/
def okA (b : List Bool) : Bool :=
  ok2 b && (decide ((rd2 b).1 = 164) || (prjX a salt cX b).isSome)

theorem okA_iff (b : List Bool) : okA a salt b = true ↔
    ok2 b = true ∧ ((rd2 b).1 = 164 ∨ (prjX a salt cX b).isSome = true) := by
  unfold okA
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff]

/-- The spelling of a body of a prover's own leaf: what `rd2` reads behind the number 164 from a
body that passes `ok2`; of any other body none. -/
def ownB (b : List Bool) : Option (ℕ × ℕ × ByteArray) :=
  if ok2 b = true ∧ (rd2 b).1 = 164 then some (rd2 b).2 else none

/-- `ownB` is `rdOk`, the reader behind the test of OnBytes/TypedOracleCompiler/StringsRead.lean. -/
theorem ownB_eq_rdOk : ownB = rdOk := by
  funext b
  by_cases h : okRd b = true
  · obtain ⟨h2, hn⟩ := ok2_of_okRd h
    exact (if_pos ⟨h2, hn⟩).trans (okRd_of_ok2 h2 hn).2.symm
  · have hn : ¬ (ok2 b = true ∧ (rd2 b).1 = 164) := fun x => h (okRd_of_ok2 x.1 x.2).1
    exact (if_neg hn).trans (if_neg h).symm

/-- What the identity on the bodies that pass `okA` writes begins with the 16 bits of 164 or of 174.
-/
theorem pBodyA_tag (y m : List Bool) (h : (pBody (okA a salt)).put y = some m) :
    16 ≤ m.length ∧ (m.take 16 = t164 ∨ m.take 16 = t174) := by
  have h0 : (if okA a salt y then some y else none) = some m := h
  by_cases hy : okA a salt y = true
  · rw [if_pos hy] at h0
    cases h0
    exact pBody2_tag y y (if_pos ((okA_iff a salt y).1 hy).1)
  · rw [if_neg hy] at h0
    cases h0

/-- On a stored symbol's body it writes what the stored symbols' code writes, and nothing where
that code writes nothing. -/
theorem pBodyA_stored (y : ℕ × List UInt64) :
    (pBody (okA a salt)).put (embX a salt cX y) = (pStored a salt).put y := by
  rw [← put_embX a salt cX y]
  show (if okA a salt (embX a salt cX y) then some (embX a salt cX y) else none) =
    (if ok2 (embX a salt cX y) then some (embX a salt cX y) else none)
  have e : okA a salt (embX a salt cX y) = ok2 (embX a salt cX y) := by
    unfold okA
    rw [prjX_embX a salt cX y]
    simp
  rw [e]

/-- On a body that is read as no stored symbol, what it writes is the bits of the label under 164
and of the bytes that `ownB` gives. -/
theorem pBodyA_own (b m : List Bool) (hg : prjX a salt cX b = none)
    (h : (pBody (okA a salt)).put b = some m) :
    ∃ z, ownB b = some z ∧
      m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2 := by
  have h0 : (if okA a salt b then some b else none) = some m := h
  by_cases hy : okA a salt b = true
  · rw [if_pos hy] at h0
    cases h0
    obtain ⟨h2, hn⟩ := (okA_iff a salt b).1 hy
    have hn' : (rd2 b).1 = 164 := by
      rcases hn with hn | hn
      · exact hn
      · rw [hg] at hn
        cases hn
    obtain ⟨-, -, he⟩ := (ok2_iff b).1 h2
    rw [hn'] at he
    exact ⟨(rd2 b).2, if_pos ⟨h2, hn'⟩, he⟩
  · rw [if_neg hy] at h0
    cases h0

/-- A body that passes `ok2` with the number 164 passes `okA`, and `ownB` gives what `rd2` reads. -/
theorem okA_ownB_of {b : List Bool} (z : ℕ × ℕ × ByteArray) (h : ok2 b = true ∧ rd2 b = (164, z)) :
    okA a salt b = true ∧ ownB b = some z := by
  have hn : (rd2 b).1 = 164 := congrArg (·.1) h.2
  have hz : (rd2 b).2 = z := congrArg (·.2) h.2
  exact ⟨(okA_iff a salt b).2 ⟨h.1, Or.inl hn⟩, (if_pos ⟨h.1, hn⟩).trans (congrArg some hz)⟩

end TypedOracleCompiler.Strings

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Strings

/-- The bodies' data at strings of bits: a stored symbol lies among the bodies as `embX`, read
back by `prjX`; a prover's own leaf's body is spelled by `ownB`. a: the stored table's depth; salt:
the length of a file's salt, in bytes. -/
def bodyS (a salt : ℕ) : BodyD (List Bool) where
  embE := Strings.embX a salt cX
  getE := Strings.prjX a salt cX
  get_e := Strings.prjX_embX a salt cX
  e_get := fun b y h =>
    (((TypedOracleCompiler.Run.pStored a salt).orElse cX esc16 (stored_no_esc a salt)).put_parse b y h).symm
  own := ownB

/-- The page's one code of bodies at strings of bits, at a description: the identity on the
bodies that pass `okA` at the description's depth and salt. The serialiser of bodies, which a page's
total code uses behind the escape alone, is `serTie` (OnBytes/TypedOracleCompiler/Run/SerTie.lean): it writes a
stored symbol's body as the library's serialiser of tagged bodies writes the stored symbol, and any
other body by its bits. -/
def leafS (D : XD) : LeafD D (bodyS D.a D.base.plan.salt) where
  p := pBody (okA D.a D.base.plan.salt)
  tag := pBodyA_tag D.a D.base.plan.salt
  stored := pBodyA_stored D.a D.base.plan.salt
  own := pBodyA_own D.a D.base.plan.salt
  ser := serTie (bodyS D.a D.base.plan.salt)
    (_root_.Iop.Ser.prod _root_.Iop.Ser.natG (_root_.Iop.Ser.list _root_.Run.PQ.serW))
    _root_.Compile.serBits

end TypedOracleCompiler.Run.PQ

namespace TypedOracleCompiler.Slice
open _root_.Iop (OPos OSym)
open _root_.Run (t164)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings

variable (salt : ℕ) (C : PQ.CK)

/-- A prover's symbol's body passes `okA`, at every depth and salt of the stored table, and `ownB`
gives the sibling's own spelling of its leaf, in one list of rounds, under the conditions on the
trees and the salt. -/
theorem okA_ownB_embTail (a' salt' : ℕ) (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) :
    okA a' salt' (embTail salt C ds p a) = true ∧
      ownB (embTail salt C ds p a) = some (PQ.leafSL C salt ds ⟨p, a⟩) :=
  okA_ownB_of a' salt' _ (ok2_rd2_embTail salt C h8 ds h p a)

/-- Such a body begins with the 16 bits of 164. -/
theorem embTail_take164 (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) :
    (embTail salt C ds p a).take 16 = t164 :=
  (ok2_tag164 (ok2_rd2_embTail salt C h8 ds h p a).1
    (congrArg (·.1) (ok2_rd2_embTail salt C h8 ds h p a).2)).2

/-- So the test `leafOK2` (OnBytes/TypedOracleCompiler/StringsStoredAt.lean; for a page made by hand over
`pBody ok2`, not for the general form's) asks nothing of a leaf query on it, whatever the salt. -/
theorem leafOK2_embTail {I X : Type} (L : _root_.Iop.BatchProtocol I X) (cfg : ByteArray)
    (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds) (p : OPos (PQ.uL C ds))
    (a : OSym (PQ.uL C ds) p) (s : List Bool) :
    leafOK2 L cfg ⟨embTail salt C ds p a, s⟩ = true :=
  leafOK2_own L cfg _ (embTail_take164 salt C h8 ds h p a)

/-- The same two at the protocol in three stretches. -/
theorem Stretches.okA_ownB_embS (G : Stretches) (a' salt' : ℕ) (h8 : salt / 8 < 2 ^ 8)
    (h : G.Small) (p : OPos G.sh) (a : OSym G.sh p) :
    okA a' salt' (G.embS salt p a) = true ∧ ownB (G.embS salt p a) = some (G.leafS salt p a) :=
  okA_ownB_of a' salt' _ (G.ok2_rd2_embS salt h8 h p a)

theorem Stretches.embS_take164 (G : Stretches) (h8 : salt / 8 < 2 ^ 8) (h : G.Small)
    (p : OPos G.sh) (a : OSym G.sh p) : (G.embS salt p a).take 16 = t164 :=
  (ok2_tag164 (G.ok2_rd2_embS salt h8 h p a).1
    (congrArg (·.1) (G.ok2_rd2_embS salt h8 h p a).2)).2

end TypedOracleCompiler.Slice
