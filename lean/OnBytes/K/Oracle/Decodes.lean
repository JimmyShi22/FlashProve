-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/Decodes.lean: A GUARD AGAINST EMPTINESS for the entry file's language: the decoder
with a record does decode, and the language is neither everything nor nothing.

Why. `EntryArmO.sound` and `EntryArm.sound` (OnBytes/K/Oracle/ArmO.lean, OnBytes/K/Left/Arm.lean)
bound the chance that a checker returns a value while the entry's language (`DecR.LangE`,
OnBytes/Slice/DecoderRec.lean) fails. That language holds for free where the first string does not
decode with its record, or where the record does not single one table out. If no string decoded with
any record, it would hold of everything, and the bound would be empty. So here the format's
encoder's tables are shown to decode for the decoder with a record, of which the two statements
speak.

 `dcd_words`, `not_coll_words` at any decoder with a record whose radius is below the code's
     distance: a table of code words, with the answers of its own message parts at any seed, decodes
     to these message parts (the library's `Cb.ood_decMinS_mulVec`), and the record singles it out:
     within the radius of a table of code words lies that table alone.
 `honestRaw`, `honestRec`, `honest_decodes` the same of the raw string of a table that the format's
     encoder makes (`honestTab`, OnBytes/Slice/Honest.lean), whatever its messages, tails and seed.
 `honest_lang` of two such tables with the same messages the language holds BY ITS LAST CLAUSE,
     whatever their tails and seeds.
 `honest_not_lang`   of two such tables whose messages differ at an entry before the pads it FAILS.
 `Guard`, `guard_of`, `guard_full`, `guard_small` the three facts as one statement, at the decoder
     of the full size and of the small example: the very terms `decRec z.T z.v z.eM z.lg z.s` of the
     two statements.

What is not claimed. These are strings and records written down here: NOTHING SAYS THAT A CHECKER
RETURNS A VALUE ON ANY FILES, under the format's hash or under a drawn oracle; nothing says that a
string read off a maker's log is one of these; nothing ties these strings to a file's bytes or to a
Merkle root. The seed in a record is any seed here: that it is the seed which the oracle gives at
the table's name is not asked. No probability. The radius is below the code's DISTANCE, not below
half of it: for strings that are no tables of code words several tables can lie within the radius,
and nothing is said of them here. Nothing on an honest prover's run. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.Honest
import OnBytes.Slice.DecoderRecTyped
import OnBytes.Slice.LinkAtRec
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.FullRecLink
import OnBytes.Slice.SmallRecLink
import OnBytes.TypedOracleCompiler.Slice.ShapesAtFull
import OnBytes.TypedOracleCompiler.Slice.ShapesAtSmall
import Cb.Gen.OodDecMinProofs

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Cb Cb.Ood Blocks OnBytes.Slice

/-! ## A table of code words, at any decoder with a record -/

section
variable (D : DecR) {d : ℕ}

/-- **A table of code words decodes with its own record, at every seed**, if the radius is below
the code's distance: with the answers of its own message parts at the seed ρ the decoder returns
these message parts. -/
theorem dcd_words (hd : HasDist D.ix.G d) (he : D.eM < d) (f : D.toDec.Pos → Run.PQ.SgX)
    (M : D.ix.Row → D.toDec.Co → GE) (hf : ∀ r x, D.tab f r x = D.ix.G.mulVec (M r) x)
    (ρ : D.Z.D) :
    D.dcd f (ρ, D.ix.ZR.val ρ (D.ix.view M)) = some (D.ix.view M) := by
  have e : D.tab f = fun a => D.ix.G.mulVec (M a) := funext fun r => funext fun x => hf r x
  unfold DecR.dcd LdIx.dec
  rw [e]
  exact ood_decMinS_mulVec _ _ _ _ _ D.ix.G d D.eM D.ix.rank D.ix.view D.ix.ZR M hd he ρ

/-- **And its record singles it out, at every seed**: within the radius of a table of code words
lies that table alone. -/
theorem not_coll_words (hd : HasDist D.ix.G d) (he : D.eM < d) (f : D.toDec.Pos → Run.PQ.SgX)
    (M : D.ix.Row → D.toDec.Co → GE) (hf : ∀ r x, D.tab f r x = D.ix.G.mulVec (M r) x)
    (ρ : D.Z.D) : ¬ D.coll f ρ := by
  have e : D.tab f = fun a => D.ix.G.mulVec (M a) := funext fun r => funext fun x => hf r x
  unfold DecR.coll LdIx.Coll ClashS Clash
  rw [e]
  rintro ⟨u, u', ⟨M₁, h₁, rfl⟩, ⟨M₂, h₂, rfl⟩, hne, -⟩
  have a : ∀ M', DecodesTo D.ix.G D.eM (fun a => D.ix.G.mulVec (M a)) M' → M' = M := fun M' h =>
    funext fun _ => DecodesTo.row_unique hd (by omega : D.eM + 0 < d) h
      (decodesTo_mulVec D.ix.G 0 M) rfl
  exact hne (by rw [a M₁ h₁, a M₂ h₂])

end

/-! ## The table that the format's encoder makes, at the link's sizes -/

section
variable (S : Sz) (lg s : ℕ) {d : ℕ}

/-- The record of the table that the format's encoder makes of the messages msg, at the seed ρ: the
seed, and the answers of these messages. -/
def honestRec (msg : ℕ → List UInt64) (ρ : (decRec S.P.T S.P.v S.eM lg s).Z.D) :
    (decRec S.P.T S.P.v S.eM lg s).Rec :=
  (ρ, (decRec S.P.T S.P.v S.eM lg s).ix.ZR.val ρ (honestMsgs S msg))

/-- The raw string of that table. -/
def honestRaw (msg tl : ℕ → List UInt64) : Raw Run.PQ.SgX :=
  rawOf (Equiv.refl _) (honestTab S msg tl)

/-- **THE GUARD: THE DECODER WITH A RECORD DOES DECODE.** The raw string of a table that the
format's encoder makes, whatever its messages and tails, with the record of its own answers at any
seed: it decodes to its messages, and the record singles it out. -/
theorem honest_decodes (hd : HasDist S.ix.G d) (he : S.eM < d) (msg tl : ℕ → List UInt64)
    (ρ : (decRec S.P.T S.P.v S.eM lg s).Z.D) :
    (decRec S.P.T S.P.v S.eM lg s).dcdRaw (honestRaw S msg tl) (honestRec S lg s msg ρ) =
        some (honestMsgs S msg) ∧
      ¬ (decRec S.P.T S.P.v S.eM lg s).collRaw (honestRaw S msg tl) ρ := by
  unfold honestRaw honestRec
  rw [(decRec S.P.T S.P.v S.eM lg s).dcdRaw_rawOf (Equiv.refl _) rfl,
    (decRec S.P.T S.P.v S.eM lg s).collRaw_rawOf (Equiv.refl _) rfl, ← view_honestPolys S msg tl]
  exact ⟨dcd_words (decRec S.P.T S.P.v S.eM lg s) hd he _ (honestPolys S msg tl)
      (tab_honestTab S msg tl) ρ,
    not_coll_words (decRec S.P.T S.P.v S.eM lg s) hd he _ (honestPolys S msg tl)
      (tab_honestTab S msg tl) ρ⟩

/-- **The entry's language holds of two such tables with the same messages, BY ITS LAST CLAUSE**:
whatever their tails and their seeds. -/
theorem honest_lang (hd : HasDist S.ix.G d) (he : S.eM < d) (msg tl₀ tl₁ : ℕ → List UInt64)
    (ρ₀ ρ₁ : (decRec S.P.T S.P.v S.eM lg s).Z.D) :
    ∃ u₀ u₁, (decRec S.P.T S.P.v S.eM lg s).dcdRaw (honestRaw S msg tl₀)
        (honestRec S lg s msg ρ₀) = some u₀ ∧
      (decRec S.P.T S.P.v S.eM lg s).dcdRaw (honestRaw S msg tl₁) (honestRec S lg s msg ρ₁) =
        some u₁ ∧ (decRec S.P.T S.P.v S.eM lg s).Agree u₁ u₀ ∧
      ¬ DecR.wayColl (decRec S.P.T S.P.v S.eM lg s) (honestRaw S msg tl₁) ρ₁ :=
  ⟨_, _, (honest_decodes S lg s hd he msg tl₀ ρ₀).1, (honest_decodes S lg s hd he msg tl₁ ρ₁).1,
    fun _ _ _ => rfl, (honest_decodes S lg s hd he msg tl₁ ρ₁).2⟩

/-- **AND IT FAILS OF TWO SUCH TABLES WHOSE MESSAGES DIFFER BEFORE THE PADS**: so the language is
not everything. -/
theorem honest_not_lang (hd : HasDist S.ix.G d) (he : S.eM < d)
    (msg₀ msg₁ tl₀ tl₁ : ℕ → List UInt64) (ρ₀ ρ₁ : (decRec S.P.T S.P.v S.eM lg s).Z.D)
    (hne : ∃ (r : S.ix.Row) (j : S.En), j.val < S.P.T.l - 3 * s ∧
      honestMsgs S msg₁ (r, j) ≠ honestMsgs S msg₀ (r, j)) :
    ¬ DecR.LangE (DecR.wayColl (decRec S.P.T S.P.v S.eM lg s)) (honestRec S lg s msg₀ ρ₀)
      (honestRec S lg s msg₁ ρ₁) (honestRaw S msg₀ tl₀) (honestRaw S msg₁ tl₁) := by
  obtain ⟨r, j, hj, hn⟩ := hne
  obtain ⟨a0, b0⟩ := honest_decodes S lg s hd he msg₀ tl₀ ρ₀
  obtain ⟨a1, -⟩ := honest_decodes S lg s hd he msg₁ tl₁ ρ₁
  rintro (h | h | ⟨u₀, u₁, h0, h1, hA, -⟩)
  · rw [a0] at h
    cases h
  · exact b0 h
  · rw [a0] at h0
    rw [a1] at h1
    obtain rfl := Option.some.inj h0
    obtain rfl := Option.some.inj h1
    exact hn (hA r j hj)

end

/-! ## The guard, and the two sizes -/

/-- **THE GUARD AGAINST AN EMPTY LANGUAGE**, of a decoder with a record: there are a raw string that
decodes with a record which singles one table out; a second string and record with which the
entry's language holds of the pair (so: by its last clause); and a third with which it fails. -/
def Guard (D : DecR) : Prop :=
  ∃ (y₀ y₁ y₂ : Raw Run.PQ.SgX) (rec₀ rec₁ rec₂ : D.Rec),
    (∃ u₀, D.dcdRaw y₀ rec₀ = some u₀) ∧ ¬ D.collRaw y₀ rec₀.1 ∧
      D.LangE (DecR.wayColl D) rec₀ rec₁ y₀ y₁ ∧ ¬ D.LangE (DecR.wayColl D) rec₀ rec₂ y₀ y₂

/-- The guard at the link's sizes, where the radius is below the code's distance and a row's message
has an entry before its pads. -/
theorem guard_of (S : Sz) (lg s : ℕ) {d : ℕ} (hd : HasDist S.ix.G d) (he : S.eM < d)
    (hl : 0 < S.P.T.l - 3 * s) : Guard (decRec S.P.T S.P.v S.eM lg s) := by
  let ρ : (decRec S.P.T S.P.v S.eM lg s).Z.D := fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)
  refine ⟨honestRaw S (fun _ => []) (fun _ => []), honestRaw S (fun _ => []) (fun _ => [1]),
    honestRaw S (fun _ => [1]) (fun _ => []), honestRec S lg s (fun _ => []) ρ,
    honestRec S lg s (fun _ => []) ρ, honestRec S lg s (fun _ => [1]) ρ,
    ⟨_, (honest_decodes S lg s hd he _ _ ρ).1⟩, (honest_decodes S lg s hd he _ _ ρ).2,
    Or.inr (Or.inr (honest_lang S lg s hd he _ _ _ ρ ρ)),
    honest_not_lang S lg s hd he _ _ _ _ ρ ρ ⟨fun _ => false, ⟨0, by omega⟩, hl, ?_⟩⟩
  show algebraMap GF GE (toF 1) ≠ algebraMap GF GE (toF 0)
  rw [toF_one, toF_zero, map_one, map_zero]
  exact one_ne_zero

open OnBytes.Slice.Shapes (zFull zSmall zFull_lg zSmall_lg) in
/-- **The guard at the full size's decoder with a record**: the decoder of which `EntryArmO.sound`
and `EntryArm.sound` speak there. -/
theorem guard_full : Guard (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s) := by
  have e : decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s =
      decRec frS.P.T frS.P.v frS.eM 29 1 :=
    congrArg (fun n => decRec zFull.T zFull.v zFull.eM n zFull.s) zFull_lg
  rw [e]
  exact guard_of frS 29 1 (hasDist_genOf frS.P.T (by decide) (by decide)) (by decide) (by decide)

open OnBytes.Slice.Shapes (zFull zSmall zFull_lg zSmall_lg) in
/-- **The guard at the small example's decoder with a record.** -/
theorem guard_small : Guard (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s) := by
  have e : decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s =
      decRec srS.P.T srS.P.v srS.eM 19 1 :=
    congrArg (fun n => decRec zSmall.T zSmall.v zSmall.eM n zSmall.s) zSmall_lg
  rw [e]
  exact guard_of srS 19 1 (hasDist_genOf srS.P.T (by decide) (by decide)) (by decide) (by decide)

end OnBytes.K.Oracle
