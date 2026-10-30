-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryClean.lean: an entry's part with the page of OnBytes/TypedOracleCompiler/Slice/EntryFill.lean
as its implementation; and three of the clauses that OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean's
`FileDebts` asks of it: `one`, `blocks`, and `clean` WHOLE: no typed query of the judge's run has a
public string, if every public string is a call under 169 with a start of 32 bytes.

`EntryAt` (OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean) holds what an entry's part is made of, as letters.
`atPage` fills three of them: bodies are strings, answers are lists of triples, the implementation
is the page. `clean` has two halves: the judge's run never asks the spare oracle
(OnBytes/TypedOracleCompiler/Slice/JudgeNoOther.lean); the string of a call under 169 is the string of no typed
query but the spare oracle's (`EntryFill.pageForE_call`). The sibling is a second form of the
library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `IsPublic s`: s is the bits of `Fmt.oStr` of a call under 169, either half, with a start of 32
   bytes;
 - `atPage`: the data of an entry's part at the page;
 - `atPage_one`, `atPage_blocks`: the clauses `one` and `blocks` (at D.K + 2);
 - `atPage_clean`: the clause `clean`, for any set of strings all of whose members are `IsPublic`.

Main definitions: `IsPublic`, `atPage`.
Main theorems: `atPage_one`, `atPage_blocks`, `atPage_clean`.

Not claimed. That a part's public strings are `IsPublic`: whoever gives the sets owes it. `reads`,
`flat`, the typing's clauses, soundness: nothing. The description, the two ways of writing symbols,
the decision, the reading, the roots, and the page's cfg, pd, `rest`, n and `back` stay arguments.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Slice.JudgeNoOther

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.EntryClean
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open OnBytes.Slice (seedEntry decRec GE)
open OnBytes.Slice.Shapes (Files)
open _root_.Run.PQ (View SgX)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open scoped ENNReal

/-- The bit string s is the string of a call under 169: either half, any tree number, any index, a
start of 32 bytes, any bytes. -/
def IsPublic (s : List Bool) : Prop :=
  ∃ (half : UInt8) (t i : ℕ) (st bs : ByteArray), (half = 0 ∨ half = 1) ∧ st.size = 32 ∧
    s = bytesToBits (_root_.Fmt.oStr half 169 t i st bs)

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s} (D : XD) (B : BodyD (List Bool))
  (E : OwnE (List Bool) D) (dec : XE (List T3) lg s → View → Bool)
  (R : Reading (Ls D d₁) B.embE) (rts : Files → List (Dig 256))
  (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)))

/-- The data of an entry's part at the page: bodies are strings, answers are lists of triples,
the implementation is `EntryFill.pageForE`. -/
def atPage : EntryAt (List T3) lg s d₁ :=
  ⟨D, List Bool, B, E, dec, R, pageForE D d₁ cfg hcfg pd rest n back, rts⟩

variable (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : List T3 → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) (εs : ℝ≥0∞)

/-- The clause `one`. -/
theorem atPage_one :
    OneBlock ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).m :=
  pageForE_one D d₁ cfg hcfg pd rest n back

/-- The clause `blocks`, at D.K + 2. -/
theorem atPage_blocks (o : TypedOracleCompiler.Compile.Batch.OracleName) :
    ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).m.blocks o ≤ D.K + 2 :=
  pageForE_blocks D d₁ cfg hcfg pd rest n back o

/-- The clause `clean`: no typed query of the judge's run has a string in a set all of whose
members are calls under 169 with a start of 32 bytes. -/
theorem atPage_clean (P : Finset (List Bool)) (hP : ∀ t ∈ P, IsPublic t)
    (F : Fam (typedOracleFamily 256 ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).W.K
      ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).L))
    (o : ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).Out) :
    ∀ e ∈ ((((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).J.run
        o).withTrace.det F).2,
      ∀ j, ((atPage D B E dec R rts cfg hcfg pd rest n back).base T v eM an εs).m.code e.1 e.2.1
        j ∉ P := by
  intro e he j hm
  obtain ⟨half, t, i, st, bs, hh, hst, hs⟩ := hP _ hm
  have hne : e.1 ≠ TypedOracleCompiler.Compile.Batch.OracleName.other := judgeRunEL_log_ne _ _ _ _ _ _ _ _ o F e he
  exact (pageForE_call D d₁ cfg hcfg pd rest n back 169 KeyPage.notSix_spare.1 half hh t i st bs
    hst).2 e.1 hne e.2.1 j hs

end TypedOracleCompiler.Slice.EntryClean
