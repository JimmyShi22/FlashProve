-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryData.lean: three letters of the entry's part as definitions, general in the
sizes and in the description: the type of a table's answers in an instance and how they are read;
the reading of the string under a root; and what follows of the entry's part at them: the clause
`reads` from what a page spells, what the judge asks of an output beside the run's yes, and the
clause `flat`.

Main definitions.
 `AnsT`, `anT v s`      a table's answers in an instance: a list of triples of words; read as the
                        decoder's answers in the order of `recAns` (OnBytes/Slice/RecordRead.lean).
 `entryR`, `EntryAt.Rw` THE ENTRY'S READING: at each place the stored symbol in the body of the leaf
                        found there, whatever the salt; (0, no word) where nothing is found: the
                        sibling's `Reading.wide` at the entry's wire
                        (OnBytes/TypedOracleCompiler/Slice/EntryX.lean).
 `entryB`               the entry's bound as one expression in the error, the typing's strings, the
                        blocks of an answer, the judge's typed queries and the maker's queries.
Main theorems.
 `recAns_anT`           the answers that stand in a key are `anT` of the key's answers as triples.
 `entryR_byLeaves`, `entryR_keeps`, `rawOf_build`   the reading goes by leaves; it keeps every
                        opening; what it builds is `mkZ` (OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean).
 `EntryAt.byWalks`, `EntryAt.reads`   THE CLAUSE `reads` FROM WHAT A PAGE SPELLS: at that reading
                        the part reads by the walks of the look through its page; so, if the page
                        meets `Spells` (OnBytes/TypedOracleCompiler/Slice/ShapesReads.lean) at a digest c of 32
                        bytes, the stored tables' depth and salts of n bytes, it reads `rawBy c a n`
                        off every log in which no two strings have one answer.
 `EntryAt.plainRead`    the part reads plainly at that depth (`PlainRead`,
                        OnBytes/TypedOracleCompiler/Slice/ShapesReadsPart.lean): so the general
                        `FileSpec.reads_of_spells` applies; `EntryAt.reads` is its like for one
                        part, shown by itself.
 `EntryAt.ok_iff`       at that reading the judge asks of an output, beside the run's yes, two roots
                        and nothing more.
 `entry_flat`, `EntryAt.tV_eq`   THE CLAUSE `flat`: if at all tables the judge has V typed queries,
                        the bound is `entryB` at all tables; that number hangs on the description's
                        shape and wiring alone.

The field `wiring` of `EntryDebts` (OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean) follows from two
conditions on a description: no round asks more than 64 bits of work; the limits `okX` on the stored
tables' openings: `wq0_okg` (EntryX.lean).

Not claimed. NO PAGE, NO DESCRIPTION, NO TYPING IS GIVEN: `Spells`, one block for a leaf's and a
vertex's answer, and that the part's reading is this one are hypotheses. `recAns_anT` speaks of a
key alone: that what a checker returns holds a key's answers is not said. That the judge's number of
typed queries is one number at all tables: a hypothesis; it is evaluated at no description. No
number is evaluated. NOTHING ON SOUNDNESS IS SHOWN. What the heads of EntryDelivers.lean,
ShapesReads.lean and ShapesRaw.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ThreeDelivers
import OnBytes.TypedOracleCompiler.Slice.ShapesReadsPart
import OnBytes.TypedOracleCompiler.Slice.ByWalks

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open _root_.Run.PQ (View SgX)
open OnBytes.Slice (DecR decRec GE NZ seedEntry Tab NoClash Raw rawOf recAns toE readE)
open OnBytes.Slice.Shapes (Files FileSpec)
open scoped ENNReal

/-! ## The answers -/

/-- A table's answers as they stand in an instance: a list of triples of words. -/
abbrev AnsT : Type := List (UInt64 × UInt64 × UInt64)

/-- How a table's answers in an instance are read as the decoder's answers: entry r * s + i is
the answer of row r under seed i, read in the extension field; 0 beyond the end. The order is that
of `recAns` (OnBytes/Slice/RecordRead.lean). -/
def anT (v s : ℕ) (l : AnsT) : (Fin v → Bool) × Fin s → GE :=
  fun x => toE (l.getD (OnBytes.Slice.Sz.rowNo x.1 * s + x.2.val) (0, 0, 0))

/-- The answers that stand in a key are these, at the key's answers as triples. -/
theorem recAns_anT (v s : ℕ) (k : OnBytes.Tie.IdKey) (h : k.2.2.answers.length = 2 ^ v * s) :
    recAns v s k = some (anT v s (k.2.2.answers.map OnBytes.E.triple)) := by
  unfold recAns
  rw [if_pos h]
  congr 1
  funext x
  unfold anT
  rw [OnBytes.Slice.readE_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases k.2.2.answers[OnBytes.Slice.Sz.rowNo x.1 * s + x.2.val]? with
  | none => rfl
  | some e => rfl

/-! ## The reading -/

section
variable {X : Type} (D : XD) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (early : X → X)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX)) (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- THE ENTRY'S READING of the string under a root: at each place the stored symbol that
`B.getE` reads from the body of the leaf found there, whatever the salt; (0, no word) where nothing
is found. It is the sibling's own reading (`Reading.wide`, OnBytes/TypedOracleCompiler/Slice/Reading.lean) at the
entry's wire. -/
def entryR : Reading (LXE (Bd := Bd) D early T) B.embE :=
  Reading.wide (W := WXE D B E early T wT eT pT) (WireE.one_ok (2 ^ D.a) SgX (0, [])) B.get_e

/-- It goes by leaves. -/
theorem entryR_byLeaves :
    (entryR D B E early T wT eT pT).ByLeaves (keepAll (WXE D B E early T wT eT pT))
      fun φ => (WireE.one (2 ^ D.a) SgX (0, [])).build fun q => φ q.val :=
  Reading.wide_byLeaves (W := WXE D B E early T wT eT pT) (WireE.one_ok (2 ^ D.a) SgX (0, []))
    B.get_e

/-- It keeps every opening. -/
theorem entryR_keeps (p : Fin (2 ^ D.a)) (y : SgX) (salt : Bits) :
    (entryR D B E early T wT eT pT).keeps p y salt := trivial

end

/-- A raw string made of what the wire of one string builds is `mkZ`
(OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean). -/
theorem rawOf_build (a : ℕ) (φ : ℕ → Option SgX) :
    rawOf (Equiv.refl SgX) ((WireE.one (2 ^ a) SgX (0, [])).build fun q => φ q.val) =
      OnBytes.Slice.Shapes.mkZ a φ := by
  funext j
  unfold rawOf OnBytes.Slice.Shapes.mkZ
  by_cases h : j < 2 ^ a
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]

/-! ## At the entry's part -/

section
variable {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)

/-- The entry's reading, at the data of an entry's part. -/
def EntryAt.Rw (x : EntryAt An lg s d₁) :
    Reading (LXEs (An := An) (Bd := x.Bd) lg s x.D d₁) x.B.embE :=
  entryR x.D x.B x.E (earlyTwo d₁) (TSE x.D (seedEntry lg s)) (wTSE x.D (seedEntry lg s))
    (embST x.D.C (seedEntry lg s) _) (prjST x.D.C (seedEntry lg s) _)

/-- THE ENTRY'S PART, WITH THE ENTRY'S READING, READS BY THE WALKS OF THE LOOK THROUGH ITS PAGE,
in the perfect tree of the stored tables' depth, with `B.getE` of the leaf's body at every place and
(0, no word) where nothing is found: the hypothesis of `Spells.reads`
(OnBytes/TypedOracleCompiler/Slice/ShapesReads.lean). Asked: one block for a leaf's and a vertex's answer. -/
theorem EntryAt.byWalks (x : EntryAt An lg s d₁) (hR : x.R = x.Rw) (εs : ℝ≥0∞)
    (h1 : OneBlock x.m) :
    (x.base T v eM an εs).toO.ByWalks (lookOf x.m) (_root_.Compile.posOf x.D.a)
      (fun _ q => x.B.getE q.body) (OnBytes.Slice.Shapes.mkZ x.D.a) where
  raw_eq := fun σ cm => by
    have hB : (x.base T v eM an εs).J.R.ByLeaves
        (keepAll (WXE x.D x.B x.E (earlyTwo d₁) (TSE x.D (seedEntry lg s))
          (wTSE x.D (seedEntry lg s)) (embST x.D.C (seedEntry lg s) _)
          (prjST x.D.C (seedEntry lg s) _)))
        fun φ => (WireE.one (2 ^ x.D.a) SgX (0, [])).build fun q => φ q.val := by
      show x.R.ByLeaves _ _
      rw [hR]
      exact entryR_byLeaves x.D x.B x.E (earlyTwo d₁) _ _ _ _
    have h := (Part.toO_byWalks (x.base T v eM an εs) h1 hB).raw_eq σ cm
    rw [h]
    show rawOf (Equiv.refl SgX) ((WireE.one (2 ^ x.D.a) SgX (0, [])).build fun q => _) = _
    rw [← rawOf_build]
    congr 2
    funext q
    have key : ∀ w : Option (LeafIn (LXEs (An := An) (Bd := x.Bd) lg s x.D d₁)),
        Option.map (Equiv.refl SgX).symm
          (w.bind fun z => Option.map (Equiv.refl SgX) (x.B.getE z.body)) =
        w.bind fun z => x.B.getE z.body := by
      intro w
      cases w with
      | none => rfl
      | some z =>
        show Option.map _ (Option.map _ (x.B.getE z.body)) = x.B.getE z.body
        cases x.B.getE z.body <;> rfl
    exact key _

/-- THE CLAUSE `reads`, AT THE ENTRY'S READING, FROM WHAT A PAGE SPELLS: if the page spells
vertices and stored leaves as the one written reading reads them, at a digest c of 32 bytes, the
stored tables' depth and salts of n bytes (`Spells`), the entry's part reads `rawBy c a n` off every
log in which no two strings have one answer. -/
theorem EntryAt.reads (x : EntryAt An lg s d₁) (hR : x.R = x.Rw) (εs : ℝ≥0∞) (h1 : OneBlock x.m)
    (c : ByteArray) (hc : c.size = 32) (n : ℕ)
    (hS : OnBytes.Slice.Shapes.Spells x.m x.B.embE c x.D.a n) (σ : Trace (rom 256))
    (hσ : NoClash σ) (cm : Dig 256) :
    (x.base T v eM an εs).raw σ cm = OnBytes.Slice.Shapes.rawBy c x.D.a n σ cm :=
  hS.reads h1 ⟨x.B.get_e, x.B.e_get⟩ hc (x.byWalks T v eM an hR εs h1) σ hσ cm

/-- THE ENTRY'S PART, WITH THE ENTRY'S READING, READS PLAINLY AT THE STORED TABLES' DEPTH
(`PlainRead`, OnBytes/TypedOracleCompiler/Slice/ShapesReadsPart.lean): so the general form of the clause `reads`
(`FileSpec.reads_of_spells`, there) applies to it. -/
theorem EntryAt.plainRead (x : EntryAt An lg s d₁) (hR : x.R = x.Rw) (εs : ℝ≥0∞) :
    OnBytes.Slice.Shapes.PlainRead (x.base T v eM an εs) x.D.a where
  depth := rfl
  len := rfl
  fill := fun φ q => by
    show (φ q.val).getD (0, []) = ((φ q.val).map (Equiv.refl SgX)).getD (0, [])
    cases φ q.val <;> rfl
  byLeaves := by
    show x.R.ByLeaves _ _
    rw [hR]
    exact entryR_byLeaves x.D x.B x.E (earlyTwo d₁) _ _ _ _
  back := x.B.get_e
  only := x.B.e_get

/-- AT THE ENTRY'S READING THE JUDGE ASKS OF AN OUTPUT, BESIDE THE RUN'S YES, TWO ROOTS AND
NOTHING MORE: the reading keeps every opening. -/
theorem EntryAt.ok_iff (x : EntryAt An lg s d₁) (hR : x.R = x.Rw) (εs : ℝ≥0∞) (o : OutE x.Z) :
    (x.base T v eM an εs).J.ok o ↔ o.1.length = 2 := by
  constructor
  · exact fun h => h.1
  · refine fun h => ⟨h, fun p op _ => ?_⟩
    show x.R.keeps _ _ _
    rw [hR]
    trivial

/-! ## The numbers of the bound -/

/-- The entry's bound as one expression: εs the error, tT the typing's strings, Bk the blocks of
an answer, V the judge's typed queries, t the maker's queries. -/
def entryB (εs : ℝ≥0∞) (tT Bk V t : ℕ) : ℝ≥0∞ :=
  (((t + 2 + (tT + (V * Bk + 0)) + V) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
      2 * (((t + 2 + (tT + (V * Bk + 0)) + V) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
    (((t + (tT + (V * Bk + 0))) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- THE CLAUSE `flat`: if at all tables the judge has V typed queries, the part's bound is that
expression at all tables. -/
theorem entry_flat (Θ : Tab → Tab → EntryAt An lg s d₁) (εs : ℝ≥0∞)
    (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
    (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool)) (V : ℕ)
    (hV : ∀ T₀ T₁, ((Θ T₀ T₁).base T v eM an εs).J.tV = V) (T₀ T₁ : Tab) (t : ℕ) :
    ((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).bound t ≤ entryB εs tT Bk V t := by
  show (((t + 2 + (tT + (((Θ T₀ T₁).base T v eM an εs).J.tV * Bk + 0)) +
      ((Θ T₀ T₁).base T v eM an εs).J.tV) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
      2 * (((t + 2 + (tT + (((Θ T₀ T₁).base T v eM an εs).J.tV * Bk + 0)) +
        ((Θ T₀ T₁).base T v eM an εs).J.tV) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
    (((t + (tT + (((Θ T₀ T₁).base T v eM an εs).J.tV * Bk + 0))) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ _
  rw [hV T₀ T₁]
  exact le_rfl

/-- The judge's typed queries: four for the seeds' chains; one for each round of the link and
one more; a leaf and a path for each opening that the wiring allows; one more. It hangs on the
description's shape and wiring alone. -/
theorem EntryAt.tV_eq (x : EntryAt An lg s d₁) (εs : ℝ≥0∞) :
    (x.base T v eM an εs).J.tV = 4 + tVQB x.Z.wq 0 := rfl

end

end TypedOracleCompiler.Slice
