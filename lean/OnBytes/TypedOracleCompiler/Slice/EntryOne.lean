-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryOne.lean: (a) for the entry file alone, as an implication from the written
list of its debts.

`entry_one_world`: over one uniformly random oracle, for every maker that asks at most t strings and
puts out five files: with probability at most b t + t^2 / 2^256 the entry's checker, at the oracle's
own values at the public strings, returns a value with two roots while the entry's language
(`DecR.LangE`, OnBytes/Slice/DecoderRec.lean) fails of the two strings that are read off the maker's
log under these roots, with the two records in that value. In words: the first string decodes with
its record, which singles one table out, and yet the second does not decode with its own record to a
table that agrees with the first's before the pads, or its record does not single one out.

It is `FileSpec.Delivers.one_world_all` (OnBytes/TypedOracleCompiler/Slice/ShapesOne.lean) at `entrySpec`, with
`EntryDebts.delivers` (ThreeDelivers.lean) and `langE_of_judgeE_out` (EntryXRun.lean).

Beside it, for (b): `EntryYes` (the same checker says yes at a hash, with the roots and records of
two keys: `Three.LinkE` for this one part), `EntryClash` (a clash in its own log), `EntryYesBy` (the
guard: on some files and keys it says yes in that sense), and `entryLose_of_yes`: the two halves
meet in one checker: a yes in the sense of (b) lies in the event of (a), or the entry's language
holds with the two keys' records.

`entry_yes_sound`: the pair's joined sentence with a probability. `entry_clash_rare`: the clash's
limb has its bound too. `EntryDebts.two_roots`: under the list every value has two roots.

What an accepted entry file does NOT guarantee by this alone. (1) Nothing where the first string
does not decode or its record does not single one table out: so without the key's part nothing
follows. (2) In `EntryLose` the two roots and the two records are whatever the checker's value
holds; that they are the key file's and the copy's, and the keys' records under the oracle, is
`EntryYes`'. (3) Agreement before the pads alone. (4) The strings are read off THE MAKER's LOG:
under a root of which the log holds nothing the reading is a table of zeros; nothing is said of any
file's bytes. (5) ONE maker makes all five files: nothing on a committer who is bound before a
prover moves. (6) A checker and a random oracle: not the program, not the format's hash.

What is not claimed. AN IMPLICATION: `EntryDebts` is met by nothing: its description, decision,
reading, implementation, roots and typing are letters. THE WAY OUT: nothing is said where the first
string does not decode or its record does not single one table out; the key is not checked here. The
checker is not the program. That the checker returns a value on anything is not shown: if it never
did, the event would be empty. b is a letter; the bound says nothing once it reaches 1. Nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ThreeDelivers
import OnBytes.TypedOracleCompiler.Slice.ShapesOne

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)
open OnBytes.Slice (DecR decRec GE NZ Tab NoClash Raw offSet)
open OnBytes.Slice.Shapes (Files FileSpec)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open OnBytes.Tie (IdKey)
open scoped ENNReal

variable {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
  (Θ : Tab → Tab → EntryAt An lg s d₁) (εs : ℝ≥0∞)
  (typ : ∀ T₀ T₁, Files → OComp (rom 256) (Option ((Θ T₀ T₁).base T v eM an εs).Out))
  (tT Bk : ℕ) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw SgX) (b : ℕ → ℝ≥0∞)

/-- THE ENTRY FILE's EVENT, IN ONE WORLD, on a maker's files and log, under the oracle g. The
entry's checker, at the oracle's own values at the public strings, returns a value with two roots
r₀, r₁, WHILE THE ENTRY's LANGUAGE FAILS of the two strings that the one written reading reads off
the maker's log under r₀ and r₁, with the two records in that value: the first string decodes with
its record, its record singles one table out, AND the second string does not decode with its own
record to a table that agrees with the first's before the pads, or its record does not single one
out. -/
def EntryLose (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  {x | ∃ (o : OutE (Θ (own₀ S₀ g) (own₁ S₀ S₁ g)).Z) (r₀ r₁ : Dig 256),
    (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ (own₀ S₀ g) (own₁ S₀ S₁ g)).chk x.1).det g =
      some o ∧ o.1 = [r₀, r₁] ∧
    ¬ DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (recE₀ T v eM an o) (recE₁ T v eM an o)
      (rd (own₀ S₀ g) (own₁ S₀ S₁ g) x.2 r₀) (rd (own₀ S₀ g) (own₁ S₀ S₁ g) x.2 r₁)}

/-- (a) FOR THE ENTRY FILE ALONE, FROM THE WRITTEN LIST OF ITS DEBTS. Over one uniformly random
oracle, for every maker with at most t queries, the entry file's event has probability at most
b t + t^2 / 2^256. Asked: `EntryDebts` (OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean), and that the written
reading does not see the entries at public strings. -/
theorem entry_one_world (h : EntryDebts T v eM an Θ εs typ tT Bk S₀ S₁ rd b)
    (hrd : ∀ T₀ T₁ S σ cm, (S = S₀ ∨ ∃ T', S = S₁ T') →
      rd T₀ T₁ (offSet S σ) cm = rd T₀ T₁ σ cm)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd) ≤
      b t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_) (h.delivers.one_world_all hrd A t hA)
  obtain ⟨o, r₀, r₁, ho, hr, hl⟩ := hx
  refine ⟨o, ho, fun hL => hl ?_⟩
  have hroots : ((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ (own₀ S₀ g)
      (own₁ S₀ S₁ g)).roots o = [r₀, r₁] := hr
  rw [hroots] at hL
  exact langE_of_judgeE_out T v eM an (Θ (own₀ S₀ g) (own₁ S₀ S₁ g)).D o _ _ hL

/-! ## What (b) says of the same checker -/

/-- THE ENTRY's CHECKER SAYS YES AT THE HASH H, WITH THE HAND's ROOTS AND RECORDS: at H's own
values at the public strings it returns a value whose two roots are the roots in the two keys k₀, k₁
(the first table's, the copy's), and whose two records are these keys' records under H (`recU`). It
is `Three.LinkE` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) for this one part. -/
def EntryYes (recU : Fam (rom 256) → IdKey → Option (decRec T v eM lg s).Rec) (H : Fam (rom 256))
    (f : Files) (k₀ k₁ : IdKey) : Prop :=
  ∃ o : OutE (Θ (own₀ S₀ H) (own₁ S₀ S₁ H)).Z,
    (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ (own₀ S₀ H) (own₁ S₀ S₁ H)).chk f).det H =
      some o ∧
    o.1 = [_root_.Run.bytesToDig k₀.2.2.root, _root_.Run.bytesToDig k₁.2.2.root] ∧
    recU H k₀ = some (recE₀ T v eM an o) ∧ recU H k₁ = some (recE₁ T v eM an o)

/-- THE FILES THEMSELVES SHOW A CLASH, IN THE ENTRY's CHECKER's OWN LOG: under H two different
strings of that log have one answer. -/
def EntryClash (H : Fam (rom 256)) (f : Files) : Prop :=
  ¬ NoClash (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ (own₀ S₀ H)
    (own₁ S₀ S₁ H)).ownLog H f)

/-- THE GUARD: on some files and two keys the checker says yes at the hash H, IN THE SENSE OF
(b): with the roots' and the records' tests. Without it the checker could be one that never
returns, or the records' reading one that is never there. It is at ONE hash: of the event under a
drawn oracle it says only that the checker is not such a one. -/
def EntryYesBy (recU : Fam (rom 256) → IdKey → Option (decRec T v eM lg s).Rec)
    (H : Fam (rom 256)) : Prop :=
  ∃ (f : Files) (k₀ k₁ : IdKey), EntryYes T v eM an Θ εs typ tT Bk S₀ S₁ recU H f k₀ k₁

/-- THE TWO HALVES MEET IN ONE CHECKER: where the checker says yes in the sense of (b), on files
that a maker has put out with the log σ, the outcome lies in the event of (a) unless the entry's
language holds of the two strings that are read off σ under the two keys' roots. -/
theorem entryLose_of_yes (recU : Fam (rom 256) → IdKey → Option (decRec T v eM lg s).Rec)
    (g : Fam (rom 256)) (f : Files) (σ : Trace (rom 256)) (k₀ k₁ : IdKey)
    (h : EntryYes T v eM an Θ εs typ tT Bk S₀ S₁ recU g f k₀ k₁) :
    (f, σ) ∈ EntryLose T v eM an Θ εs typ tT Bk S₀ S₁ rd g ∨
      ∃ r₀ r₁ : (decRec T v eM lg s).Rec, recU g k₀ = some r₀ ∧ recU g k₁ = some r₁ ∧
        DecR.LangE (DecR.wayColl (decRec T v eM lg s)) r₀ r₁
          (rd (own₀ S₀ g) (own₁ S₀ S₁ g) σ (_root_.Run.bytesToDig k₀.2.2.root))
          (rd (own₀ S₀ g) (own₁ S₀ S₁ g) σ (_root_.Run.bytesToDig k₁.2.2.root)) := by
  obtain ⟨o, ho, hr, h0, h1⟩ := h
  by_cases hL : DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (recE₀ T v eM an o)
      (recE₁ T v eM an o)
      (rd (own₀ S₀ g) (own₁ S₀ S₁ g) σ (_root_.Run.bytesToDig k₀.2.2.root))
      (rd (own₀ S₀ g) (own₁ S₀ S₁ g) σ (_root_.Run.bytesToDig k₁.2.2.root))
  · exact Or.inr ⟨_, _, h0, h1, hL⟩
  · exact Or.inl ⟨o, _, _, ho, hr, hL⟩

/-- THE PAIR's JOINED SENTENCE, WITH A PROBABILITY. Over one uniformly random oracle, for every
maker with at most t queries: with probability at most b t + t^2 / 2^256 the checker says yes in the
sense of (b) on the maker's files, at some two keys, while it is NOT so that both keys have a record
under the oracle with which the entry's language holds of the two strings that are read off the
maker's log under the keys' roots. -/
theorem entry_yes_sound (h : EntryDebts T v eM an Θ εs typ tT Bk S₀ S₁ rd b)
    (hrd : ∀ T₀ T₁ S σ cm, (S = S₀ ∨ ∃ T', S = S₁ T') →
      rd T₀ T₁ (offSet S σ) cm = rd T₀ T₁ σ cm)
    (recU : Fam (rom 256) → IdKey → Option (decRec T v eM lg s).Rec)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (fun g => {x | ∃ k₀ k₁ : IdKey,
      EntryYes T v eM an Θ εs typ tT Bk S₀ S₁ recU g x.1 k₀ k₁ ∧
      ¬ ∃ r₀ r₁ : (decRec T v eM lg s).Rec, recU g k₀ = some r₀ ∧ recU g k₁ = some r₁ ∧
        DecR.LangE (DecR.wayColl (decRec T v eM lg s)) r₀ r₁
          (rd (own₀ S₀ g) (own₁ S₀ S₁ g) x.2 (_root_.Run.bytesToDig k₀.2.2.root))
          (rd (own₀ S₀ g) (own₁ S₀ S₁ g) x.2 (_root_.Run.bytesToDig k₁.2.2.root))}) ≤
      b t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (entry_one_world T v eM an Θ εs typ tT Bk S₀ S₁ rd b h hrd A t hA)
  obtain ⟨k₀, k₁, hy, hn⟩ := hx
  exact (entryLose_of_yes T v eM an Θ εs typ tT Bk S₀ S₁ rd recU g x.1 x.2 k₀ k₁ hy).resolve_right
    hn

/-- The clash's limb of (b) has its bound too: (t + r)^2 / 2^256, if at all tables the checker
asks at most r strings. -/
theorem entry_clash_rare (h : EntryDebts T v eM an Θ εs typ tT Bk S₀ S₁ rd b) (r : ℕ)
    (hr : ∀ T₀ T₁, ((entrySpec T v eM an Θ εs typ tT Bk).part T₀ T₁).tR ≤ r)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (fun g => {x | EntryClash T v eM an Θ εs typ tT Bk S₀ S₁ g x.1}) ≤
      (((t + r) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  h.delivers.one_world_clash r hr A t hA

/-- Under the list of debts every value of the checker has two roots: so the clause on the roots
in `EntryLose` shuts nothing out. -/
theorem EntryDebts.two_roots (h : EntryDebts T v eM an Θ εs typ tT Bk S₀ S₁ rd b) (T₀ T₁ : Tab)
    (g : Fam (rom 256)) (f : Files) (o : OutE (Θ T₀ T₁).Z)
    (ho : (((entrySpec T v eM an Θ εs typ tT Bk).toO S₀ S₁ T₀ T₁).chk f).det g = some o) :
    ∃ r₀ r₁, o.1 = [r₀, r₁] := by
  have h1 : (OnBytes.Slice.Shapes.chkT ((Θ T₀ T₁).base T v eM an εs) (typ T₀ T₁) f).det
      (OnBytes.Slice.over (S₀ ∪ S₁ T₀) (OnBytes.Slice.Shapes.mergeT S₀ T₀ T₁) g) = some o := by
    rw [← OnBytes.Slice.det_pinOn]
    exact ho
  have h2 := (OnBytes.Slice.Shapes.chkT_det ((Θ T₀ T₁).base T v eM an εs) (typ T₀ T₁) f
    (OnBytes.Slice.over (S₀ ∪ S₁ T₀) (OnBytes.Slice.Shapes.mergeT S₀ T₀ T₁) g) o h1).1
  have hl : o.1.length = 2 := (h.file.okT T₀ T₁ _ f o h2).1
  obtain ⟨l, x⟩ := o
  match l, hl with
  | [r₀, r₁], _ => exact ⟨r₀, r₁, rfl⟩

end TypedOracleCompiler.Slice
