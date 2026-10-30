-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryHome.lean: the entry file's verifier as "PRE-PROCESS, THEN THE COMPILED
VERIFIER", at written terms; what is left of the list of its debts; and that what a run computes is
the checker's value.

`EntryDebts` (OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean) lists what is owed for the entry's file; there
the part is made of letters (`EntryAt`) and its typing is a letter. This file puts the terms that
are written into these letters, so that a misfit of types between files shows; it
takes for the typing A PLAIN CONVERTER, any function from the five files to what the typed verifier
takes in, which asks the oracle nothing; it calls the theorems that lie; and it names what is left.

Main definitions.
 `HomeData z d₁` what is STILL a letter, at sizes z: the description as a function of the
     configuration's digest, with the second compiler's test; the entry's parameter bytes as a
     function of that digest; the decision; one datum of the page.
 `HomeData.atR`, `HomeData.at` the part but for its checker: `EntryClean.atPage` at bodies that are
     strings (`bodyS`, `ownES`), the entry's own reading (`entryR`), the page `EntryFill.pageForE`
     at the two digests that the tables hold and at the sizes' salt; answers are read by `anT`.
 `HomeData.Conv` a converter. IT IS TRUSTED FOR NOTHING. `conv2`: cut to values with two roots;
     `rts`: the roots in its value; `typ`: the converter as a typing (`pureTyp`,
     OnBytes/TypedOracleCompiler/Slice/ShapesConv.lean).
 `HomeData.spec` the entry file's spec: pre-process, then the compiled verifier.
 `HomeData.Left` WHAT IS LEFT of the list: ten named fields. None names the converter.
Main theorems.
 `Left.debts` from what is left to the whole list, for every converter. Called: `recNums_of_fit`,
     `pageForE_one`, `pageForE_blocks`, `reads_ofTyping` with `EntryAt.plainRead`, `atPage_clean`,
     `entry_flat`, `EntryAt.ok_iff`.
 `Left.one_world` (a) for the entry file: for every converter and every maker with t queries the
     event of OnBytes/TypedOracleCompiler/Slice/EntryOne.lean has probability at most `entryB εs 0 Bk V t` + t^2 /
     2^256: a written bound.
 `chk_eq_run` under every oracle g, at g's own public values, the checker of which the bound speaks
     returns what the converter makes of the files, if the compiled verifier's run accepts it under
     the family read out of g through the page; else nothing.

`chk_eq_runF` the same with the judge's run as a plain definition of a truth value (`judgeRunELF`).

WHAT THE SHORT WORD STANDS FOR. "The compiled verifier" is here the judge's run: a wrap written by
hand (the seeds' chain once for each root, two comparisons), behind the test "two roots", and then
the second compiler's lax verifier at the written link.

A YES IS A YES OF THE VALUE THAT THE CHECKER RETURNS, NOT OF THE FILES. The converter makes the
statement, not only the proof: the two roots and the two lists of answers in its value are bound
into the chain's first query, and none of them is derived. Whoever relies on a yes takes them from
the checker's value and holds them against what they hold: the first root and answers against those
that the key's part accepted, the second against those that the proof's part accepts. No file here
makes these comparisons. Nobody tests the number of answers: `anT` reads 0 beyond a list's end and
nothing beyond the sizes' number.

HOW THE BOUND IS TO BE TOLD. For EVERY converter: among them one that merely parses a typed value
out of the maker's bytes, so that the maker, who asks the oracle, picks the typed value as it likes.
Whatever evaluations of the hash go into that value, a pre-processor's among them, are then the
maker's: they count in t and stand in the log off which the strings are read. That such a parser
onto the typed values exists is not shown here. No sentence should rest on the instance at one
converter. A run at one hash shows completeness at one file, no more.

What is not claimed. NOTHING IS DELIVERED: no `HomeData` is given, and `Left` is met by nothing.
That a converter returns anything on any file, or that the run accepts anything. That the run's
value can be computed: `det`, `readBlocks` and the page are no programs here. All that is checked
under the oracle is checked by the judge's run; what that run takes from the converter's value
without deriving it is to be read in OnBytes/TypedOracleCompiler/Slice/JudgeE.lean. The limits of
OnBytes/TypedOracleCompiler/Slice/EntryOne.lean stand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryOne
import OnBytes.TypedOracleCompiler.Slice.EntryData
import OnBytes.TypedOracleCompiler.Slice.EntryClean
import OnBytes.TypedOracleCompiler.Slice.PartChainStr
import OnBytes.TypedOracleCompiler.Slice.ShapesPub
import OnBytes.TypedOracleCompiler.Slice.ShapesNums
import OnBytes.TypedOracleCompiler.Slice.ShapesReadsPage
import OnBytes.TypedOracleCompiler.Slice.ShapesConv
import OnBytes.TypedOracleCompiler.Slice.EntryRunForm

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (DecR decRec recZ seedBS seedEntry GE NZ Tab NoClash Raw offSet s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁ rdC Spells pureTyp)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-- WHAT IS STILL A LETTER IN THE ENTRY's PART, at sizes z. All else of `EntryAt` is a written
term (`HomeData.at`). -/
structure HomeData (z : Size) (d₁ : Sd1 z.lg z.s) where
  /-- the description of the entry's chain, as a function of the configuration's digest -/
  DX : ByteArray → XD
  /-- at a digest of 32 bytes its chain passes the second compiler's test of descriptions (which
  asks that length of the digest in the description) -/
  ok : ∀ c, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (DX c).base = true
  /-- the entry's parameter bytes, as a function of the configuration's digest -/
  prm : ByteArray → ByteArray
  /-- the decision, as a function of the digest and an instance -/
  dec : ByteArray → XE (List T3) z.lg z.s → View → Bool
  /-- the page's code behind the escape -/
  back : ∀ c, StrCode (AllPts 256 ((DX c).K + 1) (EntryFill.Ls (DX c) d₁))

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- THE ENTRY's PART BUT FOR ITS CHECKER, AT WRITTEN TERMS, with given roots. The description at
the digest that the first table holds; bodies are strings; stored and own symbols lie among them as
the format spells their leaves; the entry's own reading (`entryR`); the implementation is the page
of OnBytes/TypedOracleCompiler/Slice/EntryFill.lean at that digest, at the parameter bytes' digest that the second
table holds, at the sizes' salt, and with a table's name as the format has it: the root, then that
digest and the sizes' six words. -/
def atR (rts : Files → List (Dig 256)) (T₀ T₁ : Tab) : EntryAt (List T3) z.lg z.s d₁ :=
  EntryClean.atPage (H.DX (dgOf cfg T₀))
    (bodyS (H.DX (dgOf cfg T₀)).a (H.DX (dgOf cfg T₀)).base.plan.salt)
    (ownES (H.DX (dgOf cfg T₀)) (H.ok _ (dgOf_size cfg T₀))) (H.dec (dgOf cfg T₀))
    (entryR (H.DX (dgOf cfg T₀)) _ (ownES (H.DX (dgOf cfg T₀)) (H.ok _ (dgOf_size cfg T₀)))
      (earlyTwo d₁)
      (TSE (H.DX (dgOf cfg T₀)) (seedEntry z.lg z.s))
      (wTSE (H.DX (dgOf cfg T₀)) (seedEntry z.lg z.s))
      (embST (H.DX (dgOf cfg T₀)).C (seedEntry z.lg z.s) _)
      (prjST (H.DX (dgOf cfg T₀)).C (seedEntry z.lg z.s) _))
    rts (dgOf cfg T₀) (dgOf_size cfg T₀) (T₁ (s0Of (H.prm (dgOf cfg T₀))))
    (TypedOracleCompiler.Run.FirstName.restOf (dgOf cfg T₀) z.T.a z.T.l z.T.r z.v z.s z.shape.saltBytes)
    (8 * z.shape.saltBytes) (H.back _)

/-- What the typed verifier takes in, at two tables: two roots, an instance, a typed string. It does
not hang on the roots that are read off the files. -/
abbrev Out (T₀ T₁ : Tab) : Type := OutE (H.atR cfg (fun _ => []) T₀ T₁).Z

/-- A CONVERTER: any plain function from the five files to what the typed verifier takes in; a
family over the two tables, so in one world it may know the oracle's values at the public strings.
IT IS TRUSTED FOR NOTHING: the bound below holds for every converter. What it returns need have
nothing to do with the bytes that it was given: A YES IS A YES OF THE VALUE THAT THE CHECKER
RETURNS, NOT OF THE FILES. -/
abbrev Conv : Type := ∀ T₀ T₁, Files → Option (H.Out cfg T₀ T₁)

variable (conv : H.Conv cfg)

/-- The converter, cut to values with two roots. -/
def conv2 (T₀ T₁ : Tab) (d : Files) : Option (H.Out cfg T₀ T₁) :=
  (conv T₀ T₁ d).filter fun o => decide (o.1.length = 2)

/-- The roots that the converter's value holds. -/
def rts (T₀ T₁ : Tab) (d : Files) : List (Dig 256) :=
  match H.conv2 cfg conv T₀ T₁ d with
  | none => []
  | some o => o.1

/-- THE ENTRY's PART BUT FOR ITS CHECKER, with the roots that the converter's value holds. -/
def «at» (T₀ T₁ : Tab) : EntryAt (List T3) z.lg z.s d₁ :=
  H.atR cfg (H.rts cfg conv T₀ T₁) T₀ T₁

/-- THE TYPING: THE CONVERTER ITSELF. It asks the oracle nothing. -/
def typ (εs : ℝ≥0∞) : ∀ T₀ T₁, Files → OComp (rom 256)
    (Option ((H.at cfg conv T₀ T₁).base z.T z.v z.eM (anT z.v z.s) εs).Out) :=
  fun T₀ T₁ => pureTyp (H.conv2 cfg conv T₀ T₁)

/-- THE ENTRY FILE's SPEC: PRE-PROCESS, THEN THE COMPILED VERIFIER. -/
abbrev spec (εs : ℝ≥0∞) (Bk : ℕ) : FileSpec :=
  entrySpec z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) εs (H.typ cfg conv εs) 0 Bk

/-- WHAT IS LEFT OF THE LIST OF THE ENTRY's DEBTS when the files that lie have been called: each
field names what is not shown at these terms. NO FIELD NAMES THE CONVERTER. Whatever is asked of
the description is asked at digests of 32 bytes alone: the part is never taken at another. -/
structure Left (εs : ℝ≥0∞) (Bk V : ℕ) : Prop where
  /-- the sizes are in order -/
  fit : z.Fit
  /-- the record's bound is at most the error -/
  price : kapSl 128 ^ (seedBS z.lg z.s).b *
    ((((Cb.listMax (2 ^ z.T.a) (2 ^ z.T.a - (z.T.r + z.T.l) + 1) z.eM).choose 2 *
      (recZ z.T.l z.lg z.s).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ z.T.l z.lg z.s).D) ≤ εs
  /-- the depth of the description's stored tables is the code's -/
  depthIs : ∀ c, c.size = 32 → (H.DX c).a = z.T.a
  /-- the description's field is the second -/
  field : ∀ c, c.size = 32 → (H.DX c).base.plan.field = .two
  /-- blocks enough for the seeds' sampler -/
  enough : ∀ c, c.size = 32 → (seedBS z.lg z.s).b ≤ (H.DX c).K
  /-- the link's wiring is lawful -/
  wiring : ∀ c, c.size = 32 → (wq0 (H.DX c) fun _ => true).OKG
  /-- SOUNDNESS RECORD BY RECORD, with one list of counts, each at most the error -/
  sound : ∀ c, c.size = 32 → ∃ ε : Err (Link0 (H.DX c) fun _ => true).shape,
    (∀ x, (Link0 (H.DX c) (H.dec c x)).Sound
      (fun _ => lgEX z.T z.v z.eM z.lg z.s (H.DX c) (anT z.v z.s) x) ε) ∧ Err.Below ε εs
  /-- the blocks of an answer -/
  blocksLe : ∀ c, c.size = 32 → (H.DX c).K + 2 ≤ Bk
  /-- the page spells vertices and stored leaves as the format does -/
  spells : ∀ T₀ T₁, Spells (H.atR cfg (fun _ => []) T₀ T₁).m
    (bodyS (H.DX (dgOf cfg T₀)).a (H.DX (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) z.T.a
    z.shape.saltBytes
  /-- the typed verifier asks V typed queries, at all tables -/
  count : ∀ T₀ T₁, ((H.atR cfg (fun _ => []) T₀ T₁).base z.T z.v z.eM (anT z.v z.s) εs).J.tV = V

variable {H cfg}

omit [DecidableEq (Sd1 z.lg z.s)] in
/-- What the cut converter returns has two roots, and they are the roots read off the files. -/
theorem conv2_some {T₀ T₁ : Tab} {d : Files} {o : H.Out cfg T₀ T₁}
    (h : H.conv2 cfg conv T₀ T₁ d = some o) : o.1.length = 2 ∧ H.rts cfg conv T₀ T₁ d = o.1 := by
  refine ⟨?_, ?_⟩
  · have h2 := (Option.filter_eq_some_iff.1 h).2
    exact of_decide_eq_true h2
  · unfold rts
    rw [h]

/-- FROM WHAT IS LEFT TO THE WHOLE LIST, FOR EVERY CONVERTER. -/
theorem Left.debts {εs : ℝ≥0∞} {Bk V : ℕ} (h : H.Left cfg εs Bk V) :
    EntryDebts z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) εs (H.typ cfg conv εs) 0 Bk (pubS₀ cfg)
      (pubS₁ [H.prm] cfg) (rdC z cfg) (entryB εs 0 Bk V) where
  nums := OnBytes.Slice.Shapes.recNums_of_fit z h.fit εs h.price
  depthIs := fun T₀ _ => h.depthIs (dgOf cfg T₀) (dgOf_size cfg T₀)
  field := fun T₀ _ => h.field (dgOf cfg T₀) (dgOf_size cfg T₀)
  enough := fun T₀ _ => h.enough (dgOf cfg T₀) (dgOf_size cfg T₀)
  wiring := fun T₀ _ => h.wiring (dgOf cfg T₀) (dgOf_size cfg T₀)
  sound := fun T₀ _ => h.sound (dgOf cfg T₀) (dgOf_size cfg T₀)
  file :=
    { one := fun _ _ => EntryFill.pageForE_one _ _ _ _ _ _ _ _
      reads := OnBytes.Slice.Shapes.reads_ofTyping _ (H.typ cfg conv εs) _ 4 0 Bk z (dgOf cfg)
        (dgOf_size cfg)
        (fun T₀ T₁ => h.depthIs (dgOf cfg T₀) (dgOf_size cfg T₀) ▸
          (H.at cfg conv T₀ T₁).plainRead z.T z.v z.eM (anT z.v z.s) rfl εs)
        (fun _ _ => EntryFill.pageForE_one _ _ _ _ _ _ _ _) h.spells
      blocks := fun T₀ _ o => le_trans (EntryFill.pageForE_blocks _ _ _ _ _ _ _ _ o)
        (h.blocksLe (dgOf cfg T₀) (dgOf_size cfg T₀))
      clean := fun T₀ T₁ F o => EntryClean.atPage_clean _ _ _ _ _ _ _ _ _ _ _ _ z.T z.v z.eM
        (anT z.v z.s) εs (pubS₀ cfg ∪ pubS₁ [H.prm] cfg T₀) (fun t ht => by
          rcases Finset.mem_union.1 ht with h0 | h1
          · exact OnBytes.Slice.Shapes.pubS₀_169 cfg t h0
          · exact OnBytes.Slice.Shapes.pubS₁_169 _ cfg T₀ t h1) F o
      flat := entry_flat z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) εs (H.typ cfg conv εs) 0 Bk
        (pubS₀ cfg) (pubS₁ [H.prm] cfg) V h.count
      typNoCoin := fun _ _ _ => trivial
      typQueries := fun _ _ _ => trivial
      few := fun T₀ T₁ x => by
        show (H.rts cfg conv T₀ T₁ x).length ≤ 2
        rcases hc : H.conv2 cfg conv T₀ T₁ x with _ | o
        · unfold rts
          rw [hc]
          exact Nat.zero_le _
        · rw [(conv2_some conv hc).2, (conv2_some conv hc).1]
      typNamed := fun T₀ T₁ _ x o ho r hr => by
        show r ∈ H.rts cfg conv T₀ T₁ x
        rw [(conv2_some conv (show H.conv2 cfg conv T₀ T₁ x = some o from ho)).2]
        exact hr
      okT := fun T₀ T₁ _ x o ho =>
        ((H.at cfg conv T₀ T₁).ok_iff z.T z.v z.eM (anT z.v z.s) rfl εs o).2
          (conv2_some conv (show H.conv2 cfg conv T₀ T₁ x = some o from ho)).1 }

/-- (a) FOR THE ENTRY FILE: PRE-PROCESS BY ANY CONVERTER, THEN THE COMPILED VERIFIER. Over one
uniformly random oracle, for every converter and every maker with at most t queries: with
probability at most `entryB εs 0 Bk V t` + t^2 / 2^256 the verifier accepts what the converter makes
of the maker's files while the entry's language fails of the two strings that are read off the
maker's log under the two roots, with the two records, in what was accepted. THE CONVERTER IS BOUND
BY "FOR EVERY": that is what "untrusted" means. NO SENTENCE SHOULD REST ON THE INSTANCE AT ONE
CONVERTER: at a converter that hashes by a fixed hash the verifier accepts under a drawn oracle all
but never, whatever the protocol, so that instance says next to nothing. Of an accepted value
([r₀, r₁], ((a₀, a₁), (s₀, s₁)), π) the bound says: if the string read off the log under r₀ decodes
with (s₀, a₀), and that record singles one table out, then the string under r₁ decodes with (s₁, a₁)
to a table that agrees with the first's before the pads, and that record singles one out. The seeds
are derived: the run refuses unless s₀, s₁ are what the oracle gives at the names of r₀ and r₁. THE
ROOTS AND THE ANSWERS ARE THE STATEMENT: the run binds them into the chain's first query and derives
none of them. -/
theorem Left.one_world {εs : ℝ≥0∞} {Bk V : ℕ} (h : H.Left cfg εs Bk V)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (EntryLose z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) εs
      (H.typ cfg conv εs) 0 Bk (pubS₀ cfg) (pubS₁ [H.prm] cfg) (rdC z cfg)) ≤
      entryB εs 0 Bk V t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  entry_one_world z.T z.v z.eM (anT z.v z.s) (H.at cfg conv) εs (H.typ cfg conv εs) 0 Bk
    (pubS₀ cfg) (pubS₁ [H.prm] cfg) (rdC z cfg) _ (h.debts conv)
    (OnBytes.Slice.Shapes.rdC_off z cfg [H.prm]) A t hA

/-- WHAT THE RUN COMPUTES IS THE CHECKER's VALUE. Under every oracle g, at g's own values at the
public strings: the checker of which the bound speaks returns what the converter makes of the files
(cut to two roots), if the compiled verifier's run accepts it under the family that is read out of g
through the page; else nothing. At g the oracle made from the format's hash this is "pre-process,
then apply the compiled verifier at that hash". THE VALUE HOLDS THE STATEMENT: a run that gives out
"yes" alone says that SOME statement was proved; whoever relies on it takes the two roots and the
two lists of answers from the checker's value and holds them against what they hold. -/
theorem chk_eq_run (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files) :
    (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g =
    (H.conv2 cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d).bind
      fun o => if (((H.at cfg conv (own₀ (pubS₀ cfg) g)
          (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).base z.T z.v z.eM (anT z.v z.s) εs).J.run
            o).det (readBlocks (H.at cfg conv (own₀ (pubS₀ cfg) g)
              (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).m g) = true then some o else none := by
  rw [FileSpec.chk_own]
  exact OnBytes.Slice.Shapes.chkT_pure_det _ _ d g

/-- THE SAME WITH THE JUDGE's RUN AS A TRUTH VALUE THAT IS A PLAIN DEFINITION (`judgeRunELF`,
OnBytes/TypedOracleCompiler/Slice/EntryRunForm.lean): the comparisons of both tables' seeds with what the seeds'
chain yields, and the lax verifier's run form. -/
theorem chk_eq_runF (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files) :
    (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g =
    (H.conv2 cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d).bind
      fun o => if judgeRunELF
          (H.at cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).D
          (H.at cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).dec
          (H.at cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).B
          (H.at cfg conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).E
          (earlyTwo d₁) (seedEntry z.lg z.s) (OnBytes.Slice.seedOfDrawnC z.lg z.s)
          (readBlocks (H.at cfg conv (own₀ (pubS₀ cfg) g)
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).m g) o = true then some o else none := by
  rw [chk_eq_run]
  refine congrArg _ (funext fun o => ?_)
  rw [EntryAt.run_eq]

end HomeData

end TypedOracleCompiler.Slice
