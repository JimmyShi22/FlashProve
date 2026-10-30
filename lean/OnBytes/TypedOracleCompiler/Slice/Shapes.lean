-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Shapes.lean: THE SHAPES: a verifier on bytes with the hash as an argument, what is
fine, the two statements that are aimed at, and what each of three files' parts must deliver.
DEFINITIONS AND STATEMENTS; NOTHING IS SHOWN OF ANY FILE.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed. So piece `LinkId` of (b), below, is not what a run
of the Lean program gives: the program compares the user's ID with `Key.commitmentId`
(OnBytes/Key/Table.lean), the hash of the rule's string, and `LinkId` at such an ID asks one answer
of the hash at two different strings (`idCode_ne`, Johnson/TypedOracleCompiler/Top/IdStringsApart.lean). By reading
the definitions; no theorem says so.

The aim is two texts and a tie. `Three.VerifyB H id d`: a verifier that takes the hash H, a
commitment ID and five byte strings (key file, entry file, proof file, request, reply). It is not
computable, and no program calls it. (a) `Three.SoundB`: over a uniformly random H, for a committer
that puts out the ID and a prover that puts out the files, it says yes while the outcome is not fine
(`Three.FineB`) with probability at most a bound. (b) where the Lean program returns 0, at one
setting of its options, `VerifyB` says yes on the same bytes at the format's hash, with the second
hash function's value at the request's string. The three configuration files (`Cfg`) are bound
outside: a `Three` is made AT a configuration.

What a yes is (`Three.Accepts`): the ID is H's value at the key's string; each of three checkers
returns a value; the roots chain [r], [r, cm'], [cm'], r and cm' the roots in the two keys that
plain readers read off the key file and the entry file; EACH CHECKER's RECORD IS ITS KEY's RECORD
UNDER THE ORACLE (`recU`: the seeds that the oracle gives at the table's name, the answers in the
key): so the answers that the ID binds are those with which the parts decode, and what one stage
hands to the next is a table, not a root alone; the proof's instance is the one read off request and
reply. It is the first half of the hypothesis `hYes` of `join_id_decR_run`
(OnBytes/Slice/JoinDecRec.lean), made a definition, sharpened at the records and at the second root,
which is the copy's key's, with one clause more (the instance).

Why tables, and why they are cut. A part's page and descriptions hold values of the hash as
constants (the configuration's digest; the digests of parameter bytes). Under a drawn oracle these
are drawn too, so each part is a family over two tables of such values. `VerifyB H` takes the parts
at H's own values AT THE PUBLIC STRINGS, and at the default value elsewhere (`pub₀`, `pub₁`): so it
hangs on H through finitely many values, three runs with their logs, the ID's string and two keys'
records, and nothing need be said on how a part reads a table off the public strings. A PART MAY
READ THE FIRST TABLE ON S₀ AND THE SECOND ON S₁ ALONE: elsewhere it is handed the default value.

Main definitions.
 `Files`, `Cfg`, `own`, `mergeT`, `cutT`, `patch`.
 `Three D Xi` three families of parts over the one oracle; the readers of keys, records and
     instance; the two readings in which "fine" is said (`recU`, `rawU`).
 `Three.Accepts`, `Three.VerifyB`, `Three.FineB`, `Three.SoundB`, `Three.eps`, `Three.Laws`.
 `Three.Hand`, `Three.LinkId`, `LinkK`, `LinkE`, `LinkF` (b), cut into four pieces at one hash,
     around the two keys that the program hands on.
 `FileSpec`, `FileSpec.toO`, `FileSpec.Delivers` what is delivered for one file: judge, page,
     numbers, typing, fit. Theorems (all short): `Three.verifyB_iff`; `Three.verifyB_of_links`,
     `verifyB_of_links_or` ((b) from its four pieces, by definition); `FileSpec.Delivers.ok` (what
     is delivered gives `PartO.OK` at all tables); `FileSpec.toO_deaf`. That `Laws` gives `SoundB`:
     OnBytes/TypedOracleCompiler/Slice/ShapesTop.lean.

What is not claimed. No `Three` and no `FileSpec` is given. NOTHING GUARDS AGAINST AN EMPTY ONE: a
`Three` whose checkers never return meets `Laws`, and its `VerifyB` says yes at a clash alone; a
claim that holds of everything makes all outcomes with a key fine. What guards is outside Lean's
statements here: a yes on an honest proof at a small configuration, the bound evaluated, an outcome
that is not fine. No matrix, range or claim (`A`) is given. The program, its shell and the format's
hash are not named here: the four pieces of (b) are stated at any H. The compiler under OnBytes/TypedOracleCompiler/
is the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.
Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.JoinDecRec
import OnBytes.TypedOracleCompiler.Slice.PartAskGuard

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Iop Rom Prob MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open OnBytes.Slice (PartO Raw Tab over NoClash offSet SameRaw twoExp lenB DecR goodDecR)
open scoped ENNReal

/-! ## 1. What a prover puts out; the oracle's own values as a table -/

/-- What the prover puts out: five byte strings. The three configuration files are no part of
it: they are fixed beforehand and stand inside the parts. -/
structure Files where
  /-- the key file -/
  key : ByteArray
  /-- the entry file -/
  ent : ByteArray
  /-- the proof file -/
  prf : ByteArray
  /-- the request -/
  req : ByteArray
  /-- the reply -/
  reply : ByteArray

/-- The oracle's own values, as a table. -/
def own (H : Fam (rom 256)) : Tab := fun s => H () s

/-- Two tables as one: the first on S₀, the second elsewhere. -/
def mergeT (S₀ : Finset (List Bool)) (T₀ T₁ : Tab) : Tab := fun s => if s ∈ S₀ then T₀ s else T₁ s

/-- The three configuration files. They are bound outside everything: a family of parts is made
AT a configuration, (a) is said for every configuration that is in order, and (b) at the files that
the program has read. No declaration of this file uses it but `SoundAll`. -/
structure Cfg where
  /-- the parameter file -/
  pol : ByteArray
  /-- the layout -/
  lay : ByteArray
  /-- the scale file -/
  KL : ByteArray

/-- An oracle with another function's values put at the strings where that function speaks. For (b):
the format's realised oracle, with the second hash function's value at the code of a request. -/
def patch (H : Fam (rom 256)) (f : List Bool → Option (Dig 256)) : Fam (rom 256) :=
  fun _ s => (f s).getD (H () s)

/-- A table cut to a set of strings: the default value elsewhere. -/
def cutT (S : Finset (List Bool)) (T : Tab) : Tab := fun s => if s ∈ S then T s else default

/-! ## 2. The three parts, as the verifier on bytes and the join see them -/

variable {D : DecR} {Xi : Type}

/-- The three files' parts over the one oracle, with what is read off their checkers' values, and
the two readings in which "fine" is said. Each part is a family over two tables: the values of the
oracle at the public strings (S₀: the configuration files' string; S₁ T₀: the strings that hang on
its value), which a part's implementation and descriptions hold as constants. -/
structure Three (D : DecR) (Xi : Type) where
  /-- the first public strings -/
  S₀ : Finset (List Bool)
  /-- the public strings that hang on the values at the first -/
  S₁ : Tab → Finset (List Bool)
  /-- shape, configuration digest and table (root and answers): meant: read off the key file -/
  key : Tab → Tab → Files → IdKey
  /-- the like for the copy: meant: read off the entry file -/
  keyC : Tab → Tab → Files → IdKey
  /-- the key file's part -/
  K : Tab → Tab → PartO 256 Files Run.PQ.SgX
  /-- the entry file's part -/
  E : Tab → Tab → PartO 256 Files Run.PQ.SgX
  /-- the proof file's part -/
  F : Tab → Tab → PartO 256 Files Run.PQ.SgX
  /-- the first table's record (seeds and answers) in the key's checker's value -/
  recK : ∀ T₀ T₁, (K T₀ T₁).Out → D.Rec
  /-- the first table's record in the entry's checker's value -/
  recE₀ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec
  /-- the copy's record in the entry's checker's value -/
  recE₁ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec
  /-- the copy's record in the proof's checker's value -/
  recF : ∀ T₀ T₁, (F T₀ T₁).Out → D.Rec
  /-- the instance (request and reply, as the claim reads them) in the proof's checker's value -/
  xOf : ∀ T₀ T₁, (F T₀ T₁).Out → Xi
  /-- the instance, read off the request's and the reply's bytes -/
  xReq : Files → Xi
  /-- matrix, range and claim: free of the tables -/
  A : D.Claims Xi
  /-- THE RECORD OF A KEY UNDER AN ORACLE: the seeds that the oracle gives at the key's table's
  name, and the answers in the key -/
  recU : Fam (rom 256) → IdKey → Option D.Rec
  /-- THE ONE WRITTEN READING of the raw string under a root off a log, at a key's configuration -/
  rawU : IdKey → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX
  /-- the keys at whose shape the raw string is read and decoded -/
  okKey : IdKey → Prop

namespace Three
variable (Θ : Three D Xi)

/-- The oracle's values at the first public strings. -/
def pub₀ (H : Fam (rom 256)) : Tab := cutT Θ.S₀ (own H)

/-- The oracle's values at the public strings that hang on these. -/
def pub₁ (H : Fam (rom 256)) : Tab := cutT (Θ.S₁ (Θ.pub₀ H)) (own H)

/-- What a yes is, at two tables, with the ID tested under H and all else under g: the ID is H's
value at the key's string; each checker returns a value; the roots chain [r], [r, cm'], [cm'], r the
key's root and cm' the copy's; THE RECORDS ARE THE ORACLE's: the key's and the entry's first are the
key's record under g, the entry's second and the proof's are the copy's; the proof's instance is the
one read off request and reply. -/
def Accepts (T₀ T₁ : Tab) (H g : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) : Prop :=
  (∃ s, idCode (Θ.key T₀ T₁ d) = some s ∧ H () s = id) ∧ ∃ oK oE oF,
    ((Θ.K T₀ T₁).chk d).det g = some oK ∧ ((Θ.E T₀ T₁).chk d).det g = some oE ∧
    ((Θ.F T₀ T₁).chk d).det g = some oF ∧
    (Θ.K T₀ T₁).roots oK = [Run.bytesToDig (Θ.key T₀ T₁ d).2.2.root] ∧
    (Θ.E T₀ T₁).roots oE = [Run.bytesToDig (Θ.key T₀ T₁ d).2.2.root,
      Run.bytesToDig (Θ.keyC T₀ T₁ d).2.2.root] ∧
    (Θ.F T₀ T₁).roots oF = [Run.bytesToDig (Θ.keyC T₀ T₁ d).2.2.root] ∧
    Θ.recU g (Θ.key T₀ T₁ d) = some (Θ.recK T₀ T₁ oK) ∧
    Θ.recU g (Θ.key T₀ T₁ d) = some (Θ.recE₀ T₀ T₁ oE) ∧
    Θ.recU g (Θ.keyC T₀ T₁ d) = some (Θ.recE₁ T₀ T₁ oE) ∧
    Θ.recU g (Θ.keyC T₀ T₁ d) = some (Θ.recF T₀ T₁ oF) ∧
    Θ.xOf T₀ T₁ oF = Θ.xReq d

/-- The files themselves show a clash: in the log of one of the three checkers on them, under g,
two different strings have one answer. -/
def ClashB (T₀ T₁ : Tab) (g : Fam (rom 256)) (d : Files) : Prop :=
  ¬ NoClash ((Θ.K T₀ T₁).ownLog g d) ∨ ¬ NoClash ((Θ.E T₀ T₁).ownLog g d) ∨
    ¬ NoClash ((Θ.F T₀ T₁).ownLog g d)

/-- THE VERIFIER ON BYTES, THE HASH AN ARGUMENT. Not computable; no program calls it. The parts
stand at H's own values at the public strings, and at the default value elsewhere. It says yes where
`Accepts` holds, AND WHERE THE FILES THEMSELVES SHOW A CLASH: there a program that reads each
opening by itself and a typed verifier that has one symbol a position may part; (a) pays for it by
a term. -/
noncomputable def VerifyB (H : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) : Bool :=
  @decide (Θ.Accepts (Θ.pub₀ H) (Θ.pub₁ H) H H id d ∨ Θ.ClashB (Θ.pub₀ H) (Θ.pub₁ H) H d)
    (Classical.propDecidable _)

/-- Its yes, unfolded. -/
theorem verifyB_iff (H : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) :
    Θ.VerifyB H id d = true ↔
      (Θ.Accepts (Θ.pub₀ H) (Θ.pub₁ H) H H id d ∨ Θ.ClashB (Θ.pub₀ H) (Θ.pub₁ H) H d) := by
  unfold VerifyB
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ## 3. (a): what is fine, the statement of soundness, and what it asks -/

/-- An outcome of "a committer, then a prover": the committer's output (the ID and a state) with its
log, the prover's output, and the log of both. -/
abbrev Outcome (St : Type) : Type :=
  (((ZKCP.Digest 256 × St) × Trace (rom 256)) × Files) × Trace (rom 256)

/-- WHAT IS FINE. The committer's own log shows a first key k for the ID, of the right shape;
with k's record under the oracle, the raw string that the one written reading reads off THE
COMMITTER's OWN LOG under k's root decodes to a matrix in range, of which the claim holds at the
instance read off the prover's request and reply. It reads the ID, the committer's log, request and
reply, and the oracle through `recU` alone. That k's configuration digest is the oracle's value at
the configuration's string is not said: in the proof of (a) k is the files' key. -/
def FineB (St : Type) (g : Fam (rom 256)) (w : Outcome St) : Prop :=
  ∃ k rec, firstId w.1.1.1.1 w.1.1.2 = some k ∧ Θ.okKey k ∧ Θ.recU g k = some rec ∧
    goodDecR Θ.A (Θ.xReq w.1.2) rec (Θ.rawU k w.1.1.2 (Run.bytesToDig k.2.2.root))

/-- (a), AS A STATEMENT. For every committer with at most tC and every prover with at most tP
queries to a uniformly random oracle: the verifier on bytes says yes on the committer's ID and the
prover's files while the outcome is not fine, with probability at most e tC tP. (`Rom.Pr` is a lower
integral; under the clause `measR` the event is measurable.) -/
def SoundB (e : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (St : Type) (C : OComp (rom 256) (ZKCP.Digest 256 × St))
    (P : ZKCP.Digest 256 × St → OComp (rom 256) Files) (tC tP : ℕ), C.QueryBound tC →
    (∀ b, (P b).QueryBound tP) →
    Rom.Pr (twoExp C P).withTrace
      (fun g => {w | Θ.VerifyB g w.1.1.1.1 w.1.2 = true ∧ ¬ Θ.FineB St g w}) ≤ e tC tP

/-- The bound: three expressions that bound the parts' bounds at all tables, at tC + tP; the
first part's term for a stable root; the ID's term; the term for a clash in the checkers' logs. -/
noncomputable def eps (bK bE bF bC : ℕ → ℝ≥0∞) (bS : ℕ → ℕ → ℝ≥0∞) (tC tP : ℕ) : ℝ≥0∞ :=
  bK (tC + tP) + (bE (tC + tP) + (bF (tC + tP) +
    (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bC (tC + tP)))))

/-- WHAT (a) ASKS, clause by clause. Of each part: its bound, its language, and that its checker
is deaf to the oracle at the public strings. Of the parts together: one raw string. Of the key's
part: a stable root, and that it reads the one written reading. Of that reading: that it does not
see the public strings. One clause on measurable sets. -/
structure Laws (bK bE bF bC : ℕ → ℝ≥0∞) (bS : ℕ → ℕ → ℝ≥0∞) : Prop where
  /-- the key's part has its bound, for every maker, at all tables -/
  okK : ∀ T₀ T₁, (Θ.K T₀ T₁).OK
  /-- the entry's -/
  okE : ∀ T₀ T₁, (Θ.E T₀ T₁).OK
  /-- the proof's -/
  okF : ∀ T₀ T₁, (Θ.F T₀ T₁).OK
  /-- one expression bounds the key's part's bound at all tables -/
  flatK : ∀ T₀ T₁ t, (Θ.K T₀ T₁).bound t ≤ bK t
  /-- the entry's -/
  flatE : ∀ T₀ T₁ t, (Θ.E T₀ T₁).bound t ≤ bE t
  /-- the proof's -/
  flatF : ∀ T₀ T₁ t, (Θ.F T₀ T₁).bound t ≤ bF t
  /-- what the key's part reads under an announced root does not change -/
  stable : ∀ T₀ T₁, (Θ.K T₀ T₁).Stable bS
  /-- key and entry read one raw string under a root, off a log without a clash -/
  sameKE : ∀ T₀ T₁, SameRaw (Θ.K T₀ T₁) (Θ.E T₀ T₁)
  /-- entry and proof likewise -/
  sameEF : ∀ T₀ T₁, SameRaw (Θ.E T₀ T₁) (Θ.F T₀ T₁)
  /-- the key's language -/
  langK : ∀ T₀ T₁ oK Y, (Θ.K T₀ T₁).Lang oK [Y] →
    DecR.LangK Θ.A (DecR.wayColl D) (Θ.recK T₀ T₁ oK) Y
  /-- the entry's language -/
  langE : ∀ T₀ T₁ oE Y₀ Y₁, (Θ.E T₀ T₁).Lang oE [Y₀, Y₁] →
    DecR.LangE (DecR.wayColl D) (Θ.recE₀ T₀ T₁ oE) (Θ.recE₁ T₀ T₁ oE) Y₀ Y₁
  /-- the proof's language -/
  langF : ∀ T₀ T₁ oF Y, (Θ.F T₀ T₁).Lang oF [Y] →
    DecR.LangP Θ.A (DecR.wayColl D) (Θ.xOf T₀ T₁ oF) (Θ.recF T₀ T₁ oF) Y
  /-- the key's checker answers the public strings by its tables -/
  deafK : ∀ T₀ T₁ g d, ((Θ.K T₀ T₁).chk d).det (over (Θ.S₀ ∪ Θ.S₁ T₀) (mergeT Θ.S₀ T₀ T₁) g) =
    ((Θ.K T₀ T₁).chk d).det g
  /-- the entry's -/
  deafE : ∀ T₀ T₁ g d, ((Θ.E T₀ T₁).chk d).det (over (Θ.S₀ ∪ Θ.S₁ T₀) (mergeT Θ.S₀ T₀ T₁) g) =
    ((Θ.E T₀ T₁).chk d).det g
  /-- the proof's -/
  deafF : ∀ T₀ T₁ g d, ((Θ.F T₀ T₁).chk d).det (over (Θ.S₀ ∪ Θ.S₁ T₀) (mergeT Θ.S₀ T₀ T₁) g) =
    ((Θ.F T₀ T₁).chk d).det g
  /-- a clash in the checkers' logs has probability at most bC t, for every maker of files -/
  clash : ∀ T₀ T₁ (γ' : Type) (A : OComp (rom 256) γ') (f : γ' → Files) (t : ℕ), A.QueryBound t →
    Rom.Pr A.withTrace (fun g => {x | Θ.ClashB T₀ T₁ g (f x.1)}) ≤ bC t
  /-- the checkers' logs are deaf to the public strings too -/
  deafC : ∀ T₀ T₁ g d, Θ.ClashB T₀ T₁ (over (Θ.S₀ ∪ Θ.S₁ T₀) (mergeT Θ.S₀ T₀ T₁) g) d →
    Θ.ClashB T₀ T₁ g d
  /-- no key's string is a public string -/
  apart : ∀ k s, idCode k = some s → s ∉ Θ.S₀ ∧ ∀ T₀, s ∉ Θ.S₁ T₀
  /-- the files' key has the right shape -/
  keyOK : ∀ T₀ T₁ d, Θ.okKey (Θ.key T₀ T₁ d)
  /-- off a log without a clash the key's part reads the one written reading -/
  rawTie : ∀ T₀ T₁ d σ cm, NoClash σ → (Θ.K T₀ T₁).raw σ cm = Θ.rawU (Θ.key T₀ T₁ d) σ cm
  /-- the written reading does not see the entries at public strings -/
  rawOff : ∀ S k σ cm, (S = Θ.S₀ ∨ ∃ T₀, S = Θ.S₁ T₀) → Θ.rawU k (offSet S σ) cm = Θ.rawU k σ cm
  /-- every property of a key's record under the oracle is a measurable set of oracles -/
  measR : ∀ k (Q : D.Rec → Prop), MeasurableSet {g | ∃ rec, Θ.recU g k = some rec ∧ Q rec}

/-! ## 4. (b): what the link at acceptance asks of each part, at ONE hash -/

/-- What the program hands from stage to stage, as the parts see it: the two keys (shape,
configuration digest, table: root and answers): the first table's and the copy's. -/
structure Hand where
  /-- the first table's key -/
  k₀ : IdKey
  /-- the copy's key -/
  k₁ : IdKey

/-- (b) for the ID and the two plain readers: the keys read off the files are the hand's, and the ID
is H's value at the first key's string. -/
def LinkId (H : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) (h : Hand) : Prop :=
  Θ.key (Θ.pub₀ H) (Θ.pub₁ H) d = h.k₀ ∧ Θ.keyC (Θ.pub₀ H) (Θ.pub₁ H) d = h.k₁ ∧
    ∃ s, idCode h.k₀ = some s ∧ H () s = id

/-- (b) for the key file: at H's own values its checker returns, with the first key's root and its
record under H. -/
def LinkK (H : Fam (rom 256)) (d : Files) (h : Hand) : Prop :=
  ∃ oK, ((Θ.K (Θ.pub₀ H) (Θ.pub₁ H)).chk d).det H = some oK ∧
    (Θ.K (Θ.pub₀ H) (Θ.pub₁ H)).roots oK = [Run.bytesToDig h.k₀.2.2.root] ∧
    Θ.recU H h.k₀ = some (Θ.recK (Θ.pub₀ H) (Θ.pub₁ H) oK)

/-- (b) for the entry file: both roots, both records. -/
def LinkE (H : Fam (rom 256)) (d : Files) (h : Hand) : Prop :=
  ∃ oE, ((Θ.E (Θ.pub₀ H) (Θ.pub₁ H)).chk d).det H = some oE ∧
    (Θ.E (Θ.pub₀ H) (Θ.pub₁ H)).roots oE =
      [Run.bytesToDig h.k₀.2.2.root, Run.bytesToDig h.k₁.2.2.root] ∧
    Θ.recU H h.k₀ = some (Θ.recE₀ (Θ.pub₀ H) (Θ.pub₁ H) oE) ∧
    Θ.recU H h.k₁ = some (Θ.recE₁ (Θ.pub₀ H) (Θ.pub₁ H) oE)

/-- (b) for the proof file: the copy's root and record, and the instance. -/
def LinkF (H : Fam (rom 256)) (d : Files) (h : Hand) : Prop :=
  ∃ oF, ((Θ.F (Θ.pub₀ H) (Θ.pub₁ H)).chk d).det H = some oF ∧
    (Θ.F (Θ.pub₀ H) (Θ.pub₁ H)).roots oF = [Run.bytesToDig h.k₁.2.2.root] ∧
    Θ.recU H h.k₁ = some (Θ.recF (Θ.pub₀ H) (Θ.pub₁ H) oF) ∧
    Θ.xOf (Θ.pub₀ H) (Θ.pub₁ H) oF = Θ.xReq d

/-- (b) FROM ITS FOUR PIECES: by the definition of the verifier on bytes. No piece names
another's checker. The readers of the two keys are opened by the first alone; the proof's piece
reads the instance off request and reply. What they share is the hand. -/
theorem verifyB_of_links (H : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) (h : Hand)
    (hI : Θ.LinkId H id d h) (hK : Θ.LinkK H d h) (hE : Θ.LinkE H d h) (hF : Θ.LinkF H d h) :
    Θ.VerifyB H id d = true := by
  obtain ⟨k0, k1, hs⟩ := hI
  obtain ⟨oK, cK, rK, eK⟩ := hK
  obtain ⟨oE, cE, rE, e0, e1⟩ := hE
  obtain ⟨oF, cF, rF, eF, xF⟩ := hF
  refine (Θ.verifyB_iff H id d).2 (Or.inl ?_)
  unfold Accepts
  rw [k0, k1]
  exact ⟨hs, oK, oE, oF, cK, cE, cF, rK, rE, rF, eK, e0, e1, eF, xF⟩

/-- The same where a piece may fail at a clash: each of the three files' pieces holds, or the
files themselves show a clash. -/
theorem verifyB_of_links_or (H : Fam (rom 256)) (id : ZKCP.Digest 256) (d : Files) (h : Hand)
    (hI : Θ.LinkId H id d h) (hK : Θ.LinkK H d h ∨ Θ.ClashB (Θ.pub₀ H) (Θ.pub₁ H) H d)
    (hE : Θ.LinkE H d h ∨ Θ.ClashB (Θ.pub₀ H) (Θ.pub₁ H) H d)
    (hF : Θ.LinkF H d h ∨ Θ.ClashB (Θ.pub₀ H) (Θ.pub₁ H) H d) : Θ.VerifyB H id d = true := by
  rcases hK with hK | hc
  · rcases hE with hE | hc
    · rcases hF with hF | hc
      · exact Θ.verifyB_of_links H id d h hI hK hE hF
      · exact (Θ.verifyB_iff H id d).2 (Or.inr hc)
    · exact (Θ.verifyB_iff H id d).2 (Or.inr hc)
  · exact (Θ.verifyB_iff H id d).2 (Or.inr hc)

end Three

/-- (a) FOR ALL CONFIGURATIONS THAT ARE IN ORDER: the three parts are made AT a configuration,
which is bound outside the probability: fixed before the oracle is drawn. -/
def SoundAll (Std : Cfg → Prop) (Θ₀ : Cfg → Three D Xi) (e : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ cfg, Std cfg → (Θ₀ cfg).SoundB e

/-! ## 5. What is delivered for one file: a part of the second compiler, at all tables -/

/-- One file's part, as it is made: at each pair of tables a part of the compiler under
OnBytes/TypedOracleCompiler/ (interface, wiring, judge, error, implementation, checker, roots, counts), what is to
be asked first among its typed oracles, and a bound on that. -/
structure FileSpec where
  /-- the part, its checker not yet answered by the tables -/
  part : Tab → Tab → TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX
  /-- what is asked first -/
  pre : ∀ T₀ T₁, (o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (part T₀ T₁).W.K (part T₀ T₁).L).ι) →
    (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (part T₀ T₁).W.K (part T₀ T₁).L).Dom o →
    TypedOracleCompiler.Compile.Batch.TypedOracleComputation 256 (part T₀ T₁).W.K (part T₀ T₁).L Unit
  /-- a bound on its queries -/
  n : ℕ

namespace FileSpec
variable (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))

/-- The part over the one oracle: its checker answers the public strings by the tables; the count is
multiplied by 1 + n; the guard's term is added. -/
noncomputable def toO (T₀ T₁ : Tab) : PartO 256 Files Run.PQ.SgX :=
  { ((φ.part T₀ T₁).on (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁)).toOAsk φ.n with
    bound := fun t => (((φ.part T₀ T₁).on (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁)).toOAsk φ.n).bound t +
      (((t + (φ.part T₀ T₁).tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 }

/-- WHAT IS TO BE DELIVERED FOR A FILE, clause by clause, each under its kind. `rd`:
the one written reading of a raw string off a log, at the tables' configuration; b: one expression
for the bound at all tables. -/
structure Delivers (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX)
    (b : ℕ → ℝ≥0∞) : Prop where
  /-- SOUNDNESS: the analysis' conclusion on the compiled verifier, for traces that ask first -/
  judge : ∀ T₀ T₁, TypedOracleCompiler.Slice.JudgeAtAsk (φ.part T₀ T₁).W (φ.part T₀ T₁).J (φ.part T₀ T₁).e
    (φ.pre T₀ T₁)
  /-- with the judge: what is asked first is asked without coins -/
  preNoCoin : ∀ T₀ T₁ o q, (φ.pre T₀ T₁ o q).NoCoin
  /-- with at most n queries -/
  preQueries : ∀ T₀ T₁ o q, (φ.pre T₀ T₁ o q).QueryBound φ.n
  /-- and unseen by the judge's reading -/
  blind : ∀ T₀ T₁ F tr cm, (φ.part T₀ T₁).J.R.at (φ.part T₀ T₁).W (lenB (φ.pre T₀ T₁) F tr) cm =
    (φ.part T₀ T₁).J.R.at (φ.part T₀ T₁).W tr cm
  /-- THE PAGE: a leaf's and a vertex's answer is one block, taken as it is -/
  one : ∀ T₀ T₁, TypedOracleCompiler.Run.OneBlock (φ.part T₀ T₁).m
  /-- off a log without a clash the part reads the one written reading: so all parts read one raw
  string -/
  reads : ∀ T₀ T₁ σ, NoClash σ → ∀ cm, (φ.part T₀ T₁).raw σ cm = rd T₀ T₁ σ cm
  /-- THE NUMBERS: one expression bounds the bound at all tables -/
  flat : ∀ T₀ T₁ t, (φ.toO S₀ S₁ T₀ T₁).bound t ≤ b t
  /-- THE TYPING: the checker tosses no coin -/
  noCoin : ∀ T₀ T₁ x, ((φ.part T₀ T₁).chk x).NoCoin
  /-- it asks at most tR strings -/
  queries : ∀ T₀ T₁ x, ((φ.part T₀ T₁).chk x).QueryBound (φ.part T₀ T₁).tR
  /-- at most a roots are read off the files -/
  few : ∀ T₀ T₁ x, ((φ.part T₀ T₁).rts x).length ≤ (φ.part T₀ T₁).a
  /-- the roots of what it returns are among these -/
  named : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : (φ.part T₀ T₁).Out),
    ((φ.part T₀ T₁).chk x).det g = some o → ∀ r ∈ (φ.part T₀ T₁).J.roots o, r ∈ (φ.part T₀ T₁).rts x
  /-- FIT: where no two strings of the checker's own log, off the public strings, have one answer:
  the compiled verifier accepts what the checker returns under the oracle with the tables, under the
  family read out of the oracle through the page -/
  fit : ∀ T₀ T₁ (g : Fam (rom 256)) (x : Files) (o : (φ.part T₀ T₁).Out),
    NoClash (offSet (S₀ ∪ S₁ T₀)
      ((φ.part T₀ T₁).toO.ownLog (over (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) g) x)) →
    ((φ.part T₀ T₁).chk x).det (over (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) g) = some o →
    ((φ.part T₀ T₁).J.run o).det (readBlocks (φ.part T₀ T₁).m g) = true ∧ (φ.part T₀ T₁).J.ok o

/-- Then the file's part has what the join asks of every part, at all tables. -/
theorem Delivers.ok {φ : FileSpec} {S₀ : Finset (List Bool)} {S₁ : Tab → Finset (List Bool)}
    {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX} {b : ℕ → ℝ≥0∞}
    (h : φ.Delivers S₀ S₁ rd b) (T₀ T₁ : Tab) : (φ.toO S₀ S₁ T₀ T₁).OK :=
  (φ.part T₀ T₁).on_toOAsk_ok_of_fit (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) (φ.pre T₀ T₁) φ.n
    (h.judge T₀ T₁) (h.preNoCoin T₀ T₁) (h.preQueries T₀ T₁) (h.blind T₀ T₁) (h.one T₀ T₁)
    (h.noCoin T₀ T₁) (h.queries T₀ T₁) (h.few T₀ T₁) (h.named T₀ T₁) (h.fit T₀ T₁)

/-- A part so made is deaf to the oracle at the public strings, once for all: its checker
answers them by the tables. -/
theorem toO_deaf (T₀ T₁ : Tab) (g : Fam (rom 256)) (d : Files) :
    ((φ.toO S₀ S₁ T₀ T₁).chk d).det (over (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) g) =
      ((φ.toO S₀ S₁ T₀ T₁).chk d).det g := by
  show (OnBytes.Slice.pinOn (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) ((φ.part T₀ T₁).chk d)).det _ =
    (OnBytes.Slice.pinOn (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) ((φ.part T₀ T₁).chk d)).det g
  rw [OnBytes.Slice.det_pinOn, OnBytes.Slice.det_pinOn]
  congr 1
  funext o s
  cases o
  by_cases hs : s ∈ S₀ ∪ S₁ T₀
  · rw [OnBytes.Slice.over_mem _ _ hs, OnBytes.Slice.over_mem _ _ hs]
  · rw [OnBytes.Slice.over_not_mem _ _ hs, OnBytes.Slice.over_not_mem _ _ hs]

end FileSpec

end OnBytes.Slice.Shapes
