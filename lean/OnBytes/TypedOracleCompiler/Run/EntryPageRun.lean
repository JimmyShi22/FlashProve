-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryPageRun.lean: THE PAGE OF AN ENTRY's JUDGE AS A TERM THAT LEAN's COMPILER
TAKES: the very implementation `EntryPage.implE`, with the four tests that its partial codes make
given as data; with computable tests. IT IS NOT TO BE EVALUATED: at a made-up description of three
rounds `codeRun` ended "out of memory" (every definition here takes the interface as a value). What
is evaluated is OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean's `famSafe`; this file is the step by which its
equation reaches `implE`.

`EntryPage.implE` (OnBytes/TypedOracleCompiler/Run/EntryPage.lean) is a total one-to-one code of all typed oracle
points as strings. Its partial codes test whether a query's plain part is a fixed one, and whether
the value beside the answers is the fixed one. OnBytes/TypedOracleCompiler/Run/EntryFb.lean makes these four tests
by classical logic: so Lean's compiler refuses `implE`, and nothing else in it (measured: of
twenty-five definitions beneath it the compiler refused the ones that hold such a test, and no
other). Here the definitions are said once more with the tests as data. A test is fixed by its law:
so there is one value of the data, and the implementation with any tests IS `implE`: every theorem
on `implE` speaks of `implT` at any tests. The sibling is a second form of the library's
soundness road, under OnBytes/TypedOracleCompiler/.
 - `Tests D early e dd`: four tests with their laws; `Tests.sub`: any two are equal;
   `Tests.byLogic`: EntryFb.lean's;
 - `e0T`, `fbLinkT`, `u0T`, `u1T`, `fbSeedsT`, `fbAllT`, `realT`, `pageT`, `implT`: EntryFb.lean's
   and EntryPage.lean's definitions at given tests;
 - `pageT_eq`, `implT_eq`: `pageT τ P K V back = pageE P dd K V back` and
   `implT τ P K V back = implE P dd K V back`, for all tests τ;
 - `Tests.run`: computable tests: by the form of a plain part; by a decision of equality on what
   stands in the seeds' place;
 - `codeRun`: the string of a typed query at a block, at the computable tests; `codeRun_eq`: it is
   `implE`'s; `famRun`: the family that is read out of an oracle through the page; `famRun_eq`: it
   is `readBlocks (implE …) g`.

Main definitions: `Tests`, `implT`, `Tests.run`, `codeRun`, `famRun`.
Main theorems: `Tests.sub`, `pageT_eq`, `implT_eq`, `codeRun_eq`, `famRun_eq`.

Not claimed. That Lean's compiler takes `codeRun` and `famRun` is a fact of the build (no
"noncomputable" stands before them), not a theorem. THAT A TERM HAS CODE DOES NOT SAY THAT ITS
EVALUATION ENDS: these do not come home (see above). NOTHING ON SPEED: strings are lists of bits,
and a digest is a function of a bit's number: by the library's own trials
(OnBytes/TypedOracleCompiler/Run/CodingFnThin.lean's head) a family of this form may hash anew for every bit that is
read: `famRun` is the plain term, not the one to run. The pins, the code of leaves and `back` stay
arguments: what runs needs computable ones. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is
the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPage

set_option autoImplicit false

namespace TypedOracleCompiler.Run.EntryPageRun
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.KeyFb (isEq isEq_iff)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry) (dd : Sd)

/-- The four tests that the partial codes make, with their laws. -/
structure Tests where
  /-- is this the fixed plain part of the link's round in front -/
  tL : PlainPart (shE D early e) (annOf (Le D early e) .link) → Bool
  /-- its law -/
  hL : ∀ p, tL p = true ↔ p = p0E D early e
  /-- is this the fixed value beside the answers -/
  tD : Sd → Bool
  /-- its law -/
  hD : ∀ s, tD s = true ↔ s = dd
  /-- is this the fixed plain part of the seeds' protocol's round in front -/
  t0 : PlainPart (shapeOf (Le D early e) .test) (annOf (Le D early e) .test) → Bool
  /-- its law -/
  h0 : ∀ p, t0 p = true ↔ p = p0S (L := Le D early e) .test D.C e _ id
  /-- is this the fixed plain part of the drawing round -/
  t1 : PlainPart (shapeOf (Le D early e) .test) (annOf (Le D early e) .test) → Bool
  /-- its law -/
  h1 : ∀ p, t1 p = true ↔ p = p1S (L := Le D early e) .test D.C e _ id

/-- A test is fixed by its law. -/
theorem test_eq {α : Type} {a : α} {f g : α → Bool} (hf : ∀ x, f x = true ↔ x = a)
    (hg : ∀ x, g x = true ↔ x = a) : f = g :=
  funext fun x => Bool.eq_iff_iff.2 ((hf x).trans (hg x).symm)

/-- Any two values of the data are equal. -/
theorem Tests.sub (τ τ' : Tests D early e dd) : τ = τ' := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd⟩ := τ
  obtain ⟨a', ha', b', hb', c', hc', d', hd'⟩ := τ'
  obtain rfl := test_eq ha ha'
  obtain rfl := test_eq hb hb'
  obtain rfl := test_eq hc hc'
  obtain rfl := test_eq hd hd'
  rfl

/-- EntryFb.lean's tests, by classical logic. -/
noncomputable def Tests.byLogic : Tests D early e dd :=
  ⟨isEq _, isEq_iff _, isEq dd, isEq_iff dd, isEq _, isEq_iff _, isEq _, isEq_iff _⟩

variable {D early e dd} (τ : Tests D early e dd) (P : PinsE D early e) (K : ℕ)

/-- The first value of the link's chain. -/
def e0T : PCode (FbIn 256 (Le D early e) .link) :=
  EntryFirst.firstPE (Le D early e) .link (p0E D early e) τ.tL dd τ.tD P.pd τ.hL τ.hD P.l

/-- What it writes is a string under 160 with the link's label. -/
theorem e0T_is (q : FbIn 256 (Le D early e) .link) (s : List Bool)
    (h : (e0T τ P).put q = some s) : Is160 P.l s :=
  is160_of_hdr _ _ (EntryFirst.firstPE_hdr _ _ _ _ _ _ _ _ _ _ q s h)

/-- The code of chain queries under the link's tag, each with a block. -/
def fbLinkT : PCode (FbIn 256 (Le D early e) .link × Fin (K + 1)) :=
  split (tailP (e0T τ P) K) (e162 P K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ P.hlt s (e0T_is τ P _ s (tailP_put _ K a s h1).1) (e162_is P K b s h2))

/-- The seeds' chain's first value. -/
def u0T : PCode (FbIn 256 (Le D early e) .test) :=
  FirstName.firstPN P.rest (Le D early e) .test (p0S (L := Le D early e) .test D.C e _ id) τ.t0
    FirstName.zeroPd τ.h0 _root_.Fmt.recordLabel

/-- The drawing round. -/
def u1T : PCode (FbIn 256 (Le D early e) .test × Fin (K + 1)) :=
  SeedRound.secondPS (Le D early e) .test (p1S (L := Le D early e) .test D.C e _ id) τ.t1 τ.h1 K

/-! ## They are EntryFb.lean's -/

theorem e0T_eq : e0T τ P = e0 P dd := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

theorem u0T_eq : u0T τ P = u0 P := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

theorem u1T_eq : u1T τ K = u1 K := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

/-- The code of chain queries under the seeds' tag, each with a block. -/
def fbSeedsT : PCode (FbIn 256 (Le D early e) .test × Fin (K + 1)) :=
  split (tailP (u0T τ P) K) (u1T τ K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ (by decide) s
      (u0_is P _ s (by rw [← u0T_eq τ P]; exact (tailP_put _ K a s h1).1))
      (u1_is K b s (by rw [← u1T_eq τ K]; exact h2)))

theorem fbLinkT_eq : fbLinkT τ P K = fbLink P dd K := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

theorem fbSeedsT_eq : fbSeedsT τ P K = fbSeeds P K := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

/-- Chain queries with a block under all tags. -/
def fbAllT : PCode (Σ t : Tag, FbIn 256 (Le D early e) t × Fin (K + 1)) :=
  byTag (fbSeedsT τ P K) (fbLinkT τ P K) (PCode.empty _) (fun _ _ _ _ h => by cases h)
    (fun a b s h1 => by
      rw [fbLinkT_eq]
      exact fbE_apart P dd K a b s (by rw [← fbSeedsT_eq τ P K]; exact h1))
    (fun _ _ _ _ h => by cases h)

theorem fbAllT_eq : fbAllT τ P K = fbAllE P dd K := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

variable (V : Leaves (Le D early e)) (back : StrCode (AllPts 256 K (Le D early e)))

/-- The partial code of the real points. -/
def realT : PCode (RealPts 256 K (Le D early e)) :=
  realOf V P.cfg P.hcfg (fbAllT τ P K) fun b s h =>
    fbAllE_facts P dd K b s (by rw [← fbAllT_eq τ P K]; exact h)

/-- The page's data. -/
def pageT : Page (Le D early e) K :=
  ⟨realT τ P K V, realOf_hd V P.cfg P.hcfg (fbAllT τ P K) _, back⟩

/-- It is `EntryPage.pageE`, for all tests. -/
theorem pageT_eq : pageT τ P K V back = pageE P dd K V back := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

/-- The page at given tests. -/
def implT : OracleCoding (typedOracleFamily 256 K (Le D early e)) 256 := implG (pageT τ P K V back)

/-- IT IS `EntryPage.implE`, FOR ALL TESTS. -/
theorem implT_eq : implT τ P K V back = implE P dd K V back := by
  rw [Tests.sub D early e dd τ (Tests.byLogic D early e dd)]
  rfl

/-! ## Computable tests -/

variable (D early e dd) in
/-- Computable tests: by the form of a plain part; by a decision of equality on what stands in
the seeds' place. -/
def Tests.run [DecidableEq Sd] : Tests D early e dd where
  tL := fun p => match p with
    | .inl (.inr _) => true
    | _ => false
  hL := fun p => by
    rcases p with (p | p) | p
    · constructor <;> intro h <;> cases h
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · constructor <;> intro h <;> cases h
  tD := fun s => decide (s = dd)
  hD := fun _ => decide_eq_true_iff
  t0 := fun p => match p with
    | .inl (.inr _) => true
    | _ => false
  h0 := fun p => by
    rcases p with (p | p) | p
    · constructor <;> intro h <;> cases h
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · constructor <;> intro h <;> cases h
  t1 := fun p => match p with
    | .inr (.inl (.inr _)) => true
    | _ => false
  h1 := fun p => by
    rcases p with (p | p) | (p | p) | p
    · constructor <;> intro h <;> cases h
    · constructor <;> intro h <;> cases h
    · constructor <;> intro h <;> cases h
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact p.elim

variable [DecidableEq Sd] (dd)

/-- The string of a typed query at a block, as a term with code. Not to be evaluated: see the
file's head. -/
def codeRun (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (Le D early e) o)
    (j : Fin (blk K o)) : List Bool :=
  (implT (Tests.run D early e dd) P K V back).code o q j

/-- It is the page's. -/
theorem codeRun_eq (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (Le D early e) o)
    (j : Fin (blk K o)) : codeRun dd P K V back o q j = (implE P dd K V back).code o q j := by
  show (implG (pageT (Tests.run D early e dd) P K V back)).code o q j =
    (implG (pageE P dd K V back)).code o q j
  rw [pageT_eq]

/-- The family that is read out of an oracle through the page, as a term with code. Not to be
evaluated: see the file's head. -/
def famRun (g : Fam (rom 256)) : Fam (typedOracleFamily 256 K (Le D early e)) :=
  readBlocks (implT (Tests.run D early e dd) P K V back) g

/-- It is the family through `EntryPage.implE`. -/
theorem famRun_eq (g : Fam (rom 256)) :
    famRun dd P K V back g = readBlocks (implE P dd K V back) g := by
  unfold famRun
  rw [implT_eq]

end TypedOracleCompiler.Run.EntryPageRun
