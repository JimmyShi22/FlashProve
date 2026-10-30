-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean: the check of an entry file on plain data with the hash
function an argument, and that at every hash function its yes is a yes of the checker of the entry's
part.

Definitions, and statements with their proofs. `verifyE` (OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean) tests
a value that an untrusted converter has made of the key file and the entry file
(`OnBytes.Tie.AskedE`: plain data) at one fixed function, and takes the digest of the three public
files from the statement. Here its first three clauses stand with the function a letter g : `Fam
(rom 256)`, and both digests that the page holds are asked of g. The fourth clause, the comparison
of the commitment ID, is not taken over: it hashes at the format's own hash.

Main names (namespace `TypedOracleCompiler.Slice`):
  `entryPartG G hok c hc pd a g` : Bool: the pins fit the description at c; the chain as read gives
    a typed string; `whyOutE` says "YES" under `EntryRunTop.famOfG … pd g`
    (OnBytes/TypedOracleCompiler/Slice/EntryRunG.lean).
  `verifyE_split`: `verifyE` is `entryPartG` at `Run.oBits` and the format's own digest of the
    parameter bytes, and the comparison of the ID.
  `verifyEntryG G hok cfg a g` : Bool: `entryPartG` with c the digest that g gives of the three
    public files cfg, and pd g's answer at the string of the parameter bytes at c.
  `verifyEntryG_iff`: at every g, a and all files d: it says yes exactly if the pins fit and the
    checker "convert; two roots; the judge's run" of the entry's part `homeOf G hok eM`, at the
    converter that hands over a whatever the files are (`valueOf`), returns a value under g. By
    `HomeData.chk_iff_whyG`.

Limits.
  1. G, hok and eM are letters. A bound over a random function is proved of the checker at two
     written grounds: `full_one_world`, `small_one_world` (OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean,
     EntrySmallTop.lean), whose parts are `homeOf` at these grounds by `homeOf_full`, `homeOf_small`
     (EntryRunAny.lean, EntryRunPlay.lean), each under a hypothesis on codes. What they bound is not
     "a yes on a false statement": the head of OnBytes/TypedOracleCompiler/Slice/EntryOne.lean says what. No bound
     is joined here.
  2. These bounds are for a converter that is fixed before the function is drawn, and a maker of
     files. In `verifyEntryG_iff` the converter holds a: so a is fixed before g there. A bound
     against a maker that picks a after its queries wants a converter that reads a off the files, or
     the bound said for makers of such values: neither is here (EntryVerdictRd.lean and
     EntryVerdictBound.lean, in this folder, have them).
  3. No yes is shown here. That the check comes home is a fact of a run, not of this file, and by
     the heads of the files on its walk `whyOutE` does not run at the full size.
  4. The commitment ID is not looked at: what ties the first table to the user's ID is another part.
     The two roots' lengths are not tested: byte strings of several lengths are one typed root.
     The description, the sizes and the decision are the ground's; of the three public files their
     digest alone enters. The decision reads the instance, which the converter hands over.
  5. A yes is a yes of the value a, not of any file. One file of three; Link's compiled verifier
     without the strict format, behind the seeds' comparison, which is written by hand. The compiler
     under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
     definitions of Compile/.
     All that the heads of EntryVerdict.lean and EntryRunG.lean do not claim.
     No probability stands here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdict
import OnBytes.TypedOracleCompiler.Slice.EntryRunG

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The check of an entry file on plain data, the hash function an argument: `verifyE`'s first three
clauses, at a digest c of the three public files, a digest pd of the parameter bytes and a function
g: the pins fit the description at c; the chain as read gives a typed string; the run's function
says "YES" on the typed value under the family that a run evaluates at pd and g. The commitment ID
is not looked at. -/
def entryPartG (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE) (g : Fam (rom 256)) :
    Bool :=
  pinsFit (entryXD G c) G.q.link.table &&
    match assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => false
    | some π =>
      whyOutE (entryXD G c) (hok c hc) (d1Run _ _) _
        (EntryRunTop.famOfG (entryXD G c) hc (d1Run _ _) G.q.link.table pd g)
        [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
        (xOfAskedC _ _ a) π == "YES"

/-- `verifyE` is that check at the realised oracle and the format's own digest of the parameter
bytes, and the comparison of the commitment ID. -/
theorem verifyE_split (x : EntryStmt) (a : AskedE) :
    verifyE G hok x a =
      (entryPartG G hok x.c x.hc (EntryRunTop.pdOf (entryXD G x.c)) a _root_.Run.oBits &&
        (stmtId G.q.link.table x.c (_root_.Run.bytesToDig a.first.root)
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1 == x.id)) := by
  unfold verifyE entryPartG
  rw [EntryRunTop.famOfG_oBits]
  cases assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
  | none => simp
  | some π => simp only [Bool.and_assoc]

/-- The check with both digests asked of g itself: c is g's digest of the three public files, pd g's
answer at the string of the parameter bytes at c. cfg: the three public files; a: what a converter
has handed over. -/
def verifyEntryG (cfg : Cfg) (a : AskedE) (g : Fam (rom 256)) : Bool :=
  entryPartG G hok (dgOf cfg (own₀ (pubS₀ cfg) g)) (dgOf_size cfg (own₀ (pubS₀ cfg) g))
    (own₁ (pubS₀ cfg) (pubS₁ [G.bytesAt] cfg) g (s0Of (G.bytesAt (dgOf cfg (own₀ (pubS₀ cfg) g)))))
    a g

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- At every g: the check says yes exactly if the pins fit and the checker of the entry's part at
the ground G (`homeOf G hok eM`), at the converter that hands over a whatever the files are, returns
a value under g. -/
theorem verifyEntryG_iff (eM : ℕ) (cfg : Cfg) (a : AskedE) (εs : ℝ≥0∞) (Bk : ℕ)
    (g : Fam (rom 256)) (d : Files) :
    verifyEntryG G hok cfg a g = true ↔
      pinsFit (entryXD G (dgOf cfg (own₀ (pubS₀ cfg) g))) G.q.link.table = true ∧
        ∃ o, ((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (valueOf G hok eM a)) εs
          Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) g)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g)).chk d).det g = some o := by
  unfold verifyEntryG entryPartG
  rw [Bool.and_eq_true]
  refine and_congr_right fun hp => ?_
  have hP : (homeOf G hok eM).PinsAtG G.q.link.table (dgOf cfg (own₀ (pubS₀ cfg) g)) :=
    ⟨rfl, rfl, salt_of_pinsFit _ _ hp, rfl⟩
  have key := fun o => (homeOf G hok eM).chk_iff_whyG cfg
    ((homeOf G hok eM).convOf cfg (valueOf G hok eM a)) εs Bk g d o G.q.link.table hP
    (dgOf_size cfg (own₀ (pubS₀ cfg) g))
  cases has : assembleS (entryXD G (dgOf cfg (own₀ (pubS₀ cfg) g)))
      (decRun (linkAtCfg G.q (dgOf cfg (own₀ (pubS₀ cfg) g))) G.q.link.table.v
        G.q.link.table.cubeBits G.q.link.table.answers) a.out with
  | none =>
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · rintro ⟨o, ho⟩
      have h1 := ((key o).1 ho).1
      have h2 : valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
          (dgOf_size cfg (own₀ (pubS₀ cfg) g)) d = some o := h1
      unfold valueOf at h2
      rw [has] at h2
      cases h2
  | some π =>
    dsimp only
    rw [beq_iff_eq]
    have hv : valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
        (dgOf_size cfg (own₀ (pubS₀ cfg) g)) d =
        some ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
          xOfAskedC _ _ a, ofPS _ _ π) := by
      unfold valueOf
      rw [has]
      rfl
    constructor
    · intro h
      exact ⟨_, (key _).2 ⟨hv, h⟩⟩
    · rintro ⟨o, ho⟩
      obtain ⟨h1, h2⟩ := (key o).1 ho
      have h3 : valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
          (dgOf_size cfg (own₀ (pubS₀ cfg) g)) d = some o := h1
      rw [hv] at h3
      obtain rfl := Option.some.inj h3
      exact h2

end TypedOracleCompiler.Slice
