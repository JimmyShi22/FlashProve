-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryTypE.lean: the entry's typing, whole.

It is the asking half (OnBytes/Tie/EntryAsked.lean: the twin of `Entry.read`, asking; both tables'
seeds, asked) and then the plain map `assembleEZ` (OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean), at the type
that `entrySpec` takes (OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean), for any x : EntryAt AnsT lg s d₁.
Here AnsT := List (UInt64 × UInt64 × UInt64): answers as the lists of triples that the statement
spells. It is the page's An := List T3, by unfolding.

The parameters under which the file is read (`qOf`) and the first table (`firstOf`) are arguments of
their own: that x.D is the description of that reading is needed in proofs alone, in no type. The
instance: both tables' answers as triples; both tables' seeds through `seedOf`.

Not claimed. No decision is taken. Values alone. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.TypedOracleCompiler.Slice.EntryData
import OnBytes.Tie.EntryAsked

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice

open Rom TypedOracleCompiler.Run
open OnBytes.Slice (Tab seedOf seedEntry)
open OnBytes.Slice.Shapes (Files)
open OnBytes.Tie (AskedE askedAt typedER typedER_det)

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}

/-- The instance that the typing makes of what was asked. -/
def xOfAsked (lg s : ℕ) (a : AskedE) : XE AnsT lg s :=
  ((a.first.answers.map OnBytes.E.triple, a.further.answers.map OnBytes.E.triple),
    (seedOf lg s a.l0, seedOf lg s a.l1))

/-- The plain half, at the judge's type: `assembleEZ` at the two roots, that instance and what
was read. -/
def asmE (x : EntryAt AnsT lg s d₁) (a : AskedE) : Option (OutE x.Z) :=
  assembleEZ x.D x.dec x.B x.E (earlyTwo d₁) (TSE x.D (seedEntry lg s)) (wTSE x.D (seedEntry lg s))
    (embST x.D.C (seedEntry lg s) _) (prjST x.D.C (seedEntry lg s) _)
    a.first.root a.further.root (xOfAsked lg s a) a.out

/-- THE ENTRY's TYPING. -/
def typE (Θ : Tab → Tab → EntryAt AnsT lg s d₁) (qOf : Tab → OnBytes.Params.Link)
    (firstOf : Tab → ByteArray → OnBytes.Params.TableName) :
    ∀ T₀ T₁, Files → OComp (rom 256) (Option (OutE (Θ T₀ T₁).Z)) :=
  fun T₀ T₁ d => typedER (asmE (Θ T₀ T₁)) (qOf T₀) (firstOf T₀ d.key) d.ent

variable (Θ : Tab → Tab → EntryAt AnsT lg s d₁) (qOf : Tab → OnBytes.Params.Link)
  (firstOf : Tab → ByteArray → OnBytes.Params.TableName)

omit [DecidableEq (Sd1 lg s)] in
/-- Its value at every oracle: the plain asking at the function that the oracle induces, then
the plain map. NO HYPOTHESIS. -/
theorem typE_det (g : Fam (rom 256)) (T₀ T₁ : Tab) (d : Files) :
    (typE Θ qOf firstOf T₀ T₁ d).det g =
      (askedAt (_root_.Run.oB (g ())) (qOf T₀) (firstOf T₀ d.key) d.ent).bind (asmE (Θ T₀ T₁)) :=
  typedER_det _ g _ _ _

omit [DecidableEq (Sd1 lg s)] in
/-- What it returns comes from something asked. -/
theorem typE_some {g : Fam (rom 256)} {T₀ T₁ : Tab} {d : Files} {o : OutE (Θ T₀ T₁).Z}
    (h : (typE Θ qOf firstOf T₀ T₁ d).det g = some o) :
    ∃ a, askedAt (_root_.Run.oB (g ())) (qOf T₀) (firstOf T₀ d.key) d.ent = some a ∧
      asmE (Θ T₀ T₁) a = some o := by
  rw [typE_det] at h
  exact Option.bind_eq_some_iff.1 h

omit [DecidableEq (Sd1 lg s)] in
/-- The roots of what it returns are the two tables' roots, as digests. -/
theorem asmE_roots {x : EntryAt AnsT lg s d₁} {a : AskedE} {o : OutE x.Z}
    (h : asmE x a = some o) :
    o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] :=
  assembleE_roots h

omit [DecidableEq (Sd1 lg s)] in
/-- The instance in what it returns is the one made of what was asked. -/
theorem asmE_x {x : EntryAt AnsT lg s d₁} {a : AskedE} {o : OutE x.Z}
    (h : asmE x a = some o) : o.2.1 = xOfAsked lg s a :=
  assembleE_x h

end TypedOracleCompiler.Slice
