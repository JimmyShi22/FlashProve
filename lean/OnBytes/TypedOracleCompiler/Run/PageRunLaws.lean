-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageRunLaws.lean: what the program of OnBytes/TypedOracleCompiler/Run/PageRun.lean is: the family
that a page-made encoding reads out of a hash function, at every oracle but the spare one; and so an
algorithm that never asks the spare oracle has, run through the encoding over one hash function g,
the value that it has under `famRun`.

Statements with their proofs, at every page C, every hash function g, every query. The program's
first argument, the interface behind a function of Unit, is `fun _ => L` throughout and is left out
in this list.
  `strR_eq`, `strG_eq`   the strings are the page's total code's (`totalG`, PageG.lean).
  `strR_some`            where `put` writes, the string is what it writes.
  `codeRun_eq`           at o ≠ `OracleName.other`:
                         `codeRun C.real.put C.back.put o q j = (implG C).code o q j`.
  `famRun_eq`            at o ≠ `OracleName.other`: `famRun .. g o q = readBlocks (implG C) g o q`.
  `det_famRun`           for c that on every path asks no query at `OracleName.other`:
                         `(c.overOne (implG C)).det g = c.det (famRun C.real.put C.back.put g)`.
  `det_famRun_of`        the same at `implOf put inj hd back` (PageOf.lean), whose parser is taken
                         by choice: of the encoding's four parts the right side names `put`
                         and `back.put` alone.
  `det_congr_asksIn`     two families that agree wherever an algorithm may ask give it one value.
"Value" is `OComp.det` (Rom/Cache.lean): the run in which every coin is 0.
The same of the proof's arm: Johnson/TypedOracleCompiler/RecCompile/ProofAnsRun.lean [not in this library; so here
read: not proved in this library].

What it is for. It takes the parser out of a run's way, and no more. The left sides have no code
where the page's parser has none. The right sides are made of the algorithm, `OComp.det`, the
interface behind `fun _ => ..`, `put`, `back.put` and the hash function g: they have code where ALL
of these have. At an interface that has none the right side has no code either: there a second
bridge, to an interface with code, is owed. The equations hold at every input, an honest file's or
not, and ask no test at run time.

Not claimed. That `put` or `back.put` has code at any value. BOTH SIDES OF AN EQUATION STAND AT ONE
INTERFACE AND ONE NUMBER OF BLOCKS: a run of the right side's text at another interface, one that
has code, is a term of another type, and these laws say nothing of it. That a run ends in bearable
time. Nothing at the spare oracle. Nothing under a probability. Nothing on soundness.

-/
import OnBytes.TypedOracleCompiler.Run.PageRun
import OnBytes.TypedOracleCompiler.Run.PageOf
import Run.DetOverOne
import Rom.SigmaExits

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageRun
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

section
variable (C : Page L K)

/-- The string of a real point is the page's total code's. -/
theorem strR_eq (a : RealPts 256 K L) :
    strR (fun _ => L) C.real.put C.back.put a = (totalG C).put (.inl a) := by
  unfold strR
  cases h : C.real.put a with
  | some s => exact (totalG_real C a s h).symm
  | none => exact (totalG_none C a h).symm

/-- Where `put` writes, the string is what it writes. -/
theorem strR_some (put : RealPts 256 K L → Option (List Bool)) (bk : AllPts 256 K L → List Bool)
    (a : RealPts 256 K L) (s : List Bool) (h : put a = some s) :
    strR (fun _ => L) put bk a = s := by
  unfold strR
  rw [h]

/-- The string of a ghost point is the page's total code's. -/
theorem strG_eq (a : GhostPts 256 K L) : strG (fun _ => L) C.back.put a = (totalG C).put (.inr a) :=
  (totalG_ghost C a).symm

/-- **The strings are the encoding's, at every oracle but the spare one.** -/
theorem codeRun_eq : ∀ (o : OracleName), o ≠ OracleName.other → ∀ (q : domOf 256 L o) (j : Fin (blk K o)),
    codeRun (fun _ => L) C.real.put C.back.put o q j = (implG C).code o q j
  | .leaf, _, q, _ => strR_eq C (.inl q)
  | .node, _, q, _ => strR_eq C (.inr (.inl q))
  | .rleaf, _, q, _ => strR_eq C (.inr (.inr (.inl q)))
  | .rnode, _, q, _ => strR_eq C (.inr (.inr (.inr (.inl q))))
  | .fb t, _, q, j => strR_eq C (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))
  | .g t, _, q, _ => strR_eq C (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩)))))
  | .ann, _, _, j => j.elim0
  | .other, h, _, _ => (h rfl).elim
  | .fbw t k, _, q, j => strG_eq C ⟨t, k, q, j⟩

/-- Two families that agree wherever an algorithm may ask give it one value. (Said also, as
`det_congr_of_asksIn`, in Johnson/Thin/Link/AsksDet.lean, in a directory that the files under
OnBytes/ may not import: scripts/IMPORTS.txt.) -/
theorem det_congr_asksIn {S : OSpec} {α : Type} {P : (o : S.ι) → S.Dom o → Prop} {g g' : Fam S}
    (h : ∀ o q, P o q → g o q = g' o q) : ∀ {c : OComp S α}, c.AsksIn P → c.det g = c.det g'
  | .pure _, _ => rfl
  | .sample _ k, hc => det_congr_asksIn h (c := k 0) (hc 0)
  | .query o q k, hc => by
    show (k (g o q)).det g = (k (g' o q)).det g'
    rw [h o q hc.1]
    exact det_congr_asksIn h (hc.2 _)

variable (g : Fam (rom 256))

/-- **The family is what the encoding reads out of g, at every oracle but the spare one.** -/
theorem famRun_eq (o : OracleName) (ho : o ≠ OracleName.other) (q : domOf 256 L o) :
    famRun (fun _ => L) C.real.put C.back.put g o q = readBlocks (implG C) g o q :=
  congrArg (rngEquiv 256 K o).symm (funext fun j => congrArg (g ()) (codeRun_eq C o ho q j))

/-- **An algorithm that never asks the spare oracle: its value through the encoding over g is its
value under the family.** -/
theorem det_famRun {α : Type} (c : OComp (typedOracleFamily 256 K L) α)
    (h : c.AsksIn fun o _ => o ≠ OracleName.other) :
    (c.overOne (implG C)).det g = c.det (famRun (fun _ => L) C.real.put C.back.put g) := by
  rw [det_overOne]
  exact (det_congr_asksIn (fun o q ho => famRun_eq C g o ho q) h).symm

end

/-- **The same at the encoding of a function that is one to one where it writes and none of whose
strings begins with a byte other than 0 and 1**: of the encoding's four parts the right side names
the function and the total code's writing side alone. -/
theorem det_famRun_of (put : RealPts 256 K L → Option (List Bool))
    (inj : ∀ a b s, put a = some s → put b = some s → a = b)
    (hd : ∀ a s, put a = some s → ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s)
    (back : StrCode (AllPts 256 K L)) (g : Fam (rom 256)) {α : Type}
    (c : OComp (typedOracleFamily 256 K L) α) (h : c.AsksIn fun o _ => o ≠ OracleName.other) :
    (c.overOne (implOf put inj hd back)).det g = c.det (famRun (fun _ => L) put back.put g) :=
  det_famRun (pageOf put inj hd back) g c h

end TypedOracleCompiler.Run.PageRun

#print axioms TypedOracleCompiler.Run.PageRun.strR_some
#print axioms TypedOracleCompiler.Run.PageRun.codeRun_eq
#print axioms TypedOracleCompiler.Run.PageRun.famRun_eq
#print axioms TypedOracleCompiler.Run.PageRun.det_congr_asksIn
#print axioms TypedOracleCompiler.Run.PageRun.det_famRun
#print axioms TypedOracleCompiler.Run.PageRun.det_famRun_of
