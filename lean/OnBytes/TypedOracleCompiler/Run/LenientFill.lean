-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LenientFill.lean: a lenient converter's last step: the library's lenient reader
(Run/ParseLaxX.lean: cutChainX: it cuts the file, recomputes the chain, tests no work, walks no
path, compares no root) hands out openings without a record of vertices; here each opening gets its
record by hashing, and nothing is compared. So the typings that look whole paths up in an opening's
own record (Slice/EntryTyping.lean: assembleS; Slice/Batch3STyping.lean) can be fed from the lenient
reader. Definitions that compute; one law. Untrusted by design: a converter stands before the
verifier. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.
Why: with the port's strict reader as the converter every damaged file of a test dies at the
converter: the untrusted stage alone is tested. The whole paths may be made by hashing in the
converter (it is untrusted: any way that gives the honest file its yes will do).
  fillO h cfg start y  an opening y = (form, list, what was read): its "seen" := the library's
      metAll … ++ noteAll … (Run/WalkPaths.lean): all that the pruned walk from the leaves' digests
      at "start" passes and notes: computed, compared with nothing; its "root" stays what the
      lenient reader noted (the root sent | the statement's)
  fillC h cfg o  every opening of every round: start := cfg where the form says "stored", else the
      chain's run value
  lenientX h S b i  cutChainX at Id and h, then fillC at S.base.cfg: Option (ChainOut × ℕ) (the
      place behind the chain: whether bytes are left over is the caller's to test or not)
  fillO_read  completeness, opening by opening: if the format's strict reader of an opening returns
      oo, then fillO of any opening with oo's columns, salts and given digests has oo's record (the
      library's reader_seen)
What the lenient reader still refuses (its own head): a description that is not admissible; a file
that cannot be cut; a query that the format does not allow (askOK); a run value of 32 zero bytes.
What is not said. That lenientX returns what the strict reader returns on an honest file, as a whole
(the library's laxX_reads says it but for the record; fillO_read gives the record: not joined).
Nothing on what a verifier behind it says. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.ParseLaxX
import Run.WalkPaths

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open _root_.Run.WalkTie Octopus

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- an opening gets its record of vertices, by hashing -/
def fillO (cfg start : ByteArray) (y : _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut) :
    _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut :=
  let oo : _root_.Fmt.OpenOut := y.2.2
  let lv := leafV h y.1 start y.2.1 (oo.cols.zip oo.salts)
  (y.1, y.2.1, { oo with seen := metAll (fun l r => h 166 0 0 cfg (l ++ r)) y.1.a y.2.1 lv oo.given ++ noteAll y.1.a y.2.1 oo.given })

/-- every opening of every round -/
def fillC (cfg : ByteArray) (o : _root_.Fmt.ChainOut) : _root_.Fmt.ChainOut :=
  let run := o.run.getD ByteArray.empty
  { o with rounds := o.rounds.map fun r =>
      { r with opens := r.opens.map fun y => fillO h cfg (if y.1.stored then cfg else run) y } }

/-- The lenient reader, with records. -/
def lenientX (S : _root_.Fmt.SpecX) (b : ByteArray) (i : ℕ) : Option (_root_.Fmt.ChainOut × ℕ) :=
  (_root_.Run.cutChainX (m := Id) h S b i).map fun z => (fillC h S.base.cfg z.1, z.2)

/-- Completeness, opening by opening. -/
theorem fillO_read (cfg : ByteArray) (f : _root_.Fmt.Fld) (salt : ℕ) (sh : _root_.Fmt.Shape)
    (start : ByteArray) (xs : List ℕ)
    (b : ByteArray) (i : ℕ) (oo oo' : _root_.Fmt.OpenOut)
    (e : _root_.Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some oo)
        (hc : oo'.cols = oo.cols)
    (hs : oo'.salts = oo.salts) (hg : oo'.given = oo.given) :
        (fillO h cfg start (sh, xs, oo')).2.2.seen = oo.seen := by
  obtain ⟨-, -, -, -, -, r5⟩ := reader_seen h cfg f salt sh start xs b i oo e
  show metAll _ sh.a xs (leafV h sh start xs (oo'.cols.zip oo'.salts)) oo'.given ++ noteAll sh.a
      xs oo'.given = _
  rw [hc, hs, hg, r5]

end

end TypedOracleCompiler.Run
