-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/JudgeNoOther.lean: the run of the one judge for three files, with the lax or the
strict verifier, never asks the spare oracle: the road's half of the clause `clean` of a part made
by the way "type, then run".

A part made by the way "type, then run" (OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean) owes `clean`: no typed
query of the judge's run has a public string. `clean_of_noOther` there splits it: the run never asks
the spare oracle; every public string is a point of the spare oracle.
OnBytes/TypedOracleCompiler/Compile/Batch/NoOther.lean says the first of the compiled verifiers and of a chain. The
judge's run (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean: `judgeRunEL`, `judgeRunE`) is the seeds' chain once for
each outer root, with a comparison, and then a compiled verifier. The sibling is a second form
of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `NotSpare`: the property "not the spare oracle" of a query;
 - `asksIn_cmpT`, `asksIn_judgeRunEL`, `asksIn_judgeRunE`: the comparisons and both runs ask only
   such queries;
 - `judgeRunEL_log_ne`, `judgeRunE_log_ne`: the log's form, at every family of oracle functions: no
   entry stands at the spare oracle.

Main theorems: `judgeRunEL_log_ne`, `judgeRunE_log_ne`.

Not claimed. The page's half of `clean` (for an entry: OnBytes/TypedOracleCompiler/Slice/EntryClean.lean). Nothing
on what the run does ask. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.JudgeE
import OnBytes.TypedOracleCompiler.Compile.Batch.NoOther

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I A Sd S : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L} {Ex : ExtRd L}

/-- "Not the spare oracle." -/
abbrev NotSpare (lam : ℕ) (L : BatchProtocolWithLeafBody I (A × Sd)) :
    (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf lam L o → Prop := fun o _ => o ≠ .other

/-- What a compiled verifier at a tag may ask is not the spare oracle. -/
theorem notSpare_of_vNames (t : Tag) (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf lam L o)
    (h : VP lam L t o q) : NotSpare lam L o q := (vNames_ne h).1

variable [DecidableEq S] (Z : WrittenE W Ex) (ZT : Written W) (saltT : Bits) (rtT : Dig lam)
  (rootsT : List (Dig lam)) (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → S)
  (Pk : Pack Ex.k S Sd)

/-- The seeds' chain under a list of roots asks no spare oracle. -/
theorem asksIn_chainT (cms : List (Dig lam)) :
    (ZT.chainT saltT rtT rootsT plainsT cms).AsksIn (NotSpare lam L) :=
  OComp.AsksIn.mono (notSpare_of_vNames ZT.t)
    (asksIn_chainAt ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT cms)

/-- The comparisons ask no spare oracle. -/
theorem asksIn_cmpT : ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
    (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s).AsksIn (NotSpare lam L)
  | [], _, _ => trivial
  | c :: l, i, s =>
    OComp.AsksIn.bind (fun z => by
      cases z with
      | none => exact trivial
      | some y =>
        show (if seedOf y.1 = Pk.get s i then cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s
          else OComp.pure false).AsksIn _
        split_ifs
        · exact asksIn_cmpT l (i + 1) s
        · exact trivial) (asksIn_chainT ZT saltT rtT rootsT plainsT [c])

/-- The judge's run with the lax verifier asks no spare oracle. -/
theorem asksIn_judgeRunEL (o : OutE Z) :
    (judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o).AsksIn (NotSpare lam L) :=
  OComp.AsksIn.bind (fun b => by
    cases b with
    | false => exact trivial
    | true =>
      exact OComp.AsksIn.mono (notSpare_of_vNames Z.t)
        (asksIn_verifyB Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) o.1 o.2.1 o.2.2))
    (asksIn_cmpT ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _)

/-- The judge's run with the strict verifier asks no spare oracle. -/
theorem asksIn_judgeRunE (sMT sFS : ℕ) (o : OutE Z) :
    (judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS o).AsksIn (NotSpare lam L) :=
  OComp.AsksIn.bind (fun b => by
    cases b with
    | false => exact trivial
    | true =>
      exact OComp.AsksIn.mono (notSpare_of_vNames Z.t)
        (asksIn_verifyBS sMT sFS Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) o.1 o.2.1
          o.2.2))
    (asksIn_cmpT ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _)

/-- The log's form: at every family of oracle functions no entry of the lax run's own log stands
at the spare oracle. -/
theorem judgeRunEL_log_ne (o : OutE Z) (F : Fam (typedOracleFamily lam W.K L)) :
    ∀ e ∈ ((judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o).withTrace.det F).2,
      e.1 ≠ TypedOracleCompiler.Compile.Batch.OracleName.other :=
  mem_trace_of_asksIn F (asksIn_judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o)

/-- The same of the strict run. -/
theorem judgeRunE_log_ne (sMT sFS : ℕ) (o : OutE Z) (F : Fam (typedOracleFamily lam W.K L)) :
    ∀ e ∈ ((judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS o).withTrace.det F).2,
      e.1 ≠ TypedOracleCompiler.Compile.Batch.OracleName.other :=
  mem_trace_of_asksIn F (asksIn_judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS o)

end TypedOracleCompiler.Slice
