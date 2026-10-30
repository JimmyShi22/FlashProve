-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/OpenedTrace.lean: two facts beside OnBytes/K/OpenedRead.lean's `read_parts`, in the form
in which the view's half of the decision asks them.



Main theorems.
 `trace_own`       `LaxFacts` of the chain without the stored tables' openings (`ownOut .. rc`)
                  holds `TraceL` at the list of rc's rounds, stripped.
 `read_trace`      so one yes of the strict reader gives such a list rc with that `TraceL`. It has
                  an rc of its own: whoever wants `TraceL` at the very rc of `read_parts` calls
                  `trace_own` on that lemma's `LaxFacts`.
 `tabGood_all` within the limits of OnBytes/TypedOracleCompiler every opening of the description is some own tree's
                   (`TabGood`).

What is not claimed. Nothing on soundness; no probability; nothing on any hash. For proofs only; the
program does not import this file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.OpenedRead
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (roundWithStoredOpenings StoredFact)

/-- `LaxFacts` of `ownOut .. rc` holds `TraceL` at rc's rounds, stripped. -/
theorem trace_own (h : HId) (S : _root_.Fmt.Spec) (pd R rho0 rho : ByteArray)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hL : LaxFacts h S (ownOut pd R rho0 rho rc)) :
    TraceL h S.plan S.rounds (rc.map fun p => stripR p.1) ⟨S.label, rho0, 0⟩ #[] := by
  have ht : ((rc.map fun p => stripR p.1).toArray).toList = rc.map fun p => stripR p.1 := by simp
  have := hL.trace
  show TraceL h S.plan S.rounds (rc.map fun p => stripR p.1) ⟨S.label, rho0, 0⟩ #[]
  rw [← ht]
  exact this

/-- One yes of the strict reader: o's rounds are rc's members joined; `TraceL` at rc's rounds,
stripped; and every stored opening has `StoredFact`. -/
theorem read_trace (S : _root_.Fmt.SpecX) (O : ByteArray → ByteArray)
    (hokb : ok (inFile S.base) = true) (hn : S.base.rand.isNone = false)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)) :
    ∃ (rho0 : ByteArray)
      (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut))),
      o.rounds.toList = rc.map roundWithStoredOpenings ∧
      TraceL (_root_.Fmt.HO O) S.base.plan S.base.rounds (rc.map fun p => stripR p.1)
        ⟨S.base.label, rho0, 0⟩ #[] ∧
      List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
          (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        List.Forall₂ (StoredFact (_root_.Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts
          p.2) S.stored rc := by
  obtain ⟨-, R, rho0, rc, -, -, ho, hL, -, -, -, hF⟩ := read_parts S O hokb hn seen b i o j e
  exact ⟨rho0, rc, ho, trace_own _ (inFile S.base) _ _ _ _ rc hL, hF⟩

/-- Within the limits of OnBytes/TypedOracleCompiler every opening of the description is some own tree's. -/
theorem tabGood_all (S : _root_.Fmt.Spec) (hok : ok S = true) :
    ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, TabGood S x n :=
  fun r hr x hx => tab_good S (tab_limits S hok) r hr x hx

end TypedOracleCompiler.Run.PQ
