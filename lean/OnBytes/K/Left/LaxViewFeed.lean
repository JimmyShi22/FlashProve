-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxViewFeed.lean: from one yes of the strict reader to what the decision's clause of
the lax verifier's yes (OnBytes/K/Left/LaxView.lean: `accept_view`) asks of what was read.



The typed description D and the reader's statement st stand apart: the reader has read under D's own
part with st put in, and D's stored tables. At an entry file D is `entryXD G c`, whose statement is
empty, and st is the two tables' statement. For proofs only; the program does not import this file.

Main theorem.
 `view_feed`       there are a start c of the chain and a list rc, one member a round, with: o's
                  rounds are rc's members joined; `TraceL` at D's plan and rounds and rc's rounds,
                  stripped; as many roots as trees, round by round (`SentR`), at D's rounds' data;
                  every stored opening's `StoredFact` at st; each round has as many draws as its
                  entry says; and the description with st put in is in order.

What is not claimed. Nothing on soundness; no probability; nothing on any hash: O is any function on
byte strings. That the reader reads any file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.OpenedTrace
import OnBytes.TypedOracleCompiler.Run.PageIsViewProofs
import OnBytes.TypedOracleCompiler.Run.AllRoots

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (roundWithStoredOpenings StoredFact)

/-- What the decision's clause asks of what was read, from one yes of the strict reader. -/
theorem _root_.OnBytes.K.Left.view_feed (D : XD) (st : ByteArray) (O : ByteArray → ByteArray)
    (hokb : ok (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
      ⟨{ D.base with statement := st }, D.stored⟩ seen b i = some (o, j)) :
    ∃ (c : _root_.Fmt.Chain)
      (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut))),
      o.rounds.toList = rc.map roundWithStoredOpenings ∧
      TraceL (_root_.Fmt.HO O) D.base.plan D.base.rounds (rc.map fun p => stripR p.1) c #[] ∧
      List.Forall₂ SentR D.ds (rc.map fun p => stripR p.1) ∧
      List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
          (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        List.Forall₂ (StoredFact (_root_.Fmt.HO O) D.base.cfg st p.1.drawn.poss) ts p.2)
        D.stored rc ∧
      List.Forall₂ (fun (z : _root_.Fmt.Round × List _root_.Fmt.Stored)
          (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        p.1.drawn.poss.length = z.1.entry.poss) (D.base.rounds.zip D.stored) rc ∧
      (⟨{ D.base with statement := st }, D.stored⟩ : _root_.Fmt.SpecX).ok = true := by
  obtain ⟨hSok, R, rho0, rc, -, -, ho, hL, -, -, hlen, hF⟩ :=
    read_parts ⟨{ D.base with statement := st }, D.stored⟩ O hokb hn seen b i o j e
  have hoo : (ownOut o.pd R rho0 o.rho rc).rounds.toList = rc.map fun p => stripR p.1 := by
    simp [ownOut]
  have hs := (tab_sent _ _ _ hokb hL).1
  rw [hoo, rds_congr (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) D.base rfl rfl]
    at hs
  have htr := trace_own (_root_.Fmt.HO O)
    (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) o.pd R rho0 o.rho rc hL
  exact ⟨⟨D.base.label, rho0, 0⟩, rc, ho, htr, hs.imp fun _ _ h => h, hF, hlen, hSok⟩

end TypedOracleCompiler.Run.PQ
