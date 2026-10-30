-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadCostLands.lean: the count of the entry's road at the library's monad of
trees of queries, with the hash that asks the one oracle (at most two questions a call).
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadCost
import Run.OCompCostP

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadCostLands

open _root_.ZKCP
open _root_.Run
open OnBytes.Tie.CostX
open OnBytes.TwoPort.M.RoadCost

/-- A reading step of a session that asks: no coin, and at most twice the description's number of
questions. -/
theorem readIn_asks (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    (readIn (Fmt.HM askB) S b i s).run.NoCoin ∧
      (readIn (Fmt.HM askB) S b i s).run.QueryBound (fileNX S * 2) :=
  have e := le_readIn (qp 256) 2 (Fmt.HM askB) qp_HM S b i s
  ⟨e.1, e.2.1⟩

/-- The named reading goes over the chain a second time where the first refuses: four times the
number. -/
theorem readNamed_asks (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    (Proof.readNamed (Fmt.HM askB) front S b i s).run.QueryBound (fileNX S * 2 + fileNX S * 2) :=
  (le_readNamed (qp 256) 2 (Fmt.HM askB) qp_HM front S b i s).2.1

/-- The check of an entry file that asks: no coin, and at most 2 T questions, if T bounds twice the
key's number and twice the number of every description that the check can make. -/
theorem check_asks (params : ByteArray) (first : Params.TableName) (file : ByteArray) (T : Nat)
    (hT : ∀ p, Params.Link.read params = some p →
      ∃ N, SpecsBelow p first N ∧ 2 * keyN p.link.table + 2 * N ≤ T) :
    (Entry.check (Fmt.HM askB) params first file).NoCoin ∧
      (Entry.check (Fmt.HM askB) params first file).QueryBound (T * 2) :=
  have e := le_check (qp 256) 2 (Fmt.HM askB) qp_HM params first file T hT
  ⟨e.1, e.2.1⟩

end OnBytes.TwoPort.M.RoadCostLands
