-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/RoadLands.lean: the check of an entry file over the monad of trees of
queries, with the hash that asks the one oracle: run at f it is the check at the hash over f; it
draws no coin.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadHom
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadKeeps
import Run.OCompHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.RoadLands

open _root_.ZKCP
open _root_.Run

/-- "Tosses no coin" is a property that `pure` has and `bind` keeps. -/
def noCoinKeeps (lam : ℕ) : Keeps (OComp lam) where
  ok := fun x => x.NoCoin
  ok_pure := fun _ => trivial
  ok_bind := fun _ _ hx hg => OComp.NoCoin.bind' hx hg

/-- The check that asks, run at f, is the check at the hash over the function that f induces. -/
theorem check_det (f : _root_.ZKCP.Oracle 256) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) :
    (Entry.check (Fmt.HM askB) params first file).det f =
      Entry.check (m := Id) (Fmt.HO (oB f)) params first file := by
  have e := RoadHom.app_check (detHom f) (Fmt.HM askB) params first file
  rw [detHom_on_HM] at e
  exact e

/-- The check that asks tosses no coin. -/
theorem check_noCoin (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    (Entry.check (Fmt.HM askB) params first file).NoCoin :=
  RoadKeeps.ok_check (noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) params first file

/-- The same two for a reading step of a session. -/
theorem readIn_det (f : _root_.ZKCP.Oracle 256) (S : Fmt.SpecX) (b : ByteArray) (i : Nat)
    (s : Session) :
    (readIn (Fmt.HM askB) S b i s).run.det f = (readIn (m := Id) (Fmt.HO (oB f)) S b i s).run := by
  have e := RoadHom.app_readIn (detHom f) (Fmt.HM askB) S b i s
  rw [detHom_on_HM] at e
  exact e

theorem readIn_noCoin (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    (readIn (Fmt.HM askB) S b i s).run.NoCoin :=
  RoadKeeps.ok_readIn (noCoinKeeps 256) (Fmt.HM askB) (fun n t i s b => noCoin_HM n t i s b) S b i s

end OnBytes.TwoPort.M.RoadLands
