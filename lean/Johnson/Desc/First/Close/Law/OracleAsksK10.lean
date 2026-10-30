-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/OracleAsksK10.lean (kind K10): WHAT THE FOUR RIDERS ON ORACLES TAKE
(`OracleAsks`, Johnson/Desc/First/Link/Law/OracleRides.lean) HOLDS ALONG K10's STEP, WHERE THE
READER OF THE OOD SAMPLES IS THE NAMED ONE (`smpNamed`, Johnson/Desc/Sound/SmpNamed.lean).
Statements and proofs.

Why. `k10_asksR_mg` (AsksAtMgAll.lean, beside this file) has one premise on the structure of
parameters: hO: `OracleAsks` at every fenced step of K10. `oracleAsks_of`
(Johnson/Desc/First/Link/Law/FenceAt.lean) pays it at two states with one statement and one book;
K10's step turns the statement.
  `k10_smpNamed`: along `K10Step s s'` the named reader answers alike at (z, s') and (z, s): it
    reads, of a message, its first stored sample row alone (`K1.formsAt`, `K1.ansAt`), and K10's
    step leaves every message's sample rows (`k10_rides`, RidesBehind.lean).
  `k10_oracleAsks`: `fenceFit`'s yes at the numbers; k ≤ pl.length; the plan's count of trees at
    pl[k]? is at most base; the decoder answers alike at any two states (hd); `K10Step s s'`: THEN
    `OracleAsks cs decT (smpNamed cs seats) Nm links pl z k base s s'`.
Limits. `fenceFit`'s yes is the table's files' to show; "at most base" is a fact on the seated
piece; hd is a premise on the decoder. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AsksAtMgAll
import Johnson.Desc.First.Close.Law.RidesBehind
import Johnson.Desc.First.Link.Law.FenceAt
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (OracleAsks fence_of_fit)
open VerifiableInference.Desc.First (ModelPart Numbers fenceFit)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- **The named reader of the OOD samples answers alike across K10's step.** -/
theorem k10_smpNamed {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (z : P)
    {s s' : VerifiableInference.Desc.First.S} (hs : K10Step s s') (x : Sending)
    (i : Fin x.l.length) : smpNamed cs seats (z, s') x i = smpNamed cs seats (z, s) x i := by
  obtain ⟨es, rs, y, hy, rfl⟩ := hs
  have hr := (k10_rides s es rs y hy).2.2.2.1
  refine smpNamed_stays cs seats (z, s) (z, _) x i ?_ ?_
  · show VerifiableInference.Desc.K1.formsAt cs _ (putRec s ⟨none, y.1, y.2⟩).st _ =
      VerifiableInference.Desc.K1.formsAt cs _ s.st _
    generalize VerifiableInference.Desc.Sound.numAt seats ⟨x, i⟩ = n
    have e := hr n
    unfold VerifiableInference.Desc.K1.formsAt
    cases h1 : (putRec s ⟨none, y.1, y.2⟩).st.oracles[n]? <;>
      cases h2 : s.st.oracles[n]? <;> simp_all
  · show VerifiableInference.Desc.K1.ansAt (putRec s ⟨none, y.1, y.2⟩).st _ =
      VerifiableInference.Desc.K1.ansAt s.st _
    generalize VerifiableInference.Desc.Sound.numAt seats ⟨x, i⟩ = n
    have e := hr n
    unfold VerifiableInference.Desc.K1.ansAt
    cases h1 : (putRec s ⟨none, y.1, y.2⟩).st.oracles[n]? <;>
      cases h2 : s.st.oracles[n]? <;> simp_all

section
variable {P Cells : Type} (cs : OnBytes.Codes)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (seats : List (ℕ × ℕ))

/-- **WHAT THE FOUR RIDERS TAKE, ALONG K10's STEP.** -/
theorem k10_oracleAsks (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k base : ℕ)
    (h : fenceFit Nm links pl = true) (hk : k ≤ pl.length) (hb : Nm.treesAt pl[k]? ≤ base)
    (hd : ∀ c (s s' : VerifiableInference.Desc.First.S), decT c (z, s') = decT c (z, s))
    {s s' : VerifiableInference.Desc.First.S} (hs : K10Step s s') :
    OracleAsks cs decT (smpNamed cs seats) Nm links pl z k base s s' :=
  ⟨fence_of_fit Nm links pl h k base hk hb, fun c => hd c s s',
    funext fun x => funext fun i => k10_smpNamed cs seats z hs x i⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_smpNamed
#print axioms VerifiableInference.Desc.First.Close.k10_oracleAsks
