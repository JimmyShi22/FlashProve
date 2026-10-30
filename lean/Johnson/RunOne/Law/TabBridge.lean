-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/TabBridge.lean: THE TABLE OF ONE TYPED MESSAGE IS WRITTEN IN TWO WAYS: THEY ARE ONE. A statement with its proof, by unfolding. GENERAL IN cs · s · e: no key file stands in it.
OBJECT. `Fill.ofU` (Johnson/Desc/Key/KeyFill.lean: the tables' table of a typed message) and `H2K.Pin.tabP` (Johnson/Desc/K12/Law/TupleWords.lean: the proximity test's).
USER. K12Hval.lean. (The bridge between the two READERS OF A WORD, and between the two spellings of a candidate, is Johnson/Top/Fire/Code/CandBridge.lean.)
  ofU_eq_tabP: ofU cs s e u = tabP cs s u: the same two branches; they part in the spelling of a code's length alone.
Limits. Two spellings of one function: it says nothing new. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Key.KeyFill
import Johnson.Desc.K12.Law.TupleWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.TabBridge
open VerifiableInference.Desc VerifiableInference.Desc.Key.Fill
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

/-- **The two tables of a typed message are one.** -/
theorem ofU_eq_tabP (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ) (u : (portOmZ cs s e).Msg) :
    ofU cs s e u = H2K.Pin.tabP cs s u := by
  funext part i
  cases part <;> rfl

end Johnson.RunOne.Law.TabBridge

#print axioms Johnson.RunOne.Law.TabBridge.ofU_eq_tabP
