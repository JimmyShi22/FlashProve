-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DAtConst.lean: ONE NAME, for both sub-protocols (K6 and K7) at the output
head: dAt h: the structure of the composed meaning's parameters under another file's one head AtMgA
(Johnson/P5J/MgAtAll.lean). That file's own name
for it holds a sign that this tree's test on characters does not allow: it is written once, here.

The name and the line come out of Law/K07AtConst.lean,
in a file of their own so that the two kinds' files at the closed term share one definition.
What it does not say: anything.
-/
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- The structure of parameters under the head. -/
noncomputable abbrev dAt (h : P5J.AtMgA o Z D r Zp Np cF x) := h.𝔇

end VerifiableInference.Desc.Kinds.Head.Law
