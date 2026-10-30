-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DecInRange.lean: WHAT THE ONE DECODER ANSWERS HOLDS AN INDEX: at another
file's closed term for the composed meaning's parameters (Johnson/P5J/MgAtAll.lean): (dAt h).decT c
a = some M → InRange M. So, where the committed table's pin stands ("the one decoder's answer is the
witness's cells"), the guard "the witness's cells hold an index", under which K6's law and
the sentence wtK6 read the output matrix's weights, IS MET.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  heldAlong_inRange: the configuration's own "held", carried along the equation of data, answers
      only a matrix in range.
  dec_inRange: THE STATEMENT.
  inRange_of_pin: from the pin of the committed table.

How. By the definitions alone: the closed decoder is the shared chain's guarded decoder (nothing at
a collision; else what is decoded, then "held"); "held" is the stored table's configuration's: "the
message's matrix, if it is in range; else nothing"; "in range" there is Flat.InRange
(Johnson/Flat/ClaimsReq.lean).
What it does not say. THAT THE DECODER ANSWERS. That a table which the key file's protocol accepts
decodes in range: that is the key file's own theorem. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.DAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Desc.K14.Law

/- The names in scope are those of Johnson/Desc/Sound/DataAlong.lean, whose heldAlong is spoken of.
-/
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain

/-- **"held", carried along the equation of data, answers only in range.** -/
theorem _root_.VerifiableInference.Desc.Kinds.Head.Law.AtTable.heldAlong_inRange (p : Par)
    (err eM : Nat) {D₀ : DecR} (e : decROfS p.S.fold eM = D₀) {X : Type} (A : D₀.Claims X)
    (R : D₀.RelationsAndEncoding A) (U) (M : A.Mat) (h : heldAlong p err eM e A R U = some M) : A.inRange M := by
  classical
  subst e
  have h' : (if A.inRange (A.mat U) then some (A.mat U) else none) = some M := h
  split at h'
  · rename_i hr
    obtain rfl := Option.some.inj h'
    exact hr
  · cases h'

end Desc.K14.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes OnBytes.Flat
open VerifiableInference.OnPublicFiles.Flat (InRange)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **THE STATEMENT.** -/
theorem dec_inRange (h : P5J.AtMgA o Z Dw r Zp Np cF x) (c : ℕ → Option (ℕ × List UInt64))
    (a : ProofFile.InstPub × First.S) (M : P5J.CellsM numsFull) (hd : (dAt h).decT c a = some M) :
    InRange M := by
  classical
  have hd' : Sound.decGuard _ _ (_root_.Desc.K14.Law.heldFull _ _ _ _ numsFull _ (P5J.At.EAt Z)) c _
      =
      some M := hd
  unfold Sound.decGuard at hd'
  split at hd'
  · cases hd'
  · obtain ⟨U, -, hU⟩ := Option.bind_eq_some_iff.1 hd'
    unfold _root_.Desc.K14.Law.heldFull at hU
    exact heldAlong_inRange _ _ _ _ _ _ U _ hU

/-- **From the pin of the committed table.** -/
theorem inRange_of_pin (h : P5J.AtMgA o Z Dw r Zp Np cF x) (a : ProofFile.InstPub × First.S) (y : Strs)
    (w : Wit (P5J.CellsM numsFull) P5J.At.Tok Sound.MsgT)
    (hp : Sound.pinWOf (dAt h).decT a y w) : InRange w.cells :=
  dec_inRange h _ a w.cells hp

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heldAlong_inRange
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.dec_inRange
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.inRange_of_pin
