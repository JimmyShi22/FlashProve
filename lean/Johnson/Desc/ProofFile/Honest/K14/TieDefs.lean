-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieDefs.lean: kind K14: TWO DEFINITIONS WITH WHICH THIS KIND's
TEXT OF A SENDING (sendingPart, Honest/K14/Sendings.lean) IS HELD AGAINST THE SHARED SENDING's
(sendPart, Honest/K1/Part.lean). No theorem is stated.

  vecData         the data that the shared sending's part is handed for a job of this kind at a
                  state: of a message that is laid plainly: its vector, as vectorData
                  (Honest/K14/SendingsVia.lean) lays it; of a fold's fresh table: none
  RowsAgree       rows of this kind's text (Laid: the program's elements) and rows of the shared
                  sending's (Rows, Johnson/Prover/Send/Core.lean: elements of the field) are the
                  same, read, WHEREVER A COLUMN OR AN ANSWER READS THEM: for each message below the
                  count: main entries and mask entries below the rows' number and the code's message
                  length; tails below the tail's length; and main rows are over the extension field

Limits. Definitions. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.K14.SendingsVia
import Johnson.Prover.Send.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Slice (GE GF rdE)
open VerifiableInference.Desc (K1.Par)
open Johnson.Prover.Send (Rows shapeAt)

/-- **The data that the shared sending's part is handed for the job J at the state t.** -/
def vecData (J : SendJob) (t : State Ask Unit) (k r j : Nat) : Option (GF ⊕ GE) :=
  match J.sort k with
  | .plain high => vectorData J.Q.codes (shapeAt J.Q k) high (J.data t k) r j
  | .fresh _ _ => none

/-- **The two texts' rows are the same, read, wherever a column or an answer reads them.** -/
structure RowsAgree (P : K1.Par) (L : Nat → Laid) (V : Nat → Rows) : Prop where
  overE : ∀ k, k < P.sent.size → (shapeAt P k).mainRows ≠ 0 → (shapeAt P k).mainDeg = 3
  main : ∀ k, k < P.sent.size → ∀ r, r < (shapeAt P k).mainRows →
    ∀ j, j < (P.codes.base.getD (shapeAt P k).code default).ell →
      (V k).mainE r j = rdE.val ((L k).main r j)
  mainTail : ∀ k, k < P.sent.size → ∀ r, r < (shapeAt P k).mainRows →
    ∀ q, q < (P.codes.base.getD (shapeAt P k).code default).r →
      (V k).mainTlE r q = rdE.val ((L k).mainTail r q)
  mask : ∀ k, k < P.sent.size → ∀ r, r < (shapeAt P k).maskRows →
    ∀ j, j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell →
      (V k).mask r j = rdE.val ((L k).mask r j)
  maskTail : ∀ k, k < P.sent.size → ∀ r, r < (shapeAt P k).maskRows →
    ∀ q, q < (P.codes.mask.getD (shapeAt P k).maskCode default).r →
      (V k).maskTl r q = rdE.val ((L k).maskTail r q)

end ProofFile.Honest.K14
