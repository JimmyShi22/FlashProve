-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/QFull.lean: a PLACEHOLDER for the proof
file's first chain's parameters at the full size, as one closed term, and the congruences that carry
a computed value to it: the kind K1's places read of these parameters the codes, the request's shape
and the shape of the linear claims alone. Definitions, and statements with their proofs by
unfolding. Why. Tests on the list of rounds that name a place of K1 (firstPar q gp, parLater q gp
link piece moment, parW q gp piece msg) are to become closed facts on written values. A value of
Params.First cannot be one written value across the goals' scope: its field given holds the
parameter bytes and the digest of the public files. But no place of K1 reads that field.
  qFull: given := an empty one; codes := codesFull2; lin := proofSizedFull.batch.shape; shape :=
      proofSizedFull.request; layout, identifiers, more: empty; pendingRows := 13; binding := ⟨6,
      40⟩
  firstPar_congr, parLater_congr, parW_congr: equal codes and equal request's shape give the same
      place
  ownGroup_congr, noticesAt_congr, firstLaid_congr: beneath these
  wMsg_congr: what goes out with W hangs on lin alone
  LikeFull q: the three equations on q; firstPar_full, parLater_full, parW_full, wMsg_full: so at
      every q with these three the places are qFull's

What is not claimed. That a computed value has the three equations: other files' theorem in
scope, under the door's pin. qFull IS NO VALUE THAT ANY FILE GIVES: its empty fields are fillings:
whatever reads given, layout, identifiers or more must not be stated at it (firstPlanOk reads the
layout: a conjunct of the first sub-protocol's own test on its parameters). Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Places
import Johnson.Desc.K1.First
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params _root_.Desc.Plain
open Johnson.G (codesFull2)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- **The placeholder.** The fields that no place of the kind reads are empty. -/
def qFull : Params.First :=
  { given :=
      { bytes := ByteArray.empty
        plan := { field := .two, salt := 0, nonce := 0, posB := 0, samples := 0, saved := 0,
                  entries := [] }
        cfg := ByteArray.empty, items := [] }
    codes := codesFull2, lin := proofSizedFull.batch.shape, shape := proofSizedFull.request
    layout := { link := [] }, identifiers := [], pendingRows := 13, binding := ⟨6, 40⟩, more := [] }

variable {q q' : Params.First}

theorem ownGroup_congr (hs : q.shape = q'.shape) : ownGroup q = ownGroup q' := by
  unfold ownGroup
  rw [hs]

theorem noticesAt_congr (hs : q.shape = q'.shape) (link moment : Nat) :
    noticesAt q link moment = noticesAt q' link moment := by
  unfold noticesAt
  rw [hs]

theorem firstLaid_congr (hs : q.shape = q'.shape) : firstLaid q = firstLaid q' := by
  unfold firstLaid frame₀
  rw [ownGroup_congr hs, hs]

/-- **The first segment's opening's place.** -/
theorem firstPar_congr (hc : q.codes = q'.codes) (hs : q.shape = q'.shape) (gp : GPar) :
    firstPar q gp = firstPar q' gp := by
  unfold firstPar firstParts
  rw [firstLaid_congr hs, hc]

/-- **A segment's later sending's place.** -/
theorem parLater_congr (hc : q.codes = q'.codes) (hs : q.shape = q'.shape) (gp : GPar)
    (link piece moment : Nat) :
    parLater q gp link piece moment = parLater q' gp link piece moment := by
  unfold parLater
  rw [noticesAt_congr hs, hc]

/-- **The place of W's sending.** -/
theorem parW_congr (hc : q.codes = q'.codes) (hs : q.shape = q'.shape) (gp : GPar) (piece : Nat)
    (msg : Array OracleNotice) : parW q gp piece msg = parW q' gp piece msg := by
  unfold parW
  rw [ownGroup_congr hs, hc]

/-- What goes out with W. -/
theorem wMsg_congr (hl : q.lin = q'.lin) : linMessageW q.lin = linMessageW q'.lin := by rw [hl]

/-- The three equations that carry a computed value to the placeholder. -/
structure LikeFull (q : Params.First) : Prop where
  codes : q.codes = codesFull2
  shape : q.shape = proofSizedFull.request
  lin : q.lin = proofSizedFull.batch.shape

theorem firstPar_full (h : LikeFull q) (gp : GPar) : firstPar q gp = firstPar qFull gp :=
  firstPar_congr h.codes h.shape gp

theorem parLater_full (h : LikeFull q) (gp : GPar) (link piece moment : Nat) :
    parLater q gp link piece moment = parLater qFull gp link piece moment :=
  parLater_congr h.codes h.shape gp link piece moment

theorem parW_full (h : LikeFull q) (gp : GPar) (piece : Nat) (msg : Array OracleNotice) :
    parW q gp piece msg = parW qFull gp piece msg := parW_congr h.codes h.shape gp piece msg

theorem wMsg_full (h : LikeFull q) : linMessageW q.lin = linMessageW qFull.lin := wMsg_congr h.lin

/-- The placeholder has the three equations. -/
theorem likeFull_qFull : LikeFull qFull := ⟨rfl, rfl, rfl⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.firstPar_congr
#print axioms VerifiableInference.Desc.K1.parLater_congr
#print axioms VerifiableInference.Desc.K1.parW_congr
#print axioms VerifiableInference.Desc.K1.wMsg_congr
#print axioms VerifiableInference.Desc.K1.firstPar_full
#print axioms VerifiableInference.Desc.K1.parLater_full
#print axioms VerifiableInference.Desc.K1.parW_full
#print axioms VerifiableInference.Desc.K1.wMsg_full
#print axioms VerifiableInference.Desc.K1.likeFull_qFull
