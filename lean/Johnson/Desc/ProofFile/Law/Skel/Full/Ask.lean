-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Ask.lean: small tools for the closed facts at the written data
(Full/Data.lean). Definitions, statements and proofs.
  `ksW`        the written lots as `LotSk`s
  `okIs x l`   x returns, and returns l: a test with code. `okIs_ok`: its yes gives `x = .ok l`
  `asW`, `lsW`  the places at which `batch`, and the numbers at which `each` and `tests`, are asked
  `RowAt G L w`: the row of one lot: its plain data at these places and numbers is w
  `rows_join`  a row a lot, in the lots' order, gives `back_of_written`'s one equation
Limits. Nothing is paid here. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

def ksW : List LotSk := wsW.map LotW.sk

def okIs (x : Except String (List Skel)) (l : List Skel) : Bool :=
  match x with
  | .ok y => decide (y = l)
  | .error _ => false

theorem okIs_ok {x : Except String (List Skel)} {l : List Skel} (h : okIs x l = true) :
    x = .ok l := by
  cases x with
  | error e => cases h
  | ok y => exact congrArg Except.ok (of_decide_eq_true h)

def asW : List VerifiableInference.Desc.Place := askedOf spotsW batchAtW subsW

def lsW : List Nat := linksOf spotsW

/-- **One lot's row.** -/
def RowAt (G : Ground) (L : Lot) (w : LotW) : Prop := lotW asW lsW (lotSk G L) = w

theorem rows_join (G : Ground) {Ls : List Lot} {ws : List LotW}
    (h : List.Forall₂ (RowAt G) Ls ws) : (Ls.map (lotSk G)).map (lotW asW lsW) = ws := by
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    rw [List.map_cons, List.map_cons, ih]
    exact congrArg (· :: _) h1

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.okIs_ok
#print axioms ProofFile.Sk.Full.rows_join
