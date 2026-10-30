-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K01KeyAt.lean: the two equations that Johnson/Desc/K1/Law/CondRow.lean leaves
as premises on a place ("its
codes and its messages are the record's"), by Lean's kernel, at ALL NINETEEN sendings of a key file,
at the library's typed sizes of a key of full size; and so, by the library's own theorem, at the
planner's sizes of the key at EVERY three public files in the scope of the goals.

Johnson/Goal/PlanValues/KeySizedReturns.lean has the typed value `keyFull`, and
Johnson/Goal/PlanValues/KeyFullAtScope.lean the theorem `key_eq_at_scope`: where the program's
planner
returns at files in scope, its sizes of the key are `keyFull`. Here what is announced at a key
file's
sendings is written as three functions of a key's sizes, and `key_test` holds them at `keyFull`
against
the records of Johnson/Desc/K1/Law/CondLit.lean, sending by sending.
  keySent0: the first chain's six: the message of masks for the index; the multiplicities with the
      first fold's mask (`Wf.messageOf`); the three code switches of the ranges' test; W's message
  keySent1: the shared chain's nine (`sharedSent`, Johnson/Desc/K1/Law/CondReal.lean)
  keySent2: the four code switches of the own test
  keySent: the three by the chain's number
  key_test: one evaluation in Lean's kernel (decide +kernel): the codes are the written list
      `codesFull0`; the three lists are the records' messages; every record of the key file stands
      under these codes
  key_sent: the three lists are the records' messages
  placeOk_key: a place with `keyFull`'s codes that announces number k of chain c is PlaceOk 0 c k
  k01_key_at_scope: the same at p.chains.made.sized.key for every p that the planner returns at
      files in scope: the kind's one Boolean holds there at the record's radii

What is not claimed. One direction: from a planner that returns. The statements speak of what the
planner made (made.sized.key), not of what a check reads back from a chain's parameter bytes. That a
block of a description of a key file announces these functions' values: keySent0's first, second and
last member and the switches are typed after Johnson/G/SendsFrom.lean, which is a reading of the
verifier's text; the shared chain's first two are K14's own `withU` and `withOmega`; a switch's is
the
text of `parSwitch`. The radii are the written list's (the limits of Johnson/G/PackList.lean). What
the heads of Johnson/Desc/K1/Law/CondRow.lean and CondLit.lean do not claim. Nothing on soundness,
on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.CondReal
import Johnson.Goal.PlanValues.KeyFullAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Plan Johnson.G
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- The first chain's sendings. -/
def keySent0 (z : KeySized) : Option (List (List OracleNotice)) :=
  (linMessageW z.once.shape).map fun w =>
    [z.once.input] :: (Wf.messageOf z.ranges.x).toList ::
      (switchesOf 1 z.ranges.x.stages ++ [w.toList])

/-- The three chains' sendings, by the chain's number. -/
def keySent (z : KeySized) : Nat → Option (List (List OracleNotice))
  | 0 => keySent0 z
  | 1 => sharedSent z.once.shape
  | _ => some (switchesOf 1 z.once.shape.testOwn)

/-- **The typed sizes of a key against the records.** By evaluation in Lean's kernel. -/
theorem key_test : (decide (keyFull.codes = codesFull0) &&
    [0, 1, 2].all fun c => decide (keySent keyFull c = some (sentOf 0 c)) &&
      (litAt sendsFullLit packFullLit 0 c).all fun y => decide (y.2.cs = codesFull0)) = true := by
  decide +kernel

/-- The three lists are the records' messages. -/
theorem key_sent {c : Nat} (hc : c ∈ [0, 1, 2]) : keySent keyFull c = some (sentOf 0 c) := by
  have ht := key_test
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  exact (ht.2 c hc).1

/-- **All nineteen places of a key file at the typed sizes.** -/
theorem placeOk_key {c k : Nat} (hc : c ∈ [0, 1, 2]) {L : List (List OracleNotice)}
    (hL : keySent keyFull c = some L) {s : List OracleNotice} (hk : L[k]? = some s) (P : Par)
    (h1 : P.codes = keyFull.codes) (h2 : P.sent.toList = s) : PlaceOk 0 c k P := by
  have ht := key_test
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  obtain ⟨t1, t2⟩ := ht
  obtain ⟨t3, t4⟩ := t2 c hc
  obtain rfl : L = sentOf 0 c := Option.some.inj (hL.symm.trans t3)
  unfold sentOf at hk
  rw [List.getElem?_map] at hk
  cases hy : (litAt sendsFullLit packFullLit 0 c)[k]? with
  | none =>
    rw [hy] at hk
    cases hk
  | some y =>
  rw [hy] at hk
  have hs : y.2.sent = s := Option.some.inj hk
  have hm := List.mem_of_getElem? hy
  have hat : y.2.At P := ⟨(h1.trans t1).trans (t4 y hm).symm, by rw [hs, ← h2]⟩
  exact ⟨y, hy, hat, (((k01_full y.2 (litAt_mem hm)).2).1 P hat).1⟩

/-- **At every three public files in the scope of the goals**, from a planner that returns. -/
theorem k01_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    {c k : Nat} (hc : c ∈ [0, 1, 2]) {L : List (List OracleNotice)}
    (hL : keySent p.chains.made.sized.key c = some L) {s : List OracleNotice}
    (hk : L[k]? = some s) (P : Par) (h1 : P.codes = p.chains.made.sized.key.codes)
    (h2 : P.sent.toList = s) : PlaceOk 0 c k P := by
  rw [key_eq_at_scope hZ hp] at hL h1
  exact placeOk_key hc hL hk P h1 h2

/-- The three lists are there and have 6, 9 and 4 members. -/
theorem key_counts : ([0, 1, 2].map fun c => (keySent keyFull c).map (·.length)) =
    [some 6, some 9, some 4] := by
  decide +kernel

end VerifiableInference.Desc.K1
