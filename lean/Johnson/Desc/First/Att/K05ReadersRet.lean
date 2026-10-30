-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadersRet.lean: kind K5: THE KIND's TWO READERS OF THE PLANES' COLUMNS (readersOfK, Att/Guest.lean: a bit's plane; the pin) RETURN AT EVERY COLUMN OF THE PLANES: K5's share of "the lookup's run «planes» returns at the verifier's state after the kind's
sub-protocol".
A reader is one call of u3at (Att/RunsP.lean): it refuses at two tests on numbers: the column is below the table's stored length; the array of the reads has a column, and the entry's row fits 32 bits.
Main names:
  u3at_ret: u3at returns where the two tests pass. u3at_ret_in: they pass where every table lies below nW (LenIn, Att/Claims/Covered.lean) and the array has nW columns or more (the entry's row is 0).
  readers_ret: both readers return below n, where each of the three tables has n entries or more.
  readers_ret_plan: the three lengths from tabs_look (Att/Claims/TablesAt.lean: from the return of tablesP and PosG): n ≤ k * (m / 2 ^ lmb) at the planes' matrix, number NAs + 2 of the list: ONE COMPARISON OF PUBLIC NUMBERS.
They are also the three premises hb0 | hb1 | hpn of readers_are (Att/Claims/PlanesHost.lean), up to naming what is returned.
What the forms are and that they pass the public test: u3at_is (Att/Claims/PlanesWorth.lean) · k5_readers_there (Att/K05ReadersThere.lean): not spoken of here.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.TablesAt
import Johnson.Desc.First.Att.Claims.Covered
import Johnson.Desc.First.Att.Guest
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open K5Law (LenIn TabsLook tabs_look oldOf matsOf PosG)

/-- **u3at returns where its two tests pass.** -/
theorem u3at_ret {i : Runs.In} {t n K : ℕ} (h1 : n < (i.t.tabLen.lookup t).getD 0) (hK : K ≠ 0) (h2 : (t + n) / K < 2 ^ 32) :
    ∃ f, (Runs.gather K (Runs.u3at i t n)).map (·.1) = some f := by
  refine ⟨Aff.ent i.iU3 ((t + n) / K) ((t + n) % K), ?_⟩
  have e1 : Decidable.decide (n < (i.t.tabLen.lookup t).getD 0) = true := decide_eq_true h1
  have e2 : (K != 0 && Decidable.decide ((t + n) / K < 2 ^ 32)) = true := by
    rw [decide_eq_true h2, Bool.and_true]
    exact bne_iff_ne.2 hK
  have m1 : (Runs.mustAs "internal-a-table-index" (Decidable.decide (n < (i.t.tabLen.lookup t).getD 0)) : Runs.W Unit) K #[] =
      some ((), #[]) := by
    unfold Runs.mustAs
    rw [e1]
    rfl
  have m2 : (Runs.mustAs "internal-L-row" (K != 0 && Decidable.decide ((t + n) / K < 2 ^ 32)) : Runs.W Unit) K #[] = some ((), #[]) := by
    unfold Runs.mustAs
    rw [e2]
    rfl
  have u : Runs.uEnt i.iU3 (t + n) K #[] = some (Aff.ent i.iU3 ((t + n) / K) ((t + n) % K), #[]) := by
    show ((Runs.mustAs "internal-L-row" (K != 0 && Decidable.decide ((t + n) / K < 2 ^ 32)) : Runs.W Unit) K #[]).bind
      (fun x => some (Aff.ent i.iU3 ((t + n) / K) ((t + n) % K), x.2)) = _
    rw [m2]
    rfl
  have v : Runs.u3at i t n K #[] = some (Aff.ent i.iU3 ((t + n) / K) ((t + n) % K), #[]) := by
    show ((Runs.mustAs "internal-a-table-index" (Decidable.decide (n < (i.t.tabLen.lookup t).getD 0)) : Runs.W Unit) K #[]).bind
      (fun x => Runs.uEnt i.iU3 (t + n) K x.2) = _
    rw [m1]
    exact u
  show Option.map (·.1) (Option.map (fun x : Aff × Array Aff => (x.1, x.2.toList)) (Runs.u3at i t n K #[])) = _
  rw [v]
  rfl

/-- Where every table lies below nW and the array of the reads has nW columns or more. -/
theorem u3at_ret_in {i : Runs.In} {t n K nW : ℕ} (hL : LenIn i nW) (hW : nW ≤ K) (h1 : n < (i.t.tabLen.lookup t).getD 0) :
    ∃ f, (Runs.gather K (Runs.u3at i t n)).map (·.1) = some f := by
  cases he : i.t.tabLen.lookup t with
  | none =>
    rw [he] at h1
    exact absurd h1 (Nat.not_lt_zero _)
  | some e =>
    rw [he] at h1
    have h1' : n < e := h1
    have hb : t + n < K := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.add_lt_add_left h1' t) (hL t e he)) hW
    refine u3at_ret (by rw [he]; exact h1') (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)) ?_
    rw [Nat.div_eq_of_lt hb]
    exact Nat.two_pow_pos 32

/-- **Both readers return below n.** -/
theorem readers_ret {St : Type} {seat : SeatC St} {c : ParC} {s : St} {i : Runs.In} {K nW n : ℕ}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hin : inOf seat c s = some (i, K)) (hr : readersOfK seat c s = some r)
    (hL : LenIn i nW) (hW : nW ≤ K) (h0 : n ≤ (i.t.tabLen.lookup i.t.tBit0).getD 0) (h1 : n ≤ (i.t.tabLen.lookup i.t.tBit1).getD 0)
    (hp : n ≤ (i.t.tabLen.lookup i.t.tPin).getD 0) :
    (∀ e col, col < n → ∃ f, r.1 e col = some f) ∧ ∀ col, col < n → ∃ f, r.2 col = some f := by
  unfold readersOfK at hr
  rw [hin] at hr
  obtain rfl := Option.some.inj hr
  refine ⟨fun e col hc => ?_, fun col hc => u3at_ret_in hL hW (Nat.lt_of_lt_of_le hc hp)⟩
  show ∃ f, (Runs.gather K (Runs.u3at i (if e == 0 then i.t.tBit0 else i.t.tBit1) col)).map (·.1) = some f
  split
  · exact u3at_ret_in hL hW (Nat.lt_of_lt_of_le hc h0)
  · exact u3at_ret_in hL hW (Nat.lt_of_lt_of_le hc h1)

/-- **The same, the three lengths from the return of the tables.** -/
theorem readers_ret_plan {St : Type} {seat : SeatC St} {c : ParC} {s : St} {i : Runs.In} {K nW nW' n : ℕ}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hin : inOf seat c s = some (i, K)) (hr : readersOfK seat c s = some r)
    (hL : LenIn i nW) (hW : nW ≤ K) {S : Attention.Shape} {tl : HTailF2} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : tablesP i.g (matsOf tl.mats) nW' lk i.p = some i.t) (hp : PosG i.g)
    (hn : n ≤ (tl.mats.getD (S.cf.NAs + 2) {}).k * ((tl.mats.getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb)) :
    (∀ e col, col < n → ∃ f, r.1 e col = some f) ∧ ∀ col, col < n → ∃ f, r.2 col = some f := by
  have T := tabs_look (tl := tl) (S := S) (gL := default) hg ht hp
  exact readers_ret hin hr hL hW (le_of_le_of_eq hn T.tBit0.size.symm) (le_of_le_of_eq hn T.tBit1.size.symm)
    (le_of_le_of_eq hn T.tPin.size.symm)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.u3at_ret
#print axioms VerifiableInference.Desc.First.Att.P.readers_ret
#print axioms VerifiableInference.Desc.First.Att.P.readers_ret_plan
