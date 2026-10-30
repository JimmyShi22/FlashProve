-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowJoin.lean: THE EXCHANGE AT THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, ITS KEYS' HALF, IN THE LOOKUP's OWN FORMULA: behind the head's block the form of
the run "join" AT THE HEAD's KEY VECTORS (reads read as the stated sums of the cells) is worth 0; with what the row closes
(Law/RowAtDecide.lean: Closed: each call's key vector is worth the extension of the call's table at its key point) THE SAME FORMULA FED
WITH THESE EXTENSIONS, AS CONSTANTS, IS WORTH 0: STATED AND PROVED. No chance in it; at one record; general in the seat and in what
the lookup has heard.
WHAT IT DOES NOT SAY. That the lookup's formula in Lean's text (joinForm: Law/JoinValue.lean, off LookClaims.lean's joinF) at constants IS the
library's claimJoin at the key vectors' extensions (the item "KEYS-AT-POINTS" of the lookup's files): THAT TIE IS THE LOOKUPS'. That gk is what
the record holds as heard by the lookup: gk is a letter. That the sentence rides from the record behind to the statement in
front (the value of gk.cEnd at an earlier ledger). Nothing on "planes".
  trueKey · rd_trueKey   the extension of a call's table at its key point, as an element.
  keysAt · trueKeys      the head's six key vectors at reads in truth; the six constants.
  JoinOpened · KeysWorth the two sentences on a record.
  keys_worth             Closed and JoinOpened give KeysWorth.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowAtDecide
import Johnson.Desc.Kinds.Law.JoinValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd S2 T)

variable {S : Type}

/-- The extension of a call's table of keys at the call's key point. -/
def trueKey [Sizes] [Policy] [Request] [Token] (c : NCells) (zk : Nat → Point) (call : Nat) : E :=
  sumTo (2 ^ (zk call).size) fun i => eq (zk call) i * keyTable c call (i / T) (i % T)

/-- The head's six key vectors, at what was heard, reads in truth: what the caller hands to "join". -/
def keysAt (g : Given) (H : HeardAll) (c : NCells) : Array Form :=
  let _ : Norm.Heard := H.1
  let _ : FinalNorm.Heard := H.2.1
  let _ : Heard := H.2.2
  let _ : FinalNorm.Reads := normReadsAtCells c
  let _ : Reads := readsAt c.toCells
  (g.calls.map fun cl => keyVector key cl.1 cl.2).toArray

/-- The six extensions, as constant forms. -/
def trueKeys (g : Given) (zk : Nat → Point) (c : NCells) : Array Form :=
  (Array.range 6).map fun call => Aff.ofConst (trueKey c zk call)

/-- The form of "join" at the head's key vectors is worth 0. gk: what the lookup has heard. -/
def JoinOpened (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) : Prop :=
  ∃ g H, given p L s = .ok g ∧ L.heard s = some H ∧
    vW (worldE (L.ledger s) mask noEnt) (Came.joinForm gk (keysAt g H c)) = 0

/-- The same formula, fed with the extensions of the calls' tables at their key points, is worth 0. -/
def KeysWorth (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) : Prop :=
  ∃ g z, given p L s = .ok g ∧ L.lookup s = some z ∧
    vW (worldE (L.ledger s) mask noEnt) (Came.joinForm gk (trueKeys g z.2 c)) = 0

namespace Came

theorem rd_trueKey [Sizes] [Policy] [Request] [Token] (c : NCells) (zk : Nat → Point) (call : Nat) :
    rd (trueKey c zk call) = (Finset.range (2 ^ (zk call).size)).sum fun i =>
      rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T)) := by
  unfold trueKey
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun _ _ => rd_mul _ _

theorem getD_map_toArray {α β : Type} (l : List α) (f : α → β) (i : Nat) (hi : i < l.length)
    (x : β) (y : α) : ((l.map f).toArray).getD i x = f (l.getD i y) := by
  have h1 : i < (l.map f).toArray.size := by simpa using hi
  rw [Array.getD, dif_pos h1]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem trueKeys_getD (g : Given) (zk : Nat → Point) (c : NCells) (call : Nat) (h : call < 6) :
    (trueKeys g zk c).getD call (Aff.ofConst zeroE) = Aff.ofConst (trueKey c zk call) := by
  simp [trueKeys, Array.getD, h]

theorem keys_worth (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (hC : Closed p L s c mask)
    (hJ : JoinOpened p L s c mask gk) : KeysWorth p L s c mask gk := by
  obtain ⟨g, H, z, hg, hH, hz, hcl⟩ := hC
  obtain ⟨g', H', hg', hH', hj⟩ := hJ
  rw [hg] at hg'
  obtain rfl : g = g' := Except.ok.inj hg'
  rw [hH] at hH'
  obtain rfl : H = H' := Option.some.inj hH'
  refine ⟨g, z, hg, hz, ?_⟩
  rw [← hj]
  have hlen : g.calls.length = 6 := by
    obtain ⟨_, _, _, _, _, rfl⟩ := given_ok p L s g hg
    rfl
  have hk : ∀ call, call < 6 → (g.calls.getD call (0, [])).2 = callKeys call := by
    obtain ⟨z', y, _, _, _, rfl⟩ := given_ok p L s g hg
    intro call hc
    exact @calls_keys p.sizes p.floor z'.1 z'.2 call hc
  have hkeys := hcl.2.1
  refine joinForm_congr Reading.gl _ gk _ _ ?_ fun call hc => ?_
  · simp [trueKeys, keysAt, hlen]
  · have hc6 : call < 6 := by simpa [trueKeys] using hc
    rw [trueKeys_getD g z.2 c call hc6, Aff.value_ofConst]
    have e2 := hkeys call hc6
    rw [rd_atWorld] at e2
    unfold keysAt
    rw [getD_map_toArray _ _ call (by rw [hlen]; exact hc6) _ (0, [])]
    rw [hk call hc6]
    exact (rd_trueKey c z.2 call).trans e2.symm

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.keys_worth
