-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/KeptFormJoin.lean: the code switch: A FORM ON A KEPT MEMBER's OLD
MAIN TABLE, carried over by the program (SwitchFrame.addKept), is the typed vector that has the
form's entries on that member's kept slots, carried along the map of names iJ.

Both the carried claim (its forms on kept members) and every old sample row of a kept member are
made by addKept. So this one join serves both. THE TEXT's SIDE: addKept_new, addKept_g,
addKept_other (OnBytes/Slice/BlkCsKept.lean). THE TYPED SIDE: pushTo iJ (slotVec …): slotVec has, at
entry j of a slot κ of the member number a, the form's entry at the index row κ + 2 ^ rowBits * j of
the member's table, and 0 elsewhere. THE DICTIONARY: keptAt, pushTo_names, readAt_kept, sum_row
(Johnson/Top/H/SwitchMaps.lean).
Main names:
  pushTo_slots    carried coefficients that are 0 outside the kept slots: a sum over the slots
  stretchAt_sum   a sum of stretches is the stretch of the sums
  Slots           what is asked of one kept member and its slots: its new message's number, which is
                  not g's; its pad's indices differ; each of its rows has just one slot; the indices
                  of its new message's entries, and of its pad, name a row of the member and a place
                  of the row
  pick            of all slots just one holds the row of a given index
  slotVec, keptForm_reads  THE JOIN
LIMITS. Slots, like NamesK, is a PREMISE (brought further, not paid: Paid.lean's paid_slots makes it
from the record AtSwitch, a premise; paid_claim alone calls it). ReadsAs speaks of the entries of
the new sending alone. The form c is any form: nothing is asked of it, and at indices that name no
entry nothing is said. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.DrawJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

theorem pushTo_slots {K A B Ent : Type} [Fintype K] [Fintype A] [Fintype B]
    (p : (Option K × A) ⊕ B → Ent) (c : (Option K × A) ⊕ B → GE)
    (h0 : ∀ a, c (.inl (none, a)) = 0) (hB : ∀ b, c (.inr b) = 0) (n : Ent) :
    pushTo p c n =
      ∑ κ, pushTo (fun a => p (.inl (some κ, a))) (fun a => c (.inl (some κ, a))) n := by
  unfold pushTo
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option]
  simp [h0, hB]

theorem stretchAt_sum {K : Type} [Fintype K] (places : SwitchPlaces) (first count : ℕ)
    (c : K → ℕ → GE) (J : ℕ) :
    ∑ κ, stretchAt places first count (c κ) J =
      stretchAt places first count (fun q => ∑ κ, c κ q) J := by
  unfold stretchAt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : places.get (first + q) = J
  · simp [h]
  · simp [h]

section Join
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] (cs : Codes) (l : List (OracleShape × ℕ))

/-- What is asked of the slots of the kept member number a, whose record in the frame is k. -/
structure Slots (W : SwitchFrame) (ids : ℕ → ℕ) (mem row : K → ℕ) (a : ℕ) (k : KeptPlace) :
    Prop where
  anewIs : ∀ n : (sigOf cs l).Ent, ids (entAt cs l n).1 = k.anew ↔ (entAt cs l n).1 = 1 + a
  notG : k.anew ≠ W.g
  nodup : (k.pad.map (·.index)).Nodup
  one : ∀ b, b < k.rows → ∃ κ, (mem κ = a ∧ row κ = b) ∧ ∀ κ', mem κ' = a → row κ' = b → κ' = κ
  entry : ∀ n : (sigOf cs l).Ent, (entAt cs l n).1 = 1 + a → (entAt cs l n).2.1 = Part.main →
    (entAt cs l n).2.2 % 2 ^ k.rowBits < k.rows ∧ (entAt cs l n).2.2 / 2 ^ k.rowBits < s.C.l
  pad : ∀ q, q < k.pad.length → (k.pad.getD q default).index % 2 ^ k.rowBits < k.rows ∧
    (k.pad.getD q default).index / 2 ^ k.rowBits < s.C.l

/-- The typed vector of a form on the old main table of the kept member number a. -/
noncomputable def slotVec (mem row : K → ℕ) (a rb : ℕ) (c : Form) : (s.cKept K).J → GE
  | .inl (some κ, j) => if mem κ = a then formAt c (row κ + 2 ^ rb * j.val) else 0
  | _ => 0

end Join

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}

omit [DecidableEq K] in
/-- Of all slots just one holds the row of the index X. -/
theorem pick {a : ℕ} {k : KeptPlace} (Sl : Slots s K cs l W ids mem row a k) (c : Form) (X : ℕ)
    (h1 : X % 2 ^ k.rowBits < k.rows) (h2 : X / 2 ^ k.rowBits < s.C.l) :
    (∑ κ, if mem κ = a then
        (if X % 2 ^ k.rowBits = row κ then
          onNat (fun j : Fin s.C.l => formAt c (row κ + 2 ^ k.rowBits * j.val)) (X / 2 ^ k.rowBits)
          else 0) else 0) = formAt c X := by
  obtain ⟨κ0, ⟨m0, r0⟩, uniq⟩ := Sl.one _ h1
  rw [Finset.sum_eq_single κ0]
  · rw [if_pos m0, if_pos r0.symm]
    unfold onNat
    rw [dif_pos h2, r0]
    exact congrArg (formAt c) (Nat.mod_add_div X _)
  · intro κ _ hne
    by_cases hm : mem κ = a
    · rw [if_pos hm, if_neg]
      intro e
      exact hne (uniq κ hm e.symm)
    · rw [if_neg hm]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **A form on a kept member's old main table, carried over.** -/
theorem keptForm_reads (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (a : ℕ) (k : KeptPlace)
    (hk : W.kept[a]? = some k) (Sl : Slots s K cs l W ids mem row a k) (c : Form) :
    ReadsAs cs l ids (W.addKept {} k c) (pushTo iJ (slotVec s K mem row a k.rowBits c)) := by
  intro n
  have hpl : ∀ κ, mem κ = a → pl κ = k := fun κ e => by
    have h := member κ
    rw [e, hk] at h
    exact (Option.some.inj h).symm
  have each : ∀ κ, pushTo (fun j : Fin s.C.l => iJ (.inl (some κ, j)))
      (fun j => slotVec s K mem row a k.rowBits c (.inl (some κ, j))) n =
      if mem κ = a then
        ((if (entAt cs l n).1 = 1 + a ∧ (entAt cs l n).2.1 = Part.main then
          (if (entAt cs l n).2.2 ∈ k.pad.map (·.index) then 0
            else if (entAt cs l n).2.2 % 2 ^ k.rowBits = row κ then
              onNat (fun j : Fin s.C.l => formAt c (row κ + 2 ^ k.rowBits * j.val))
                ((entAt cs l n).2.2 / 2 ^ k.rowBits) else 0) else 0) +
        if (entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart then
          stretchAt W.places k.oldPadAt k.pad.length
            (fun q => if (k.pad.getD q default).index % 2 ^ k.rowBits = row κ then
              onNat (fun j : Fin s.C.l => formAt c (row κ + 2 ^ k.rowBits * j.val))
                ((k.pad.getD q default).index / 2 ^ k.rowBits) else 0) (entAt cs l n).2.2
        else 0) else 0 := by
    intro κ
    by_cases hm : mem κ = a
    · have hp := hpl κ hm
      have hb : row κ < 2 ^ k.rowBits := hp ▸ DK.rowLt κ
      have hmsg : ∀ j : Fin s.C.l, entAt cs l (iJ (.inl (some κ, j))) =
          keptAt W a k (row κ) j.val := fun j => by
        rw [DK.keptMsg κ j, hm, hp]
      have e : (fun j : Fin s.C.l => slotVec s K mem row a k.rowBits c (.inl (some κ, j))) =
          fun j => formAt c (row κ + 2 ^ k.rowBits * j.val) := by
        funext j
        show (if mem κ = a then formAt c (row κ + 2 ^ k.rowBits * j.val) else 0) = _
        rw [if_pos hm]
      rw [if_pos hm, e]
      refine ((pushTo_names cs l (fun j : Fin s.C.l => iJ (.inl (some κ, j))) _ hmsg _ n).trans
        (readAt_kept W a k (row κ) s.C.l _ Sl.nodup (entAt cs l n).1 (entAt cs l n).2.1
          (entAt cs l n).2.2)).trans ?_
      simp only [sum_row k.rowBits (row κ) s.C.l hb]
    · have e : (fun j : Fin s.C.l => slotVec s K mem row a k.rowBits c (.inl (some κ, j))) =
          fun _ => 0 := by
        funext j
        show (if mem κ = a then formAt c (row κ + 2 ^ k.rowBits * j.val) else 0) = _
        rw [if_neg hm]
      rw [if_neg hm, e]
      unfold pushTo
      simp
  have split := pushTo_slots (K := K) (A := Fin s.C.l) (B := Fin s.Z.l ⊕ Fin s.Z.l) iJ
    (slotVec s K mem row a k.rowBits c) (fun _ => rfl) (fun _ => rfl) n
  rw [split]
  simp only [each]
  by_cases cA : (entAt cs l n).1 = 1 + a ∧ (entAt cs l n).2.1 = Part.main
  · have n0 : ¬ ((entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart) := fun c => by
      have := cA.1
      omega
    simp only [if_pos cA, if_neg n0, add_zero]
    rw [(Sl.anewIs n).2 cA.1, cA.2]
    show coefAt (switchAddKept {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c) k.anew
      Part.main (entAt cs l n).2.2 = _
    rw [addKept_new {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c Sl.notG Sl.nodup,
      coefAt_empty, zero_add]
    by_cases hp : (entAt cs l n).2.2 ∈ k.pad.map (·.index)
    · simp [hp]
    · simp only [if_neg hp]
      exact (pick Sl c _ (Sl.entry n cA.1 cA.2).1 (Sl.entry n cA.1 cA.2).2).symm
  · by_cases cB : (entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart
    · simp only [if_neg cA, if_pos cB, zero_add]
      rw [(D.gIs n).2 cB.1, cB.2]
      show coefAt (switchAddKept {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c) W.g
        W.restPart (entAt cs l n).2.2 = _
      rw [addKept_g {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c Sl.notG, coefAt_empty,
        zero_add]
      have e : ∀ (κ : K) (f : ℕ → GE),
          (if mem κ = a then stretchAt W.places k.oldPadAt k.pad.length f (entAt cs l n).2.2
            else 0) =
          stretchAt W.places k.oldPadAt k.pad.length (fun q => if mem κ = a then f q else 0)
            (entAt cs l n).2.2 := by
        intro κ f
        by_cases hm : mem κ = a
        · simp [hm]
        · simp [hm, stretchAt]
      simp only [e]
      rw [stretchAt_sum]
      exact stretchAt_congr _ _ _ _ _
        (fun q hq => (pick Sl c _ (Sl.pad q hq).1 (Sl.pad q hq).2).symm) _
    · simp only [if_neg cA, if_neg cB, add_zero]
      show coefAt (switchAddKept {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c) _ _ _ = _
      rw [addKept_other {} k.pad k.anew W.g W.restPart W.places k.oldPadAt c _ _
        (fun h => cA ⟨(Sl.anewIs n).1 h.1, h.2⟩) (fun h => cB ⟨(D.gIs n).1 h.1, h.2⟩), coefAt_empty]
      simp

end Join

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.pick
#print axioms VerifiableInference.Desc.First.K2Hands.keptForm_reads
