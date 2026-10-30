-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadJoin.lean: the one claim that ties the key vectors of the output head's lookup
calls to the lookup.

The check of the output head's sub-proof builds one form for each lookup call (keyForm), hands the
forms to the lookup's routine Forest.join (OnBytes/Model/Look.lean), and adds the form that this
routine returns as a claim (claimJoin in OnBytes/Model/Head.lean). This file says which form
Forest.join returns and what it is worth in the calls' forms. That claimJoin adds that form is in
Johnson/Road/HeadLink.lean (claimJoin_form).

Main theorems: ok_paid; foldl_addMul_value; ok_join (the form that Forest.join returns), join_value.

What is not claimed. What a call's form is worth is not said here (Johnson/Road/HeadCols.lean has
it). Nothing is said about the hidden value at the end of the lookup's key side, about the
weights of the calls, or about what a lookup shows. The theorems begin "if the routine succeeds".
The program does not import this file.
-/
import Johnson.Road.HeadCall

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)

/-- Marking an owed claim as added always succeeds; it changes the list of owed claims alone. -/
theorem ok_paid (i : ℕ) (F G : Fork) (C D : Ctx) (u : Unit) :
    Ok (SubM.paid i) F C u G D ↔ G = F.paid i ∧ D = C := by
  have e : SubM.paid i F C = .ok (((), F.paid i), C) := rfl
  unfold Ok
  rw [e]
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

section Join

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- A fold that adds k c times the form g c for c below n. -/
theorem foldl_addMul_value (g : ℕ → Aff) (k : ℕ → E) (a : Aff) : ∀ n : ℕ,
    ((List.range n).foldl (fun f c => Aff.addMul f (g c) (k c)) a).value ρ W =
      a.value ρ W + ∑ c ∈ range n, ρ.val (k c) * (g c).value ρ W
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Aff.value_addMul,
      foldl_addMul_value g k a n, Finset.sum_range_succ, add_assoc]

/-- The part of the lookup's join on the trees that hold padding alone. -/
def emptyE (g : Model.Forest.Heard) : E :=
  (List.range (2 ^ g.shape.rK - g.shape.NT)).foldl
    (fun s i => addE s (mulE ((Model.eqTab g.zy).getD (g.shape.NT + i) zeroE)
      (subE g.alpha (g.padKey 0)))) zeroE

variable {ρ W}

/-- What Forest.join returns: it marks its claim as added, leaves the context, and the form is the
sum over the calls, plus the part of the trees with padding alone, minus the end of the key side. -/
theorem ok_join {g : Model.Forest.Heard} {KF : Array Aff} {F G : Fork} {C D : Ctx} {f : Aff}
    (h : Ok (Model.Forest.join g KF) F C f G D) :
    G = F.paid g.owedJoin ∧ D = C ∧ KF.size = g.shape.calls.size ∧
      f = (List.range KF.size).foldl
          (fun (f : Aff) c =>
            Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
              KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE))
          (Aff.ofConst zeroE) + Aff.ofConst (emptyE g) - g.cEnd := by
  unfold Model.Forest.join at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h2⟩ := h
  rw [ok_lift, mustAs_ok] at h1
  obtain ⟨⟨hb, rfl⟩, rfl⟩ := h1
  rw [ok_bind] at h2
  obtain ⟨_, F2, C2, h3, h4⟩ := h2
  have h3' : Ok (SubM.paid g.owedJoin) F1 C1 () F2 C2 := h3
  rw [ok_paid] at h3'
  obtain ⟨rfl, rfl⟩ := h3'
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  have hb' := (Bool.and_eq_true _ _ ▸ hb)
  exact ⟨rfl, rfl, beq_iff_eq.mp hb'.1, rfl⟩

/-- What the join's form is worth. -/
theorem join_value (g : Model.Forest.Heard) (KF : Array Aff) :
    ((List.range KF.size).foldl
        (fun (f : Aff) c =>
          Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
            KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE))
        (Aff.ofConst zeroE) + Aff.ofConst (emptyE g) - g.cEnd).value ρ W =
      ∑ c ∈ range KF.size, ρ.val (g.e.getD c zeroE) *
          (ρ.val g.alpha - ρ.val (ofF c.toUInt64) * ρ.val g.theta -
            (KF.getD c (Aff.ofConst zeroE)).value ρ W) +
        ρ.val (emptyE g) - g.cEnd.value ρ W := by
  rw [Aff.value_sub, Aff.value_add, Aff.value_ofConst,
    foldl_addMul_value ρ W
      (fun c => Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
        KF.getD c (Aff.ofConst zeroE)) (fun c => g.e.getD c zeroE),
    Aff.value_ofConst, ρ.zero, zero_add]
  congr 2
  refine sum_congr rfl fun c _ => ?_
  rw [Aff.value_sub, Aff.value_ofConst, ρ.sub, scaleE_val]

end Join

#print axioms ok_join
#print axioms join_value

end OnBytes.Road.Hd
