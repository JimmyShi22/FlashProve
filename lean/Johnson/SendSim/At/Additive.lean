-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Additive.lean: if the job fits its place and RidesAdd holds, the field lay of the
instance of the general model is additive. The proof of Spec.additiveOf; and, under the same
premises, a row's entries at a sum of two values of the coins.
Terms: Johnson/SendSim/At/Sim.lean; sender, put, entry, RidesAdd, RidesZero:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Algebra; no distribution is named.
  additiveOf     Spec.additiveOf, the statement of the title. Its premises: the job fits its place
                 (sendFits), and RidesAdd (the entries of a table that is sent along, in its 2 ^ h
                 rows, are additive in its coins).
  put_add        put (s + s') is addC (put s) (put s'), the sum coin by coin. No premise.
  entry_add      Under the premises of additiveOf: an entry of a row's message at the data and addC
                 c c' is the entry at the data and c plus the entry at no data and c'.
  entry_zadd     If the job fits its place and RidesZero (a table that is sent along has entries 0
                 in its 2 ^ h rows if its coins are all 0) holds: an entry of a row's message at the
                 data and c is the entry at the data and coins that are all 0 plus the entry at no
                 data and c.
  tailEntry_add  The analogue of entry_add for an entry of a row's tail. No premise. It completes
                 entry_add; no file uses it.
  sum_ite_add, cs_ext, add_f, add_e   Tools: a sum of "if p n then (s + s') n else 0" splits; two
                 values of the coins with the same fields are equal; the fields of addC.

Limits. RidesAdd and RidesZero are premises here; both hold for every ride (ridesAdd, ridesZero,
Johnson/SendSim/At/RideLay.lean).

How it fits. additive_paid (Johnson/SendSim/At/Paid.lean) is additiveOf without RidesAdd;
Johnson/SendSim/At/ClearOfFold.lean and Johnson/SendSim/At/FoldAny.lean use it for the model's
premise MendsOff, so for rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny
(Johnson/SendSim/At/FreshWideProofs.lean). Johnson/SendSim/At/Split.lean uses entry_zadd,
Johnson/SendSim/At/MendsOf.lean uses put_add, so the file serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) too, and Johnson/SendSim/At/Runs.lean, CutProof.lean and
WriteAll.lean use cs_ext. The proofs rest on the lemmas on the six fields of rowsR
(Johnson/SendSim/At/Rows.lean).
-/
import Johnson.SendSim.At.Rows
import Johnson.SendSim.At.Put

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

theorem sum_ite_add {N : Type} [Fintype N] (p : N → Prop) [DecidablePred p] (s s' : N → GF) :
    (∑ n, if p n then (s + s') n else 0) =
      (∑ n, if p n then s n else 0) + ∑ n, if p n then s' n else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : p n
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem cs_ext {d : Due} (c c' : Cs d) (hf : c.f = c'.f) (he : c.e = c'.e) : c = c' := by
  cases c
  cases c'
  simp only at hf he
  rw [hf, he]

theorem add_f {d : Due} (c c' : Cs d) : (addC c c').f = c.f + c'.f := rfl

theorem add_e {d : Due} (c c' : Cs d) : (addC c c').e = c.e + c'.e := rfl

/-- put is additive: put (s + s') is the sum, coin by coin, of put s and put s'. -/
theorem put_add (s s' : CoinN P ride → GF) :
    put P ride (s + s') = addC (put P ride s) (put P ride s') := by
  refine cs_ext _ _ (funext fun i => ?_) (funext fun i => ?_)
  · rw [add_f, Pi.add_apply, put_f, put_f, put_f]
    exact sum_ite_add _ s s'
  · rw [add_e, Pi.add_apply, put_e, put_e, put_e, ← against_add]
    refine congrArg against (funext fun t => ?_)
    exact sum_ite_add _ s s'

variable (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c c' : Cs (dueR P ride))

/-- If the job fits its place (sendFits) and RidesAdd holds, an entry of a row's message at the data
and addC c c' is the entry at the data and c plus the entry at no data and c'. -/
theorem entry_add (hf : sendFits P ride = true) (hR : RidesAdd ride) (ρ : RowN P) (j : ℕ) :
    entry P (rowsR P ride data (addC c c')) ρ j =
      entry P (rowsR P ride data c) ρ j + entry P (rowsR P ride (fun _ _ _ => none) c') ρ j := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · show (if (shapeAt P k).mainDeg == 3 then _ else _) =
      (if (shapeAt P k).mainDeg == 3 then _ else _) + if (shapeAt P k).mainDeg == 3 then _ else _
    split
    · rw [mainE_add, crd_add]
    · rw [mainF_add]
  · show crd t _ = crd t _ + crd t _
    rw [mask_add P ride data c k c' hf hR k.isLt, crd_add]

/-- If the job fits its place (sendFits) and RidesZero holds, an entry of a row's message at the
data and c is the entry at the data and coins that are all 0 plus the entry at no data and c. -/
theorem entry_zadd (hf : sendFits P ride = true) (hZ : RidesZero ride) (ρ : RowN P) (j : ℕ) :
    entry P (rowsR P ride data c) ρ j =
      entry P (rowsR P ride data (zc _)) ρ j +
        entry P (rowsR P ride (fun _ _ _ => none) c) ρ j := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · have h1 := mainE_add P ride data (zc _) k c r.val j
    have h2 := mainF_add P ride data (zc _) k c r.val j
    rw [zc_add] at h1 h2
    show (if (shapeAt P k).mainDeg == 3 then _ else _) =
      (if (shapeAt P k).mainDeg == 3 then _ else _) + if (shapeAt P k).mainDeg == 3 then _ else _
    split
    · rw [h1, crd_add]
    · rw [h2]
  · show crd t _ = crd t _ + crd t _
    rw [mask_zadd P ride data c k hf hZ k.isLt, crd_add]

/-- An entry of a row's tail at the data and addC c c' is the entry at the data and c plus the entry
at no data and c'. No premise. -/
theorem tailEntry_add (ρ : RowN P) (q : ℕ) :
    tailEntry P (rowsR P ride data (addC c c')) ρ q =
      tailEntry P (rowsR P ride data c) ρ q +
        tailEntry P (rowsR P ride (fun _ _ _ => none) c') ρ q := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · show (if (shapeAt P k).mainDeg == 3 then _ else _) =
      (if (shapeAt P k).mainDeg == 3 then _ else _) + if (shapeAt P k).mainDeg == 3 then _ else _
    split
    · rw [mainTlE_add, crd_add]
    · rw [mainTlF_add]
  · show crd t _ = crd t _ + crd t _
    rw [maskTl_add, crd_add]

/-- Proof of Spec.additiveOf: if the job fits its place and RidesAdd holds, the instance's lay is
additive. -/
theorem additiveOf : Spec.additiveOf := by
  intro P ride hf hR a b
  funext ρ j
  show entry P (rowsR P ride (fun _ _ _ => none) (put P ride (a + b))) ρ j =
    entry P (rowsR P ride (fun _ _ _ => none) (put P ride a)) ρ j +
      entry P (rowsR P ride (fun _ _ _ => none) (put P ride b)) ρ j
  have e : put P ride (a + b) = addC (put P ride a) (put P ride b) := put_add P ride a b
  rw [e]
  exact entry_add P ride _ _ _ hf hR ρ j

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.put_add
#print axioms OnBytes.SendSim.At.entry_add
#print axioms OnBytes.SendSim.At.additiveOf
