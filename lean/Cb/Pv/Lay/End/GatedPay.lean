-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedPay.lean: from the ledger of the verifier's claims on the gated products to what
the chain of a layers' sub-proof's own rounds owes at its end for the two product layers.

The chain owes at its end (Cb/Pv/Lay/End/Last.lean) all output claims of the sumchecks of the two
product layers of the gated products. This file pays these two clauses, at the records of
Cb/Pv/Lay/At/Foot.lean, from three things. The ledger of the claims on the gated products holds of
early entries m and late entries u. The late entries are what the tables of reads are meant to be
(GatedTables in Cb/Pv/Lay/End/GatedCl.lean). For each sumcheck, the claim which it leaves, a letter
of the ledger, says its first output claim.

Main definitions: GatedReads (names of the late entries), gNamesAt, gatedEAt (the letters of the
claims, off the two sumchecks' outputs), gatedLed (the ledger).
Main theorems: gated_bill_at (GatedLast at these letters gives the rows on the four end values),
gated_pay.

Limits. hU5, hU6 (what the letters u5, u6 say) and GatedTables are premises here;
Cb/Pv/Lay/End/GatedShare.lean takes both away (gated_pull). That the ledger is a program's is not
said here. There are at least two layers (1 ≤ lL); the number of hidden units of an expert is a
power of two; a block is no longer than the hidden units of a layer or of an expert.


-/
import Cb.Pv.Lay.End.Led
import Cb.Pv.Lay.At.Foot
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model.FFSeg (slV upV slV' upV' lF lFe)
open Blocks (ext)

/-- The members of a list with one thing before it and one thing behind its first two members. -/
theorem mem_two_two {α : Type} (a b f : α) (l : List α) :
    f ∈ a :: (l.take 2 ++ b :: l.drop 2) ↔ f = a ∨ f = b ∨ f ∈ l := by
  simp only [List.mem_cons, List.mem_append]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (List.mem_of_mem_take h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_of_mem_drop h))
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · have h' : f ∈ l.take 2 ++ l.drop 2 := by
        rw [List.take_append_drop]
        exact h
      rcases List.mem_append.mp h' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

/-- The names of the late entries that the claims on the gated products read. -/
structure GatedReads (J₂ : Type) where
  uS5 : ℕ → ℕ → ℕ → J₂
  uU5 : ℕ → ℕ → ℕ → J₂
  uS6 : ℕ → ℕ → ℕ → J₂
  uU6 : ℕ → ℕ → ℕ → J₂

variable {E : Type} [Field E] [Fintype E] (P : FootPar0 E) {J₂ : Type}

/-- The names of the entries. -/
def gNamesAt (U : GatedReads J₂) : GatedNames (P.J ⊕ J₂) where
  mL5 := .inl (P.c5 false)
  mR5 := .inl (P.c5 true)
  mL6 := .inl (P.c6 false)
  mR6 := .inl (P.c6 true)
  uS5 l lam kh := .inr (U.uS5 l lam kh)
  uU5 l lam kh := .inr (U.uU5 l lam kh)
  uS6 l lam kh := .inr (U.uS6 l lam kh)
  uU6 l lam kh := .inr (U.uU6 l lam kh)

/-- The letters of the claims, off the outputs of the two sumchecks. -/
noncomputable def gatedEAt (o5 : P.gp.toSum.T.par.Out) (o6 : P.rt.L.toSum.T.par.Out) :
    GatedE E where
  r5 := Blocks.nat fun i => (noKept P.gp.Sm).outPt P.gp.Mk o5 (P.gp.e.symm i)
  r6 := Blocks.nat fun i => (noKept P.rt.L.Sm).outPt P.rt.L.Mk o6 (P.rt.L.e.symm i)
  β5 := (noKept P.gp.Sm).outB P.gp.Mk o5
  β6 := (noKept P.rt.L.Sm).outB P.rt.L.Mk o6
  shL5 := o5.vals false
  shR5 := o5.vals true
  shL6 := o6.vals false
  shR6 := o6.vals true

/-- With a bit of layers there are 2^(lL - 1) routed layers. -/
theorem ne_pow (h1 : 1 ≤ P.D.lL) : P.D.ne = 2 ^ (P.D.lL - 1) := by
  show 2 ^ P.D.lL / 2 = _
  obtain ⟨n, hn⟩ : ∃ n, P.D.lL = n + 1 := ⟨P.D.lL - 1, by omega⟩
  rw [hn, pow_succ, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by norm_num)]

/-- What the four claims pay of what the chain owes at its end. -/
theorem gated_bill_at (U : GatedReads J₂) (o5 : P.gp.toSum.T.par.Out)
    (o6 : P.rt.L.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E) (h1 : 1 ≤ P.D.lL)
    (L : GatedLast (gNamesAt P U) (gatedEAt P o5 o6) P.D (P.rd m) (Sum.elim m u)) :
    (∀ b, P.gp.toSum.T.par.EHolds o5 m b) ∧ ∀ b, P.rt.L.toSum.T.par.EHolds o6 m b := by
  refine ⟨fun b => ?_, fun b => ?_⟩
  · rw [ProdL.kval_iff]
    cases b
    · have h := L.L5
      show ext (P.D.lL + lF P.D + P.D.lT) (slV P.D (P.rd m)) (gatedEAt P o5 o6).r5 +
        m (P.c5 false) * (gatedEAt P o5 o6).β5 = o5.vals false
      rw [← h]
      show o5.vals false - (gatedEAt P o5 o6).β5 * m (P.c5 false) + _ = _
      ring
    · have h := L.R5
      show ext (P.D.lL + lF P.D + P.D.lT) (upV P.D (P.rd m)) (gatedEAt P o5 o6).r5 +
        m (P.c5 true) * (gatedEAt P o5 o6).β5 = o5.vals true
      rw [← h]
      show o5.vals true - (gatedEAt P o5 o6).β5 * m (P.c5 true) + _ = _
      ring
  · rw [ProdL.kval_iff]
    have hk : P.D.lL - 1 + (lFe P.D + P.D.lT) = P.D.lL - 1 + lFe P.D + P.D.lT :=
      (Nat.add_assoc _ _ _).symm
    cases b
    · have h := L.L6
      have hc : ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (P.rt.L.vm o6.st m false)
          (gatedEAt P o5 o6).r6 =
          ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (slV' P.D (P.rd m)) (gatedEAt P o5 o6).r6 := by
        refine Blocks.ext_congr (fun X hX => ?_) _
        show (if P.D.ne * 2 ^ (lFe P.D + P.D.lT) ≤ X then 0 else slV' P.D (P.rd m) X) = _
        rw [if_neg]
        rw [ne_pow P h1, ← pow_add]
        omega
      show ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (P.rt.L.vm o6.st m false)
        (gatedEAt P o5 o6).r6 + m (P.c6 false) * (gatedEAt P o5 o6).β6 = o6.vals false
      rw [hc, hk, ← h]
      show o6.vals false - (gatedEAt P o5 o6).β6 * m (P.c6 false) + _ = _
      ring
    · have h := L.R6
      show ext (P.D.lL - 1 + (lFe P.D + P.D.lT)) (upV' P.D (P.rd m)) (gatedEAt P o5 o6).r6 +
        m (P.c6 true) * (gatedEAt P o5 o6).β6 = o6.vals true
      rw [hk, ← h]
      show o6.vals true - (gatedEAt P o5 o6).β6 * m (P.c6 true) + _ = _
      ring

variable [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The claims on the gated products as a ledger. u5, u6: the claims that the two sumchecks
leave. The order: the claim that the first sumcheck leaves, the claims on its two end values, then
the like for the second. -/
def gatedLed (N : GatedNames (P.J ⊕ J₂)) (e : GatedE E) (u5 u6 : Blocks.Form (P.J ⊕ J₂) E)
    (s : ℕ) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (u5 :: ((gatedCl N e P.D s).take 2 ++ u6 :: (gatedCl N e P.D s).drop 2))

/-- The two clauses that the chain owes at its end for the two product layers. -/
theorem gated_pay (U : GatedReads J₂) (o5 : P.gp.toSum.T.par.Out) (o6 : P.rt.L.toSum.T.par.Out)
    (u5 u6 : Blocks.Form (P.J ⊕ J₂) E) (m : P.J → E) (u : J₂ → E) (s : ℕ) (h1 : 1 ≤ P.D.lL)
    (hs1 : s ≤ lF P.D) (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D)
    (T : GatedTables (gNamesAt P U) (gatedEAt P o5 o6) P.D (P.rd m) s (Sum.elim m u))
    (h : TWhole.Ledger.Holds (gatedLed P (gNamesAt P U) (gatedEAt P o5 o6) u5 u6 s)
      (Sum.elim m u))
    (hU5 : Blocks.Form.val (Sum.elim m u) u5 = 0 → P.gp.toSum.T.par.UHolds o5 m)
    (hU6 : Blocks.Form.val (Sum.elim m u) u6 = 0 → P.rt.L.toSum.T.par.UHolds o6 m) :
    P.gp.toSum.T.par.OutHolds o5 m ∧ P.rt.L.toSum.T.par.OutHolds o6 m := by
  have hl := (ledOf_holds _ _).1 h
  have L := gated_last (gNamesAt P U) (gatedEAt P o5 o6) P.D (P.rd m) s (Sum.elim m u) hs1 hs2 hfe
    T fun f hf => hl f ((mem_two_two _ _ _ _).2 (Or.inr (Or.inr hf)))
  obtain ⟨a5, a6⟩ := gated_bill_at P U o5 o6 m u h1 L
  exact ⟨⟨hU5 (hl u5 ((mem_two_two _ _ _ _).2 (Or.inl rfl))), a5⟩,
    ⟨hU6 (hl u6 ((mem_two_two _ _ _ _).2 (Or.inr (Or.inl rfl)))), a6⟩⟩

end Cb.Pv.Lay.End.Gated
