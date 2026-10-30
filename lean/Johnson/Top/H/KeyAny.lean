-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyAny.lean: the keys of the two lookups of a key file over any matrix and any
configuration.

Definitions, statements and proofs. This file builds the record
over any configuration and any reading of a matrix off a message.



Main names:





  `baseP C k mat`: a record over the configuration C that holds the reading `mat` of a matrix off a
    message, and nothing else: no oracle message, no forest that means anything.
  `keyDA`, `keyTA C k mat l₀ l₁`: the data and the record with the keys of the two lookups, over
    `baseP`.
  `PartsIn`, `keyTA_inT`: "the keys of all parts of both lookups over the matrix M lie in their
    tables"; it is what the record's `InT` says at all 24 forests.
  `keyTA_laws`: `LdWfP.Laws` of the record, if a message holds an index exactly when `PartsIn` holds
    of its matrix, and the configuration has the two laws `held_hold` and `dcd_enc`.
Limits: at the configuration of a stored table (`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean) an index is
any matrix, and a message holds its matrix only if that is in range; so the hypothesis `held_hold`
cannot be met there, whatever the honest side's data are, as soon as one matrix is out of range: at
that configuration `keyTA_laws` says nothing. The three conditions of `keyTA_laws` are hypotheses;
no configuration is given here. Where a configuration defines "holds an index" by `PartsIn`, the
first is met by definition; what `PartsIn` then means is not shown here: the library's
`keysGl_describes` is stated for matrices over the base field and is not joined here. The
messages' half of the record is empty, and its `mult` is the condition that is always true
(Johnson/Pack/KeyHalf.lean, Limits). Nothing on multiplicities or on knowledge soundness.
-/
import Johnson.Top.H.KeyRangesThm

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Iop Prob Hiop Cb Cb.Lkp Cm Cm.WfGl OnBytes.Slice
open Inst.Model.Layout (hRef)
open OnBytes.Params (WfRun WfPart WfLookup)

/-- The keys of all parts of both lookups, over the matrix M, lie in their tables. -/
def PartsIn (l₀ l₁ : WfLookup) (k : ℕ) (M : Fin hRef × (Fin k → Bool) → GE) : Prop :=
  (∀ f < 12, InTable ((partAt l₀ f).logPlaces + k) 8
    (keyOf k M (oP l₀ (partAt l₀ f)) (coP hRef l₀ (partAt l₀ f))) fun u => ((u : ℕ) : GE)) ∧
  ∀ f < 12, InTable ((partAt l₁ f).logPlaces + k) 13
    (keyOf k M (oP l₁ (partAt l₁ f)) (coP hRef l₁ (partAt l₁ f))) fun u => ((u : ℕ) : GE)

section Any
variable (C : ConfigurationWithOutOfDomainSample) (k : ℕ) (mat : C.Msg → Fin hRef × (Fin k → Bool) → GE)

/-- A record that holds the reading of a matrix off a message, and nothing else. -/
@[reducible] noncomputable def baseP : LdWfP GE C where
  S := Sig.nil GE
  Sd := Sig.Seeds.indep _
  Body := Unit
  body := fun _ => ()
  bodyOf := fun _ => ()
  N := Unit
  ent := fun _ _ => 0
  n := 0
  v := fun _ => 0
  d := fun _ => 0
  key := fun _ _ _ => 0
  tab := fun _ _ => 0
  mult := fun _ _ _ => True
  nR := fun _ => 0
  gC := fun _ _ => False
  gR := fun _ b => b.elim0
  Rw := Fin hRef
  k := k
  mat := mat
  off := fun _ _ => 0
  gOf := fun _ _ _ => 0
  cOf := fun _ _ _ => 0
  Z := Evader.powers GE 1
  deg := 2
  wAt := fun _ => ()

variable (l₀ l₁ : WfLookup)

/-- The data: forest f < 12 is part f of the first lookup, forest 12 + j part j of the second. -/
noncomputable def keyDA : KeysD (baseP C k mat) where
  n := 23
  rv := fun f => (partAt (lkP l₀ l₁ f) (ptI f)).logPlaces
  d := dK
  o := fun f => oP (lkP l₀ l₁ f) (partAt (lkP l₀ l₁ f) (ptI f))
  co := fun f => coP hRef (lkP l₀ l₁ f) (partAt (lkP l₀ l₁ f) (ptI f))
  tab := fun _ u => (u : GE)
  Z := Evader.powers GE 24

/-- The record. -/
noncomputable abbrev keyTA : LdWfP GE C := (keyDA C k mat l₀ l₁).T

/-- What the record's `InT` says at all 24 forests. -/
theorem keyTA_inT (U : C.Msg) :
    (∀ f, f ≤ (keyDA C k mat l₀ l₁).n → (keyTA C k mat l₀ l₁).InT f U) ↔
      PartsIn l₀ l₁ k (mat U) := by
  have one : ∀ f, (keyTA C k mat l₀ l₁).InT f U ↔
      InTable ((partAt (lkP l₀ l₁ f) (ptI f)).logPlaces + k) (dK f)
        (keyOf k (mat U) (oP (lkP l₀ l₁ f) (partAt (lkP l₀ l₁ f) (ptI f)))
          (coP hRef (lkP l₀ l₁ f) (partAt (lkP l₀ l₁ f) (ptI f))))
        (fun u => ((u : ℕ) : GE)) := fun _ => Iff.rfl
  constructor
  · intro g
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := (one j).1 (g j (show j ≤ 23 by omega))
      simp only [lkP, dK, ptI, if_pos hj] at this
      exact this
    · have := (one (12 + j)).1 (g (12 + j) (show 12 + j ≤ 23 by omega))
      simp only [lkP, dK, ptI, if_neg (show ¬ 12 + j < 12 by omega),
        Nat.add_sub_cancel_left] at this
      exact this
  · intro g f hf
    rw [one]
    by_cases hlt : f < 12
    · simp only [lkP, dK, ptI, if_pos hlt]
      exact g.1 f hlt
    · have hf' : f ≤ 23 := hf
      simp only [lkP, dK, ptI, if_neg hlt]
      exact g.2 (f - 12) (by omega)

/-- The laws of the record. -/
theorem keyTA_laws (hd : ∀ U, (C.held U).isSome ↔ PartsIn l₀ l₁ k (mat U))
    (h1 : ∀ i η, C.held (C.hold i η) = some i)
    (h2 : ∀ m r s, C.dcd (C.enc m r) (s, C.smp s m) = some m) : (keyTA C k mat l₀ l₁).Laws :=
  (keyDA C k mat l₀ l₁).laws (fun U => (hd U).trans (keyTA_inT C k mat l₀ l₁ U).symm) h1 h2

end Any
end Johnson.Pack

#print axioms Johnson.Pack.keyTA_inT
#print axioms Johnson.Pack.keyTA_laws
