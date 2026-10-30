-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/JoinValue.lean: THE LOOKUP's CLAIM ON THE CALLS' KEY VECTORS HANGS ON THE CALLER's FORMS THROUGH THEIR VALUES ALONE. A small law on
the lookup's own formula joinF (Johnson/Desc/First/Look/LookClaims.lean), for the exchange at a calling kind's row of the
table of joints: behind the caller's block: the form of "join" AT THE CALLER's FORMS is worth 0; in front of it: the same
formula FED WITH EACH CALL's KEY VECTOR's TRUE VALUE AT ITS KEY POINT is worth 0. No chance in it; general in the caller.
  joinForm      the formula's form, as a function of what was heard and the forms fed: it reads no ledger.
  joinF_spec    where joinF returns: its one test on sizes passes, the ledger behind is the ledger with the debt marked as
                paid, the tape is left, and the form is joinForm. And conversely.
  joinForm_congr   two arrays of forms of one size whose members are worth the same in a world: the two forms are worth the same.
  join_exchange    THE EXCHANGE: where joinF returns at the caller's forms KF, and v c is what KF's member number c is worth:
                it returns at the constants v c, with the same ledger and tape, a form that is worth the same.

-/
import Mathlib
import OnBytes.Model.HideLaws
import Johnson.Desc.First.Look.LookClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look (joinF joinAddedF paidF)

/-- One call's term. -/
def joinStep (g : Forest.Heard) (KF : Array Aff) (f : Aff) (c : Nat) : Aff :=
  Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta))
    - KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE)

/-- The public term for the trees that no call fills. -/
def joinEmpty (g : Forest.Heard) : E :=
  (List.range (2 ^ g.shape.rK - g.shape.NT)).foldl
    (fun s i => addE s (mulE ((eqTab g.zy).getD (g.shape.NT + i) zeroE)
      (subE g.alpha (g.padKey 0)))) zeroE

/-- **The formula's form.** -/
def joinForm (g : Forest.Heard) (KF : Array Aff) : Aff :=
  (List.range KF.size).foldl (joinStep g KF) (Aff.ofConst zeroE) + Aff.ofConst (joinEmpty g) - g.cEnd

theorem joinF_eq (g : Forest.Heard) (KF : Array Aff) :
    joinF g KF = (do
      Fl.must (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size)
      joinAddedF g
      pure (joinForm g KF)) := rfl

theorem joinF_spec (g : Forest.Heard) (KF : Array Aff) (F G : Fork) (t t' : Tape) (x : Aff) :
    joinF g KF F t = some (x, G, t') ↔
      (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size) = true ∧
        G = F.paid g.owedJoin ∧ t' = t ∧ x = joinForm g KF := by
  rw [joinF_eq]
  show Fl.andThen (Fl.must _) (fun _ => Fl.andThen (joinAddedF g) fun _ => Fl.ret (joinForm g KF)) F t
    = _ ↔ _
  cases hb : (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size) with
  | false => simp [Fl.andThen, Fl.must]
  | true =>
    simp only [Fl.andThen, Fl.must, joinAddedF, paidF, Fl.change, Fl.ret, if_true, Option.map_some,
      Option.some.injEq, Prod.mk.injEq, true_and]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

section Value
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem joinFold_congr (g : Forest.Heard) (KF KF' : Array Aff) : ∀ (l : List Nat) (f f' : Aff),
    f.value ρ W = f'.value ρ W →
    (∀ c, c ∈ l → (KF.getD c (Aff.ofConst zeroE)).value ρ W
      = (KF'.getD c (Aff.ofConst zeroE)).value ρ W) →
    (l.foldl (joinStep g KF) f).value ρ W = (l.foldl (joinStep g KF') f').value ρ W
  | [], _, _, h, _ => h
  | c :: l, f, f', h, hk => by
    simp only [List.foldl_cons]
    refine joinFold_congr g KF KF' l _ _ ?_ fun c' hc' => hk c' (List.mem_cons_of_mem _ hc')
    unfold joinStep
    rw [Aff.value_addMul, Aff.value_addMul, Aff.value_sub, Aff.value_sub, h,
      hk c (List.mem_cons_self)]

/-- **The form is worth what the fed forms' values make it.** -/
theorem joinForm_congr (g : Forest.Heard) (KF KF' : Array Aff) (hs : KF.size = KF'.size)
    (hk : ∀ c, c < KF.size → (KF.getD c (Aff.ofConst zeroE)).value ρ W
      = (KF'.getD c (Aff.ofConst zeroE)).value ρ W) :
    (joinForm g KF).value ρ W = (joinForm g KF').value ρ W := by
  unfold joinForm
  rw [Aff.value_sub, Aff.value_sub, Aff.value_add, Aff.value_add, ← hs,
    joinFold_congr ρ W g KF KF' (List.range KF.size) _ _ rfl
      fun c hc => hk c (List.mem_range.1 hc)]

/-- **THE EXCHANGE.** -/
theorem join_exchange (g : Forest.Heard) (KF : Array Aff) (F G : Fork) (t t' : Tape) (x : Aff)
    (h : joinF g KF F t = some (x, G, t')) (v : Nat → E)
    (hv : ∀ c, c < KF.size → (KF.getD c (Aff.ofConst zeroE)).value ρ W = ρ.val (v c)) :
    ∃ x', joinF g ((Array.range g.shape.calls.size).map fun c => Aff.ofConst (v c)) F t
        = some (x', G, t') ∧ x'.value ρ W = x.value ρ W := by
  obtain ⟨hb, rfl, rfl, rfl⟩ := (joinF_spec g KF F G t t' x).1 h
  have hb' := hb
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hb'
  have hsz : ((Array.range g.shape.calls.size).map fun c => Aff.ofConst (v c)).size
      = g.shape.calls.size := by simp
  refine ⟨_, (joinF_spec g _ F _ _ _ _).2 ⟨?_, rfl, rfl, rfl⟩, ?_⟩
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact ⟨hsz, hb'.2⟩
  · refine joinForm_congr ρ W g _ KF (by rw [hsz, hb'.1]) fun c hc => ?_
    rw [hsz] at hc
    rw [hv c (by rw [hb'.1]; exact hc)]
    have e : ((Array.range g.shape.calls.size).map fun c => Aff.ofConst (v c)).getD c
        (Aff.ofConst zeroE) = Aff.ofConst (v c) := by
      simp [Array.getD, hc]
    rw [e, Aff.value_ofConst]

end Value

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.join_exchange
