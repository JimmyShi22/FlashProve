-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AnySeat.lean: kind K5: the claims' law over every seat: the block's
three named runs as Johnson/Desc/First/Att/RunsK.lean states them (firstK, keysOfK, secondK),
general in the carried record St and in the seat (SeatC St).

Main names:
  `inOf_some`: what inOf hands on: i.g = c.geo; i.iU3 = c.iU3; i.zk is what the seat's accessor zk
    gives; i.p what pts gives; i.t what tablesP makes of them.
  `Spec.FirstSeat`, `KeysSeat`, `SecondSeat`, `WholeSeat`: where the seated run returns: the carried
    record is handed back untouched, and the forms and key forms are the written ones at oldOf Sh gL
    i and K, i and K being what inOf hands on.
Premises, all named in the statements: c.geo = geoOf Sh (parCOf A gives it at Sh := A.S by
unfolding); seat.zk s = some gL.zk; A.NC = Sh.calls.size.
Used of OnBytes: what Johnson/Desc/First/Att/Claims/Any.lean names.
Not claimed: that a claim holds.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts TablesP ParC SeatC geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)

variable {St : Type}

theorem inOf_some (seat : SeatC St) (c : ParC) (s : St) (i : P.Runs.In) (K : ℕ)
    (h : P.inOf seat c s = some (i, K)) :
    i.g = c.geo ∧ i.iU3 = c.iU3 ∧ seat.zk s = some i.zk ∧ seat.pts s = some i.p ∧ seat.cols s = some K ∧
      ∃ lk, seat.look s = some lk ∧ P.tablesP c.geo c.mats c.nW lk i.p = some i.t := by
  unfold P.inOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨p, hp, lk, hl, t, ht, zk, hz, K', hK, e, eK⟩ := h
  subst e eK
  exact ⟨rfl, rfl, hz, hp, hK, lk, hl, ht⟩

namespace Spec

def FirstSeat : Prop :=
  ∀ (St : Type) (seat : SeatC St) (c : ParC) (A : Plan) (Sh : Shape) (gL : Forest.Heard) (s s' : St)
    (l : List Aff),
    c.geo = geoOf Sh → seat.zk s = some gL.zk → A.NC = Sh.calls.size →
    P.firstK seat c s = some (l, s') →
      s' = s ∧ ∃ i K, P.inOf seat c s = some (i, K) ∧
        l = Fo.claim3T (oldOf Sh gL i) K ++ (Fo.claim4T (oldOf Sh gL i) K ++ Fo.claim5T (oldOf Sh gL i) K)

def KeysSeat : Prop :=
  ∀ (St : Type) (seat : SeatC St) (c : ParC) (A : Plan) (Sh : Shape) (gL : Forest.Heard) (s : St)
    (kf : Array Aff),
    c.geo = geoOf Sh → seat.zk s = some gL.zk → A.NC = Sh.calls.size →
    P.keysOfK seat c s = some kf →
      ∃ i K, P.inOf seat c s = some (i, K) ∧ kf = (Fo.attJoinsT A (oldOf Sh gL i)).kf

def SecondSeat : Prop :=
  ∀ (St : Type) (seat : SeatC St) (c : ParC) (Sh : Shape) (gL : Forest.Heard) (s s' : St)
    (l : List Aff),
    c.geo = geoOf Sh → seat.zk s = some gL.zk → P.secondK seat c s = some (l, s') →
      s' = s ∧ ∃ i K, P.inOf seat c s = some (i, K) ∧
        l = Fo.claim6T (oldOf Sh gL i) K ++ (Fo.claim7T (oldOf Sh gL i) K ++ Fo.claim8T (oldOf Sh gL i) K)

def WholeSeat : Prop :=
  ∀ (St : Type) (seat : SeatC St) (c : ParC) (A : Plan) (Sh : Shape) (gL : Forest.Heard)
    (s s₁ s₂ : St) (l₁ l₂ : List Aff) (kf : Array Aff),
    c.geo = geoOf Sh → seat.zk s = some gL.zk → A.NC = Sh.calls.size →
    P.firstK seat c s = some (l₁, s₁) → P.keysOfK seat c s = some kf →
    P.secondK seat c s = some (l₂, s₂) →
      ∃ i K, P.inOf seat c s = some (i, K) ∧
        Fo.attT A (oldOf Sh gL i) K = gL.rows.toList ++ (l₁ ++ ([Fo.joinForm gL kf] ++ (l₂ ++
          (Fo.planeFormsT gL Sh.cf.lmb
            (fun e col => Fo.u3Form i.iU3 K ((if e == 0 then i.t.tBit0 else i.t.tBit1) + col))
            (fun col => Fo.u3Form i.iU3 K (i.t.tPin + col))).toList)))

end Spec

theorem zk_of {seat : SeatC St} {c : ParC} {s : St} {i : P.Runs.In} {K : ℕ} {gL : Forest.Heard}
    (h : P.inOf seat c s = some (i, K)) (hz : seat.zk s = some gL.zk) : i.zk = gL.zk := by
  have e := (inOf_some seat c s i K h).2.2.1
  rw [hz] at e
  exact (Option.some.inj e).symm

theorem first_seat : Spec.FirstSeat := by
  intro St seat c A Sh gL s s' l hg hz hN hr
  unfold P.firstK at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨⟨i, K⟩, hi, x, hx, e1, e2⟩ := hr
  refine ⟨e2.symm, i, K, hi, ?_⟩
  rw [← e1]
  exact (first_any A Sh gL i K x.1 x.2 ((inOf_some seat c s i K hi).1.trans hg) (zk_of hi hz) hN hx).1

theorem keys_seat : Spec.KeysSeat := by
  intro St seat c A Sh gL s kf hg hz hN hr
  unfold P.keysOfK at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
  obtain ⟨⟨i, K⟩, hi, pad, _, x, hx, hk⟩ := hr
  refine ⟨i, K, hi, ?_⟩
  rw [keys_is _ _ _ _ hk,
    (first_any A Sh gL i K x.1 x.2 ((inOf_some seat c s i K hi).1.trans hg) (zk_of hi hz) hN hx).2]
  rfl

theorem second_seat : Spec.SecondSeat := by
  intro St seat c Sh gL s s' l hg hz hr
  unfold P.secondK at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨⟨i, K⟩, hi, x, hx, e1, e2⟩ := hr
  refine ⟨e2.symm, i, K, hi, ?_⟩
  rw [← e1]
  exact second_any Sh gL i K x ((inOf_some seat c s i K hi).1.trans hg) (zk_of hi hz) hx

theorem whole_seat : Spec.WholeSeat := by
  intro St seat c A Sh gL s s₁ s₂ l₁ l₂ kf hg hz hN h1 hk h2
  obtain ⟨_, i, K, hi, e1⟩ := first_seat St seat c A Sh gL s s₁ l₁ hg hz hN h1
  obtain ⟨i', K', hi', ek⟩ := keys_seat St seat c A Sh gL s kf hg hz hN hk
  obtain ⟨_, i'', K'', hi'', e2⟩ := second_seat St seat c Sh gL s s₂ l₂ hg hz h2
  rw [hi] at hi' hi''
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi'')
  subst e1 e2 ek
  refine ⟨i, K, hi, ?_⟩
  unfold Fo.attT
  simp only [List.append_assoc]
  rfl

end K5Law
