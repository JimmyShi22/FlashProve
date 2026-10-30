-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Guard.lean: guards of the hypothesis `AdvAlw` of CompileK/SpecDefer2.lean at a joint
class: at a toy it can be met, and it can fail.

A toy: one oracle on pairs of strings, one class, charged jointly; a challenger that makes one
vertex: two fresh tokens a, b of L bits, a marked evaluation at the point (a, b). The lemma:
`Spec.defer2` (deferred programming), CompileK/SpecDefer2.lean; the language and the two modes: the
head of Rom/Defer.lean. Definitions, statements and proofs (`guard1`, `guard2`, `guard3`,
`guardBd`). Nothing assumed.

Main names:
  `dgC1 L`: fresh a, fresh b, marked (a, b); nothing is shown.
  `dgC2 L`: the same, then one reveal of a, b and the answer's tail.
  `dgC3 L`: as `dgC1 L`, then a reveal of b alone.
  `dgAdv q`: the adversary: one call, then one query at q, then halt.
  `Spec.defer2_guard1`: `AdvAlw` holds at `dgC1 L`, `dgAdv q`, at ℓ := 2 L, M := 1, e := 0,
    ks := {()}.
  `Spec.defer2_guardB`: so, by `defer2`, the two modes of `dgC1 L` are within 1 · (1 / 2^(2 L)) + 1
    · (0 + 1) / 2^(2 L) for `dgAdv q`: the bits of both tokens count (`Spec.defer`, Rom/Defer.lean,
    gives 2^L in the place of 2^(2 L)). `dgAdv q` halts with (): both laws in `Spec.defer2_guardB`
    are on `Unit`, so their distance is 0; the row shows the lemma's formula at ℓ := 2 L.
  `Spec.defer2_guard2`: `AdvAlw` holds at `dgC2 L`, `dgAdv q`, at the same ℓ, M, e, ks: both
    children shown in one step.
  `Spec.defer2_guard3`: `AdvAlw` fails at `dgC3 L`, `dgAdv q`, whatever ℓ, M, e, ks: an unreleased
    evaluation's second token is shown (there the sharp bound would be false: after b is shown a
    query meets (a, b) with chance 2^-L) (no declaration of this file states this; `dgC3 L` itself
    replies () and `dgAdv q` halts with ()).

Limits: this file says nothing on a compiled prover. A toy has one vertex; "b stands in no earlier
marked point" is met emptily here.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
namespace Defer2Guard
open DeferTail DeferTail2

/-- One oracle on pairs of strings; an answer is one secret bit. -/
def dgS : OSpec := { ι := Unit, Dom := fun _ => Bits × Bits, Rng := fun _ => Unit × (Fin 1 → Bool) }

def dgSp : Split dgS := { Vis := fun _ => Unit, tl := fun _ => 1, split := fun _ => Equiv.refl _ }

def dgCl : PtCls dgS Unit := { of := fun _ => (), orc := fun _ => (), orc_of := fun _ => rfl }

def dgVtx {α : Type} (a b : Tok) (k : Tok → Step dgS dgSp α) : Step dgS dgSp α :=
  Step.marked (S := dgS) () a [b] (fun v vs => ((v, vs.headD []) : Bits × Bits))
    (fun _ _ _ h => (Prod.mk.inj h).1) fun _ d => k d

def dgC1 (L : ℕ) : Chall dgS dgSp Unit Unit :=
  { τ := Unit,
    step := fun _ _ =>
        Step.fresh L fun a => Step.fresh L fun b => dgVtx a b fun _ => Step.pure ((), ()) }
def dgC2 (L : ℕ) : Chall dgS dgSp Unit Unit :=
  { τ := Unit,
    step := fun _ _ =>
        Step.fresh L fun a =>
          Step.fresh L fun b =>
            dgVtx a b fun d => Step.reveal [a, b, d] fun _ => Step.pure ((), ()) }
def dgC3 (L : ℕ) : Chall dgS dgSp Unit Unit :=
  { τ := Unit,
    step := fun _ _ =>
        Step.fresh L fun a =>
          Step.fresh L fun b => dgVtx a b fun _ => Step.reveal [b] fun _ => Step.pure ((), ()) }

def dgAdv (q : Bits × Bits) : Adv dgS Unit Unit Unit :=
  .call () fun _ => .query (S := dgS) () q fun _ => .halt ()

end Defer2Guard

open Defer2Guard DeferTail

def Spec.defer2_guard1 : Prop :=
  ∀ (L : ℕ) (q : Bits × Bits), AdvAlw (dgC1 L) dgCl (fun _ => true)
    (DSt.Ok2 dgCl (fun _ => true) (fun _ => 2 * L) {()}) (DSt.CntK2 dgCl (fun _ => 0) (fun _ => 1))
    (dgAdv q) ((), DSt.init dgS)

def Spec.defer2_guard2 : Prop :=
  ∀ (L : ℕ) (q : Bits × Bits), AdvAlw (dgC2 L) dgCl (fun _ => true)
    (DSt.Ok2 dgCl (fun _ => true) (fun _ => 2 * L) {()}) (DSt.CntK2 dgCl (fun _ => 0) (fun _ => 1))
    (dgAdv q) ((), DSt.init dgS)

def Spec.defer2_guard3 : Prop :=
  ∀ (L : ℕ) (q : Bits × Bits) (ℓ M : Unit → ℕ) (e : Unit → ℕ) (ks : Finset Unit),
    ¬ AdvAlw (dgC3 L) dgCl (fun _ => true) (DSt.Ok2 dgCl (fun _ => true) ℓ ks) (DSt.CntK2 dgCl e M)
      (dgAdv q) ((), DSt.init dgS)

def Spec.defer2_guardB : Prop :=
  ∀ (L : ℕ) (q : Bits × Bits),
    tv ((interact ((dgC1 L).world false) (dgAdv q) ((), DSt.init dgS)).map Prod.fst)
        ((interact ((dgC1 L).world true) (dgAdv q) ((), DSt.init dgS)).map Prod.fst) ≤
      1 / 2 ^ (2 * L) + 1 / 2 ^ (2 * L)

namespace Defer2Guard

theorem ptFit1 :
    PtFit dgCl (fun _ => true) (o := ()) (fun v vs => ((v, vs.headD []) : Bits × Bits)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩⟩

/-- The state after the vertex. -/
theorem ok_vtx (L : ℕ) (u₁ u₂ : Fin L → Bool) (r : dgS.Rng ()) :
    (postMarked dgSp (postFresh (postFresh (DSt.init dgS) (List.ofFn u₁)) (List.ofFn u₂)) () 0 [1]
        ((List.ofFn u₁, List.ofFn u₂) : Bits × Bits) r (Table.empty dgS)).Ok2
      dgCl (fun _ => true) (fun _ => 2 * L) {()} := by
  refine ⟨by simp [postMarked, postFresh, DSt.init, markedBad], fun v hv => ?_⟩
  have hv' : v = ⟨(), ((List.ofFn u₁, List.ofFn u₂) : Bits × Bits), r, 0, [1], 2, false⟩ := by
    simpa [postMarked, postFresh, DSt.init] using hv
  subst hv'
  refine ⟨by simp,
    fun h => by
      simp at h, fun _ => ⟨1, rfl, ?_, fun _ => by simp [postMarked, postFresh, DSt.init]⟩⟩
  simp [postMarked, postFresh, DSt.init, DSt.val]
  omega

/-- The state before the vertex, the vertex as an evaluation, the state after it. -/
def dgD2 (L : ℕ) (u₁ u₂ : Fin L → Bool) : DSt dgS :=
  postFresh (postFresh (DSt.init dgS) (List.ofFn u₁)) (List.ofFn u₂)
def dgEv (L : ℕ) (u₁ u₂ : Fin L → Bool) (r : dgS.Rng ()) : Ev dgS :=
  ⟨(), ((List.ofFn u₁, List.ofFn u₂) : Bits × Bits), r, 0, [1], 2, false⟩
def dgD3 (L : ℕ) (u₁ u₂ : Fin L → Bool) (r : dgS.Rng ()) : DSt dgS :=
  postMarked dgSp (dgD2 L u₁ u₂) () 0 [1]
    ((List.ofFn u₁, List.ofFn u₂) : Bits × Bits) r (Table.empty dgS)

theorem markFit1 (L : ℕ) (u₁ u₂ : Fin L → Bool) :
    MarkFit dgCl (fun _ => true) (dgD2 L u₁ u₂) (o := ()) [1]
      (fun v vs => ((v, vs.headD []) : Bits × Bits)) :=
  fun _ => ⟨1, rfl, by simp [dgD2, postFresh, DSt.init], by simp [dgD2, postFresh, DSt.init]⟩

theorem cnt_d3 (L : ℕ) (u₁ u₂ : Fin L → Bool) (r : dgS.Rng ()) (T : Table dgS) :
    (withT (dgD3 L u₁ u₂ r) T).CntK2 dgCl (fun _ => 0) (fun _ => 1) :=
  ⟨fun _ => le_rfl, fun _ => by simp [withT, dgD3, dgD2, postMarked, postFresh, DSt.init, dgCl]⟩

theorem guard1 : Spec.defer2_guard1 := fun L _ u₁ u₂ =>
  ⟨ptFit1, markFit1 L u₁ u₂, fun r => ⟨ok_vtx L u₁ u₂ r, fun y _ => cnt_d3 L u₁ u₂ r y.2⟩⟩

theorem evs_rev (L : ℕ) (u₁ u₂ : Fin L → Bool) (r : dgS.Rng ()) (ts : List Tok) :
    (postReveal true (dgD3 L u₁ u₂ r) ts).evs = [rel1 ts (dgEv L u₁ u₂ r)] := by
  show (releaseAll true ((dgD3 L u₁ u₂ r).shown ++ ts)
      (dgD3 L u₁ u₂ r).evs (dgD3 L u₁ u₂ r).table).1 = _
  rw [releaseAll_fst]
  rfl

theorem guard2 : Spec.defer2_guard2 := by
  intro L q u₁ u₂
  refine ⟨ptFit1, markFit1 L u₁ u₂, fun r => ⟨ok_vtx L u₁ u₂ r, ?_, fun y _ => ?_⟩⟩
  · have he := evs_rev L u₁ u₂ r [0, 1, 2]
    have hr : rel1 [0, 1, 2] (dgEv L u₁ u₂ r) = { dgEv L u₁ u₂ r with released := true } :=
      rel1_of_newly ⟨rfl, by simp [dgEv]⟩
    refine ⟨?_, fun v hv => ?_⟩
    · show ((dgD3 L u₁ u₂ r).viol ||
          !closedUnder ((dgD3 L u₁ u₂ r).shown ++ [0, 1, 2])
            (releaseAll true ((dgD3 L u₁ u₂ r).shown ++ [0, 1, 2])
              (dgD3 L u₁ u₂ r).evs (dgD3 L u₁ u₂ r).table).1 ||
          [0, 1, 2].any (fun u => decide ((dgD3 L u₁ u₂ r).vals.length ≤ u))) = false
      rw [releaseAll_fst]
      simp [closedUnder, rel1, dgD3, dgD2, postMarked, postFresh, DSt.init, markedBad]
    · have hv' : v ∈ (postReveal true (dgD3 L u₁ u₂ r) [0, 1, 2]).evs := hv
      rw [he, hr] at hv'
      obtain rfl := List.mem_singleton.1 hv'
      refine ⟨by simp, fun h => by simp at h, fun _ => ⟨1, rfl, ?_, fun h => by simp at h⟩⟩
      show 2 * L ≤ ((dgD3 L u₁ u₂ r).val 0).length + ((dgD3 L u₁ u₂ r).val 1).length
      simp [dgD3, dgD2, postMarked, postFresh, DSt.init, DSt.val]
      omega
  · refine ⟨fun _ => le_rfl, fun _ => ?_⟩
    show ((postReveal true (dgD3 L u₁ u₂ r) [0, 1, 2]).evs.filter _).length ≤ 1
    rw [evs_rev]
    exact le_trans (List.length_filter_le _ _) le_rfl

theorem guard3 : Spec.defer2_guard3 := by
  intro L q ℓ M e ks h
  have h1 := ((h (fun _ => false) (fun _ => false)).2.2 (Classical.arbitrary _)).2.1
  have he := evs_rev L (fun _ => false) (fun _ => false) (Classical.arbitrary _) [1]
  have hr : rel1 [1] (dgEv L (fun _ => false) (fun _ => false) (Classical.arbitrary _)) =
      dgEv L (fun _ => false) (fun _ => false) (Classical.arbitrary _) :=
    rel1_of_not_newly fun hn => by simp [Newly, dgEv] at hn
  have h2 := h1.2 (dgEv L (fun _ => false) (fun _ => false) (Classical.arbitrary _)) (by
    show _ ∈
      (postReveal true (dgD3 L (fun _ => false) (fun _ => false) (Classical.arbitrary _)) [1]).evs
    rw [he, hr]
    exact List.mem_singleton.2 rfl)
  obtain ⟨b, hb, _, hs⟩ := h2.2.2 rfl
  have hb1 : b = 1 := by
    have : [1] = [b] := hb
    simpa using this.symm
  subst hb1
  exact hs rfl (by
    show 1 ∈ (dgD3 L (fun _ => false) (fun _ => false) (Classical.arbitrary _)).shown ++ [1]
    simp)

theorem guardBd : Spec.defer2_guardB := by
  intro L q
  have h := DeferTail2.defer2 dgS dgSp Unit Unit Unit Unit (dgC1 L) () (dgAdv q) 1
    (fun _ => 0) (fun _ => 1) (fun _ => 2 * L) 1 {()} dgCl (fun _ => true)
    (by simp [dgAdv, Adv.TotalBound]) (guard1 L q)
  simpa using h

end Defer2Guard
end Rom
