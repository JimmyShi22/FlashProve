-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyQLaws.lean: the laws of the toy of Run/ToyQ.lean (`Run.Toy1`: this library's own, not the
programs'): its verifier is local, and its wiring obeys the laws of a wire, given one law on the
drawn positions.

Statements and proofs. A first step towards a theorem about the toy; no such theorem is here beyond
the four statements under "Main names:" and their lemmas. (`toy1_wire`, Run/Toy1Laws.lean, is made
from them and does not assume `ChalUnif`.)
The laws of a wire are the conditions `ProtocolQueryLayout.OK` and, for a wiring whose rounds may have a
proof-of-work test, `ProtocolQueryLayout.OKG` (Iop/BatchWire.lean). Many statements of this library are written
twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same name
outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `Spec.q0_local`, `Spec.qT_local`: the decision depends on the oracle of round 1 only at the
    positions read (`Iop.InteractiveOracleProof.IsLocal`): without work, and with it (by the library's step
    `InteractiveOracleProof.IsLocal.grind`, Iop/GrindProofs.lean).
  `ChalUnif`: the one law that is a hypothesis here: uniform blocks give uniform positions: (unif
    (Fin 1 → Dig 256)).map w1.chal = unif (Fin 3 → Fin 16). Run/ToyChalLaw.lean states and proves it
    (`toy1_unif`).
  `Spec.wq0_ok`: `ChalUnif` → `wq0.OK` (Iop/BatchWire.lean): places and leaves answer each other; a
    component without a tree has no position; at most three openings; depths at most 4; no test.
  `Spec.wqT_okg`: `ChalUnif` → `wqT.OKG`: the same for the wiring with the test of 8 bits (by the
    library's step `ProtocolQueryLayout.OKG.grindLocal`, Iop/GrindWire.lean), nonces read back up to the bound of
    the toy's data.

Limits: this file does not say `ChalUnif` itself (it is stated and assumed here, not proved). This
file does not say that the protocol is sound for anything: its relation is not even named. It says
nothing on the ambient interface, the spellings, the parser or a run.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyQ
import Iop.GrindProofs

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch Prob

/-- States that uniform blocks give uniform positions. -/
def ChalUnif : Prop := (unif (Fin 1 → Dig 256)).map w1.chal = unif (Fin 3 → Fin 16)

def Spec.q0_local : Prop := Q0.IsLocal
def Spec.qT_local : Prop := QT.IsLocal
def Spec.wq0_ok : Prop := ChalUnif → wq0.OK
def Spec.wqT_okg : Prop := ChalUnif → wqT.OKG

theorem foldl_congr_mem (f g : Fin 16 → E3) :
    ∀ (l : List (Fin 16)) (c : E3), (∀ x ∈ l, f x = g x) →
      l.foldl (fun a x => addE a (f x)) c = l.foldl (fun a x => addE a (g x)) c
  | [], _, _ => rfl
  | x :: l, c, h => by
      show l.foldl (fun a x => addE a (f x)) (addE c (f x)) =
        l.foldl (fun a x => addE a (g x)) (addE c (g x))
      rw [h x (List.mem_cons_self),
        foldl_congr_mem f g l _ fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem mem_listOf (c : Fin 3 → Fin 16) (x : Fin 16) : x ∈ listOf c ↔ ∃ i, c i = x := by
  simp [listOf]

theorem q0_local : Spec.q0_local := by
  rintro x y y' ⟨m0, c0, m1, c1, m2, c2, u⟩ ⟨m0', c0', m1', c1', m2', c2', u'⟩ hρ hp _ hr
  have e1 : c1 = c1' := congrArg (fun z : Rho shp => z.2.1) hρ
  have e2 : m2.2 = m2'.2 := congrArg (fun z : Plains shp => z.2.2.1) hp
  subst e1
  show decide (m2.2 = (listOf c1).foldl (fun a x => addE a (m1.1 x)) x) =
    decide (m2'.2 = (listOf c1).foldl (fun a x => addE a (m1'.1 x)) x)
  rw [e2, foldl_congr_mem m1.1 m1'.1 (listOf c1) x fun z hz => ?_]
  obtain ⟨i, rfl⟩ := (mem_listOf c1 z).1 hz
  exact hr (Sum.inr (Sum.inl (c1 i))) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

theorem qT_local : Spec.qT_local := q0_local.grind gW

theorem unif_unit (C : Type) [Fintype C] [Nonempty C] : (unif C).map (fun _ => ()) = unif Unit := by
  rw [map_unif_eq_unif_iff]
  intro d
  simp [cnt]

theorem w0_ok : w0.OK :=
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun _ _ h => by cases h
    no0 := fun _ _ =>
      rfl, noJ := fun _ _ => rfl, chal_unif := unif_unit _, gr0_none := rfl, grJ_none := rfl }

theorem w2_ok : w2.OK :=
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun _ _ h => by cases h
    no0 := fun _ _ =>
      rfl, noJ := fun _ _ => rfl, chal_unif := unif_unit _, gr0_none := rfl, grJ_none := rfl }

theorem w1_ok (hc : ChalUnif) : w1.OK :=
  { place_lt0 := fun _ h => by cases h
    place_ltJ := fun p _ => p.isLt
    posAt0_place := fun _ h => by cases h
    posAtJ_place := fun p _ => by
      show (if h : p.val < 16 then some (⟨p.val, h⟩ : Fin 16) else none) = some p
      rw [dif_pos p.isLt]
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun j p h => by
      have h' : (if h : j < 16 then some (⟨j, h⟩ : Fin 16) else none) = some p := h
      by_cases hj : j < 16
      · rw [dif_pos hj] at h'
        exact ⟨rfl, by rw [← Option.some.inj h']; rfl⟩
      · rw [dif_neg hj] at h'
        cases h'
    no0 := fun _ _ => rfl
    noJ := fun h => by cases h
    chal_unif := hc, gr0_none := rfl, grJ_none := rfl }

theorem wq0_ok : Spec.wq0_ok := fun hc =>
  { sh := ⟨w0_ok, w1_ok hc, w2_ok, trivial⟩
    ext := ⟨List.nodup_nil, fun p => p.elim, fun _ p => p.elim⟩
    opens := fun _ _ _ => le_trans (Nat.add_le_add_right Finset.card_image_le _) (le_refl 3)
    depth := ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, ⟨Nat.zero_le _, le_refl 4⟩,
      ⟨Nat.zero_le _, Nat.zero_le _⟩, trivial⟩ }

theorem wqT_okg : Spec.wqT_okg := fun hc =>
  ProtocolQueryLayout.OKG.grindLocal (wq0_ok hc).toG (D := Dn) (n := 8) (fun _ _ _ _ => rfl) (by decide)
    (g := gW) ⟨Nat.zero_le _, le_refl 8, Nat.zero_le _, trivial⟩

end Run.Toy1
