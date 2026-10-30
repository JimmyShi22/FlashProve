-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SameCore.lean: WHAT THE RUNS OF CLAIMS LEAVE OF THE LEDGER, WITH THREE FIELDS
MORE THAN `SameSums` (Johnson/Desc/K8/Honest/FallFold.lean): the mark that the batching element is
drawn, the map of the weights handed out, the mark that the door is shut. Definitions, statements
and proofs. No prover. Lemmas; none of the library's goals.

Why. The batching's adding reads these three of the ledger behind the runs. Each source of a
`SameSums` has them: the library's K4.Core (Johnson/Desc/First/K4/RunsCore.lean), Law.OnlySide
(Johnson/Desc/First/TailClaims/EquationsTame.lean), and Fork.paid, which turns one other field.
  `SameCore F G`   `SameSums F G`, and G has F's thetaDrawnF, kapMapF, doorShutF
  `SameCore.refl`, `.trans`, `.ofCore`, `.ofSide`, `.paid`
  `FlCore m`   a routine on a ledger and a tape leaves these ten fields: the clause "same" of `FlOk`
      (Johnson/Desc/K8/Honest/FreeChi.lean), said of `SameCore`; closed under pure, bind, must,
      need, change, foldlM; `FlCore.paid`, `FlCore.hideRun`
  `joinF_core`, `planesAtF_core`, `leavesRowOwn_core`, `planeClaimsOwn_core`, `planesProg_core`,
  `pscRow_core`   the lookup's and the merge's routines, by the terms of their `FlOk` lemmas
The ten: trees, ns, LS, c0, nClaim, theta, planClaimsF (the seven of `SameSums`); thetaDrawnF,
kapMapF, doorShutF. NOT CARRIED, of the ledger's fifteen fields: vp, mf, gotF, owed, which K4.Core
does not name (Fork.paid turns owed); next, which K4.Core names and Law.OnlySide does not.
Limits. Equations of fields: nothing on what any field's value is. Nothing on the five others.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- `SameSums`, and the three marks that the adding reads. -/
structure SameCore (F G : Fork) : Prop where
  sums : SameSums F G
  drawn : G.thetaDrawnF = F.thetaDrawnF
  kapMap : G.kapMapF = F.kapMapF
  door : G.doorShutF = F.doorShutF

theorem SameCore.refl (F : Fork) : SameCore F F := ⟨SameSums.refl F, rfl, rfl, rfl⟩

theorem SameCore.trans {F G H : Fork} (a : SameCore F G) (b : SameCore G H) : SameCore F H :=
  ⟨a.sums.trans b.sums, b.drawn.trans a.drawn, b.kapMap.trans a.kapMap, b.door.trans a.door⟩

theorem SameCore.ofCore {F G : Fork} (h : OnBytes.Desc.First.K4.Core F G) : SameCore F G :=
  ⟨SameSums.ofCore h, h.thetaDrawnF, h.kapMapF, h.doorShutF⟩

theorem SameCore.ofSide {F G : Fork} (h : Law.OnlySide F G) : SameCore F G :=
  ⟨SameSums.ofSide h, h.drawn, h.kapMap, h.door⟩

theorem SameCore.paid (F : Fork) (i : Nat) : SameCore F (F.paid i) :=
  ⟨SameSums.paid F i, rfl, rfl, rfl⟩

/-! ## Routines on a ledger and a tape -/

/-- The routine leaves the ten fields. -/
def FlCore {α : Type} (m : Fl α) : Prop := ∀ F u x, m F u = some x → SameCore F x.2.1

theorem FlCore.pure {α : Type} (a : α) : FlCore (Pure.pure a : Fl α) := fun F u x h => by
  obtain rfl : (a, F, u) = x := Option.some.inj h
  exact SameCore.refl F

theorem FlCore.bind {α β : Type} {m : Fl α} {f : α → Fl β} (hm : FlCore m)
    (hf : ∀ a, FlCore (f a)) : FlCore (m >>= f) := by
  intro F u x h
  have h' : (match m F u with
    | some (a, G, w) => f a G w
    | none => none) = some x := h
  cases hx : m F u with
  | none => rw [hx] at h'; cases h'
  | some y =>
    obtain ⟨a, G, w⟩ := y
    rw [hx] at h'
    exact (hm F u _ hx).trans (hf a G w x h')

theorem FlCore.must (b : Bool) : FlCore (Fl.must b) := by
  intro F u x h
  unfold Fl.must at h
  cases b with
  | false => cases h
  | true =>
    obtain rfl : ((), F, u) = x := Option.some.inj h
    exact SameCore.refl F

theorem FlCore.need {α : Type} (o : Option α) : FlCore (Fl.need o) := by
  intro F u x h
  unfold Fl.need at h
  cases o with
  | none => cases h
  | some a =>
    obtain rfl : (a, F, u) = x := Option.some.inj h
    exact SameCore.refl F

theorem FlCore.change {f : Fork → Option Fork} (h2 : ∀ F G, f F = some G → SameCore F G) :
    FlCore (Fl.change f) := by
  intro F u x h
  unfold Fl.change at h
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
  exact h2 F G hG

theorem FlCore.foldlM {α β : Type} {f : β → α → Fl β} (hf : ∀ b a, FlCore (f b a)) :
    ∀ (l : List α) (b : β), FlCore (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact FlCore.pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact FlCore.bind (hf b a) fun c => FlCore.foldlM hf l c

theorem FlCore.paid (i : Nat) : FlCore (Fl.change fun F => some (F.paid i)) :=
  FlCore.change fun F G h => by
    obtain rfl : F.paid i = G := Option.some.inj h
    exact SameCore.paid F i

theorem FlCore.hideRun (first : Nat) (v : Array E) (k : E) :
    FlCore (Fl.change (·.hideRun first v k)) :=
  FlCore.change fun _ _ h => SameCore.ofCore (OnBytes.Desc.First.K4.hideRun_core h)

theorem joinF_core (g : Forest.Heard) (KF : Array Aff) : FlCore (First.Look.joinF g KF) :=
  FlCore.bind (FlCore.must _) fun _ => FlCore.bind (FlCore.paid _) fun _ => FlCore.pure _

theorem planesAtF_core (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Fl Aff)
    (hb : ∀ e col, FlCore (bit e col)) : FlCore (First.Look.planesAtF g lm e bit) :=
  FlCore.foldlM (fun _ col => FlCore.bind (hb e col) fun _ => FlCore.pure _) _ _

theorem leavesRowOwn_core (p : Psc) (S0 : E) (kept : Aff) :
    FlCore (First.Look.leavesRowOwn p S0 kept) :=
  FlCore.bind (FlCore.must _) fun _ => FlCore.bind (FlCore.hideRun _ _ _) fun _ => FlCore.pure _

theorem planeClaimsOwn_core (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) (hb : ∀ e col, FlCore (bit e col)) (hp : ∀ col, FlCore (pin col)) :
    FlCore (First.Look.planeClaimsOwn g lm bit pin) :=
  FlCore.bind (FlCore.must _) fun _ =>
    FlCore.bind (planesAtF_core g lm 0 bit hb) fun _ =>
      FlCore.bind (planesAtF_core g lm 1 bit hb) fun _ =>
        FlCore.bind (FlCore.foldlM (fun _ col => FlCore.bind (hp col) fun _ => FlCore.pure _) _ _)
          fun _ => FlCore.bind (leavesRowOwn_core _ _ _) fun _ => FlCore.pure _

theorem planesProg_core (lm : Nat) (g : Forest.Heard)
    (r : (Nat → Nat → Option Aff) × (Nat → Option Aff)) : FlCore (K9.planesProg lm g r) :=
  FlCore.bind (planeClaimsOwn_core g lm _ _ (fun _ _ => FlCore.need _) fun _ => FlCore.need _)
    fun _ => FlCore.bind (FlCore.paid _) fun _ => FlCore.pure _

theorem pscRow_core (p : Psc) (S0 : E) (kept : Aff) : FlCore (Fl.pscRow p S0 kept) :=
  FlCore.bind (FlCore.must _) fun _ => FlCore.bind (FlCore.hideRun _ _ _) fun _ => FlCore.pure _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.SameCore.ofCore
#print axioms VerifiableInference.Desc.First.K8.Honest.SameCore.ofSide
#print axioms VerifiableInference.Desc.First.K8.Honest.joinF_core
#print axioms VerifiableInference.Desc.First.K8.Honest.planesProg_core
#print axioms VerifiableInference.Desc.First.K8.Honest.pscRow_core
