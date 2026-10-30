-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutSlots.lean: the annotation of any plan of splits and merges, if only the slots send (there
is no shared prover message).

An annotated plan (`AXPlan`, Iop/BatchRecut.lean) has one `ACut` for each split of an `XPlan`
(Iop/Recut.lean) (words of this library: lean/GLOSSARY.md). In a protocol with slots (`BatchInteractiveOracleProof`,
Iop/Batch.lean) a round is shared or local (its kind: one challenge for all slots, or one for each),
and its annotation (`RAnn`) divides the prover message into a shared component and the slot's
component. Here the annotated plan is given by one definition for all plans, for the rounds of a
front reduction, which are all local and sent by the slots only.

Why: `ACut.ofSlot` (Iop/SplitKit.lean) annotates a split of a round with the annotation
`RAnn.ofSlot k r`. After a merge by (J1) of Iop/Join.lean the annotation of the merged round is not
of that form (its shared component is Unit × Unit), so a split of a merged round has to be
annotated separately. And the annotation of a list s ++ t, `RoundSplits.allLocal (s ++ t)`, does not
reduce to that of s followed by that of t while s is a variable, so `AXPlan.app` does not apply to
it. Here all that the definition uses of an annotation is that its shared component has one value.
  `RAnn.SlotOnly`: the shared component has one value. `RAnn.SlotLaw`: all positions belong to the
      slot's component. For all rounds: `RoundSplits.SlotOnly`, `RoundSplits.SlotLaw`. The annotation with
      `RAnn.ofSlot k` in every round has them, whatever form the list of rounds has.
  `ACut.slots k1 c a h`: the annotation of a split: both parts are sent by the slots; its remainder
      has the annotation `RAnn.ofSlot a.kind c.snd`.
  `AXPlan.slots k1 P A h`: the annotated plan, for every plan P, with `slots_ok` (`AXPlan.OK`, if
      `RoundSplits.SlotLaw A`) and `slots_cutKinds`.
  `XPlan.FirstOfRun n`: the old round n is not merged into the round before it.
  `AXPlan.late_of_allLo`: if all rounds and all first parts are local, `AXPlan.Late` at the round n
      requires only `XPlan.FirstOfRun n`.
  `AXPlan.allLocal P : AXPlan P (RoundSplits.allLocal s)`: the form for a front reduction, for every plan
      P. It satisfies `AXPlan.OK` (`allLocal_ok`), `AXPlan.Kinds` (`allLocal_kinds`), `AXPlan.Fit`
      (`allLocal_fit`) and, from `XPlan.FirstOfRun`, `AXPlan.Late` (`allLocal_late`), and, from K :
      `P.Kits`, it has its further data (`AXPlan.Kits.allLocal`): no condition is left on the
      annotation.
-/
import Iop.RecutKit

namespace Iop

/-! ## 1. Only the slots send -/

/-- The shared component has one value. -/
structure RAnn.SlotOnly {r : Round} (a : RAnn r) where
  u : a.M0 ≃ Unit

/-- All positions belong to the slot's component. -/
def RAnn.SlotLaw {r : Round} (a : RAnn r) : Prop := ∀ p, a.own p = true

def RAnn.slotOnly_ofSlot (k : Kind) (r : Round) : (RAnn.ofSlot k r).SlotOnly := ⟨Equiv.refl Unit⟩
theorem RAnn.slotLaw_ofSlot (k : Kind) (r : Round) : (RAnn.ofSlot k r).SlotLaw := fun _ => rfl

section
variable {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2}

def RAnn.SlotOnly.joinMsg (h1 : a1.SlotOnly) (h2 : a2.SlotOnly) : (a1.joinMsg a2).SlotOnly :=
  ⟨(Equiv.prodCongr h1.u h2.u).trans (Equiv.punitProd Unit)⟩
def RAnn.SlotOnly.joinChal (h1 : a1.SlotOnly) (r2 : Round) : (a1.joinChal r2).SlotOnly := ⟨h1.u⟩

theorem RAnn.SlotLaw.joinMsg (h1 : a1.SlotLaw) (h2 : a2.SlotLaw) : (a1.joinMsg a2).SlotLaw
  | .inl p => h1 p
  | .inr p => h2 p
theorem RAnn.SlotLaw.joinChal (h1 : a1.SlotLaw) (r2 : Round) : (a1.joinChal r2).SlotLaw := h1

end

def RoundSplits.SlotOnly : {s : Shape} → RoundSplits s → Type
  | [], _ => Unit
  | _ :: _, (a, A) => a.SlotOnly × RoundSplits.SlotOnly A

def RoundSplits.SlotLaw : {s : Shape} → RoundSplits s → Prop
  | [], _ => True
  | _ :: _, (a, A) => a.SlotLaw ∧ RoundSplits.SlotLaw A

def RoundSplits.slotOnly_const (k : Kind) : (s : Shape) → RoundSplits.SlotOnly (RoundSplits.const (RAnn.ofSlot k) s)
  | [] => ()
  | r :: s => (RAnn.slotOnly_ofSlot k r, RoundSplits.slotOnly_const k s)

theorem RoundSplits.slotLaw_const (k : Kind) : ∀ s : Shape, RoundSplits.SlotLaw (RoundSplits.const (RAnn.ofSlot k) s)
  | [] => trivial
  | r :: s => ⟨RAnn.slotLaw_ofSlot k r, RoundSplits.slotLaw_const k s⟩

/-! ## 2. One split -/

section OneCut
variable {r : Round}

/-- The annotation of a split of a round in which only the slots send. k1 is the kind of the round
of the first part. -/
def ACut.slots (k1 : Kind) (c : RCut r) (a : RAnn r) (h : a.SlotOnly) : ACut c a where
  kind := k1
  A := RComp.ofSlot c.fst
  B := RComp.ofSlot c.snd
  m0 := h.u.trans (Equiv.punitProd Unit).symm
  mj := ((Equiv.punitProd a.Mj).symm.trans (Equiv.prodCongr h.u.symm (Equiv.refl a.Mj))).trans
    (a.split.symm.trans c.msg)

theorem ACut.slots_ann1 (k1 : Kind) (c : RCut r) (a : RAnn r) (h : a.SlotOnly) :
    (ACut.slots k1 c a h).ann1 = RAnn.ofSlot k1 c.fst := rfl
theorem ACut.slots_ann2 (k1 : Kind) (c : RCut r) (a : RAnn r) (h : a.SlotOnly) :
    (ACut.slots k1 c a h).ann2 = RAnn.ofSlot a.kind c.snd := rfl

theorem ACut.slots_ok (k1 : Kind) (c : RCut r) (a : RAnn r) (h : a.SlotOnly) (hl : a.SlotLaw) :
    (ACut.slots k1 c a h).OK := by
  refine ⟨fun m0 mj => ?_, fun p => (hl _).symm, fun p => (hl _).symm,
    fun _ _ => rfl, fun _ _ => rfl⟩
  have e : h.u.symm () = m0 := h.u.symm_apply_apply m0
  show a.split.symm (m0, mj) =
    c.join (c.left (a.split.symm (h.u.symm (), mj))) (c.right (a.split.symm (h.u.symm (), mj)))
  rw [c.join_left_right, e]

end OneCut

/-! ## 3. Plans -/

/-- The annotated plan. All first parts are rounds of the kind k1. -/
def AXPlan.slots (k1 : Kind) :
    {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → RoundSplits.SlotOnly A → AXPlan P A
  | _, .nil => fun _ _ => PUnit.unit
  | _, .keep r P =>
    fun (A : RAnn r × RoundSplits _) (h : A.1.SlotOnly × RoundSplits.SlotOnly A.2) => AXPlan.slots k1 P A.2 h.2
  | _, .cut (r := r) (s := s) c P => fun (A : RAnn r × RoundSplits s) (h : A.1.SlotOnly × RoundSplits.SlotOnly A.2) =>
      ⟨ACut.slots k1 c A.1 h.1,
        AXPlan.slots k1 P (show RoundSplits (c.snd :: s) from (RAnn.ofSlot A.1.kind c.snd, A.2))
          (RAnn.slotOnly_ofSlot A.1.kind c.snd, h.2)⟩
  | _, .msg r1 r2 (s := s) _ P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s)
          (h : A.1.SlotOnly × A.2.1.SlotOnly × RoundSplits.SlotOnly A.2.2) =>
      AXPlan.slots k1 P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
        (h.1.joinMsg h.2.1, h.2.2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun (A : RAnn r1 × RAnn r2 × RoundSplits s)
          (h : A.1.SlotOnly × A.2.1.SlotOnly × RoundSplits.SlotOnly A.2.2) =>
      AXPlan.slots k1 P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))
        (h.1.joinChal r2, h.2.2)

theorem AXPlan.slots_ok (k1 : Kind) {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (h : RoundSplits.SlotOnly A),
      RoundSplits.SlotLaw A → AXPlan.OK P A (AXPlan.slots k1 P A h) := by
  induction P with
  | nil => intro _ _ _; trivial
  | keep r P ih => exact fun A h hl => ih A.2 h.2 hl.2
  | cut c P ih =>
    exact fun A h hl =>
      ⟨ACut.slots_ok k1 c A.1 h.1 hl.1,
        ih (RAnn.ofSlot A.1.kind c.snd, A.2)
          (RAnn.slotOnly_ofSlot A.1.kind c.snd, h.2) ⟨RAnn.slotLaw_ofSlot _ _, hl.2⟩⟩
  | msg r1 r2 u P ih =>
    exact fun A h hl =>
      ih (A.1.joinMsg A.2.1, A.2.2) (h.1.joinMsg h.2.1, h.2.2) ⟨hl.1.joinMsg hl.2.1, hl.2.2⟩
  | chal r1 r2 np P ih =>
    exact fun A h hl =>
      ih (A.1.joinChal r2, A.2.2) (h.1.joinChal r2, h.2.2) ⟨hl.1.joinChal r2, hl.2.2⟩

theorem AXPlan.slots_cutKinds (k1 : Kind) {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (h : RoundSplits.SlotOnly A), AXPlan.CutKinds k1 P A (AXPlan.slots k1 P A h) := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih => exact fun A h => ih A.2 h.2
  | cut c P ih =>
    exact fun A h =>
      ⟨rfl, ih (RAnn.ofSlot A.1.kind c.snd, A.2) (RAnn.slotOnly_ofSlot A.1.kind c.snd, h.2)⟩
  | msg r1 r2 u P ih => exact fun A h => ih (A.1.joinMsg A.2.1, A.2.2) (h.1.joinMsg h.2.1, h.2.2)
  | chal r1 r2 np P ih => exact fun A h => ih (A.1.joinChal r2, A.2.2) (h.1.joinChal r2, h.2.2)

/-! ## 4. The round `BatchProtocol.late`

`late : Option ℕ`, a field of `BatchProtocol` (Iop/Batch.lean): the round of Batch (counted from 0) into whose
query layer 1 (the compiler, Compile/) writes the whole instance; none: there is no such round.
`AXPlan.Late .. n` (Iop/BatchRecut.lean): what is asked of the plan for Batch at the round n =
`L.late`. -/

/-- The old round n is not merged into the round before it. -/
def XPlan.FirstOfRun : {s : Shape} → XPlan s → ℕ → Prop
  | _, .nil, _ => True
  | _, .keep _ _, 0 => True
  | _, .keep _ P, n + 1 => P.FirstOfRun n
  | _, .cut _ _, 0 => True
  | _, .cut _ P, n + 1 => P.FirstOfRun (n + 1)
  | _, .msg _ _ _ P, 0 => P.FirstOfRun 0
  | _, .msg _ _ _ _, 1 => False
  | _, .msg _ _ _ P, n + 2 => P.FirstOfRun (n + 1)
  | _, .chal _ _ _ P, 0 => P.FirstOfRun 0
  | _, .chal _ _ _ _, 1 => False
  | _, .chal _ _ _ P, n + 2 => P.FirstOfRun (n + 1)

/-- If all rounds and all first parts are local, `XPlan.FirstOfRun` is all that `AXPlan.Late`
requires. -/
theorem AXPlan.late_of_allLo {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (n : ℕ),
      RoundSplits.AllKind .lo A → AXPlan.CutKinds .lo P A Z → P.FirstOfRun n → AXPlan.Late P A Z n := by
  induction P with
  | nil => intro _ _ _ _ _ _; trivial
  | keep r P ih =>
      rintro A Z (_ | n) hA hc hf
      · trivial
      · exact ih A.2 Z n hA.2 hc hf
  | cut c P ih =>
      rintro A Z (_ | n) hA hc hf
      · exact hc.1
      · exact ⟨hc.1, ih (Z.1.ann2, A.2) Z.2 (n + 1) ⟨hA.1, hA.2⟩ hc.2 hf⟩
  | msg r1 r2 u P ih =>
      rintro A Z (_ | _ | n) hA hc hf
      · exact ⟨hA.2.1, ih (A.1.joinMsg A.2.1, A.2.2) Z 0 ⟨hA.2.1, hA.2.2⟩ hc hf⟩
      · exact hf.elim
      · exact ih (A.1.joinMsg A.2.1, A.2.2) Z (n + 1) ⟨hA.2.1, hA.2.2⟩ hc hf
  | chal r1 r2 np P ih =>
      rintro A Z (_ | _ | n) hA hc hf
      · exact ih (A.1.joinChal r2, A.2.2) Z 0 ⟨hA.1, hA.2.2⟩ hc hf
      · exact hf.elim
      · exact ih (A.1.joinChal r2, A.2.2) Z (n + 1) ⟨hA.1, hA.2.2⟩ hc hf

/-! ## 5. Further data -/

def AXPlan.Kits.slots (k1 : Kind) :
    {s : Shape} → (P : XPlan s) → (K : P.Kits) → (A : RoundSplits s) → (h : RoundSplits.SlotOnly A) →
    AXPlan.Kits P K A (AXPlan.slots k1 P A h)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun K (A : RAnn r × RoundSplits _) (h : A.1.SlotOnly × RoundSplits.SlotOnly A.2) =>
      AXPlan.Kits.slots k1 P K A.2 h.2
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits)
          (A : RAnn r × RoundSplits s) (h : A.1.SlotOnly × RoundSplits.SlotOnly A.2) =>
      (AKit.ofSlot k1 K.1,
        AKit.ofSlot A.1.kind K.2.1,
        AXPlan.Kits.slots k1 P K.2.2 (show RoundSplits (c.snd :: s) from (RAnn.ofSlot A.1.kind c.snd, A.2))
          (RAnn.slotOnly_ofSlot A.1.kind c.snd, h.2))
  | _, .msg r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s)
          (h : A.1.SlotOnly × A.2.1.SlotOnly × RoundSplits.SlotOnly A.2.2) =>
      AXPlan.Kits.slots k1 P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
        (h.1.joinMsg h.2.1, h.2.2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s)
          (h : A.1.SlotOnly × A.2.1.SlotOnly × RoundSplits.SlotOnly A.2.2) =>
      AXPlan.Kits.slots k1 P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))
        (h.1.joinChal r2, h.2.2)

/-! ## 6. The rounds of a front reduction: all local, only the slots send -/

/-- The annotation of any plan of rounds that are all local and sent by the slots. -/
def AXPlan.allLocal {s : Shape} (P : XPlan s) : AXPlan P (RoundSplits.allLocal s) :=
  AXPlan.slots .lo P (RoundSplits.allLocal s) (RoundSplits.slotOnly_const .lo s)

theorem RoundSplits.allKind_allLocal (s : Shape) : RoundSplits.AllKind .lo (RoundSplits.allLocal s) :=
  RoundSplits.allKind_const .lo _ (fun _ => rfl) s

theorem AXPlan.allLocal_ok {s : Shape} (P : XPlan s) : AXPlan.OK P _ (AXPlan.allLocal P) :=
  AXPlan.slots_ok .lo P _ _ (RoundSplits.slotLaw_const .lo s)
theorem AXPlan.allLocal_kinds {s : Shape} (P : XPlan s) : AXPlan.Kinds P _ (AXPlan.allLocal P) :=
  AXPlan.kinds_of_allKind .lo P _ _ (RoundSplits.allKind_allLocal s)
theorem AXPlan.allLocal_fit {s : Shape} (P : XPlan s) (ph : FPhase) :
    AXPlan.Fit P _ (AXPlan.allLocal P) ph :=
  AXPlan.fit_allLo P _ _ ph (RoundSplits.allKind_allLocal s) (AXPlan.slots_cutKinds .lo P _ _)
theorem AXPlan.allLocal_late {s : Shape} (P : XPlan s) {n : ℕ} (h : P.FirstOfRun n) :
    AXPlan.Late P _ (AXPlan.allLocal P) n :=
  AXPlan.late_of_allLo P _ _ n (RoundSplits.allKind_allLocal s) (AXPlan.slots_cutKinds .lo P _ _) h
def AXPlan.Kits.allLocal {s : Shape} (P : XPlan s) (K : P.Kits) :
    AXPlan.Kits P K _ (AXPlan.allLocal P) :=
  AXPlan.Kits.slots .lo P K _ _

end Iop
