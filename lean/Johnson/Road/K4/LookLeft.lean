-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/LookLeft.lean: WHAT THE LOOKUP LEFT, AS THE THREE LETTERS zOf, kTg, kIncS OF THE
VALUE OF Johnson/Road/K4/Value.lean: functions of the lookup's return (`Forest.Heard`) and of the
sub-proof's ledger (`Fork`) in front of the layers' own rounds. Six definitions and three theorems.
No protocol is run here: functions on records.

  `slotCo ρ a s`: the coefficient of slot s in the form a (a slot may occur more than once).
  `sum_slotCo`: a sum over the slots below n of such coefficients, each times f s, is the sum over
    the form's list of slots, if all of these are below n.
  `value_mask`: a form's value in a ledger's world (`Fork.worldOf`) is its value at the mask row 0,
    less the sum over its slots of coefficient times factor times mask entry.
  `zAt fo`: the lookup's point, read (`Road.zOf`).
  `padFo fo`: the public number for the lookup's padding trees: `Road.padOf`'s text, off the
    lookup's return.
  `keysPub fo`: the sum over the calls q of weight e_q times (alpha - q theta), plus `padFo`.
  `kTgAt fo F`: `keysPub` less the value of the lookup's end form cEnd at what was shown (the mask
    row 0, all entries of virtual rows 0).
  `kIncAt fo F s`: minus cEnd's coefficient at slot s times the ledger's factor at s.
  `kEnd_at`: if cEnd names no entry of a virtual row and slots below n alone: for every mask row,
    kTgAt less the sum over s < n of kIncAt s times the mask entry is `keysPub` LESS cEnd's VALUE IN
    THE LEDGER's WORLD.

Why these. The typed chain's start claim has "what the lookup's end leaves" as a public part and a
form in the entries. K4's start form holds, beside the calls' parts, the padding's number and minus
cEnd. By Johnson/Road/K4/StartLine.lean (`start_lines`): each call's part is worth
alpha - q theta less the call's own affine share; so what is left for the calls' joint extension is
`keysPub` less cEnd's worth.

Limits. THAT THIS CHOICE MAKES THE TYPED START TARGET THE PROGRAMS' PUBLIC PART AS A NUMBER IS NOT
SHOWN HERE. That a run's cEnd names no entry, and which slots, is a premise of `kEnd_at`.

-/
import Johnson.Road.FormsKeysLook
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Finset
open OnBytes.Model (Reading World Aff Fork Forest.Heard eqTab slotValue Ent.value)

section General
variable {K : Type} [Field K] (ρ : Reading K)

/-- The coefficient of slot s in a form. -/
def slotCo (a : Aff) (s : ℕ) : K :=
  ((a.slots.toList.filter fun x => x.1 == s).map fun x => ρ.val x.2).sum

/-- Summed slot by slot, or along the list. -/
theorem sum_slotCo (g : ℕ × E → K) (f : ℕ → K) (n : ℕ) :
    ∀ l : List (ℕ × E), (∀ x ∈ l, x.1 < n) →
      ∑ s : Fin n, ((l.filter fun x => x.1 == (s : ℕ)).map g).sum * f s =
        (l.map fun x => g x * f x.1).sum
  | [], _ => by simp
  | x :: l, h => by
    have hx : x.1 < n := h x List.mem_cons_self
    have ih := sum_slotCo g f n l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e : ∀ s : Fin n, (((x :: l).filter fun y => y.1 == (s : ℕ)).map g).sum =
        (if (s : ℕ) = x.1 then g x else 0) + ((l.filter fun y => y.1 == (s : ℕ)).map g).sum := by
      intro s
      by_cases hs : (s : ℕ) = x.1
      · simp [hs]
      · have hs' : ¬ x.1 = (s : ℕ) := fun h' => hs h'.symm
        simp [hs, hs']
    simp only [e, add_mul, sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_eq_single (⟨x.1, hx⟩ : Fin n)]
    · simp
    · intro s _ hs
      have hs' : ¬ (s : ℕ) = x.1 := fun h' => hs (Fin.ext h')
      simp [hs']
    · intro h'
      exact absurd (mem_univ _) h'

/-- A form's value in a ledger's world, against its value at the mask row 0. -/
theorem value_mask (F : Fork) (a : Aff) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    a.value ρ (F.worldOf ρ mask entry) = a.value ρ (F.worldOf ρ (fun _ => 0) entry) -
      (a.slots.toList.map fun x =>
        ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum := by
  have hs : ∀ l : List (ℕ × E), (l.map (slotValue ρ (F.worldOf ρ mask entry))).sum =
      (l.map (slotValue ρ (F.worldOf ρ (fun _ => 0) entry))).sum -
        (l.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum := by
    have hx : ∀ x : ℕ × E, slotValue ρ (F.worldOf ρ mask entry) x =
        slotValue ρ (F.worldOf ρ (fun _ => 0) entry) x -
          ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1) := by
      intro x
      simp only [slotValue, Fork.worldOf]
      ring
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, ih, hx x]
      ring
  have he : (a.ents.toList.map (Ent.value ρ (F.worldOf ρ mask entry))).sum =
      (a.ents.toList.map (Ent.value ρ (F.worldOf ρ (fun _ => 0) entry))).sum := rfl
  unfold Aff.value
  rw [hs, he]
  ring

end General

/-- The lookup's point, read. -/
def zAt (fo : Forest.Heard) : ℕ → Cb.Gl.E := zOf Reading.gl fo.zx fo.zy

/-- The public number for the padding trees of the lookup. -/
def padFo (fo : Forest.Heard) : E :=
  (List.range (2 ^ fo.shape.rK - fo.shape.NT)).foldl
    (fun a t => addE a (mulE ((eqTab fo.zy).getD (fo.shape.NT + t) zeroE)
      (subE fo.alpha (fo.padKey 0)))) zeroE

/-- The calls' weights times alpha - q theta, and the padding's number. -/
noncomputable def keysPub (fo : Forest.Heard) : Cb.Gl.E :=
  ∑ q ∈ range fo.e.size, Reading.gl.val (fo.e.getD q zeroE) *
    (Reading.gl.val fo.alpha - (q : Cb.Gl.E) * Reading.gl.val fo.theta) +
    Reading.gl.val (padFo fo)

/-- The public part of what the lookup's end leaves. -/
noncomputable def kTgAt (fo : Forest.Heard) (F : Fork) : Cb.Gl.E :=
  keysPub fo - fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0)

/-- Its coefficient at the mask entry of slot s. -/
noncomputable def kIncAt (fo : Forest.Heard) (F : Fork) (s : ℕ) : Cb.Gl.E :=
  -(slotCo Reading.gl fo.cEnd s * Reading.gl.val (F.mf.getD s zeroE))

/-- **What the lookup's end leaves is `keysPub` less the end form's value in the ledger's
world.** -/
theorem kEnd_at (fo : Forest.Heard) (F : Fork) (n : ℕ) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (he : fo.cEnd.ents = #[])
    (hs : ∀ x ∈ fo.cEnd.slots.toList, x.1 < n) :
    kTgAt fo F - ∑ s : Fin n, kIncAt fo F s * mask s =
      keysPub fo - fo.cEnd.value Reading.gl (F.worldOf Reading.gl mask entry) := by
  have e0 : fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) entry) =
      fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) := by
    unfold Aff.value
    rw [he]
    rfl
  have e1 := sum_slotCo (fun x : ℕ × E => Reading.gl.val x.2)
    (fun s => Reading.gl.val (F.mf.getD s zeroE) * mask s) n fo.cEnd.slots.toList hs
  have e2 : ∑ s : Fin n, kIncAt fo F s * mask s =
      -∑ s : Fin n, ((fo.cEnd.slots.toList.filter fun x => x.1 == (s : ℕ)).map
        fun x : ℕ × E => Reading.gl.val x.2).sum *
          (Reading.gl.val (F.mf.getD s zeroE) * mask s) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun s _ => ?_
    unfold kIncAt slotCo
    ring
  rw [e2, e1, value_mask Reading.gl F fo.cEnd mask entry, e0]
  unfold kTgAt
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sum_slotCo
#print axioms OnBytes.Road.K4.value_mask
#print axioms OnBytes.Road.K4.kEnd_at
