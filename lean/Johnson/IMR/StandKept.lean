--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/IMR/StandKept.lean:
WHERE THE VERIFIER's STATE STANDS IS KEPT: the three
things that the table of joints' book-keeping at a border reads of the state that the description's
fold carries from block to block (Johnson/Desc/First/Borders.lean: shapeAt: standOf; S.noneWaits;
the open link's number).
  StandKept s s': standOf s' = standOf s; where no count of rows waited none waits; the open link's
    number, or that none is open, stays. Reflexive, transitive.
  stand_of_quiet: a Quiet step (Johnson/Goal/Meaning/RecQuiet.lean) keeps it: off Quiet.arm,
    Quiet.ctx, Quiet.waits. whole_stand: so every Quiet maker's block: kinds K3, K4, K5, K6, K7, K8,
    K11 and the quiet steps behind the reads.
  commitAtS_stand: kind K1's later sending keeps it too (it is not Quiet): behind it nothing is
    owed; what ctxOf reads stays by Johnson/Goal/Meaning/OwnMakers.lean's commitAtS_ctx.
OBJECT: the makers' blocks, at every letter. USER: the pen of the row on the first chain's last
state at the proof file.
Not claimed: that the table says the same stand at two borders. No soundness.
-/
import Johnson.Goal.Meaning.RecSeated
import Johnson.Desc.First.Borders
import Johnson.Goal.Meaning.OwnMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)

/-- **The relation.** -/
def StandKept (s s' : S) : Prop :=
  standOf s' = standOf s ∧ (s.noneWaits = true → s'.noneWaits = true) ∧
    s'.link?.map (·.link) = s.link?.map (·.link)

theorem stand_refl (s : S) : StandKept s s := ⟨rfl, id, rfl⟩

theorem stand_trans (a b c : S) (h : StandKept a b) (k : StandKept b c) : StandKept a c :=
  ⟨k.1.trans h.1, fun w => k.2.1 (h.2.1 w), k.2.2.trans h.2.2⟩

/-- The form of the state's own part and what ctxOf reads fix the stand and the open link's
number. -/
theorem stand_of_arm {s s' : S} (ha : armOf s' = armOf s) (hc : ctxOf s' = ctxOf s) :
    standOf s' = standOf s ∧ s'.link?.map (·.link) = s.link?.map (·.link) := by
  cases hs : s.here <;> cases hs' : s'.here <;> simp [armOf, hs, hs'] at ha <;>
    simp [ctxOf, hs, hs'] at hc <;>
    simp [standOf, S.inLink, S.fork?, S.link?, hs, hs']
  · exact hc.2.2.1
  · exact hc.2.2.1
  · rename_i a a'
    obtain ⟨-, ho, -, hl, -⟩ := hc
    have e : a'.opened = a.opened := by
      cases h1 : a'.opened <;> cases h2 : a.opened <;> simp [h1, h2] at ho ⊢
    rw [e, hl]
    exact ⟨rfl, rfl⟩

theorem stand_of_quiet {s s' : S} (q : Quiet s s') : StandKept s s' :=
  ⟨(stand_of_arm q.arm q.ctx).1, q.waits, (stand_of_arm q.arm q.ctx).2⟩

theorem whole_stand {Cl : Type} {b : Block S Cl} (W : Whole Quiet b) : Whole StandKept b :=
  whole_mono (fun _ _ => stand_of_quiet) W

/-! ## Kind K1's later sending -/

theorem arm_putLink (s : S) (L : LinkCtx) : armOf (s.putLink L) = armOf s := by
  unfold S.putLink
  split
  · simp [armOf, *]
  · simp [armOf, *]
  · split <;> simp [armOf, *]
  · rfl

theorem waits_putLink (s : S) (L : LinkCtx) : (s.putLink L).noneWaits = s.noneWaits := by
  unfold S.putLink
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem commitAtS_stand {Cl : Type} (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole StandKept (K1.commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have hc : ctxOf s' = ctxOf s := (commitAtS_ctx P link moment arrays).1 s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · obtain ⟨y, -, rfl⟩ := Keeps.emap_ok h
    have ha : armOf (((K1.laid s y.held.w).putLink y.held.L).putFork y.held.F) = armOf s := by
      rw [(quiet_putFork _ _).arm, arm_putLink]
      rfl
    exact ⟨(stand_of_arm ha hc).1,
      fun _ => (quiet_putFork _ _).waits ((waits_putLink _ _).trans rfl), (stand_of_arm ha hc).2⟩
  · cases h

#print axioms stand_of_quiet
#print axioms commitAtS_stand

end Meaning.K2
