-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevOut.lean: what is read off the state behind m key sides, as lists.

  `sidesCl`     the parts' masked claims, in the parts' order. `sidesRows`: all levels' rows.
  `clsHold ps cs x0 m`  claim number i of the list cs holds of part i's keys, read at the state x0.
  `sidesOut_iff`  `sidesOut` says: the rows hold, and `clsHold` at the state of entry.
  `rootsHold_iff`, `clsHold_iff`  both by index: for every i below the list's length.
Conditions: none, but that `clsHold_iff` asks lists of equal length.
The rows stand in the order of the sumchecks.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Iop IOR Hiop Prob

noncomputable section
variable {E : Type} [Field E] [Fintype E] {B : KeyBase E}

def sidesCl : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) →
    SidesSt p ps X pr → List (MCl E B.J)
  | p, [], X, pr, x => [p.cl X pr x]
  | p, r :: ps, X, pr, x =>
    p.cl X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x) :: sidesCl r ps (p.SideSt X pr) (p.prN
        X pr) x

def sidesRows : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) →
    SidesSt p ps X pr → List (Row E B.J)
  | p, [], X, pr, x => p.rows X pr x
  | p, r :: ps, X, pr, x =>
    p.rows X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x) ++
      sidesRows r ps (p.SideSt X pr) (p.prN X pr) x

theorem sidesCl_length : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0)
    (x : SidesSt p ps X pr), (sidesCl p ps X pr x).length = ps.length + 1
  | [], _, _, _, _ => rfl
  | r :: ps, p, X, pr, x =>
    congrArg (· + 1) (sidesCl_length ps r (p.SideSt X pr) (p.prN X pr) x)

/-- claim number i holds of part number i's keys -/
def clsHold : List (KeyPart B) → List (MCl E B.J) → B.X0 → (B.J → E) → Prop
  | p :: ps, c :: cs, x0, m => c.Holds (p.v' + 1) (p.key (B.st x0) m) m ∧ clsHold ps cs x0 m
  | _, _, _, _ => True

theorem rowsHold_append (a b : List (Row E B.J)) (m : B.J → E) :
    RowsHold (a ++ b) m ↔ RowsHold a m ∧ RowsHold b m :=
  ⟨fun h => ⟨fun r hr => h r (List.mem_append_left _ hr), fun r hr => h r (List.mem_append_right _
      hr)⟩,
    fun h r hr => (List.mem_append.1 hr).elim (h.1 r) (h.2 r)⟩

theorem sidesOut_iff : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0)
    (x : SidesSt p ps X pr) (m : B.J → E),
    sidesOut p ps X pr x m ↔
      RowsHold (sidesRows p ps X pr x) m ∧
        clsHold (p :: ps) (sidesCl p ps X pr x) (pr (sidesOld p ps X pr x)) m
  | [], p, X, pr, x, m =>
    ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩
  | r :: ps, p, X, pr, x, m => by
    have ih := sidesOut_iff ps r (p.SideSt X pr) (p.prN X pr) x m
    show (p.OutHolds X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x) m ∧
        sidesOut r ps (p.SideSt X pr) (p.prN X pr) x m) ↔
      RowsHold (p.rows X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x) ++
          sidesRows r ps (p.SideSt X pr) (p.prN X pr) x) m ∧
        ((p.cl X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x)).Holds (p.v' + 1)
            (p.key (B.st (p.prN X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x))) m) m ∧
          clsHold (r :: ps) (sidesCl r ps (p.SideSt X pr) (p.prN X pr) x)
            (p.prN X pr (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x)) m)
    rw [rowsHold_append, ih]
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩

/-- by index -/
theorem rootsHold_iff : ∀ (ps : List (KeyPart B)) (x0 : B.X0) (m : B.J → E),
    rootsHold ps x0 m ↔ ∀ (i : ℕ) (h : i < ps.length), ps[i].RootHolds x0 m
  | [], _, _ => ⟨fun _ i h => absurd h (Nat.not_lt_zero i), fun _ => trivial⟩
  | p :: ps, x0, m => by
    show (p.RootHolds x0 m ∧ rootsHold ps x0 m) ↔ _
    rw [rootsHold_iff ps x0 m]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi)
    · intro h
      exact ⟨h 0 (Nat.succ_pos _), fun i hi => h (i + 1) (Nat.succ_lt_succ hi)⟩

theorem clsHold_iff : ∀ (ps : List (KeyPart B)) (cs : List (MCl E B.J)) (x0 : B.X0) (m : B.J → E),
    cs.length = ps.length →
    (clsHold ps cs x0 m ↔ ∀ (i : ℕ) (h : i < ps.length) (h' : i < cs.length),
      cs[i].Holds (ps[i].v' + 1) (ps[i].key (B.st x0) m) m)
  | [], [], _, _, _ => ⟨fun _ i h => absurd h (Nat.not_lt_zero i), fun _ => trivial⟩
  | [], _ :: _, _, _, e => absurd e (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, e => absurd e.symm (Nat.succ_ne_zero _)
  | p :: ps, c :: cs, x0, m, e => by
    show (c.Holds (p.v' + 1) (p.key (B.st x0) m) m ∧ clsHold ps cs x0 m) ↔ _
    rw [clsHold_iff ps cs x0 m (Nat.succ.inj e)]
    constructor
    · rintro ⟨h0, h1⟩ i hi hi'
      cases i with
      | zero => exact h0
      | succ i => exact h1 i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')
    · intro h
      exact ⟨h 0 (Nat.succ_pos _) (Nat.succ_pos _),
        fun i hi hi' => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi')⟩

end
end Lk6

#print axioms Lk6.sidesOut_iff
#print axioms Lk6.clsHold_iff
