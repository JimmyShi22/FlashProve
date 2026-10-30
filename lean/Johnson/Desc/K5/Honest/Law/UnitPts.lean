-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/UnitPts.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the premises of the readings of a softmax-table unit's summand
(Law/ReadKM.lean, Law/ReadKD.lean), FROM WHAT THE LOOKUP HANDS ON. A definition, and statements with
their proofs.

The two files on the units' summands take as premises that the unit's named points, read, are the
library's (`UnitReads`), and some facts on the place (`UnitPlace`). Here these are drawn from the
text of the verifier's function of the points (`pointsOf`, Johnson/Desc/First/Att/Points.lean) and
from two premises of Johnson/Desc/First/Att/K05LookAll.lean: `KeyPtsAre` (each lookup call's key
point, read, is the library's) and `UnitIs` (the unit is the library's family of looked-up values:
public).

Main names:
  `UnitLaid`, `units_laid`, `unit_laid`
                    what the verifier's function lays into a unit's points: the unit's flag and
                    pieces, and two cuts of its inner point
  `np_of_unitIs`    the unit has a piece for each pair
  `unitReads_below`, `unitReads_on`
                    `UnitReads` of a unit below the diagonal, on it
  `sKM_reads_of`, `sKD_reads_of`
                    `StepReads` (Law/ProductsLaw.lean) of the two summands, from these premises; its
                    `total` and `tame` give the sum and the prover's properties

EVERY STATEMENT IS CONDITIONAL. The premises that are left, and who is meant to show each:
  `Sized`, `UnitIs`, `PairsAre`, the unit's flag (hbel: no field of `UnitIs` holds it), the number
    of variables, that the place has the unit: public, the
    caller's. `UnitIs` has a test with code (`unitOk`, K05LookAll.lean); it is run at small made-up
    places in Law/PremisesToy.lean and Law/UnitPtsToy.lean, and at no other place that is known.
    `PairsAre` does not follow from `UnitIs`, whose test reads a piece's layer and head for the
    pieces' order alone and compares neither with a fixed number; the tree's
    `PiecesAll` (Johnson/Road/Rows/AttRead.lean) says the same of the same pieces in another type.
  that the verifier's function of the points returns: tests on lengths alone, the caller's.
  `KeyPtsAre`: the lookup's to show of what it hands on (`K3Pts`, K05LookAll.lean).
  on the diagonal: that a piece of the list below the diagonal is no longer than its call: public.
Limits. A PLAN IN WHICH THE LAYERS OF THE GROUP HAVE MORE THAN ONE SHIFT IS NOT REACHED: there a
softmax-table unit has the pieces of some layers alone, while the library's step sums over all
pairs, and the premise that the unit has a piece for each pair fails. `KeyPtsAre` speaks of four
lookup calls. Nothing here says that a premise holds at any place. No property is claimed by a
definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.ReadKM
import Johnson.Desc.K5.Honest.Law.ReadKD
import Johnson.Desc.First.Att.Claims.PointsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff)
open OnBytes.Road (pt)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.First.Att.P (Geo W1 ScoreP UnitG Heard Left Pts pointsOf piecesOf
  inner weights KeyPtsAre UnitIs inner_read inner_size unitPtsM_of unitPtsD_of weights_eq pcsSorted)
open K5Law (cutB)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## What the verifier's function lays into a unit's points -/

/-- **What the verifier's function of the points lays into the points k of the unit u**: the unit's
flag and pieces, and the two cuts of its inner point that are the query's and the key's place in a
tile. -/
structure UnitLaid (g : Geo) (zk : Array (Array E)) (u : UnitG) (k : ScoreP) : Prop where
  flag : k.below = u.below
  pw : k.pw = piecesOf u (zk.getD u.call #[])
  zi : k.zi = (inner u (zk.getD u.call #[])).extract (cutB g u.below) (cutB g u.below + g.lB)
  zj : k.zj =
    (inner u (zk.getD u.call #[])).extract (cutB g u.below + g.lB) (cutB g u.below + 2 * g.lB)

/-- Two lists that are related member by member are related at each number. -/
theorem UnitLaid.forall₂_at {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ (i : ℕ) (a : α) (b : β), l[i]? = some a → l'[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h _, 0, a, b, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha hb
    exact h
  | _, _, .cons _ t, i + 1, a, b, ha, hb =>
    UnitLaid.forall₂_at t i a b (by simpa using ha) (by simpa using hb)

/-- Where the verifier's function returns, its units' points are laid so, unit by unit. -/
theorem units_laid {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) :
    List.Forall₂ (fun (k : ScoreP) (u : UnitG) => UnitLaid g zk u k) p.scores.toList g.scores := by
  have PA := K5Law.points_are hp
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, _, uX, _, uH, _, _, hs, _, _, e⟩ := hp
  rw [← Array.foldlM_toList] at hf
  obtain ⟨ks, e2, f2, _⟩ := K5Law.foldlM_push _
    (fun (k : ScoreP) (x : (UnitG × ℕ × MaskedSum.Heard) × Aff) => UnitLaid g zk x.1.1 k)
    (fun acc x acc1 h1 => by
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h1
      obtain ⟨_, _, e1⟩ := h1
      exact ⟨_, _, e1.symm, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩) _ _ _ hf
  rw [← K5Law.zipped_fst PA, List.forall₂_map_right_iff]
  subst e
  show List.Forall₂ _ a.2.toList _
  rw [e2]
  simpa using f2.imp fun _ _ h => h.1

/-- The same at the unit number i of the place, for the prover's call of that function. -/
theorem unit_laid {P : Pub5} {c : Chal} {i : ℕ} {u : UnitG} {k : ScoreP}
    (hu : P.g.scores[i]? = some u) (hk : (ptsOf P c).bind (·.scores[i]?) = some k) :
    UnitLaid P.g c.zk u k := by
  obtain ⟨pts, hp, hk'⟩ := Option.bind_eq_some_iff.1 hk
  exact UnitLaid.forall₂_at (units_laid hp) i k u (by rw [Array.getElem?_toList]; exact hk') hu

/-- A unit that is a family of the library's has a piece for each pair. -/
theorem np_of_unitIs {D : Dim} {C : Calls} {fam : Fam} {q : Fin 4} {u : UnitG}
    (U : UnitIs D C fam q u) : u.pcs.length = D.nb := by
  have h := U.nPw #[]
  rw [weights_eq] at h
  simpa [pcsSorted] using h

/-! ## The named points, read -/

variable {P : Pub5} {C : Calls} {z : ℕ → K} {zk : Array (Array E)} {u : UnitG} {k : ScoreP}

/-- **The named points of a unit below the diagonal, read, are the library's.** CONDITIONAL on: the
shape's numbers, the unit is the library's family, piece b is pair b (public); the points are laid
by the verifier's function; the key points, read, are the library's (the lookup's to show). -/
theorem unitReads_below (H : Sized P) (Ld : UnitLaid P.g zk u k) (hbel : u.below = true)
    (Kp : KeyPtsAre ρ C z zk) {q : Fin 4} (U : UnitIs P.D C .m1 q u) (pr : PairsAre P.g k.pw) :
    UnitReads ρ P C z k := by
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  have hs : (inner u (zk.getD u.call #[])).size =
      P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB := inner_size Kp U
  have cB : cutB P.g u.below = P.D.lg + P.D.lP + (P.D.lP + 1) := by
    rw [hbel]
    show P.D.lg + (P.g.lnT - 1) + P.g.lnT = _
    omega
  have ezi : k.zi = (inner u (zk.getD u.call #[])).extract (P.D.lg + P.D.lP + (P.D.lP + 1))
      (P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB) := by rw [Ld.zi, cB]; rfl
  have ezj : k.zj = (inner u (zk.getD u.call #[])).extract
      (P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB) (P.D.lg + P.D.lP + (P.D.lP + 1) + 2 * P.D.lB) := by
    rw [Ld.zj, cB]
    rfl
  refine ⟨?_, fun j hj => ?_, ?_, fun j hj => ?_, pr⟩
  · rw [ezi, size_extract_le _ (by omega)]
    omega
  · rw [ezi, pt_extract ρ _ _ _ j (by omega)]
    exact inner_read Kp U _ (by
      show _ < P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB
      omega)
  · rw [ezj, size_extract_le _ (by omega)]
    omega
  · rw [ezj, pt_extract ρ _ _ _ j (by omega)]
    exact inner_read Kp U _ (by
      show _ < P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB
      omega)

/-- **The named points of a unit on the diagonal, read, are the library's**, which cuts them from
the list below the diagonal: the two lists' inner points are the last coordinates of one key point.
CONDITIONAL as `unitReads_below`, and on: a piece of the list below the diagonal is no longer than
its call (public). -/
theorem unitReads_on (H : Sized P) (Ld : UnitLaid P.g zk u k) (hbel : u.below = false)
    (Kp : KeyPtsAre ρ C z zk) {q : Fin 4} (U : UnitIs P.D C .d1 q u) (hM : P.D.lM ≤ C.a 0)
    (pr : PairsAre P.g k.pw) : UnitReads ρ P C z k := by
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  have hs : (inner u (zk.getD u.call #[])).size = P.D.lg + (P.D.lP + 1) + P.D.lB + P.D.lB :=
    inner_size Kp U
  have hM' : P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB ≤ C.a 0 := hM
  have cB : cutB P.g u.below = P.D.lg + (P.D.lP + 1) := by
    rw [hbel]
    show P.D.lg + P.g.lnT = _
    omega
  have ezi : k.zi = (inner u (zk.getD u.call #[])).extract (P.D.lg + (P.D.lP + 1))
      (P.D.lg + (P.D.lP + 1) + P.D.lB) := by rw [Ld.zi, cB]; rfl
  have ezj : k.zj = (inner u (zk.getD u.call #[])).extract (P.D.lg + (P.D.lP + 1) + P.D.lB)
      (P.D.lg + (P.D.lP + 1) + 2 * P.D.lB) := by rw [Ld.zj, cB]; rfl
  have tail : ∀ t, t < P.D.lg + (P.D.lP + 1) + P.D.lB + P.D.lB →
      pt ρ (inner u (zk.getD u.call #[])) t = inn P.D C z .m1 (P.D.lP + t) := fun t ht => by
    refine (inner_read Kp U t ht).trans ?_
    show C.zC 0 z (C.a 0 - (P.D.lg + (P.D.lP + 1) + P.D.lB + P.D.lB) + t) =
      C.zC 0 z (C.a 0 - (P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB) + (P.D.lP + t))
    congr 1
    omega
  refine ⟨?_, fun j hj => ?_, ?_, fun j hj => ?_, pr⟩
  · rw [ezi, size_extract_le _ (by omega)]
    omega
  · rw [ezi, pt_extract ρ _ _ _ j (by omega), tail _ (by omega)]
    show inn P.D C z .m1 _ = inn P.D C z .m1 (P.D.lg + P.D.lP + (P.D.lP + 1) + j)
    congr 1
    omega
  · rw [ezj, size_extract_le _ (by omega)]
    omega
  · rw [ezj, pt_extract ρ _ _ _ j (by omega), tail _ (by omega)]
    show inn P.D C z .m1 _ = inn P.D C z .m1 (P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + j)
    congr 1
    omega

/-! ## The two summands, from what the lookup hands on -/

variable {p : Pub K} (w : K5In)

/-- **The summand of a unit below the diagonal reads as the library's of step s6b.** CONDITIONAL on
what the head of this file lists. -/
theorem sKM_reads_of (H : Sized P) {c : Chal} {i : ℕ} (hu : P.g.scores[i]? = some u)
    (hk : (ptsOf P c).bind (·.scores[i]?) = some k) (hbel : u.below = true)
    (hv : (cut P.x).getD i 3 - 3 = Step.s6b.g P.D) (Kp : KeyPtsAre ρ C p.z c.zk) {q : Fin 4}
    (U : UnitIs P.D C .m1 q u) (pr : PairsAre P.g k.pw) :
    StepReads ρ (sK P w c i) P.D C p (tOf ρ w) .s6b := by
  have Ld := unit_laid hu hk
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  refine sKM_reads ρ w H ⟨hu, hk, Ld.flag, (inner_size Kp U).trans ?_, hv, np_of_unitIs U⟩ hbel
    (unitReads_below ρ H Ld hbel Kp U pr) (unitPtsM_of Kp U)
  show P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB + P.D.lB =
    P.D.lg + (P.g.lnT - 1) + P.g.lnT + 2 * P.D.lB
  omega

/-- **The summand of a unit on the diagonal reads as the library's of step s6d.** CONDITIONAL on
what the head of this file lists. -/
theorem sKD_reads_of (H : Sized P) {c : Chal} {i : ℕ} (hu : P.g.scores[i]? = some u)
    (hk : (ptsOf P c).bind (·.scores[i]?) = some k) (hbel : u.below = false)
    (hv : (cut P.x).getD i 3 - 3 = Step.s6d.g P.D) (Kp : KeyPtsAre ρ C p.z c.zk) {q : Fin 4}
    (U : UnitIs P.D C .d1 q u) (hM : P.D.lM ≤ C.a 0) (pr : PairsAre P.g k.pw) :
    StepReads ρ (sK P w c i) P.D C p (tOf ρ w) .s6d := by
  have Ld := unit_laid hu hk
  have hl : P.g.lnT = P.D.lP + 1 := H.lnT
  refine sKD_reads ρ w H ⟨hu, hk, Ld.flag, (inner_size Kp U).trans ?_, hv, np_of_unitIs U⟩ hbel
    (unitReads_on ρ H Ld hbel Kp U hM pr) (unitPtsD_of Kp U)
  show P.D.lg + (P.D.lP + 1) + P.D.lB + P.D.lB = P.D.lg + P.g.lnT + 2 * P.D.lB
  omega

end H2K5.Honest

#print axioms H2K5.Honest.UnitLaid.forall₂_at
#print axioms H2K5.Honest.units_laid
#print axioms H2K5.Honest.unit_laid
#print axioms H2K5.Honest.np_of_unitIs
#print axioms H2K5.Honest.unitReads_below
#print axioms H2K5.Honest.unitReads_on
#print axioms H2K5.Honest.sKM_reads_of
#print axioms H2K5.Honest.sKD_reads_of
