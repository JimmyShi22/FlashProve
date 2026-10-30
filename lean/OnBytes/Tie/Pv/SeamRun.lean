-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/SeamRun.lean: where the fields of RowTie (OnBytes/Tie/Pv/Seam.lean) come from.

RowTie ties the output statement of a typed masked sumcheck to the record p and the state F with
which the shipped Lean verifier ends that sumcheck. This file fills its fields from smaller facts.

Definitions. slotNo l s i: the number of the slot under which the coefficient i of the hiding
polynomial lies, if the sumcheck's slots begin at s: by variable, then by degree from 1 up; the last
variable begins with the constant. hCount l: the number of these coefficients. slotP: slotNo on the
variables' formats alone.

Statements.
  place_slotNo, slotNo_mem   the value that stands for a coefficient (place,
      OnBytes/Tie/Pv/Psc/StepWalk.lean) is the one under slot slotNo; that slot lies among the
      hCount l slots from s on.
  slotNo_pIx, hw_of   slotNo does not read the variables' data; so the first premise of hid_of
      follows from a fact on Y.wAt alone.
  hid_of   the field hid, from two facts: the entry that serves as the coefficient i is entry
      slotNo of the mask row; under each of the sumcheck's own slots the state holds the shown
      scalar 0 and the factor -1 (what pscRow puts there).
  rowTie_of_tie   the fields walk, ne, eps and fin, for the output of the short sumcheck on a typed
      transcript: from PscAt (the record's weights, challenges and running claim), Fits (the
      verifier's weights fit the library's variables) and ReadsAs (the verifier's rounds, read, are
      the typed transcript's): the three premises of row_iff_UHolds
      (OnBytes/Tie/Pv/Psc/PscTie.lean), by its lemmas match_of and claimAfter_hFin. The fields hid
      and inc are handed through.

Not claimed. That a run of the verifier's routines gives PscAt and the two facts on the state; that
a typed transcript reads as the verifier's rounds. The premises are facts on one run's end: see the
head of OnBytes/Tie/Pv/Seam.lean. Nothing on soundness or on hiding.

-/
import OnBytes.Tie.Pv.Seam
import OnBytes.Tie.Pv.Psc.PscTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv
open Iop Cb OnBytes OnBytes.Model OnBytes.Road.Hd Johnson.L5.Layers

section Places
variable {K : Type}

/-- The slot of a coefficient of the hiding polynomial. -/
def slotNo : (l : List (HVar K)) → ℕ → HIdx l → ℕ
  | [], s, _ => s
  | [_], s, Sum.inl t => s + 1 + (t : ℕ)
  | [_], s, Sum.inr _ => s
  | _ :: _ :: _, s, Sum.inl t => s + (t : ℕ)
  | v :: v' :: l, s, Sum.inr i => slotNo (v' :: l) (s + v.n) i

/-- The number of coefficients of the hiding polynomial. -/
def hCount : List (HVar K) → ℕ
  | [] => 1
  | v :: l => v.n + hCount l

theorem place_slotNo (mask : ℕ → K) : ∀ (l : List (HVar K)) (s : ℕ) (i : HIdx l),
    place mask l s i = mask (slotNo l s i)
  | [], _, _ => rfl
  | [_], _, Sum.inl _ => rfl
  | [_], _, Sum.inr _ => rfl
  | _ :: _ :: _, _, Sum.inl _ => rfl
  | v :: v' :: l, s, Sum.inr i => place_slotNo mask (v' :: l) (s + v.n) i

theorem slotNo_mem : ∀ (l : List (HVar K)) (s : ℕ) (i : HIdx l),
    s ≤ slotNo l s i ∧ slotNo l s i < s + hCount l
  | [], s, _ => ⟨Nat.le_refl s, Nat.lt_succ_self s⟩
  | [v], s, Sum.inl t => by
    have ht : (t : ℕ) < v.n := t.isLt
    show s ≤ s + 1 + (t : ℕ) ∧ s + 1 + (t : ℕ) < s + (v.n + 1)
    omega
  | [v], s, Sum.inr _ => by
    show s ≤ s ∧ s < s + (v.n + 1)
    omega
  | v :: v' :: l, s, Sum.inl t => by
    have ht : (t : ℕ) < v.n := t.isLt
    show s ≤ s + (t : ℕ) ∧ s + (t : ℕ) < s + (v.n + hCount (v' :: l))
    omega
  | v :: v' :: l, s, Sum.inr i => by
    obtain ⟨h1, h2⟩ := slotNo_mem (v' :: l) (s + v.n) i
    show s ≤ slotNo (v' :: l) (s + v.n) i ∧
      slotNo (v' :: l) (s + v.n) i < s + (v.n + hCount (v' :: l))
    omega

/-- slotNo on the formats alone. -/
def slotP : (l : List (PFmt K)) → ℕ → PIdx l → ℕ
  | [], s, _ => s
  | [_], s, Sum.inl t => s + 1 + (t : ℕ)
  | [_], s, Sum.inr _ => s
  | _ :: _ :: _, s, Sum.inl t => s + (t : ℕ)
  | f :: f' :: l, s, Sum.inr i => slotP (f' :: l) (s + f.n) i

theorem slotNo_pIx : ∀ (l : List (PFmt K)) (d : PDats l) (s : ℕ) (i : HIdx (pVars l d)),
    slotNo (pVars l d) s i = slotP l s (pIx l d i)
  | [], _, _, _ => rfl
  | [_], _, _, Sum.inl _ => rfl
  | [_], _, _, Sum.inr _ => rfl
  | _ :: _ :: _, _, _, Sum.inl _ => rfl
  | f :: f' :: l, d, s, Sum.inr i => slotNo_pIx (f' :: l) d.2 (s + f.n) i

end Places

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) (Y : PscPar K)

omit [Fintype K] in
/-- The first premise of hid_of, from the places of the sumcheck's own masks. -/
theorem hw_of (mask : (Y.J → K) → ℕ → K) (st : Y.St) (first : ℕ)
    (h : ∀ m q, m (Y.wAt q) = mask m (slotP Y.fmt first q)) (m : Y.J → K)
    (i : HIdx (Y.vars st)) : Y.W st m i = mask m (slotNo (Y.vars st) first i) := by
  rw [slotNo_pIx]
  exact h m _

omit [Fintype K] in
/-- The field hid of RowTie. -/
theorem hid_of (F : Fork) (mask : (Y.J → K) → ℕ → K) (entry : (Y.J → K) → ℕ → ℕ → ℕ → K)
    (st : Y.St) (first : ℕ)
    (hw : ∀ m i, Y.W st m i = mask m (slotNo (Y.vars st) first i))
    (hz : ∀ j, first ≤ j → j < first + hCount (Y.vars st) →
      ρ.val (F.vp.getD j zeroE) = 0 ∧ ρ.val (F.mf.getD j zeroE) = -1) (m : Y.J → K) :
    Y.W st m = place (F.worldOf ρ (mask m) (entry m)).slot (Y.vars st) first := by
  funext i
  rw [place_slotNo]
  obtain ⟨h1, h2⟩ := slotNo_mem (Y.vars st) first i
  obtain ⟨z1, z2⟩ := hz _ h1 h2
  show _ = ρ.val (F.vp.getD (slotNo (Y.vars st) first i) zeroE) -
    ρ.val (F.mf.getD (slotNo (Y.vars st) first i) zeroE) * mask m (slotNo (Y.vars st) first i)
  rw [z1, z2, hw]
  ring

/-- RowTie for the output of the short sumcheck on a typed transcript that reads as the verifier's
rounds. -/
theorem rowTie_of_tie (Ex : ExtSpec) (F : Fork) (mask : (Y.J → K) → ℕ → K)
    (entry : (Y.J → K) → ℕ → ℕ → ℕ → K) (p : Psc) (ws : List OnBytes.Psc.Weight)
    (rs : List (List E × E)) (mu : E) (st : Y.St) (Fx : HFixs (Y.vars st))
    (τ : Tr (sRounds Y.fmt ++ [pRoundV K Y.A]))
    (hp : PscAt p ws rs mu) (hF : Fits ρ ws Y.fmt (Y.dat st) Fx)
    (hR : ReadsAs ρ rs Y.fmt [pRoundV K Y.A] τ) (hne : ws.zip (rs.map (·.2)) ≠ [])
    (hid : ∀ m, Y.W st m = place (F.worldOf ρ (mask m) (entry m)).slot (Y.vars st) p.first)
    (inc : ∀ m, Y.inc st m =
      ρ.val p.target - p.start.value ρ (F.worldOf ρ (mask m) (entry m))) :
    RowTie ρ Y F mask entry p
      (outS Y (ρ.val p.target, st) Fx Ex (((), ρ.val mu), ρ.val p.eps, τ)) where
  walk := by
    rw [zipT_eq, hp.vars, hp.r]
    exact match_of ρ ws rs Y.fmt (Y.dat st) Fx [pRoundV K Y.A] τ
      (ρ.val mu + ρ.val p.eps * ρ.val p.target) hF hR
  ne := by
    rw [zipT_eq, hp.vars, hp.r]
    exact hne
  eps := rfl
  fin := by
    have hc := claimAfter_hFin ρ ws rs Y.fmt (Y.dat st) Fx [pRoundV K Y.A] τ
      (addE mu (mulE p.eps p.target)) hF hR
    rw [← hp.claim, ρ.add, ρ.mul] at hc
    exact hc.symm
  hid := hid
  inc := inc

end OnBytes.Tie.Pv

#print axioms OnBytes.Tie.Pv.hid_of
#print axioms OnBytes.Tie.Pv.rowTie_of_tie
