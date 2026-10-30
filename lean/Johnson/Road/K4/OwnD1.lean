-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnD1.lean: (D1) OF A SUMCHECK'S OWN ROW: THE TYPED HIDING COEFFICIENTS ARE THE
WORLD's VALUES UNDER THE SUMCHECK's OWN SLOTS, in every ledger later than the one in which the text
has made the row. `SumSaid.row` (OnBytes/Tie/Pv/Lay/SumSaid.lean), `row_uForm`
(OnBytes/Desc/First/P1/RowForms.lean) and `stgT_row` (OwnRows.lean) have it as their premise (D1).
Statements and proofs.

  `hCount_pVars`: the number of coefficients of the hiding polynomial (`hCount`,
    OnBytes/Tie/Pv/SeamRun.lean) is 1 plus the sum of the formats' degrees.
  `hCount_cube`: at k variables of degree 2 and a further one of degree dY: 1 + 2 k + dY.
  `entries_three`: the text's number (`hidingEntries`, OnBytes/Iop/Psc.lean) at weights that all
  have three coefficients, and a further one with dY + 1: 1 + 2 (their number) + dY.
  `d1_of_run`: for every `PscPar` Y and state st: if a ledger F with arrays of the right sizes takes
    n zeros with the factor -1 under the slots from first on and becomes G, n is at least the number
    of coefficients, H is later than G, and the entry that serves as the coefficient q is the mask's
    entry at `slotP Y.fmt first q`: then `Y.W st m = place (H.worldOf gl (mask m) (entry m)).slot
    (Y.vars st) first`.
  `d1_of_ended`: the same for a record p that is `Ended` at weights of three coefficients, where the
    typed format is k variables of degree 2 and a further one of degree dY: n is the length of the
    record's walk, first is `p.first`: the `hideRun` equation is the one that `pscRow_spec`,
    `levelIn_heard` and `stack_heard` hand out.

NO NEW ARGUMENT: `hid_of`, `hw_of` (SeamRun.lean), `hideRun_ok`
(OnBytes/Tie/Pv/Psc/PscFork.lean), `Fo.Later.keep`.

Limits. PREMISES: `Sized F`; the `hideRun` equation; H later than G; hw: WHICH ENTRY SERVES AS WHICH
COEFFICIENT (at the value: `msg_wS` … `msg_w7`, Johnson/Road/K4/ValueMasks.lean, once the record's
first slot is the value's number). The merge's text makes no row of its own: its caller does.
Nothing on (D2) to (D4). Nothing on soundness.
-/
import OnBytes.Tie.Pv.SeamRun
import OnBytes.Tie.Pv.Psc.Run.PscSeam
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Desc.First.P1.RoundRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Cb OnBytes OnBytes.Model OnBytes.Road.Hd Johnson.L5.Layers
open OnBytes.Tie.Pv (hCount slotP slotNo hid_of hw_of)
open OnBytes.PscRun (Sized hideRun_ok)
open OnBytes.Model.Road (Ended)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.P1 (gl)
open OnBytes.Slice (GE)

theorem hCount_pVars {K : Type} : ∀ (l : List (PFmt K)) (d : PDats l),
    hCount (pVars l d) = 1 + (l.map (·.n)).sum
  | [], _ => rfl
  | f :: l, d => by
    show f.n + hCount (pVars l d.2) = _
    rw [hCount_pVars l d.2, List.map_cons, List.sum_cons]
    omega

theorem hCount_cube (k dY : ℕ) (d : PDats (List.replicate k (pfCube GE 2) ++ [pDummy GE dY])) :
    hCount (pVars _ d) = 1 + 2 * k + dY := by
  rw [hCount_pVars, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate]
  show 1 + (k • 2 + (dY + 0)) = _
  rw [smul_eq_mul]
  omega

theorem entries_three : ∀ (ws : List Weight) (dY : ℕ), (∀ w ∈ ws, w.d = 3) →
    OnBytes.Psc.hidingEntries (ws ++ [Weight.atZero (dY + 1)]) = 1 + 2 * ws.length + dY := by
  intro ws dY h
  have e : (ws.map fun w => w.d - 1).sum = 2 * ws.length := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      rw [List.map_cons, List.sum_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx),
        h w List.mem_cons_self, List.length_cons]
      omega
  unfold OnBytes.Psc.hidingEntries
  rw [List.map_append, List.sum_append, e]
  show 1 + (2 * ws.length + (dY + 1 - 1 + 0)) = _
  omega

/-- **(D1), from the run that lays zeros with the factor -1 under the sumcheck's own slots.** -/
theorem d1_of_run (Y : PscPar GE) (st : Y.St) {F G H : Fork} {first n : ℕ} (hF : Sized F)
    (hrow : F.hideRun first (Array.replicate n zeroE) (subE zeroE oneE) = some G)
    (hL : Fo.Later G H) (hn : hCount (Y.vars st) ≤ n) (mask : (Y.J → GE) → ℕ → GE)
    (entry : (Y.J → GE) → ℕ → ℕ → ℕ → GE)
    (hw : ∀ m q, m (Y.wAt q) = mask m (slotP Y.fmt first q)) (m : Y.J → GE) :
    Y.W st m = place (H.worldOf gl (mask m) (entry m)).slot (Y.vars st) first := by
  refine hid_of gl Y H mask entry st first (hw_of Y mask st first hw) (fun j h1 h2 => ?_) m
  obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by omega⟩
  have hi : i < (Array.replicate n zeroE).size := by
    rw [Array.size_replicate]
    omega
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first _ _ hF hrow
  obtain ⟨_, _, k3, k4, k5⟩ := hin i hi
  obtain ⟨_, g2, g3⟩ := hL.keep (first + i) k3
  have hz : (Array.replicate n zeroE).getD i zeroE = zeroE := by
    simp [Array.getD]
  refine ⟨?_, ?_⟩
  · rw [g2, k4, hz]
    exact gl.zero
  · rw [g3, k5, gl.sub, gl.zero, gl.one]
    ring

/-- **(D1) for a record that is `Ended`.** -/
theorem d1_of_ended (Y : PscPar GE) (st : Y.St) {p : Psc} {C : Aff} {τ mu eps : E} {first : ℕ}
    {ws : List Weight} {rs : List (List E × E)} {dY : ℕ} {sentY : List E} {beta : E}
    (a : Ended p C τ mu eps first ws rs dY sentY beta) (hd : ∀ w ∈ ws, w.d = 3)
    (hfmt : Y.fmt = List.replicate ws.length (pfCube GE 2) ++ [pDummy GE dY]) {F G H : Fork}
    (hF : Sized F)
    (hrow : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G)
    (hL : Fo.Later G H) (mask : (Y.J → GE) → ℕ → GE) (entry : (Y.J → GE) → ℕ → ℕ → ℕ → GE)
    (hw : ∀ m q, m (Y.wAt q) = mask m (slotP Y.fmt p.first q)) (m : Y.J → GE) :
    Y.W st m = place (H.worldOf gl (mask m) (entry m)).slot (Y.vars st) p.first := by
  refine d1_of_run Y st hF hrow hL ?_ mask entry hw m
  rw [a.walkLen, entries_three ws dY hd]
  show hCount (pVars Y.fmt (Y.dat st)) ≤ _
  rw [hCount_pVars, hfmt, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate]
  show 1 + (ws.length • 2 + (dY + 0)) ≤ _
  rw [smul_eq_mul]
  omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hCount_pVars
#print axioms OnBytes.Road.K4.entries_three
#print axioms OnBytes.Road.K4.d1_of_run
#print axioms OnBytes.Road.K4.d1_of_ended
