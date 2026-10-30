-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneAt.lean.
The three claims of the byte-level verifier that read the planes of the counts are the flat
function's three rows on the planes.

A run of `Forest.planeClaims` (OnBytes/Model/Look.lean) makes three forms from the record g that the
lookup's routine has left. This file states that, where g holds what the flat function computes from
a trace t at the forest's numbers, their values are the residues of the rows `TwV.rowEnd`,
`TwV.rowBitE` and `TwV.rowNum`, the second with the opposite sign.

Main names:
  `onMasks_hide`, `onMasks_incTop`: the form of a hiding polynomial and the form with which the
    leaves' sumcheck is entered name entries of the mask row alone. `onMasks_hide` asks that the
    ledger's places are entries of the mask row.
  `planesK_congr`, `countK_congr`: the planes' value and the sum of the counts read the columns
    below NC * 2 ^ (kT + 5 - lm) alone.
  `planeClaims_at`: in every later state, at all entries μ that read the place that is no cell as 0,
    if the caller's forms for the columns below NC * 2 ^ (kT + 5 - lm) are worth the columns' sums
    (`colsK` at the two points,
    `pinColK`), then the three forms are worth rowRes μ (rowEnd ..), - rowRes μ (rowBitE ..) and
    rowRes μ (rowNum ..).

Under: the shape is lawful (`FoNums.ok`); the caller's routines are quiet; the state's arrays have
their sizes; and what the record g holds, each a hypothesis by name: the leaves' sumcheck is in the
state `Ran` from the ledger's slot on, with the flat function's degrees; the form with which it was
entered is read by `FormIs` in an earlier state, and its target reads as that form's public part;
its factor, last value and challenges, the factor leavesA and the two
points are the trace's; under the slot g.sBit stands the value that the bits' sumcheck has shown
(`FormIs`, in an earlier state).

Limits: that the record of a run holds these is not stated here. That the caller's forms are worth
  the columns' sums is the caller's to state.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRead
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false

namespace Cb.Fo.PlaneClaims
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K]

omit [CommRing K] in
theorem onMasks_append {a b : List (Pl × K)} (ha : OnMasks a) (hb : OnMasks b) :
    OnMasks (a ++ b) := fun pc h =>
  (List.mem_append.mp h).elim (ha pc) (hb pc)

theorem onMasks_scale {a : List (Pl × K)} (u : K) (ha : OnMasks a) : OnMasks (scale u a) := by
  intro pc h
  unfold scale at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact ha q hq

theorem onMasks_hideGo (pw : ℕ → ℕ → Pl) (hp : ∀ r t, ∃ j, pw r t = Pl.mask j) :
    ∀ (dg : List ℕ) (xs : List K) (r : ℕ), OnMasks (hideGo pw r dg xs)
  | [], _, _ => by
    intro pc h
    simp [hideGo] at h
  | _ :: _, [], _ => by
    intro pc h
    simp [hideGo] at h
  | n :: dg, x :: xs, r => by
    show OnMasks (((List.range n).map fun t => (pw r t, x ^ (t + 1))) ++ hideGo pw (r + 1) dg xs)
    refine onMasks_append (fun pc h => ?_) (onMasks_hideGo pw hp dg xs (r + 1))
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact hp r t

theorem onMasks_hide (L : Led Pl) (hp : ∀ r t, ∃ j, L.pw r t = Pl.mask j)
    (hc : ∃ j, L.c0 = Pl.mask j) (dg : List ℕ) (xs : List K) : OnMasks (hide L dg xs) := by
  unfold hide
  refine onMasks_append (onMasks_hideGo _ hp dg xs 0) fun pc h => ?_
  rw [List.mem_singleton.mp h]
  exact hc

theorem onMasks_incTop (h : Forest.Shape) (lm jLK : ℕ) (θ : K) (t : Trace K) :
    OnMasks (incTop (numsF h lm jLK θ).ledT (incT0 (numsF h lm jLK θ) t) t.tabl.reverse) := by
  cases t.tabl.reverse with
  | nil =>
    show OnMasks (incT0 (numsF h lm jLK θ) t)
    intro pc hpc
    unfold incT0 at hpc
    obtain ⟨th, _, h2⟩ := List.mem_flatMap.mp hpc
    refine onMasks_scale _ (fun q hq => ?_) pc h2
    unfold formT at hq
    split_ifs at hq
    · rw [List.mem_singleton.mp hq]
      exact ⟨_, rfl⟩
    · rw [List.mem_singleton.mp hq]
      exact ⟨_, rfl⟩
    · exact absurd hq List.not_mem_nil
  | cons s rest =>
    intro pc hpc
    have : pc ∈ lineForm ((numsF h lm jLK θ).ledT rest.length) s.1 s.2 := hpc
    unfold lineForm at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem foldl_congr_mem {α σ : Type} (f g : σ → α → σ) : ∀ (l : List α) (s : σ),
    (∀ x ∈ l, ∀ s, f s x = g s x) → l.foldl f s = l.foldl g s
  | [], _, _ => rfl
  | a :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self s]
    exact foldl_congr_mem f g l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The planes' value reads the columns below NC * 2 ^ (kT + 5 - lm) alone. -/
theorem planesK_congr (h : Forest.Shape) (lm : ℕ) (z : List K) (b b' : ℕ → K)
    (hb : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → b col = b' col) :
    planesK h lm z b = planesK h lm z b' := by
  unfold planesK
  exact foldl_congr_mem _ _ _ _ fun col hc s => by rw [hb col (List.mem_range.mp hc)]

/-- So does the sum of the counts. -/
theorem countK_congr (h : Forest.Shape) (lm : ℕ) (p p' : ℕ → K)
    (hp : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → p col = p' col) :
    Pin.countK h lm p = Pin.countK h lm p' := by
  unfold Pin.countK
  exact foldl_congr_mem _ _ _ _ fun col hc s => by rw [hp col (List.mem_range.mp hc)]

variable (ρ : OnBytes.Model.Reading K)

theorem planeClaims_at (g : Heard) (lm jLK : ℕ) (θ : K) (t : Trace K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F1 F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c'))
    (hok : FoNums.ok g.shape = true) (h0 : Later F0 F) (h1 : Later F1 F) (hF : Sized F)
    {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hRan : Ran g.leaves (jLK + (FoNums.S g.shape).fEnd) mu eps zd rs)
    (hdg : dgOf zd = dgE (numsF g.shape lm jLK θ)) {tg : K}
    (hC : FormIs ρ F0 g.leaves.start tg
      (incTop (numsF g.shape lm jLK θ).ledT (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse))
    (ht : ρ.val g.leaves.target = tg)
    (hEps : ρ.val g.leaves.eps = t.cls.eps) (hFin : ρ.val g.leaves.claim = t.cls.fin)
    (hXs : g.leaves.r.toList.map ρ.val = t.cls.xs)
    (hA : ρ.val g.leavesA = ((List.range (2 ^ g.shape.d)).map fun r =>
      eqN ((byVar (FoNums.ordE g.shape) t.cls.xs).drop FoNums.w) r *
        (t.lam - 1 - tabF g.shape θ r)).sum)
    (hz0 : rdL ρ g.zb0 = (byVar (FoNums.ordE g.shape) t.cls.xs).reverse)
    (hz1 : rdL ρ g.zb1 = (byVar (FoNums.ordB g.shape) t.bits.xs).reverse)
    (hBit : FormIs ρ F1 (Aff.slot g.sBit) (t.bits.v 0)
      [((numsF g.shape lm jLK θ).ledB.sh 0, t.bits.be)]) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (μ : Pl → K) (entry : ℕ → ℕ → ℕ → K), μ .zero = 0 →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (pin col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            Pin.pinColK lm μ col) →
          r0.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowEnd (numsF g.shape lm jLK θ) t) ∧
          r1.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              -rowRes μ (rowBitE (numsF g.shape lm jLK θ) t) ∧
          r2.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowNum (numsF g.shape lm jLK θ)) := by
  have hsc : dgE (numsF g.shape lm jLK θ) = (FoNums.S g.shape).scEnd.degs :=
    (nums_led g.shape jLK lm θ).2.2.2.2.2.2
  have hL : LedAt (ledF jLK (FoNums.S g.shape).pEndC) (jLK + (FoNums.S g.shape).fEnd)
      (dgOf zd) 0 := by
    rw [hdg, hsc]
    exact ledAt_end g.shape jLK
  have hv : g.shape.v < 64 := lt_trans (Cb.Fo.ok_parts hok).1.2.2.2.2.1 (by decide)
  obtain ⟨hm, a1, a2, a3, a4, r0, r1, r2, hr, hval⟩ :=
    planeClaims_rows ρ g lm bit pin hb hp F0 F G c c' rows h hRan hC ht h0 hF hL hv []
  have hlm : 5 ≤ lm ∧ lm ≤ g.shape.kT + 5 := by
    unfold planeCols at hm
    by_contra hc
    have : (lm < 5 || lm > g.shape.kT + 5) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    rw [if_pos this] at hm
    exact absurd hm (by decide)
  refine ⟨a1, a2, a3, a4, r0, r1, r2, hr, fun H hH μ entry hz hB0 hB1 hP => ?_⟩
  obtain ⟨v0, v1, v2⟩ := hval H hH (fun j => μ (.mask j)) entry
  have hE : ρ.val eps = t.cls.eps := by
    rw [← hRan.eps_eq]
    exact hEps
  refine ⟨?_, ?_, ?_⟩
  · have hM : OnMasks (hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK θ))
        t.cls.xs ++ scale t.cls.eps (incTop (numsF g.shape lm jLK θ).ledT
          (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse)) :=
      onMasks_append (onMasks_hide _ (fun _ _ => ⟨_, rfl⟩) ⟨_, rfl⟩ _ _)
        (onMasks_scale _ (onMasks_incTop g.shape lm jLK θ t))
    have hP0 : evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordE g.shape) t.cls.xs)) =
        planesK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse
          (colsK g.shape lm (byVar (FoNums.ordE g.shape) t.cls.xs).reverse μ) :=
      plane_sum_g g.shape hok lm jLK hlm.1 hlm.2 θ μ hz _ (by rw [byVar_len, ordE_len])
    have hR : rowRes μ (rowEnd (numsF g.shape lm jLK θ) t) =
        evalL μ (hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK θ)) t.cls.xs ++
          scale t.cls.eps (incTop (numsF g.shape lm jLK θ).ledT
            (incT0 (numsF g.shape lm jLK θ) t) t.tabl.reverse)) +
          t.cls.eps * ((List.range (2 ^ g.shape.d)).map fun r =>
            eqN ((byVar (FoNums.ordE g.shape) t.cls.xs).drop FoNums.w) r *
              (t.lam - 1 - tabF g.shape θ r)).sum *
            evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordE g.shape) t.cls.xs)) -
          (t.cls.fin - t.cls.eps * 1) := by
      show evalL μ (_ ++ scale _ _) - _ = _
      rw [evalL_append, evalL_scale]
      rfl
    rw [v0, planesK_congr g.shape lm _ _ _ hB0, hdg, hEps, hFin, hXs, hE, hA, hz0, hR, hP0]
    unfold rowRes rowU
    simp only
    rw [evalL_muOf hM μ]
    ring
  · have hP1 : evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordB g.shape) t.bits.xs)) =
        planesK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse
          (colsK g.shape lm (byVar (FoNums.ordB g.shape) t.bits.xs).reverse μ) :=
      plane_sum_g g.shape hok lm jLK hlm.1 hlm.2 θ μ hz _ (by rw [byVar_len, ordB_len])
    have hS := (hBit H ((h1.trans a2).trans hH)).2 (fun j => μ (.mask j)) entry
    rw [Aff.value_slot, evalL_muOf (fun pc hpc => by
      rw [List.mem_singleton.mp hpc]
      exact ⟨_, rfl⟩) μ] at hS
    have hR : rowRes μ (rowBitE (numsF g.shape lm jLK θ) t) =
        evalL μ (bitsForm (numsF g.shape lm jLK θ) (byVar (FoNums.ordB g.shape) t.bits.xs)) +
          evalL μ [((numsF g.shape lm jLK θ).ledB.sh 0, t.bits.be)] - t.bits.v 0 := by
      show evalL μ (_ ++ _) - _ = _
      rw [evalL_append]
      rfl
    rw [v1, planesK_congr g.shape lm _ _ _ hB1, hS, hz1, hR, hP1]
    ring
  · rw [v2, countK_congr g.shape lm _ _ hP]
    unfold rowRes Pin.countK
    rw [Pin.foldl_add_from, show evalL μ (rowNum (numsF g.shape lm jLK θ)).cf = _ from
      Pin.pin_sum g.shape lm jLK θ μ hz (Cb.Fo.ok_parts hok).1.2.2.1 hlm.1 hlm.2,
      PadFac.pin_target g.shape hok]
    ring

end
end Cb.Fo.PlaneClaims
