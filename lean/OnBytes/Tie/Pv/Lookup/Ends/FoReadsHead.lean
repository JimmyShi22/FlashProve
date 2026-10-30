-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadsHead.lean.
The head sub-proof: the law of the reads at the three tables of its lookup's planes, from the law at
all its tables.

States:
  tab_bits0, tab_bits1, tab_pin: what the list of the head's fifteen asks makes holds the three
    tables of the planes' matrix, each of one part, with blocks of 2^lmbH rows and the weights
    asked.
  head_planeTabs: if a run of Head.tablesOf returns the tables t, and the lookup's record holds the
    flat function's end values (Fo.HeardIs), then the three tables are tables of the lookup's planes
    (Fo.PlaneTab, OnBytes/Tie/Pv/Lookup/Ends/FoReadsIn.lean) among t's list, at the first entries
      that Fo.headTab finds under
    their names, with the weights of the flat function's two points and the powers of two.
  head_readsLaw: so the law of the reads at all of t's tables (Fo.ReadsAll) gives Fo.ReadsLaw at
    these first entries.
Premises on public numbers: the planes' matrix has its rows in one block of 2^lmbH, and at least the
planes' columns. On the cells: the cells of the planes' matrix are the lookup's cells under ν.
Limit: Fo.ReadsAll is asked at ALL of t's tables; the list Fo.funsH, at which the head's key forms
ask it, leaves the planes' tables out (Fo.ReadsAll.filter gives that one from this one).
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsIn
import OnBytes.Tie.Pv.Lookup.Ends.FoHeadLookTied
import OnBytes.Tie.Pv.Lookup.Ends.FoTabsTied
import OnBytes.Tie.Pv.Lookup.Forest.FoPhi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun Cb.Fo

section
variable {h : Head.Shape} {L : Head.HL} {cov : Head.Covered} {x : Head.Heard} {ZV YN : Array E}
  {qFC qROW : ℕ} {b0 b1 : Array E} {mats : Array TMat} {t : Head.Tables}

theorem tab_bits0 (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "bH-bits-0" (h.NHf + 1 + 1) 1 (2 ^ h.lmbH) b0 :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 12) _
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b0, "bH-bits-0") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only; decide))

theorem tab_bits1 (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "bH-bits-1" (h.NHf + 1 + 1) 1 (2 ^ h.lmbH) b1 :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 13) _
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b1, "bH-bits-1") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only; decide))

theorem tab_pin (e : (asksH h L cov x ZV YN qFC qROW b0 b1).foldlM (askStep mats) {} = some t) :
    TabIs mats t "bH-pin" (h.NHf + 1 + 1) 1 (2 ^ h.lmbH) (Forest.phiP h.lmbH) :=
  asks_find mats ((asksH h L cov x ZV YN qFC qROW b0 b1).take 14) _
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, Forest.phiP h.lmbH, "bH-pin") {} t e
    (fun _ he => absurd he (by simp))
    (fun b hb => by
      simp only [asksH, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> (dsimp only; decide))

end

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A table of one part, found under its name, as a table of the planes. -/
theorem planeTab_of_tabIs {mats : Array TMat} {t : Head.Tables} {nm : String} {M0 lm : ℕ}
    {phi : Array E} (T : TabIs mats t nm M0 1 (2 ^ lm) phi) (cellM : ℕ → ℕ → ℕ → K) (w : ℕ → K)
    (h : FoNums.Sh) (ν : Pl → K) (h1 : (mats.getD M0 {}).m / 2 ^ lm = 1)
    (h2 : planeCols h lm ≤ (mats.getD M0 {}).k)
    (h3 : ∀ j < 2 ^ lm, ρ.val (phi.getD j zeroE) = w j)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols h lm, cellM M0 r c = ν (.cell r c)) :
    ∃ p0 f, ((t.tab.find? fun e => e.1 == nm).map (·.2.1)) = some p0 ∧
      PlaneTab ρ mats t.funs cellM f p0 w h lm ν := by
  obtain ⟨p0, len, e1, _, e3⟩ := T
  refine ⟨p0, partRec mats M0 (2 ^ lm) p0 phi 0, by rw [e1]; rfl, e3 0 (by norm_num), rfl, rfl, rfl,
    h1, h2, h3, h4⟩

/-- The three tables of the planes at the head. -/
theorem head_planeTabs (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (cov : Head.Covered) (x : Head.Heard) (iU3 : ℕ) (F G : Fork) (c c' : Ctx) (t : Head.Tables)
    (hh : Head.tablesOf s Y hp cov x F c = .ok ((t, G), c')) (F0 : Fork) (jLK : ℕ)
    (rsK : Rounds K) (hI : HeardIs ρ x.g1 F0 (endsOf x.g1.shape s.lmbH jLK rsK))
    (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (hp.tl.mats.getD (s.NHf + 1 + 1) {}).m / 2 ^ s.lmbH = 1)
    (h2 : planeCols x.g1.shape s.lmbH ≤ (hp.tl.mats.getD (s.NHf + 1 + 1) {}).k)
    (h4 : ∀ r < 2 ^ s.lmbH, ∀ c < planeCols x.g1.shape s.lmbH,
      cellM (s.NHf + 1 + 1) r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP f0 f1 fP,
      headTab (hRun s Y b hp cov x t iU3) "bH-bits-0" = some tB0 ∧
      headTab (hRun s Y b hp cov x t iU3) "bH-bits-1" = some tB1 ∧
      headTab (hRun s Y b hp cov x t iU3) "bH-pin" = some tP ∧
      PlaneTab ρ hp.tl.mats t.funs cellM f0 tB0
        (fun r => (phiBK x.g1.shape s.lmbH (endsOf x.g1.shape s.lmbH jLK rsK).zb0).getD r 0)
        x.g1.shape s.lmbH ν ∧
      PlaneTab ρ hp.tl.mats t.funs cellM f1 tB1
        (fun r => (phiBK x.g1.shape s.lmbH (endsOf x.g1.shape s.lmbH jLK rsK).zb1).getD r 0)
        x.g1.shape s.lmbH ν ∧
      PlaneTab ρ hp.tl.mats t.funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) x.g1.shape s.lmbH
        ν := by
  obtain ⟨_, _, _, _, _, ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, _, z3, z4, e⟩ :=
    tablesOf_tied s Y hp cov x F G c c' t hh
  have w0 : ∀ j < 2 ^ s.lmbH, ρ.val (b0.getD j zeroE) =
      (phiBK x.g1.shape s.lmbH (endsOf x.g1.shape s.lmbH jLK rsK).zb0).getD j 0 := fun j _ => by
    rw [rdL_getD, phiB_val ρ x.g1 s.lmbH 0 b0 z3, ← show rdL ρ x.g1.zb0 = _ from hI.zb0]
    rfl
  have w1 : ∀ j < 2 ^ s.lmbH, ρ.val (b1.getD j zeroE) =
      (phiBK x.g1.shape s.lmbH (endsOf x.g1.shape s.lmbH jLK rsK).zb1).getD j 0 := fun j _ => by
    rw [rdL_getD, phiB_val ρ x.g1 s.lmbH 1 b1 z4, ← show rdL ρ x.g1.zb1 = _ from hI.zb1]
    rfl
  obtain ⟨tB0, f0, a0, T0⟩ := planeTab_of_tabIs ρ (tab_bits0 e) cellM _ x.g1.shape ν h1 h2 w0 h4
  obtain ⟨tB1, f1, a1, T1⟩ := planeTab_of_tabIs ρ (tab_bits1 e) cellM _ x.g1.shape ν h1 h2 w1 h4
  obtain ⟨tP, fP, a2, TP⟩ := planeTab_of_tabIs ρ (tab_pin e) cellM _ x.g1.shape ν h1 h2
    (fun j hj => phiP_val ρ s.lmbH j hj) h4
  exact ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩

/-- The law of the reads at the planes' three tables of the head. -/
theorem head_readsLaw (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (cov : Head.Covered) (x : Head.Heard) (iU3 : ℕ) (F G : Fork) (c c' : Ctx) (t : Head.Tables)
    (hh : Head.tablesOf s Y hp cov x F c = .ok ((t, G), c')) (F0 : Fork) (jLK : ℕ)
    (rsK : Rounds K) (hI : HeardIs ρ x.g1 F0 (endsOf x.g1.shape s.lmbH jLK rsK))
    (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (hp.tl.mats.getD (s.NHf + 1 + 1) {}).m / 2 ^ s.lmbH = 1)
    (h2 : planeCols x.g1.shape s.lmbH ≤ (hp.tl.mats.getD (s.NHf + 1 + 1) {}).k)
    (h4 : ∀ r < 2 ^ s.lmbH, ∀ c < planeCols x.g1.shape s.lmbH,
      cellM (s.NHf + 1 + 1) r c = ν (.cell r c))
    (entry : ℕ → ℕ → ℕ → K) (K3 : ℕ) (hA : ReadsAll ρ hp.tl.mats t.funs entry iU3 K3 cellM)
    (tB0 tB1 tP : ℕ) (t0 : headTab (hRun s Y b hp cov x t iU3) "bH-bits-0" = some tB0)
    (t1 : headTab (hRun s Y b hp cov x t iU3) "bH-bits-1" = some tB1)
    (t2 : headTab (hRun s Y b hp cov x t iU3) "bH-pin" = some tP) :
    ReadsLaw x.g1.shape s.lmbH (endsOf x.g1.shape s.lmbH jLK rsK).zb0
      (endsOf x.g1.shape s.lmbH jLK rsK).zb1 ν entry iU3 K3 tB0 tB1 tP := by
  obtain ⟨tB0', tB1', tP', f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    head_planeTabs ρ s Y b hp cov x iU3 F G c c' t hh F0 jLK rsK hI cellM ν h1 h2 h4
  obtain rfl : tB0' = tB0 := Option.some.inj (a0.symm.trans t0)
  obtain rfl : tB1' = tB1 := Option.some.inj (a1.symm.trans t1)
  obtain rfl : tP' = tP := Option.some.inj (a2.symm.trans t2)
  exact readsLaw_of_readsAll ρ hA T0 T1 TP

end
end Fo
