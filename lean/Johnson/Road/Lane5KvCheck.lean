-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvCheck.lean

The three public premises of the bridge at attention as tests that a program can run, each with its
theorem: if the test says true, the premise holds. So a run (#guard) is a witness of the premise
itself, not of a text that only resembles it. The verifier runs none of these tests: it admits
configurations with another call list or several shifts in a group; there the premises fail and
these files say nothing.

Main definitions and theorems:
* "numsB S", "numsA_of_numsB": NumsA S (Lane5KvKey.lean).
* "callAt S q", "famB", "laidB S", "laidA_of_laidB": LaidA S (fun q => callAt S q)
  (Lane5KvVec.lean).
* "tabsB S fs", "tabsA_of_tabsB": TabsA S fs (Lane5BridgeA.lean). The test compares integers, row u
  with row u: more than the premise asks.
* **"attBridge_of_tests"**: the three tests give AttBridge S Z (callsA S fs Z), for every Z.

The runs: Lane5KvWit.lean.
-/
import Johnson.Road.Lane5BridgeA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Shape Seg ACall)
open Inst.Model.AttSeg

/-! ## The numbers -/

/-- NumsA, line by line. -/
def numsB (S : Shape) : Bool :=
  S.B == (dimOf S).B && S.nT == (dimOf S).nBlk && S.hP == (dimOf S).hP && S.G == (dimOf S).nG &&
    S.T == (dimOf S).T && S.dh == (dimOf S).ch && S.cf.lt == (dimOf S).lT && S.atQ.nl == 2 &&
    S.atK.nl == 2 && S.atV.nl == 2 && S.atO.nl == 2 && ((S.Smax : ℕ) : ℤ) == Inst.Model.Smax

theorem numsA_of_numsB {S : Shape} (h : numsB S = true) : NumsA S := by
  simp only [numsB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## How the calls are laid -/

/-- Call number q. -/
def callAt (S : Shape) (q : ℕ) : ACall := S.calls.getD q default

/-- A family of pieces lies in call q where LaidA says. -/
def famB (S : Shape) (q : ℕ) (s : Seg) (l base : ℕ) : Bool :=
  (List.range (dimOf S).nb).all fun b => decide (pcAt S s l base b ∈ (callAt S q).pcs.toList)

theorem fam_of_famB {S : Shape} {q : ℕ} {s : Seg} {l base : ℕ} (h : famB S q s l base = true) :
    ∀ b < (dimOf S).nb, pcAt S s l base b ∈ (callAt S q).pcs.toList := by
  intro b hb
  simp only [famB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h b hb

/-- LaidA, line by line. -/
def laidB (S : Shape) : Bool :=
  decide (S.calls.size = 4) &&
    ((List.range 4).all fun q => decide ((callAt S q).pcs.toList.Pairwise fun p r =>
      p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off)) &&
    decide ((callAt S 1).sh = S.cf.sh.getD 0 0) &&
    famB S 0 .rm (dimOf S).lM 0 && famB S 0 .rd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) &&
    famB S 1 .fm (dimOf S).lM 0 && famB S 1 .fd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) &&
    famB S 2 .wl (dimOf S).lW 0 && famB S 2 .ix (dimOf S).lX ((dimOf S).nb * 2 ^ (dimOf S).lW) &&
    famB S 3 .wh (dimOf S).l4 0

theorem laidA_of_laidB {S : Shape} (h : laidB S = true) :
    LaidA S fun q : Fin 4 => callAt S q.val := by
  simp only [laidB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hap⟩, hsh⟩, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩ := h
  refine ⟨?_, fun q => hap q.val q.isLt, hsh, fam_of_famB f1, fam_of_famB f2, fam_of_famB f3,
    fam_of_famB f4, fam_of_famB f5, fam_of_famB f6, fam_of_famB f7⟩
  intro q
  have hq : q.val < S.calls.size := by rw [hs]; exact q.isLt
  unfold callAt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq]
  rfl

/-! ## The tables -/

/-- TabsA: with the library's row u for the verifier's row u; between integers. -/
def tabsB (S : Shape) (fs : Model.Forest.Shape) : Bool :=
  (List.finRange 4).all fun c =>
    decide ((lut (scl := sclOf S) (dimOf S) (tbOf S) c).rows = 2 ^ kN fs c.val) &&
      ((List.range (2 ^ kN fs c.val)).all fun u =>
        decide (((tauN fs c.val u : ℕ) : ℤ) = (lut (scl := sclOf S) (dimOf S) (tbOf S) c).row u)) &&
      decide ((dimOf S).used c ≤ 2 ^ (callAt S c.val).call.n)

theorem tabsA_of_tabsB {S : Shape} {fs : Model.Forest.Shape} (h : tabsB S fs = true) :
    TabsA S fs := by
  simp only [tabsB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at h
  refine ⟨fun c u hu => ?_, fun c => (h c (List.mem_finRange c)).2⟩
  obtain ⟨⟨hr, hrow⟩, -⟩ := h c (List.mem_finRange c)
  refine ⟨u, by rw [hr]; exact hu, ?_⟩
  rw [← hrow u hu, Int.cast_natCast]

/-! ## The bridge from the three tests -/

/-- **The three tests give the bridge at attention.** -/
theorem attBridge_of_tests {S : Shape} {fs : Model.Forest.Shape} (h1 : numsB S = true)
    (h2 : laidB S = true) (h3 : tabsB S fs = true) (Z : Zs) : AttBridge S Z (callsA S fs Z) :=
  attBridge (numsA_of_numsB h1) (laidA_of_laidB h2) (tabsA_of_tabsB h3) Z

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.numsA_of_numsB
#print axioms OnBytes.Road.L5.laidA_of_laidB
#print axioms OnBytes.Road.L5.tabsA_of_tabsB
#print axioms OnBytes.Road.L5.attBridge_of_tests
