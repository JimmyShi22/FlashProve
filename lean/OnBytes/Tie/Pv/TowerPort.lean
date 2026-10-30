-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/TowerPort.lean: the rounds of a proximity test's stages (fold, code switch,
last step) as the planner adds them, against counts in the form of the proof library's blocks.

The planner's lists are `foldList`, `csList`, `baseList` (OnBytes/Params/PlanListsProx.lean). The
library's blocks have the errors `SumPar.err` (Cb/Ld/LdSum.lean), `LdSwW.err1`, `LdSwW.err2`
(Cb/Ld/LdSwitchWords.lean) and, for the last step, bad + L2 and (n - e - 1) ^ t. Every statement
here is on numbers: a pair (bad values, values) is covered by the planned round (`Cb.Pv.Covered`,
OnBytes/Tie/Pv/PortKit.lean). No block is imported. Statements with their proofs.
Main names:
  `valuesP q y`: the values of the verifier's message of y, drawn positions counted too.
  `runs_fold'`, `runs_cs'`, `runs_base'`: the planner's routines add the three lists.
  `fold_first_covered`: "FOLD epsilon" covers L of q, for L up to the library's bound on the list.
  `foldCount g e j`, `fold_round_covered`: "FOLD round" number j covers c of q, for c up to that
    count.
  `fold_row_le`: the error of round i of `SumPar.err` is at most `foldCount g e (i + 1)`, if its
    four numbers are at most the library's bounds and the degree is 2.
  `forall₂_foldFrom`: a relation that holds round by round holds of the planner's list of rounds.
  `seed_covered`: "SEND seed" for one message covers c of n, in the numbers of a sample.
  `csRound`, `csList_eq`, `cs_covered`: "CS" covers (n - e - 1) ^ t * q + n ^ t * (L * (rows - 1))
    of n ^ t * q: the form of `err2` at the powers of one element.
  `baseFirst`, `baseLast`, `baseList_eq`, `baseSum`, `base_first_covered`, `base_last_covered`:
    "BASE lambda" covers c of q for c up to `baseSum`; "BASE" covers (n - e - 1) ^ t of n ^ t.
Limits: inequalities, under the conditions `JohnsonGroup` (OnBytes/Params/GroupPrices.lean) on a
group with a mask whose main code rules, and a radius from the upper radius on for the draws of
positions. Groups of the two other kinds are not treated.
The scope is `.once`. That a price is not marked bad is a hypothesis. That the counts of a given
block are at most the library's bounds is a hypothesis. Bytes and roots are not compared.

-/
import OnBytes.Tie.Pv.PortKit
import OnBytes.Params.PlanListsProx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open OnBytes OnBytes.Params

/-- The values of the verifier's message, drawn positions counted too. -/
def valuesP (q : ℕ) : RoundSpec → ℕ
  | .said n w e d b r a => valuesOf q (.said n w e d b r a) * (2 ^ d.logN) ^ d.poss
  | y => valuesOf q y

section Runs
variable (s : Setting) (c : Scope)

theorem runs_fold' (g : GroupSize) (roots : ℕ) :
    Runs s c 0 0 0 (planFold g roots) () (foldList s g roots) 0 0 0 := runs_fold g roots

theorem runs_cs' (source target : GroupSize) (cubeBits oldRows symbols roots : ℕ) :
    Runs s c 0 0 0 (planCs source target cubeBits oldRows symbols roots)
      (csCount s c source target oldRows symbols)
      (csList s c source target cubeBits oldRows symbols roots) 0 0 0 :=
  runs_cs source target cubeBits oldRows symbols roots

theorem runs_base' (g : GroupSize) (roots : ℕ) :
    Runs s c 0 0 0 (planBase g roots) (baseCount s c g) (baseList s c g roots) 0 0 0 :=
  runs_base g roots

end Runs

/-- The length of a group's main code; the library's bounds on its lists. -/
abbrev lenOf (g : GroupSize) : ℕ := (wordOf g.main).n
abbrev listMain (g : GroupSize) (e : ℕ) : ℕ :=
  Cb.listMax (lenOf g) (lenOf g - (wordOf g.main).k) e
abbrev listMask (g : GroupSize) (e : ℕ) : ℕ :=
  Cb.listMax (lenOf g) (lenOf g - (repeated g.mask g.main.logN).k) e

variable {s : Setting} {g : GroupSize} {e : ℕ}

/-! ### the fold -/

theorem fold_first_values (roots : ℕ) : valuesOf s.cardE (foldFirst s g roots) = s.cardE := by
  simp [valuesOf, foldFirst]

theorem fold_round_values (a : Analysis) (j : ℕ) :
    valuesOf s.cardE (foldRound s g a j) = s.cardE := by
  simp [valuesOf, foldRound]

/-- "FOLD epsilon". -/
theorem fold_first_covered (J : JohnsonGroup s g e) (roots L : ℕ) (hL : L ≤ listMain g e)
    (gd : (Bound.ofNat (analysisOfM s g).list * fieldError s 1).bad = false) :
    Covered s .once (L, s.cardE) (foldFirst s g roots) := by
  unfold Covered foldFirst
  rw [(round_once s _ _ _ _ _ _ _).1, J.analysis_eq]
  have h := list_field_covers s 1 (hL.trans (listMax_le_group J)) gd
  simpa using h

/-- The count that the price of round j of a fold covers. -/
noncomputable def foldCount (g : GroupSize) (e j : ℕ) : ℕ :=
  ⌊Cb.bchksBound (lenOf g) (wordOf g.main).k e⌋₊ + listMain g e * 2 +
    (if (g.hasMask && decide (j ≤ g.h)) = true then
      2 * (⌊Cb.bchksBound (lenOf g) (repeated g.mask g.main.logN).k e⌋₊ + listMask g e) else 0)

/-- "FOLD round" number j. -/
theorem fold_round_covered (J : JohnsonGroup s g e) (j c : ℕ) (hc : c ≤ foldCount g e j)
    (gd : (foldRoundError s g (analysisOfM s g) j).bad = false) :
    Covered s .once (c, s.cardE) (foldRound s g (analysis s g) j) := by
  unfold Covered foldRound
  rw [(round_once s _ _ _ _ _ _ _).1, J.analysis_eq]
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _))
    (fold_covers_floor J j gd)

/-- The error of round i of the library's fold is at most the count of round i + 1. -/
theorem fold_row_le (n h i : ℕ) (Lst mC mS mW : ℕ → ℕ) (hn : n = 2) (hh : h = g.h)
    (hm : g.hasMask = true) (hC : mC (i + 1) ≤ ⌊Cb.bchksBound (lenOf g) (wordOf g.main).k e⌋₊)
    (hL : Lst i ≤ listMain g e)
    (hM : mS (i + 1) + mW (i + 1) ≤
      2 * (⌊Cb.bchksBound (lenOf g) (repeated g.mask g.main.logN).k e⌋₊ + listMask g e)) :
    mC (i + 1) + (if i + 1 ≤ h then mS (i + 1) + mW (i + 1) else 0) + Lst i * n ≤
      foldCount g e (i + 1) := by
  subst hn hh
  unfold foldCount
  by_cases hi : i + 1 ≤ g.h
  · simp only [hm, hi, decide_true, Bool.and_self, if_true]
    omega
  · simp only [hm, hi, decide_false, Bool.and_false, if_false, Bool.false_eq_true]
    omega

/-- A relation that holds round by round holds of the planner's list. -/
theorem forall₂_foldFrom {a : Analysis} {R : ℕ × ℕ → RoundSpec → Prop} (c : ℕ → ℕ × ℕ) :
    ∀ fuel j : ℕ, (∀ i, i < fuel → R (c (j + i)) (foldRound s g a (j + i))) →
      List.Forall₂ R ((List.range fuel).map fun i => c (j + i)) (foldFromList s g a fuel j)
  | 0, _, _ => .nil
  | fuel + 1, j, h => by
    have h0 := h 0 (Nat.succ_pos _)
    have ih := forall₂_foldFrom c fuel (j + 1) fun i hi => by
      have := h (i + 1) (Nat.succ_lt_succ hi)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, foldFromList]
    refine .cons h0 ?_
    have e' : ((fun i => c (j + i)) ∘ Nat.succ) = fun i => c (j + 1 + i) := by
      funext i
      show c (j + (i + 1)) = c (j + 1 + i)
      rw [show j + (i + 1) = j + 1 + i by omega]
    rw [e']
    exact ih

/-! ### the code switch -/

theorem one_le_largestList (σ : Setting) : ∀ gs : List GroupSize, 1 ≤ largestList σ gs
  | [] => le_rfl
  | _ :: gs => le_trans (one_le_largestList σ gs) (le_max_right _ _)

/-- "SEND seed" for one message, in the numbers of a sample. -/
theorem seed_covered (x : SampleSize) (roots L c n : ℕ) (hq : 2 ≤ s.cardE)
    (hL : L ≤ largestList s x.groups) (hn : n = allSeeds s.cardE x.cubeBits ^ s.samples)
    (hc : c ≤ L.choose 2 * clashSeeds s.cardE x.cubeBits ^ s.samples)
    (gd : (sampleSum s [x] (Bound.ofWord 0)).bad = false) :
    Covered s .once (c, n) (sendSeed s [x] roots) := by
  subst hn
  unfold Covered sendSeed
  rw [(round_once s _ _ _ _ _ _ _).1]
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _))
    (send_one_covers s hq hL (one_le_largestList s x.groups) gd)

/-- The second round of a code switch. -/
def csRound (s : Setting) (c : Scope) (source target : GroupSize) (oldRows symbols : ℕ) :
    RoundSpec :=
  .said "CS" .query
    (Bound.pow (analysis s source).mainAt.agree (csCount s c source target oldRows symbols) +
      Bound.ofNat (analysis s target).list *
        powersError s (oldRows + s.samples + symbols * csCount s c source target oldRows symbols))
    { poss := csCount s c source target oldRows symbols, logN := source.main.logN, drawE := 1,
      rows := oldRows + s.samples + symbols * csCount s c source target oldRows symbols,
      group := pricedOf source, priced := .callersWord }
    (24 * (s.samples * 1)) 0 (s.samples * 1)

theorem csList_eq (c : Scope) (source target : GroupSize) (cubeBits oldRows symbols roots : ℕ) :
    csList s c source target cubeBits oldRows symbols roots =
      [sendSeed s [⟨cubeBits, [target]⟩] roots, csRound s c source target oldRows symbols] := rfl

theorem cs_values (c : Scope) (source target : GroupSize) (oldRows symbols : ℕ) :
    valuesP s.cardE (csRound s c source target oldRows symbols) =
      s.cardE * lenOf source ^ csCount s c source target oldRows symbols := by
  simp [valuesP, valuesOf, csRound, lenOf, Word.n, wordOf]

/-- A share in the form of the library's second error of a code switch. -/
theorem share_split (N A t q L r : ℕ) (hN : 0 < N) (hq : 0 < q) :
    (((A ^ t * q + N ^ t * (L * r) : ℕ) : ℝ)) / ((N ^ t * q : ℕ) : ℝ) =
      ((A : ℝ) / (N : ℝ)) ^ t + (L : ℝ) * (r : ℝ) / (q : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  rw [div_pow]
  field_simp

/-- "CS". -/
theorem cs_covered {g' : GroupSize} {e' : ℕ} (J : JohnsonGroup s g e) (J' : JohnsonGroup s g' e')
    (gp : ((analysisOfM s g).mainAt.delta * Bound.ofNat (lenOf g)).bad = false)
    (hu : upperRadius (analysisOfM s g).mainAt.delta (lenOf g) ≤ e) (oldRows symbols L : ℕ)
    (hq : 0 < s.cardE) (hL : L ≤ listMain g' e')
    (gd : (Bound.pow (analysisOfM s g).mainAt.agree (csCount s .once g g' oldRows symbols) +
      Bound.ofNat (analysisOfM s g').list *
        powersError s
          (oldRows + s.samples + symbols * csCount s .once g g' oldRows symbols)).bad = false) :
    Covered s .once
      ((lenOf g - e - 1) ^ csCount s .once g g' oldRows symbols * s.cardE +
          lenOf g ^ csCount s .once g g' oldRows symbols *
            (L * (oldRows + s.samples + symbols * csCount s .once g g' oldRows symbols - 1)),
        lenOf g ^ csCount s .once g g' oldRows symbols * s.cardE)
      (csRound s .once g g' oldRows symbols) := by
  have hN : 0 < lenOf g := by
    unfold lenOf Word.n
    positivity
  unfold Covered csRound
  rw [(round_once s _ _ _ _ _ _ _).1, J.analysis_eq, J'.analysis_eq]
  refine le_trans (le_of_eq (share_split _ _ _ _ _ _ hN hq)) ?_
  refine le_trans ?_ (group_switch_covers J J' gp hu _ _ gd)
  have hL' : (L : ℝ) ≤ (listMain g' e' : ℝ) := by exact_mod_cast hL
  gcongr

/-! ### the last step -/

def baseFirst (s : Setting) (g : GroupSize) (roots : ℕ) : RoundSpec :=
  .said "BASE lambda" .closeness (baseError s g (analysis s g))
    { drawE := 1, group := pricedOf g, rests := weakestSource (analysis s g), priced := .asSaid }
    (32 * roots + 24 * 1) roots 0

def baseLast (s : Setting) (c : Scope) (g : GroupSize) : RoundSpec :=
  .said "BASE" .query (Bound.pow (analysis s g).mainAt.agree (baseCount s c g))
    { poss := baseCount s c g, logN := g.main.logN, group := pricedOf g, priced := .asSaid }
    (24 * (g.main.dim * g.slots + (if g.hasMask then g.mask.dim else 0))) 0 0

theorem baseList_eq (c : Scope) (roots : ℕ) :
    baseList s c g roots = [baseFirst s g roots, baseLast s c g] := rfl

/-- The count that the price of "BASE lambda" covers. -/
noncomputable def baseSum (g : GroupSize) (e : ℕ) : ℕ :=
  ⌊Cb.bchksBound (lenOf g) (wordOf g.main).k e⌋₊ + listMain g e +
    (⌊Cb.bchksBound (lenOf g) (repeated g.mask g.main.logN).k e⌋₊ + listMask g e)

/-- "BASE lambda". -/
theorem base_first_covered (J : JohnsonGroup s g e) (roots c : ℕ) (hc : c ≤ baseSum g e)
    (gd : (baseError s g (analysisOfM s g)).bad = false) :
    Covered s .once (c, s.cardE) (baseFirst s g roots) := by
  unfold Covered baseFirst
  rw [(round_once s _ _ _ _ _ _ _).1, J.analysis_eq]
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _))
    (base_covers_floor J gd)

/-- "BASE". -/
theorem base_last_covered (J : JohnsonGroup s g e)
    (gp : ((analysisOfM s g).mainAt.delta * Bound.ofNat (lenOf g)).bad = false)
    (hu : upperRadius (analysisOfM s g).mainAt.delta (lenOf g) ≤ e)
    (gd : (Bound.pow (analysisOfM s g).mainAt.agree (baseCount s .once g)).bad = false) :
    Covered s .once
      ((lenOf g - e - 1) ^ baseCount s .once g, lenOf g ^ baseCount s .once g)
      (baseLast s .once g) := by
  unfold Covered baseLast
  rw [(round_once s _ _ _ _ _ _ _).1, J.analysis_eq]
  have h := group_positions_cover J gp hu (baseCount s .once g) gd
  rw [div_pow] at h
  exact_mod_cast h

theorem base_values (c : Scope) :
    valuesP s.cardE (baseLast s c g) = lenOf g ^ baseCount s c g := by
  simp [valuesP, valuesOf, baseLast, lenOf, Word.n, wordOf]

end Cb.Pv.Tower

#print axioms Cb.Pv.Tower.fold_first_covered
#print axioms Cb.Pv.Tower.fold_round_covered
#print axioms Cb.Pv.Tower.fold_row_le
#print axioms Cb.Pv.Tower.cs_covered
#print axioms Cb.Pv.Tower.base_first_covered
#print axioms Cb.Pv.Tower.base_last_covered
