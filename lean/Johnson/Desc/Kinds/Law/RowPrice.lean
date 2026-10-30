-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowPrice.lean: THE OUTPUT HEAD's ONE RULE HAS A TIGHT CEILING BY THE ROUND's NUMBER: 1 at the round that draws the point (a coordinate), 8 and 6
at the two rounds that batch nine and seven hidden scalars, 1 at the first round of each of the four sumchecks, 2 at each of
their variables' rounds and the one behind these, 0 from the round of the end values on (the level's last round too): STATED
AND PROVED; and K6's row under the rule cut at that ceiling.
WHY. Law/RowK6.lean's ceiling is "the scalars that the round sends, and one": above what the plan's accounting gives a round.
The "and one" is our own (HeadLaw.lean's Lemma 2b's ceiling; Law/Bad.lean's cut): the masked sumcheck's law
(MaskedSumTruth.lean: sound_hear_true) has at most one bad eps and fewer bad challenges than a variable has coefficients.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE; whoever
may pick mask behind the draws makes every hidden scalar what they like. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
THAT THESE NUMBERS ARE THE PLAN's PRICES: no file of the plan's accounting is imported: the tie to its
list is other files' to show. No written challenge is counted; no sum of errors. All that Law/RowK6.lean does not say.
  tight3 m n       at a front of n rounds of a sumcheck on m coordinates: 1 · 2 · 0.
  bad_tight        the rule bad (Law/Bad.lean), at the masked sumcheck's law's own counts: at most tight3; behind the variables' rounds it
                   is empty (raw_behind, Law/NormTrue.lean).
  badG_tight · badP_tight · badLv_tight · normedRule_tight · productsRule_tight · squaresRule_tight · gamRule_le · omRule_le
  lvl, smc, tightAt   the level's and a short sumcheck's numbers of rounds; THE CEILING BY THE ROUND's NUMBER.
  norm_length      the normalization's hearing consumes just 3 + lvl + smc rounds.
  normRule_tight · blockRule_tight · rowRule_tight · rowRuleC_tight   AT EVERY FRONT (a WellLaid ledger; zt has lt coordinates).
  priceAt p j      the smaller of sentAt p j + 1 and tightAt j.   ruleK6T   ruleCutAt cut at priceAt.   ruleK6T_length.
  cut_takes_nothingT · RowPriceStatement · rowPrice   K6's row, general in the seat, under ruleK6T.
IMPORTED: Law/Bad.lean, Law/Lemma2b.lean; Law/NormRule.lean and what it rests on; the lookups' counts
cnt_BadG, cnt_BadO.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowK6
import Johnson.Desc.Kinds.Law.NormTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Sound (cutTo strikeLast)
open OnBytes.Model (Fork Reading World)
open Norm (lt ls d lPd S2 T)
open Polynomial
open OnBytes.Desc.First.P1 (dAt IsSum)
open Part.MaskedSum (Var Call)

/-! ## 1. The parts' rules -/

/-- At a front of n rounds of a sumcheck on m coordinates: 1 at its first round; 2 at its m rounds and the one behind them;
0 from the round of the end values on. -/
def tight3 (m n : Nat) : Nat := if n ≤ 1 then 1 else if n ≤ m + 2 then 2 else 0

theorem dAt_le3 (all : List Var) (hd : ∀ v ∈ all, v.d = 3) (i : Nat) :
    dAt (all.map (Var.wt Reading.gl)) i ≤ 3 := by
  unfold dAt
  cases h : (all.map (Var.wt Reading.gl))[i]? with
  | none => simp
  | some w =>
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
    simp only [Option.map_some, Option.getD_some]
    exact le_of_eq ((Var.wt_d Reading.gl v).trans (hd v hv))

theorem bad_tight (all : List Var) (cvOf : E → K) (bE : K → K → K → Finset K)
    (bd : K → K → K → K → List (K[X] × K) → K[X] → Finset K) (m : Nat) (hlen : all.length = m + 1)
    (hd3 : ∀ v ∈ all, v.d = 3) (hE : ∀ a b m, (bE a b m).card ≤ 1)
    (hD : ∀ a b m e pre g, (bd a b m e pre g).card < dAt (all.map (Var.wt Reading.gl)) pre.length)
    (h : List Fmt.RoundView) : (bad all cvOf bE bd h).length ≤ tight3 m h.length := by
  unfold bad
  refine le_trans (List.length_take_le' _ _) ?_
  match h with
  | [] =>
    show ([] : List E).length ≤ _
    exact Nat.zero_le _
  | [r0] =>
    have ht : tight3 m [r0].length = 1 := by
      unfold tight3
      exact if_pos (by simp)
    rw [ht]
    show (List.map ofK (Finset.toList _)).length ≤ 1
    rw [List.length_map, Finset.length_toList]
    exact hE _ _ _
  | r0 :: r1 :: tl =>
    by_cases hb : tl.length ≤ m
    · have ht : tight3 m (r0 :: r1 :: tl).length = 2 := by
        unfold tight3
        rw [if_neg (by simp only [List.length_cons]; omega),
          if_pos (by simp only [List.length_cons]; omega)]
      rw [ht]
      show (List.map ofK (Finset.toList _)).length ≤ 2
      rw [List.length_map, Finset.length_toList]
      exact Nat.le_of_lt_succ (lt_of_lt_of_le (hD _ _ _ _ _ _) (dAt_le3 all hd3 _))
    · rw [raw_behind all cvOf bE bd hD r0 (r1 :: tl) (by
        rw [hlen, List.length_cons]
        omega)]
      exact Nat.zero_le _

theorem allG_length (z : Point) (n : Nat) : (kG z n).all.length = z.size + 1 := by
  show (vsG z ++ [Var.point OnBytes.zeroE 3]).length = _
  unfold vsG
  simp

theorem badG_tight (z : Point) (n : Nat) (hn : 1 ≤ n) (Sm : List K → K) (sig : K)
    (hS : IsSum ((⟨1, vsG z, some ⟨2, n⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
    (mask : Nat → E) (F0 : Fork) (h : List Fmt.RoundView) :
    (badG z n hn Sm sig hS mask F0 h).length ≤ tight3 z.size h.length := by
  unfold badG
  exact bad_tight _ _ _ _ z.size (allG_length z n) (allG_d z n)
    (fun a b m => (specG z n hn Sm sig hS mask F0 a b).2.1 m)
    (fun a b m e pre g => (specG z n hn Sm sig hS mask F0 a b).2.2.1 m e pre g) h

theorem badLv_tight (z : Point) (Sm : List K → K) (sig : K)
    (hS : IsSum ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
    (mask : Nat → E) (F0 : Fork) (Tt : E) (Cv : K) (h : List Fmt.RoundView) :
    (badLv z Sm sig hS mask F0 Tt Cv h).length ≤ tight3 z.size h.length := by
  unfold badLv
  refine le_trans (List.length_take_le' _ _) ?_
  rw [← modR_length (tgt Tt) h]
  unfold badL1
  exact bad_tight _ _ _ _ z.size (allG_length z 2) (allG_d z 2)
    (fun _ _ m => (specL z Sm sig hS mask F0 Tt Cv).2.1 m)
    (fun _ _ m e pre g => (specL z Sm sig hS mask F0 Tt Cv).2.2.1 m e pre g) _

section Sized
variable [Sizes] [Policy] [Request] [Token]

theorem productsRule_tight (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (om : E)
    (h : List Fmt.RoundView) : (productsRule c mask F0 pV om h).length ≤ tight3 pV.size h.length :=
  badG_tight _ _ _ _ _ _ _ _ h

theorem squaresRule_tight (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (gam Tt : E)
    (Cv : K) (h : List Fmt.RoundView) :
    (squaresRule c mask F0 pV gam Tt Cv h).length ≤ tight3 (zS pV).size h.length :=
  badLv_tight _ _ _ _ _ _ _ _ h

theorem gamRule_le (c : NCells) (mask : Nat → E) (F : Fork) (pV : Point) (p : List Fmt.RoundView) :
    (gamRule c mask F pV p).length ≤ 8 := by
  unfold gamRule
  cases laidBy 9 F p with
  | none => simp
  | some Fa => exact listOf_length _ 8 (D6.Bridge.cnt_BadG _ _ _)

theorem omRule_le (c : NCells) (mask : Nat → E) (Fb : Fork) (pV : Point) (p : List Fmt.RoundView) :
    (omRule c mask Fb pV p).length ≤ 6 := by
  unfold omRule
  cases laidBy 7 Fb p with
  | none => simp
  | some Fc => exact listOf_length _ 6 (D6.Bridge.cnt_BadO (dataOf c) _ _)

theorem normedRule_tight [FinalNorm.In] (c : NCells) (mask : Nat → E) (F0 : Fork)
    (h : List Fmt.RoundView) : (normedRule c mask F0 h).length ≤ tight3 (FinalNorm.zt).size h.length :=
  badG_tight _ _ _ _ _ _ _ _ h

theorem allP_length [FinalNorm.In] [In] : kP.all.length = (FinalNorm.zt).size + lPd + 1 := by
  show (vsP ++ [Var.point OnBytes.zeroE 3]).length = _
  have hh : (halves lPd).size = lPd := by
    unfold halves
    simp
  rw [List.length_append, List.length_singleton]
  unfold vsP zP
  rw [List.length_map, Array.length_toList, Array.size_append, hh]

theorem badP_tight [FinalNorm.In] [In] (c : Cells) (mask : Nat → E) (F0 : Fork) (h : List Fmt.RoundView) :
    (badP c mask F0 h).length ≤ tight3 ((FinalNorm.zt).size + lPd) h.length := by
  unfold badP
  exact bad_tight _ _ _ _ _ allP_length allP_d (fun a b m => (specT c mask F0 a b).2.1 m)
    (fun a b m e pre g => (specT c mask F0 a b).2.2.1 m e pre g) h

/-! ## 2. The ceiling by the round's number -/

/-- The number of the level's rounds; of a sumcheck's on the positions. -/
def lvl : Nat := lPd + lt + 4
@[inherit_doc lvl] def smc : Nat := lt + 3

/-- **THE CEILING AT ROUND NUMBER j OF THE BLOCK.** Round 0 draws the point (the number is for one coordinate); round 1 batches
the nine sums; then the squares' level; round 2 + lvl batches the seven products; then the three sumchecks. -/
def tightAt (j : Nat) : Nat :=
  if j = 0 then 1 else if j = 1 then 8
  else if j < 2 + lvl then tight3 (lPd + lt) (j - 1)
  else if j = 2 + lvl then 6
  else if j < 3 + lvl + smc then tight3 lt (j - (2 + lvl))
  else if j < 3 + lvl + 2 * smc then tight3 lt (j - (2 + lvl + smc))
  else tight3 (lt + lPd) (j - (2 + lvl + 2 * smc))

theorem tightAt_level {j : Nat} (h1 : 2 ≤ j) (h2 : j < 2 + lvl) :
    tightAt j = tight3 (lPd + lt) (j - 1) := by
  unfold tightAt
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tightAt_six : tightAt (2 + lvl) = 6 := by
  unfold tightAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem tightAt_products {j : Nat} (h1 : 3 + lvl ≤ j) (h2 : j < 3 + lvl + smc) :
    tightAt j = tight3 lt (j - (2 + lvl)) := by
  unfold tightAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tightAt_normed {j : Nat} (h1 : 3 + lvl + smc ≤ j) (h2 : j < 3 + lvl + 2 * smc) :
    tightAt j = tight3 lt (j - (2 + lvl + smc)) := by
  unfold tightAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h2]

theorem tightAt_logits {j : Nat} (h1 : 3 + lvl + 2 * smc ≤ j) :
    tightAt j = tight3 (lt + lPd) (j - (2 + lvl + 2 * smc)) := by
  unfold tightAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem backRule_tight (c : NCells) (mask : Nat → E) (pV : Point) (hz : pV.size = lt) (Fb : Fork)
    (f : List Fmt.RoundView) : (backRule c mask pV Fb f).length ≤ tightAt (f.length + lvl + 1) := by
  have hs : smc = lt + 3 := rfl
  match f with
  | [] => simp [backRule]
  | [r2] =>
    have e : [r2].length + lvl + 1 = 2 + lvl := by
      rw [List.length_singleton]
      omega
    rw [e, tightAt_six]
    exact omRule_le c mask Fb pV [r2]
  | r2 :: a :: fr =>
    show (match sendThenBatch 7 7 Fb [r2] with
      | none => []
      | some ((_, om), Fc, _) =>
        if (a :: fr).length ≤ pV.size + 3 then productsRule c mask Fc pV om (a :: fr)
        else []).length ≤ _
    split
    · simp
    · split
      · rename_i hle
        rw [hz] at hle
        have hpos : 0 < (a :: fr).length := by simp
        have e0 : (r2 :: a :: fr).length = (a :: fr).length + 1 := rfl
        rw [e0, tightAt_products (by omega) (by omega)]
        have e : (a :: fr).length + 1 + lvl + 1 - (2 + lvl) = (a :: fr).length := by omega
        rw [e, ← hz]
        exact productsRule_tight c mask _ pV _ (a :: fr)
      · simp

theorem midRule_tight (c : NCells) (mask : Nat → E) (pV : Point) (hz : pV.size = lt)
    (W : Array Hid) (gam : E) (Fa : Fork) (f : List Fmt.RoundView) (hne : f ≠ []) :
    (midRule c mask pV W gam Fa f).length ≤ tightAt (f.length + 1) := by
  have hn : nS pV = lvl := by
    unfold nS lvl
    rw [zS_size pV hz]
  have hpos : 0 < f.length := List.length_pos_iff.mpr hne
  unfold midRule
  split
  · rename_i hle
    rw [hn] at hle
    rw [tightAt_level (by omega) (by omega)]
    have e : f.length + 1 - 1 = f.length := by omega
    rw [e, ← zS_size pV hz]
    exact squaresRule_tight c mask Fa pV gam _ _ f
  · rename_i hgt
    rw [hn] at hgt
    split
    · simp
    · rename_i _ Fb _ _
      have hx := backRule_tight c mask pV hz Fb (f.drop (nS pV))
      have e : (f.drop (nS pV)).length + lvl + 1 = f.length + 1 := by
        rw [List.length_drop, hn]
        omega
      rw [e] at hx
      exact hx

theorem normRule_tight (c : NCells) (mask : Nat → E) (F : Fork) (h : List Fmt.RoundView) :
    (normRule c mask F h).length ≤ tightAt (h.length - 1) := by
  match h with
  | [] => simp [normRule]
  | [_] => simp [normRule]
  | [r0, r1] =>
    have e : tightAt ([r0, r1].length - 1) = 8 := by
      show tightAt 1 = 8
      unfold tightAt
      rw [if_neg (by omega), if_pos rfl]
    rw [e]
    show (match drawPoint lt F [r0] with
      | none => []
      | some (pV, _, _) => gamRule c mask F pV [r1]).length ≤ 8
    split
    · simp
    · exact gamRule_le c mask F _ _
  | r0 :: r1 :: a :: fr =>
    have e : (r0 :: r1 :: a :: fr).length - 1 = (a :: fr).length + 1 := by
      simp only [List.length_cons]
      omega
    rw [e]
    show (match drawPoint lt F [r0], sendThenBatch 9 9 F [r1] with
      | some (pV, _, _), some ((W, gam), Fa, _) => midRule c mask pV W gam Fa (a :: fr)
      | _, _ => []).length ≤ _
    split
    · rename_i pV _ _ W gam Fa _ h0 _
      exact midRule_tight c mask pV (drawPoint_size h0) W gam Fa (a :: fr) (by simp)
    · simp

/-- **The normalization's hearing consumes just so many rounds.** -/
theorem norm_length {F G : Fork} (hW : WellLaid F) {h left : List Fmt.RoundView} {H : Norm.Heard}
    (hN : Norm.hear F h = some (H, G, left)) : h.length = 3 + lvl + smc + left.length := by
  have hs : smc = lt + 3 := rfl
  have hl : lvl = lPd + lt + 4 := rfl
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, rfl, h0, h1, _, h3, h4, h5, _⟩ := norm_parts hW hN
  obtain ⟨r0, rfl⟩ := drawPoint_one h0
  obtain ⟨r1, _, rfl, _, _, _⟩ := batch_one h1
  obtain ⟨r2, _, rfl, _, _, _⟩ := batch_one h4
  have hz : H.pV.size = lt := drawPoint_size h0
  have lS : tS.length = (zS H.pV).size + 4 := level_length h3
  rw [zS_size H.pV hz] at lS
  have lP : tP.length = H.pV.size + 3 := by
    obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec h5
    exact a1
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

variable [FinalNorm.In] [In]

theorem badP_nil (c : Cells) (mask : Nat → E) (F0 : Fork) : badP c mask F0 [] = [] := by
  simp [badP, bad, raw]

theorem blockRule_tight (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    (hzt : (FinalNorm.zt).size = lt) (h : List Fmt.RoundView) :
    (blockRule c mask F h).length ≤ tightAt (h.length - 1) := by
  have hs : smc = lt + 3 := rfl
  unfold blockRule tailRule
  cases hN : Norm.hear F h with
  | none => simp
  | some v =>
    obtain ⟨H, Fa, l1⟩ := v
    have hlen := norm_length hW hN
    dsimp only
    split
    · rename_i hle
      rw [hzt] at hle
      by_cases h0 : l1 = []
      · subst h0
        rw [normedRule_nil]
        exact Nat.zero_le _
      · have hpos : 0 < l1.length := List.length_pos_iff.mpr h0
        rw [tightAt_normed (by omega) (by omega)]
        have e : h.length - 1 - (2 + lvl + smc) = l1.length := by omega
        rw [e, ← hzt]
        exact normedRule_tight c mask Fa l1
    · rename_i hgt
      rw [hzt] at hgt
      cases hS : sumcheck FinalNorm.zt 2 Fa l1 with
      | none => simp
      | some u =>
        obtain ⟨SN, Fb, l2⟩ := u
        obtain ⟨p2, e2, c2⟩ := consumes_sumcheck _ _ _ _ _ _ _ hS
        have c2' := c2 []
        rw [List.append_nil] at c2'
        have lp : p2.length = (FinalNorm.zt).size + 3 := by
          obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec c2'
          exact a1
        rw [hzt] at lp
        have hl1 : l1.length = p2.length + l2.length := by rw [e2, List.length_append]
        dsimp only
        by_cases h0 : l2 = []
        · subst h0
          rw [badP_nil]
          exact Nat.zero_le _
        · have hpos : 0 < l2.length := List.length_pos_iff.mpr h0
          rw [tightAt_logits (by omega)]
          have e : h.length - 1 - (2 + lvl + 2 * smc) = l2.length := by omega
          rw [e, ← hzt]
          exact badP_tight c.toCells mask Fb l2

theorem rowRule_tight (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    (hzt : (FinalNorm.zt).size = lt) (h : List Fmt.RoundView) :
    (rowRule c mask F h).length ≤ tightAt (h.length - 1) := by
  unfold rowRule
  cases hN : Norm.hear F h with
  | none =>
    rw [blockRule_none c mask F hN, List.append_nil]
    exact normRule_tight c mask F h
  | some v =>
    obtain ⟨H, G, left⟩ := v
    by_cases hl : left = []
    · subst hl
      rw [blockRule_at_end c mask F hN, List.append_nil]
      exact normRule_tight c mask F h
    · rw [normRule_behind c mask F hW hN hl, List.nil_append]
      exact blockRule_tight c mask F hW hzt h

theorem strikeLast_length (g : List Fmt.RoundView) : (strikeLast g).length = g.length := by
  induction g using List.reverseRecOn with
  | nil => rfl
  | append_singleton p r _ =>
    rw [strikeLast_concat]
    simp

/-- **THE TIGHT CEILING OF THE BLOCK's ONE RULE, AT EVERY FRONT.** -/
theorem rowRuleC_tight (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    (hzt : (FinalNorm.zt).size = lt) (g : List Fmt.RoundView) :
    (rowRuleC c mask F g).length ≤ tightAt (g.length - 1) := by
  unfold rowRuleC
  rw [List.length_append]
  match g with
  | [] =>
    have h := rowRule_tight c mask F hW hzt (strikeLast [])
    rw [strikeLast_length] at h
    have e : pointRule c [] = [] := rfl
    rw [e]
    simpa using h
  | [r] =>
    have e : strikeLast [r] = [cutTo r 0] := strikeLast_concat [] r
    have e2 : rowRule c mask F [cutTo r 0] = [] := by
      unfold rowRule
      rw [blockRule_one c mask F hW]
      rfl
    have e3 : tightAt ([r].length - 1) = 1 := by
      show tightAt 0 = 1
      unfold tightAt
      exact if_pos rfl
    rw [e, e2, e3]
    have := pointRule_length c [r]
    simp only [List.length_nil]
    omega
  | r :: a :: fr =>
    have e : pointRule c (r :: a :: fr) = [] := rfl
    have h := rowRule_tight c mask F hW hzt (strikeLast (r :: a :: fr))
    rw [strikeLast_length] at h
    rw [e]
    simpa using h

end Sized

end VerifiableInference.Desc.Kinds.Head.Law.Came

/-! ## 3. At the block's decision -/

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Sound (cutTo strikeLast)

variable {S : Type}

/-- **THE CEILING AT ROUND NUMBER j: a number of the plan alone.** -/
def priceAt (p : Par) (j : Nat) : Nat :=
  let _ := p.sizes
  min (sentAt p j + 1) (Came.tightAt j)

/-- **K6's RULE, CUT AT THE TIGHT CEILING.** -/
noncomputable def ruleK6T (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (g : List Fmt.RoundView) : List E :=
  (ruleCutAt p L s c mask g).take (priceAt p (g.length - 1))

/-- **K6's ROW, UNDER THE RULE CUT AT THE TIGHT CEILING.** -/
def RowPriceStatement : Prop :=
  ∀ (S Cl : Type) (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) (s : S)
    (c : NCells) (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (kind cl L link piece p).decide s rs gs = .ok s' → SeatBack p L s → WellLaid (L.ledger s) →
    p.ok = true → hasFeatures p → p.okStart (L.request s) = true →
    (∀ y, Reply.token L.toSeat s = some y → y < p.sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6T p L s c mask) rs →
    Opened p L s' c mask → ClosedWhole p L s' c mask

namespace Came

theorem ruleK6T_length (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (g : List Fmt.RoundView) : (ruleK6T p L s c mask g).length ≤ priceAt p (g.length - 1) :=
  List.length_take_le _ _

theorem ruleCutAt_tight (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (hW : WellLaid (L.ledger s)) (hplan : p.ok = true) (h : List Fmt.RoundView) :
    (ruleCutAt p L s c mask h).length ≤ @tightAt p.sizes (h.length - 1) := by
  unfold ruleCutAt
  cases hg : given p L s with
  | error _ => simp
  | ok g =>
    obtain ⟨z, y, _, _, hP, rfl⟩ := given_ok p L s g hg
    letI := p.sizes
    letI := p.policy
    letI : Request := L.request s
    letI : Token := ⟨y⟩
    have P := planFacts hplan
    have hV : 0 < V := by have := P.hV2; omega
    have Lt := fromLookup_law p.floor z.1 z.2 hV (lens_small hplan) hP
    exact @rowRuleC_tight p.sizes p.policy (L.request s) ⟨y⟩ (fromLookup p.floor z.1 z.2).norm
      (fromLookup p.floor z.1 z.2).head c mask _ hW Lt.zt h

/-- **On the rounds on which the decision went on the tight cut takes nothing away.** -/
theorem cut_takes_nothingT {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (c : NCells)
    (mask : Nat → E) (hd : (kind cl L link piece p).decide s rs gs = .ok s')
    (hW : WellLaid (L.ledger s)) (hplan : p.ok = true) (hnb : Sound.NoBad (ruleK6T p L s c mask) rs) :
    Sound.NoBad (ruleCutAt p L s c mask) rs := by
  intro i r hi j x hj hm
  refine hnb i r hi j x hj ?_
  show E.ofTriple x ∈ ruleK6T p L s c mask (rs.take i ++ [cutTo r j])
  have hil : i < rs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : (rs.take i ++ [cutTo r j]).length - 1 = i := by
    rw [List.length_append, List.length_take, List.length_singleton]
    omega
  have hle := ruleCutAt_length p L s c mask hW (rs.take i ++ [cutTo r j])
  have hlast : (((rs.take i ++ [cutTo r j]).getLast?.map fun r => r.vals.length).getD 0)
      = r.vals.length := by simp [cutTo]
  rw [hlast, decide_shape cl L link piece p hd i r hi] at hle
  have hti := ruleCutAt_tight p L s c mask hW hplan (rs.take i ++ [cutTo r j])
  rw [hlen] at hti
  have hle' : (ruleCutAt p L s c mask (rs.take i ++ [cutTo r j])).length ≤ priceAt p i :=
    Nat.le_min.mpr ⟨hle, hti⟩
  unfold ruleK6T
  rw [hlen, List.take_of_length_le hle']
  exact hm

/-- What is cut is a part of what is not. -/
theorem noBadCut_take {b : List Fmt.RoundView → List E} {n : List Fmt.RoundView → Nat} {rs : List Fmt.RoundView}
    (h : Sound.NoBad b rs) : Sound.NoBad (fun g => (b g).take (n g)) rs :=
  fun i r hi j x hj hm => h i r hi j x hj (List.mem_of_mem_take hm)

theorem rowPrice : RowPriceStatement := by
  intro S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hd0 hreq hy hcan hnb hopen
  exact rowK6 S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hd0 hreq hy hcan
    (noBadCut_take (cut_takes_nothingT cl L link piece p c mask hd hWL hplan hnb)) hopen

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowRuleC_tight
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ruleK6T_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cut_takes_nothingT
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowPrice
