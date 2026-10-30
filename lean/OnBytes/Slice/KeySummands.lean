-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeySummands.lean: the summands of a lookup's sumchecks have towers.

The soundness of the written sumcheck (OnBytes/Slice/KeyPsc.lean, KeyPscN.lean) asks for a tower of
the summand (OnBytes/Slice/KeyPscRun.lean: Sums). This file gives one for each summand of a lookup
(OnBytes/Iop/Lkp.lean), under equality weights, for all multilinear maps and all values of the mask
entries, and says what the tower's sum is: the multilinear extension, at the weights' point, of the
summand's table.

 summandProduct    y0 y1                  a level of a tree; the parts' roots
 summandTieFirst   y0 - a y1^2 y2         the first step of the tie
 summandTie        y0^2 y1                a later step of the tie
 summandBits       y^2 - y                the bits are bits
 summandLeaves     1 + factor · bit       the leaves of the table's tree; the bits are a kept map
 summandMinus      c - y0 y1              not a lookup's: a kept map less the product of two maps

The first four and the last have a further variable Y. The general statement for them is sums_eqY,
for the fifth sums_eqN. Both rest on OnBytes/Slice/KeyTowerOf.lean (a tower for every function that
is a polynomial in each variable) and OnBytes/Slice/KeyDegrees.lean (degrees).

Main definitions: eqVars, summandTieFirst, summandTie, summandBits, summandLeaves, summandMinus,
masked, maskOf.

Main theorems: sums_eqY, sums_eqN, dg_masked, ext_congr, and for each summand: summandAt_product and
its like (the summand at a list of challenges, written out), sums_product and its like.

Not claimed. That the maps of a given lookup are multilinear, or that its claims are these sums.
summandLeaves takes the factor as a function of the point round by round; the program computes it
from the public table, which is not in this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyDegrees
import OnBytes.Slice.KeyLevel

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb

/-! ## Equality weights -/

/-- Equality weights: for each variable its coordinate of the point and the number of coefficients
of its polynomials. -/
def eqVars (l : List (GE × ℕ)) : List Weight := l.map fun p => Weight.equality p.1 p.2

/-- One weight for each variable. -/
theorem eqVars_length (l : List (GE × ℕ)) : (eqVars l).length = l.length := List.length_map _

/-- Equality weights are sums of the values at 0 and 1. -/
theorem eqVars_twoNode (l : List (GE × ℕ)) (hl : ∀ p ∈ l, 2 ≤ p.2) :
    ∀ w ∈ eqVars l, w.TwoNode ∧ 1 ≤ w.d := by
  intro w hw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
  exact ⟨(equality_twoNode p.1 p.2 (hl p hp)).1, Nat.le_trans (by decide) (hl p hp)⟩

/-- A summand with a shown map, under equality weights. If the summand at a list of challenges
has the degree k i in coordinate i, below the number of coefficients of that variable's polynomials,
then it has a tower, and the tower's sum is the extension, at the weights' point, of the summand's
table with 0 for Y. -/
theorem sums_eqY (W : World) (V Kp : ℕ → List GE → GE) (l : List (GE × ℕ)) (masks : MaskForm)
    (target : GE) (S : Summand) (fr : List Slot) (hS : S.shown ≠ 0) (hg : 1 ≤ S.degree)
    (hl : ∀ p ∈ l, 2 ≤ p.2) (k : ℕ → ℕ) (hk : ∀ i (h : i < l.length), k i < l[i].2)
    (hkY : k l.length < S.degree + 1)
    (hd : Dg k (l.length + 1) (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr)) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ S fr
        (towN (eqVars l ++ [Weight.atZero (S.degree + 1)])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr)) ∧
      towN (eqVars l ++ [Weight.atZero (S.degree + 1)])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr) [] =
        ext l.length (fun q => summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr (q ++ [0]))
          (l.map (·.1)) := by
  have hv : varsOf ⟨eqVars l, masks, target⟩ S = eqVars l ++ [Weight.atZero (S.degree + 1)] := by
    unfold varsOf
    rw [if_neg (by simpa using hS)]
  have h2 : 2 ≤ S.degree + 1 := Nat.succ_le_succ hg
  have hlen : (eqVars l ++ [Weight.atZero (S.degree + 1)]).length = l.length + 1 := by
    rw [List.length_append, eqVars_length]
    rfl
  have hw : ∀ w ∈ eqVars l ++ [Weight.atZero (S.degree + 1)], w.TwoNode ∧ 1 ≤ w.d := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact eqVars_twoNode l hl w hw
    · rw [List.mem_singleton.1 hw]
      exact ⟨(equality_twoNode 0 _ h2).1, Nat.le_trans (by decide) h2⟩
  refine ⟨⟨?_, fun γ hγ => ?_⟩, ?_⟩
  · rw [hv]
    refine tower_towN _ _ hw (polyIn_of_dg _ (k := k) (fun i hi => ?_) (by rw [hlen]; exact hd))
    by_cases hil : i < l.length
    · rw [List.getElem_append_left (by rw [eqVars_length]; exact hil)]
      unfold eqVars
      rw [List.getElem_map]
      exact hk i hil
    · have hie : i = l.length := by
        rw [hlen] at hi
        omega
      subst hie
      rw [List.getElem_append_right (by rw [eqVars_length])]
      simp only [eqVars_length, Nat.sub_self, List.getElem_cons_zero]
      exact hkY
  · rw [hv] at hγ
    exact towN_full _ _ γ hγ
  · rw [towN_nil]
    exact sumN_equality_zero _ h2 l _ hl

/-- A summand without a shown map, under equality weights. -/
theorem sums_eqN (W : World) (V Kp : ℕ → List GE → GE) (l : List (GE × ℕ)) (masks : MaskForm)
    (target : GE) (S : Summand) (fr : List Slot) (hS : S.shown = 0) (hl : ∀ p ∈ l, 2 ≤ p.2)
    (k : ℕ → ℕ) (hk : ∀ i (h : i < l.length), k i < l[i].2)
    (hd : Dg k l.length (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr)) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ S fr
        (towN (eqVars l) (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr)) ∧
      towN (eqVars l) (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr) [] =
        ext l.length (summandAt W V Kp ⟨eqVars l, masks, target⟩ S fr) (l.map (·.1)) := by
  have hv : varsOf ⟨eqVars l, masks, target⟩ S = eqVars l := by
    unfold varsOf
    rw [if_pos (by simp [hS])]
  refine ⟨⟨?_, fun γ hγ => ?_⟩, ?_⟩
  · rw [hv]
    refine tower_towN _ _ (eqVars_twoNode l hl)
      (polyIn_of_dg _ (k := k) (fun i hi => ?_) (by rw [eqVars_length]; exact hd))
    unfold eqVars
    rw [List.getElem_map]
    exact hk i (by rwa [eqVars_length] at hi)
  · rw [hv] at hγ
    exact towN_full _ _ γ hγ
  · rw [towN_nil]
    exact sumN_equality l _ hl

/-! ## A shown map with its mask -/

/-- A shown map's masked value at a list of challenges: the map at the first n challenges, plus
the last challenge times the map's mask entry. -/
def masked (n : ℕ) (V : List GE → GE) (r : GE) (γ : List GE) : GE :=
  V (γ.take n) + γ.getLast?.getD 0 * r

/-- The masked value of a multilinear map has the degree 1 in each coordinate. -/
theorem dg_masked {n : ℕ} {V : List GE → GE} (hV : ML n V) (r : GE) :
    Dg (fun _ => 1) (n + 1) (masked n V r) :=
  Dg.add (dg_take (dg_of_ml hV))
    (Dg.congr (fun _ _ => mul_comm _ _) (Dg.cmul r (dg_last n)))

/-- With 0 for Y the masked value is the map's. -/
theorem masked_zero (n : ℕ) (V : List GE → GE) (r : GE) (q : List GE) (hq : q.length = n) :
    masked n V r (q ++ [0]) = V q := by
  unfold masked
  rw [← hq, List.take_left', List.getLast?_append]
  · simp
  · rfl

/-- The extension reads a table at lists of n elements alone. -/
theorem ext_congr : ∀ (n : ℕ) {t t' : List GE → GE}, (∀ q, q.length = n → t q = t' q) →
    ∀ zs, ext n t zs = ext n t' zs
  | 0, _, _, h, _ => h [] rfl
  | n + 1, _, _, h, [] => ext_congr n (fun q hq => h (0 :: q) (congrArg (· + 1) hq)) []
  | n + 1, t, t', h, z :: zs => by
    show (1 - z) * ext n (fun q => t (0 :: q)) zs + z * ext n (fun q => t (1 :: q)) zs =
      (1 - z) * ext n (fun q => t' (0 :: q)) zs + z * ext n (fun q => t' (1 :: q)) zs
    rw [ext_congr n (fun q hq => h (0 :: q) (congrArg (· + 1) hq)) zs,
      ext_congr n (fun q hq => h (1 :: q) (congrArg (· + 1) hq)) zs]

/-- A difference has the degrees of its two parts. -/
theorem Dg.sub {n : ℕ} {k : ℕ → ℕ} {f g : List GE → GE} (hf : Dg k n f) (hg : Dg k n g) :
    Dg k n fun q => f q - g q :=
  Dg.congr (fun q _ => by ring) (Dg.add hf (Dg.cmul (-1) hg))

/-! ## The summands -/

/-- The mask entry of shown map number j: the fresh entries behind those of the hiding
polynomial. -/
def maskOf (W : World) (c : Claim) (S : Summand) (fr : List Slot) (j : ℕ) : GE :=
  W.mask ((fr.drop (hidingEntries (varsOf c S))).getD j default)

/-- The first step of the tie: y0 - a y1^2 y2. -/
def summandTieFirst (a : GE) : Summand where
  shown := 3
  kept := 0
  degree := 3
  coeffs := fun _ y => [y.getD 0 0 - a * y.getD 1 0 * y.getD 1 0 * y.getD 2 0]

/-- A later step of the tie: y0^2 y1. -/
def summandTie : Summand where
  shown := 2
  kept := 0
  degree := 3
  coeffs := fun _ y => [y.getD 0 0 * y.getD 0 0 * y.getD 1 0]

/-- y^2 - y, which is 0 exactly at 0 and 1. -/
def summandBits : Summand where
  shown := 1
  kept := 0
  degree := 2
  coeffs := fun _ y => [y.getD 0 0 * y.getD 0 0 - y.getD 0 0]

/-- The leaves of the table's tree: 1 + bit · factor. The bits are a kept map. factor: a function of
the point round by round. -/
def summandLeaves (factor : List GE → GE) : Summand where
  shown := 0
  kept := 1
  degree := 0
  coeffs := fun byRound _ => [1, factor byRound]

/-- A kept map less the product of two shown maps. -/
def summandMinus : Summand where
  shown := 2
  kept := 1
  degree := 2
  coeffs := fun _ y => [-(y.getD 0 0 * y.getD 1 0), 1]

section
variable (W : World) (V Kp : ℕ → List GE → GE) (c : Claim) (fr : List Slot) {n : ℕ}
  (hn : c.vars.length = n)
include hn

/-- The product, at a list of challenges. -/
theorem summandAt_product : summandAt W V Kp c summandProduct fr = fun γ =>
    masked n (V 0) (maskOf W c summandProduct fr 0) γ *
      masked n (V 1) (maskOf W c summandProduct fr 1) γ := by
  subst hn
  funext γ
  unfold summandAt masked maskOf
  simp [summandProduct, List.range_succ, dot_nil_left]

/-- The first step of the tie, at a list of challenges. -/
theorem summandAt_tieFirst (a : GE) : summandAt W V Kp c (summandTieFirst a) fr = fun γ =>
    masked n (V 0) (maskOf W c (summandTieFirst a) fr 0) γ -
      a * masked n (V 1) (maskOf W c (summandTieFirst a) fr 1) γ *
        masked n (V 1) (maskOf W c (summandTieFirst a) fr 1) γ *
        masked n (V 2) (maskOf W c (summandTieFirst a) fr 2) γ := by
  subst hn
  funext γ
  unfold summandAt masked maskOf
  simp [summandTieFirst, List.range_succ, dot_nil_left]

/-- A later step of the tie, at a list of challenges. -/
theorem summandAt_tie : summandAt W V Kp c summandTie fr = fun γ =>
    masked n (V 0) (maskOf W c summandTie fr 0) γ *
      masked n (V 0) (maskOf W c summandTie fr 0) γ *
      masked n (V 1) (maskOf W c summandTie fr 1) γ := by
  subst hn
  funext γ
  unfold summandAt masked maskOf
  simp [summandTie, List.range_succ, dot_nil_left]

/-- y^2 - y, at a list of challenges. -/
theorem summandAt_bits : summandAt W V Kp c summandBits fr = fun γ =>
    masked n (V 0) (maskOf W c summandBits fr 0) γ *
      masked n (V 0) (maskOf W c summandBits fr 0) γ -
      masked n (V 0) (maskOf W c summandBits fr 0) γ := by
  subst hn
  funext γ
  unfold summandAt masked maskOf
  simp [summandBits, List.range_succ, dot_nil_left]

/-- The leaves, at a list of challenges. -/
theorem summandAt_leaves (factor : List GE → GE) :
    summandAt W V Kp c (summandLeaves factor) fr = fun γ =>
      1 + factor (γ.take n) * Kp 0 (γ.take n) := by
  subst hn
  funext γ
  unfold summandAt
  simp [summandLeaves, List.range_succ, dot_cons, dot_nil_left]

/-- A kept map less a product, at a list of challenges. -/
theorem summandAt_minus : summandAt W V Kp c summandMinus fr = fun γ =>
    -(masked n (V 0) (maskOf W c summandMinus fr 0) γ *
      masked n (V 1) (maskOf W c summandMinus fr 1) γ) +
      Kp 0 (γ.take n) := by
  subst hn
  funext γ
  unfold summandAt masked maskOf
  simp [summandMinus, List.range_succ, dot_cons, dot_nil_left]

end

/-! ## Their towers -/

section
variable (W : World) (V Kp : ℕ → List GE → GE) (l : List (GE × ℕ)) (masks : MaskForm)
  (target : GE) (fr : List Slot)

/-- The product of two shown maps has a tower, and the tower's sum is the extension of the
product's table. -/
theorem sums_product (h0 : ML l.length (V 0)) (h1 : ML l.length (V 1)) (hl : ∀ p ∈ l, 3 ≤ p.2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ summandProduct fr
        (towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandProduct fr)) ∧
      towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandProduct fr) [] =
        ext l.length (fun q => V 0 q * V 1 q) (l.map (·.1)) := by
  have he := summandAt_product W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l)
  obtain ⟨hs, ht⟩ := sums_eqY W V Kp l masks target summandProduct fr (by decide) (by decide)
    (fun p hp => le_trans (by decide) (hl p hp)) (fun _ => 1 + 1)
    (fun i hi => hl _ (List.getElem_mem hi)) (by decide : 1 + 1 < 2 + 1) (by
      rw [he]
      exact Dg.mul (dg_masked h0 _) (dg_masked h1 _))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show masked _ _ _ _ * masked _ _ _ _ = _
  rw [masked_zero _ _ _ _ hq, masked_zero _ _ _ _ hq]

/-- The first step of the tie has a tower. -/
theorem sums_tieFirst (a : GE) (h0 : ML l.length (V 0)) (h1 : ML l.length (V 1))
    (h2 : ML l.length (V 2)) (hl : ∀ p ∈ l, 4 ≤ p.2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ (summandTieFirst a) fr
        (towN (eqVars l ++ [Weight.atZero 4])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ (summandTieFirst a) fr)) ∧
      towN (eqVars l ++ [Weight.atZero 4])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ (summandTieFirst a) fr) [] =
        ext l.length (fun q => V 0 q - a * V 1 q * V 1 q * V 2 q) (l.map (·.1)) := by
  have he := summandAt_tieFirst W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l) a
  obtain ⟨hs, ht⟩ := sums_eqY W V Kp l masks target (summandTieFirst a) fr
    (by decide : 3 ≠ 0) (by decide : 1 ≤ 3) (fun p hp => le_trans (by decide) (hl p hp))
    (fun _ => 1 + 1 + 1) (fun i hi => hl _ (List.getElem_mem hi))
    (by decide : 1 + 1 + 1 < 3 + 1) (by
      rw [he]
      exact Dg.sub (Dg.mono (fun _ _ => by decide) (dg_masked h0 _))
        (Dg.mul (Dg.mul (Dg.cmul a (dg_masked h1 _)) (dg_masked h1 _)) (dg_masked h2 _)))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show masked _ _ _ _ - a * masked _ _ _ _ * masked _ _ _ _ * masked _ _ _ _ = _
  rw [masked_zero _ _ _ _ hq, masked_zero _ _ _ _ hq, masked_zero _ _ _ _ hq]

/-- A later step of the tie has a tower. -/
theorem sums_tie (h0 : ML l.length (V 0)) (h1 : ML l.length (V 1)) (hl : ∀ p ∈ l, 4 ≤ p.2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ summandTie fr
        (towN (eqVars l ++ [Weight.atZero 4])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandTie fr)) ∧
      towN (eqVars l ++ [Weight.atZero 4])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandTie fr) [] =
        ext l.length (fun q => V 0 q * V 0 q * V 1 q) (l.map (·.1)) := by
  have he := summandAt_tie W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l)
  obtain ⟨hs, ht⟩ := sums_eqY W V Kp l masks target summandTie fr (by decide) (by decide)
    (fun p hp => le_trans (by decide) (hl p hp)) (fun _ => 1 + 1 + 1)
    (fun i hi => hl _ (List.getElem_mem hi)) (by decide : 1 + 1 + 1 < 3 + 1) (by
      rw [he]
      exact Dg.mul (Dg.mul (dg_masked h0 _) (dg_masked h0 _)) (dg_masked h1 _))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show masked _ _ _ _ * masked _ _ _ _ * masked _ _ _ _ = _
  rw [masked_zero _ _ _ _ hq, masked_zero _ _ _ _ hq]

/-- y^2 - y has a tower, and the tower's sum is the extension of the table bit^2 - bit. -/
theorem sums_bits (h0 : ML l.length (V 0)) (hl : ∀ p ∈ l, 3 ≤ p.2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ summandBits fr
        (towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandBits fr)) ∧
      towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandBits fr) [] =
        ext l.length (fun q => V 0 q * V 0 q - V 0 q) (l.map (·.1)) := by
  have he := summandAt_bits W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l)
  obtain ⟨hs, ht⟩ := sums_eqY W V Kp l masks target summandBits fr (by decide) (by decide)
    (fun p hp => le_trans (by decide) (hl p hp)) (fun _ => 1 + 1)
    (fun i hi => hl _ (List.getElem_mem hi)) (by decide : 1 + 1 < 2 + 1) (by
      rw [he]
      exact Dg.sub (Dg.mul (dg_masked h0 _) (dg_masked h0 _))
        (Dg.mono (fun _ _ => by decide) (dg_masked h0 _)))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show masked _ _ _ _ * masked _ _ _ _ - masked _ _ _ _ = _
  rw [masked_zero _ _ _ _ hq]

/-- A kept map less the product of two shown maps has a tower, and the tower's sum is the
extension of the table c - x b. -/
theorem sums_minus (h0 : ML l.length (V 0)) (h1 : ML l.length (V 1)) (hc : ML l.length (Kp 0))
    (hl : ∀ p ∈ l, 3 ≤ p.2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ summandMinus fr
        (towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandMinus fr)) ∧
      towN (eqVars l ++ [Weight.atZero 3])
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ summandMinus fr) [] =
        ext l.length (fun q => Kp 0 q - V 0 q * V 1 q) (l.map (·.1)) := by
  have he := summandAt_minus W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l)
  obtain ⟨hs, ht⟩ := sums_eqY W V Kp l masks target summandMinus fr (by decide) (by decide)
    (fun p hp => le_trans (by decide) (hl p hp)) (fun _ => 1 + 1)
    (fun i hi => hl _ (List.getElem_mem hi)) (by decide : 1 + 1 < 2 + 1) (by
      rw [he]
      exact Dg.add (Dg.congr (fun q _ => by ring)
          (Dg.cmul (-1) (Dg.mul (dg_masked h0 _) (dg_masked h1 _))))
        (Dg.mono (fun _ _ => by decide) (dg_take (dg_of_ml hc))))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show -(masked _ _ _ _ * masked _ _ _ _) + Kp 0 ((q ++ [0]).take l.length) = _
  rw [masked_zero _ _ _ _ hq, masked_zero _ _ _ _ hq, ← hq, List.take_left']
  · ring
  · rfl

/-- The leaves' summand has a tower, and the tower's sum is the extension of the table
1 + factor · bit. kf i: the degree of the factor in the variable of round i. -/
theorem sums_leaves (factor : List GE → GE) (kf : ℕ → ℕ) (hf : Dg kf l.length factor)
    (hb : ML l.length (Kp 0)) (hl : ∀ p ∈ l, 2 ≤ p.2)
    (hk : ∀ i (h : i < l.length), kf i + 1 < l[i].2) :
    Sums W V Kp ⟨eqVars l, masks, target⟩ (summandLeaves factor) fr
        (towN (eqVars l) (summandAt W V Kp ⟨eqVars l, masks, target⟩ (summandLeaves factor) fr)) ∧
      towN (eqVars l)
          (summandAt W V Kp ⟨eqVars l, masks, target⟩ (summandLeaves factor) fr) [] =
        ext l.length (fun q => 1 + factor q * Kp 0 q) (l.map (·.1)) := by
  have he := summandAt_leaves W V Kp ⟨eqVars l, masks, target⟩ fr (eqVars_length l) factor
  have ht' : ∀ q : List GE, q.length = l.length → q.take l.length = q := fun q hq =>
    List.take_of_length_le (le_of_eq hq)
  obtain ⟨hs, ht⟩ := sums_eqN W V Kp l masks target (summandLeaves factor) fr rfl hl
    (fun i => kf i + 1) hk (by
      rw [he]
      refine Dg.congr (f := fun q => 1 + factor q * Kp 0 q) (fun q hq => by rw [ht' q hq]) ?_
      exact Dg.add (Dg.const 1 _ _) (Dg.mul hf (dg_of_ml hb)))
  refine ⟨hs, ht.trans (ext_congr _ (fun q hq => ?_) _)⟩
  rw [he]
  show 1 + factor (q.take l.length) * Kp 0 (q.take l.length) = _
  rw [ht' q hq]

end

end OnBytes.Slice.PscF
