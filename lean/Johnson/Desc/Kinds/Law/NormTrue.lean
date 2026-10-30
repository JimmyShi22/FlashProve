-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormTrue.lean.
WHAT IT DOES NOT SHOW. THAT THERE IS A TRANSCRIPT AT THE TRUTH: that rounds of the program's
elements exist on which Norm.hear returns and whose completed polynomials are the true round
polynomials is stated nowhere here. These polynomials (tqL, tqG) are CHOSEN out of the law
sound_hear_true (Classical.choose): no run can evaluate them. No soundness, no probability.
SO IT DOES NOT SHOW THAT norm_blockC's PREMISE "NO BAD DRAW" CAN BE MET: only: NormTruth gives it.
WHAT IT IS. AT THE TRUTH THE LISTS OF THE NORM's RULE ARE EMPTY, WHATEVER IS DRAWN. NormTruth c
mask F rs: at the five stretches into which the hearing falls: the cells hold; the nine hidden sums
and the seven hidden products behind their messages are the true ones at pV; the start form of the
squares' level is worth the true sum; the claimed sum of "products" hides the true sum; each
round's completed polynomial, in both sumchecks, is the true round polynomial. norm_true: where
Norm.hear returns, NormTruth gives Sound.NoBad (normRuleC c mask F) (the rule's form:
Johnson/Desc/Sound/RuleForm.lean).
BENEATH, generic: noBad_snoc, noBad_one, noBad_glue (a rule clean on stretches is clean on the
whole); movesOf_length; raw_behind (behind all its variables the sumcheck's rule is empty: its
sets have fewer members than dAt, which is 1 there); noBadG_true (Law/SumLaw.lean's badG);
noBad_unmod, noBadLv_true (Law/LevelLaw.lean's badLv, the last round LINE with it); listOf_nil;
cut_of_noBad. THE PATTERN IS Law/NoBadTrue.lean (noBad_of_empty is called;
noBad_true is followed closely in noBadG_true). midRule_level, midRule_behind, normRule_past: the
lines stand inside norm_block (Law/NormRule.lean) and in Law/RowCeil.lean
(midRule_back, normRule_behind), which this file cannot import without reaching Block.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NoBadTrue
import Johnson.Desc.Kinds.Law.NormPointRule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE okE)
open OnBytes.Model (Aff Reading World Fork)
open Polynomial
open Norm (lt ls d lPd T S2)
open OnBytes.Desc.First.P1 (IsSum dAt)
open Part.MaskedSum (Var Call Ends Sent VarsRead movesOf scalars readAll leadScalars)
open Sound (cutTo strikeLast)
open Came (val vsG kG allG_d cvG bEG bdG tqG bEG_empty bdG_empty badG bEL bdL tqL bEL_empty
  bdL_empty specL badL1 badLv modR mul_tgt heardBy_cut)

/-! ## A rule that is clean on stretches -/

theorem noBad_nil (b : List Fmt.RoundView → List E) : NoBad b [] := by
  intro i r hi
  simp at hi

theorem noBad_none (t : List Fmt.RoundView) : NoBad (fun _ => []) t := by
  intro i r _ x _ hm
  simp at hm

theorem noBad_snoc {b : List Fmt.RoundView → List E} {t : List Fmt.RoundView} {l : Fmt.RoundView} (h : NoBad b t)
    (hl : ∀ x, x ∈ l.drawn.elems →
      E.ofTriple x ∉ b (t ++ [{ l with drawn := ⟨[], [], [], none⟩ }])) :
    NoBad b (t ++ [l]) := by
  intro i r hi x hx
  by_cases hit : i < t.length
  · rw [List.getElem?_append_left hit] at hi
    rw [List.take_append_of_le_length (le_of_lt hit)]
    exact h i r hi x hx
  · have hle : t.length ≤ i := Nat.le_of_not_lt hit
    rw [List.getElem?_append_right hle] at hi
    cases hk : i - t.length with
    | zero =>
      rw [hk] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have e : i = t.length := by omega
      rw [e, List.take_left]
      exact hl x hx
    | succ k =>
      rw [hk] at hi
      simp at hi

/-- One round more, at whose front the rule is empty. -/
theorem noBad_one {b : List Fmt.RoundView → List E} {t : List Fmt.RoundView} {l : Fmt.RoundView} (h : NoBad b t)
    (he : b (t ++ [{ l with drawn := ⟨[], [], [], none⟩ }]) = []) : NoBad b (t ++ [l]) :=
  noBad_snoc h fun x _ hm => by
    rw [he] at hm
    simp at hm

/-- A stretch more, on whose fronts the rule is b. -/
theorem noBad_glue {rule b : List Fmt.RoundView → List E} {pre t : List Fmt.RoundView} (hpre : NoBad rule pre)
    (he : ∀ i r, t[i]? = some r →
      rule (pre ++ (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }]))
        = b (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }]))
    (ht : NoBad b t) : NoBad rule (pre ++ t) := by
  intro i r hi x hx
  by_cases hip : i < pre.length
  · rw [List.getElem?_append_left hip] at hi
    rw [List.take_append_of_le_length (le_of_lt hip)]
    exact hpre i r hi x hx
  · have hle : pre.length ≤ i := Nat.le_of_not_lt hip
    rw [List.getElem?_append_right hle] at hi
    rw [List.take_append, List.take_of_length_le hle, List.append_assoc, he _ r hi]
    exact ht _ r hi x hx

/-- Clean in the struck form, beside a rule that is empty: clean in the cut form. -/
theorem cut_of_noBad {p b : List Fmt.RoundView → List E} {t : List Fmt.RoundView} (hp : ∀ g, p g = [])
    (h : NoBad b t) : Sound.NoBad (fun g => p g ++ b (strikeLast g)) t := by
  intro i r hi j x hj hm
  simp only [hp, List.nil_append, strikeLast_concat] at hm
  exact h i r hi x (List.mem_of_getElem? hj) hm

theorem listOf_nil {P : K → Prop} (h : ∀ x, ¬ P x) : listOf P = [] :=
  List.eq_nil_of_length_eq_zero
    (Nat.le_zero.mp (listOf_length P 0 (le_of_eq (Prob.cnt_false h))))

/-! ## Behind all its variables a sumcheck's rule is empty -/

theorem movesOf_length (ρ : Reading K) : ∀ (vs : List Var) (l : List (List E × E)) (c : E),
    (movesOf ρ vs l c).length = min vs.length l.length
  | [], _, _ => by simp [movesOf]
  | _ :: _, [], _ => by simp [movesOf]
  | v :: vs, x :: l, c => by
    have ih := movesOf_length ρ vs l
      (Part.MaskedSum.valueAt (Part.MaskedSum.complete v x.1 c) x.2)
    show (movesOf ρ vs l _).length + 1 = min (vs.length + 1) (l.length + 1)
    rw [ih]
    omega

theorem raw_behind (all : List Var) (cvOf : E → K) (bE : K → K → K → Finset K)
    (bd : K → K → K → K → List (K[X] × K) → K[X] → Finset K)
    (hcard : ∀ Tv C m e pre g,
      (bd Tv C m e pre g).card < dAt (all.map (Var.wt Reading.gl)) pre.length)
    (r0 : Fmt.RoundView) (tl : List Fmt.RoundView) (h : all.length + 1 ≤ tl.length) :
    raw all cvOf bE bd (r0 :: tl) = [] := by
  have hne : tl ≠ [] := by
    intro e
    rw [e] at h
    simp at h
  have key : ∀ s : Finset K, s.card < 1 → s.toList.map ofK = [] := by
    intro s hs
    have e : s = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [e, Finset.toList_empty]
    rfl
  rw [raw_cons all cvOf bE bd r0 tl hne]
  apply key
  refine lt_of_lt_of_eq (hcard _ _ _ _ _ _) ?_
  rw [List.length_take, movesOf_length]
  unfold dAt
  rw [List.getElem?_eq_none (by
    unfold roundsOf
    rw [List.length_map, List.length_map]
    omega)]
  rfl

/-! ## "sumcheck z n" at the truth -/

/-- **AT THE TRUTH NO DRAW IS BAD**, of Law/SumLaw.lean's rule. R and c0 are what the part's reading
makes of the rounds t. -/
theorem noBadG_true (z : Point) (n : Nat) (hn : 1 ≤ n) (Sm : List K → K) (sig : K)
    (hS : IsSum ((⟨1, vsG z, some ⟨2, n⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
    (mask : Nat → E) (F0 : Fork) {t : List Fmt.RoundView} {R : Part.MaskedSum.Read} {c0 : E}
    (hread : readAll (kG z n) t = some R) (hlead : leadScalars (kG z n) t = some [c0])
    (hC : cvG mask F0 c0 = sig)
    (hq : ∀ i m, (movesOf Reading.gl (kG z n).all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqG z n hn Sm sig hS mask F0 (rd (tgt c0)) sig (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG z n).all R.rounds (addE R.mu (mulE R.eps (tgt c0)))).take i).map
          (·.2))) :
    NoBad (badG z n hn Sm sig hS mask F0) t := by
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsG z, some ⟨2, n⟩⟩ t = some R from hread)
  obtain ⟨c1, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c1, R.mu] [R.eps] := hs0
  have hc : c1 = c0 := by
    have h1 : leadScalars ⟨1, vsG z, some ⟨2, n⟩⟩ t = some [c0] := hlead
    rw [ht, lead_of_sent hs0'] at h1
    simpa using h1
  subst hc
  have hrv : rv.drawn.elems = [] := List.length_eq_zero_iff.mp hsv.2.2.1
  unfold badG
  refine noBad_of_empty (kG z n).all (cvG mask F0) (bEG z n hn Sm sig hS mask F0)
    (bdG z n hn Sm sig hS mask F0) ht hs0' hvr (allG_d z n) hrv ?_ ?_
  · rw [hC]
    exact bEG_empty z n hn Sm sig hS mask F0 _ _
  · intro i m hm
    rw [hC, hq i m hm]
    exact bdG_empty z n hn Sm sig hS mask F0 _ _ _ _ _

/-! ## "level z start" at the truth -/

section Level
variable (z : Point) (Sm : List K → K) (sig : K)
  (hS : IsSum ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
  (mask : Nat → E) (F0 : Fork) (Tt : E) (Cv : K)

/-- None under Law/Bad.lean's rule at the turned rounds: none under the level's rule. -/
theorem noBad_unmod {t : List Fmt.RoundView}
    (h : NoBad (badL1 z Sm sig hS mask F0 Tt Cv) (modR (tgt Tt) t)) :
    NoBad (badLv z Sm sig hS mask F0 Tt Cv) t := by
  intro i r hi x hx hm
  unfold badLv at hm
  have hm' := List.mem_of_mem_take hm
  cases t with
  | nil => simp at hi
  | cons r0 tl =>
    cases i with
    | zero =>
      have hr : r0 = r := by simpa using hi
      subst hr
      exact h 0 { r0 with vals := .e (tgt Tt).triple :: r0.vals } rfl x hx hm'
    | succ i =>
      have hi' : tl[i]? = some r := by simpa using hi
      have e1 : modR (tgt Tt) ((r0 :: tl).take (i + 1) ++ [{ r with drawn := ⟨[], [], [], none⟩ }])
          = (modR (tgt Tt) (r0 :: tl)).take (i + 1)
            ++ [{ r with drawn := ⟨[], [], [], none⟩ }] := by
        simp [modR, List.take_succ_cons]
      rw [e1] at hm'
      exact h (i + 1) r (by simpa [modR] using hi') x hx hm'

/-- **AT THE TRUTH NO DRAW IS BAD**, of Law/LevelLaw.lean's rule: t: the level's rounds but the
last; line: its last round, whose element nothing reads. -/
theorem noBadLv_true {t : List Fmt.RoundView} {line : Fmt.RoundView} {R : Part.MaskedSum.Read}
    (hread : readAll ⟨0, vsG z, some ⟨2, 2⟩⟩ t = some R)
    (hq : ∀ i m, (movesOf Reading.gl (kG z 2).all R.rounds
        (addE R.mu (mulE R.eps Tt)))[i]? = some m →
      m.1 = tqL z Sm sig hS mask F0 Tt sig (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG z 2).all R.rounds (addE R.mu (mulE R.eps Tt))).take i).map
          (·.2))) :
    NoBad (badLv z Sm sig hS mask F0 Tt sig) (t ++ [line]) := by
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hfr : front = [] := List.length_eq_zero_iff.mp hfl
  subst hfr
  have hs0' : Sent r0 1 1 [R.mu] [R.eps] := hs0
  have hs2 : Sent { r0 with vals := .e (tgt Tt).triple :: r0.vals } 2 1 [tgt Tt, R.mu]
      [R.eps] := by
    obtain ⟨b1, _, b3, b4⟩ := hs0'
    refine ⟨?_, rfl, b3, b4⟩
    show (scalars r0.vals).map (E.ofTriple (tgt Tt).triple :: ·) = _
    rw [b1, E.ofTriple_triple, Option.map_some]
  have hrv : rv.drawn.elems = [] := List.length_eq_zero_iff.mp hsv.2.2.1
  have hL1 : NoBad (badL1 z Sm sig hS mask F0 Tt sig) (modR (tgt Tt) t) := by
    rw [ht]
    show NoBad (badL1 z Sm sig hS mask F0 Tt sig)
      ({ r0 with vals := .e (tgt Tt).triple :: r0.vals } :: (used ++ [rv]))
    unfold badL1
    refine noBad_of_empty (kG z 2).all (fun _ => sig) (fun _ _ => bEL z Sm sig hS mask F0 Tt sig)
      (fun _ _ => bdL z Sm sig hS mask F0 Tt sig) rfl hs2 hvr (allG_d z 2) hrv
      (bEL_empty z Sm sig hS mask F0 Tt _) ?_
    intro i m hm
    simp only [mul_tgt] at hm ⊢
    rw [hq i m hm]
    exact bdL_empty z Sm sig hS mask F0 Tt sig _ _ _
  refine noBad_snoc (noBad_unmod z Sm sig hS mask F0 Tt sig hL1) fun x _ hm => ?_
  unfold badLv at hm
  have hm' := List.mem_of_mem_take hm
  rw [ht] at hm'
  have e : modR (tgt Tt) (r0 :: (used ++ [rv]) ++ [{ line with drawn := ⟨[], [], [], none⟩ }])
      = { r0 with vals := .e (tgt Tt).triple :: r0.vals }
        :: (used ++ [rv] ++ [{ line with drawn := ⟨[], [], [], none⟩ }]) := rfl
  rw [e] at hm'
  unfold badL1 bad at hm'
  have hm'' := List.mem_of_mem_take hm'
  have hlen : used.length = (kG z 2).all.length := hvr.length.1
  rw [raw_behind (kG z 2).all (fun _ => sig) (fun _ _ => bEL z Sm sig hS mask F0 Tt sig)
    (fun _ _ => bdL z Sm sig hS mask F0 Tt sig)
    (fun _ _ m e pre g => (specL z Sm sig hS mask F0 Tt sig).2.2.1 m e pre g) _ _ (by
      simp only [List.length_append, List.length_singleton]
      omega)] at hm''
  simp at hm''

end Level

variable [Sizes] [Policy] [Request] [Token]

/-! ## The norm's rule on its stretches -/

theorem midRule_level (c : NCells) (mask : Nat → E) (pV : Point) (W : Array Hid) (gam : E)
    (Fa : Fork) {Tt : E} (hT : Fa.publicPart (Norm.squaresStart W gam #[]) = some Tt)
    {fr : List Fmt.RoundView} (hle : fr.length ≤ nS pV) :
    midRule c mask pV W gam Fa fr =
      squaresRule c mask Fa pV gam Tt (cvAt mask Fa W gam) fr := by
  unfold midRule
  rw [if_pos hle, hT]
  rfl

theorem midRule_behind (c : NCells) (mask : Nat → E) {pV : Point} {W : Array Hid} {gam : E}
    {Fa Fb : Fork} {tS : List Fmt.RoundView} {S : Sum}
    (h3 : level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []))
    {fr : List Fmt.RoundView} (hne : fr ≠ []) :
    midRule c mask pV W gam Fa (tS ++ fr) = backRule c mask pV Fb fr := by
  have lS : tS.length = nS pV := level_length h3
  have hpos : 0 < fr.length := List.length_pos_iff.mpr hne
  unfold midRule
  rw [if_neg (by rw [List.length_append, lS]; omega), ← lS, List.take_left, List.drop_left, h3]

theorem backRule_past (c : NCells) (mask : Nat → E) (pV : Point) (Fb : Fork) {r2 : Fmt.RoundView}
    {fr : List Fmt.RoundView} (hlen : pV.size + 3 < fr.length) :
    backRule c mask pV Fb (r2 :: fr) = [] := by
  cases fr with
  | nil => simp at hlen
  | cons a tl =>
    show (match sendThenBatch 7 7 Fb [r2] with
      | none => []
      | some ((_, om), Fc, _) =>
        if (a :: tl).length ≤ pV.size + 3 then productsRule c mask Fc pV om (a :: tl) else []) = []
    split
    · rfl
    · exact if_neg (by omega)

/-! ## The truth -/

/-- The squares' level at the truth: each round's completed polynomial is the true one. -/
def SquaresTrue (c : NCells) (mask : Nat → E) (Fa : Fork) (pV : Point) (gam Tt : E)
    (tS : List Fmt.RoundView) : Prop :=
  ∀ R, readAll ⟨0, vsG (zS pV), some ⟨2, 2⟩⟩ (tS.take ((zS pV).size + 3)) = some R →
    ∀ i m, (movesOf Reading.gl (kG (zS pV) 2).all R.rounds
        (addE R.mu (mulE R.eps Tt)))[i]? = some m →
      m.1 = tqL (zS pV) (SmS c mask Fa pV gam) (sigS c pV gam) (hSS c mask Fa pV gam) mask Fa Tt
        (sigS c pV gam) (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG (zS pV) 2).all R.rounds (addE R.mu (mulE R.eps Tt))).take i).map
          (·.2))

/-- "products" at the truth: the claimed sum hides the true sum; each round's completed polynomial
is the true one. -/
def ProductsTrue (c : NCells) (mask : Nat → E) (Fc : Fork) (pV : Point) (om : E)
    (tP : List Fmt.RoundView) : Prop :=
  ∀ R c0, readAll (kG pV 4) tP = some R → leadScalars (kG pV 4) tP = some [c0] →
    cvG mask Fc c0 = sigR c pV om ∧
    ∀ i m, (movesOf Reading.gl (kG pV 4).all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqG pV 4 (by omega) (SmR c mask Fc pV om) (sigR c pV om) (hSR c mask Fc pV om) mask Fc
        (rd (tgt c0)) (sigR c pV om) (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG pV 4).all R.rounds
          (addE R.mu (mulE R.eps (tgt c0)))).take i).map (·.2))

theorem squares_true (c : NCells) (mask : Nat → E) {Fa Fb : Fork} {pV : Point} {gam Tt : E}
    {start : Form} {tS : List Fmt.RoundView} {S : Sum}
    (h3 : level (zS pV) start Fa tS = some (S, Fb, []))
    (hq : SquaresTrue c mask Fa pV gam Tt tS) :
    NoBad (squaresRule c mask Fa pV gam Tt (sigS c pV gam)) tS := by
  have lS : tS.length = (zS pV).size + 4 := level_length h3
  obtain ⟨line, hl⟩ : ∃ line, tS.drop ((zS pV).size + 3) = [line] :=
    List.length_eq_one_iff.mp (by rw [List.length_drop]; omega)
  have e : tS = tS.take ((zS pV).size + 3) ++ [line] := by
    rw [← hl, List.take_append_drop]
  unfold level at h3
  obtain ⟨cs, G1, l1, h1, _⟩ := bind_some h3
  obtain ⟨cc, s⟩ := cs
  obtain ⟨e1, _, _⟩ := heardBy_cut h1
  obtain ⟨ld, Fx, G, hd, es, _, _, _, a4, _⟩ := heardBy_spec e1
  obtain ⟨_, _, R, _, hread, _⟩ := Part.MaskedSum.hear_spec a4
  rw [e]
  exact noBadLv_true (zS pV) _ _ _ mask Fa Tt hread (hq R hread)

theorem products_true (c : NCells) (mask : Nat → E) {Fc G : Fork} {pV : Point} {om : E}
    {tP : List Fmt.RoundView} {S : Sum} (h5 : sumcheck pV 4 Fc tP = some (S, G, []))
    (hq : ProductsTrue c mask Fc pV om tP) : NoBad (productsRule c mask Fc pV om) tP := by
  obtain ⟨ld, cA, Fx, Gx, hd, es, _, a2, _, a4, _⟩ := sumcheck_spec h5
  obtain ⟨_, _, R, _, hread, _⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, _⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsG pV, some ⟨2, 4⟩⟩ tP = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hlead : leadScalars (kG pV 4) tP = some [c0] := by
    rw [ht]
    exact lead_of_sent hs0'
  obtain ⟨hC, hm⟩ := hq R c0 hread hlead
  exact noBadG_true pV 4 (by omega) _ _ _ mask Fc hread hlead hC hm

/-- **THE NORM's ROUNDS AT THE TRUTH**: at the stretches into which the hearing falls. -/
def NormTruth (c : NCells) (mask : Nat → E) (F : Fork) (rs : List Fmt.RoundView) : Prop :=
  (dataOf c).Holds ∧
  ∀ (r0 r1 r2 : Fmt.RoundView) (tS tP left : List Fmt.RoundView) (pV : Point) (W P : Array Hid) (gam om Tt : E)
    (Fa Fb Fc G : Fork) (S Sp : Sum),
    rs = [r0] ++ ([r1] ++ (tS ++ ([r2] ++ (tP ++ left)))) →
    drawPoint lt F [r0] = some (pV, F, []) →
    sendThenBatch 9 9 F [r1] = some ((W, gam), Fa, []) →
    level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []) →
    sendThenBatch 7 7 Fb [r2] = some ((P, om), Fc, []) →
    sumcheck pV 4 Fc tP = some (Sp, G, []) →
    Fa.publicPart (Norm.squaresStart W gam #[]) = some Tt →
    (∀ s, s < 9 → rd (hidden Fa mask (F.next + s)) =
      (dataOf c).sumWAt (Blocks.nat (tupK pV)) 0 s) ∧
    (∀ n, n < 7 → rd (hidden Fc mask (Fb.next + n)) =
      (dataOf c).prodRAt (Blocks.nat (tupK pV)) 0 n) ∧
    cvAt mask Fa W gam = sigS c pV gam ∧
    SquaresTrue c mask Fa pV gam Tt tS ∧ ProductsTrue c mask Fc pV om tP

/-- **AT THE TRUTH NO DRAW OF THE NORM's ROUNDS IS BAD, WHATEVER IS DRAWN.** -/
theorem norm_true (c : NCells) (mask : Nat → E) (F : Fork) (hWL : WellLaid F)
    {rs left : List Fmt.RoundView} {H : Norm.Heard} {G : Fork}
    (hhear : Norm.hear F rs = some (H, G, left)) (ht : NormTruth c mask F rs) :
    Sound.NoBad (normRuleC c mask F) rs := by
  obtain ⟨hH, ht⟩ := ht
  refine cut_of_noBad (p := pointRule c) (b := normRule c mask F) (pointRule_empty c hH) ?_
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _, h3, h4, h5, Wa, _, _⟩ :=
    norm_parts hWL hhear
  obtain ⟨_, Tt, _, _, _, _, hT, _, _⟩ := level_runs _ _ Wa h3
  obtain ⟨r0, rfl⟩ := drawPoint_one h0
  obtain ⟨r1, x1, rfl, _, _, hl1⟩ := batch_one h1
  obtain ⟨r2, x2, rfl, _, _, hl2⟩ := batch_one h4
  obtain ⟨tW, tPr, tC, tS2, tP2⟩ :=
    ht r0 r1 r2 tS tP left H.pV H.W H.P H.gam H.om Tt Fa Fb Fc G H.squares H.products hrs h0 h1 h3
      h4 h5 hT
  have lS : tS.length = nS H.pV := level_length h3
  have lP : tP.length = H.pV.size + 3 := by
    obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec h5
    exact a1
  have n0 : NoBad (normRule c mask F) ([] ++ [r0]) := noBad_one (noBad_nil _) rfl
  have n1 : NoBad (normRule c mask F) ([r0] ++ [r1]) := by
    refine noBad_one n0 ?_
    show (match drawPoint lt F [r0] with
      | none => []
      | some (pV, _, _) => gamRule c mask F pV [{ r1 with drawn := ⟨[], [], [], none⟩ }]) = _
    rw [h0]
    show gamRule c mask F H.pV [{ r1 with drawn := ⟨[], [], [], none⟩ }] = _
    unfold gamRule
    rw [hl1]
    refine listOf_nil ?_
    rintro g ⟨⟨i, hi, s, hs, hne⟩, _⟩
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    apply hne
    show rd (hidden Fa mask (F.next + (9 * 0 + s))) - _ = 0
    rw [Nat.mul_zero, Nat.zero_add, tW s hs, sub_self]
  have n2 : NoBad (normRule c mask F) ([r0, r1] ++ tS) := by
    refine noBad_glue n1 (fun i r hi => ?_) (squares_true c mask h3 tS2)
    have hil : i < tS.length := (List.getElem?_eq_some_iff.mp hi).1
    show normRule c mask F (r0 :: r1 :: (tS.take i ++ [_])) = _
    rw [normRule_mid c mask F h0 h1 (by simp), midRule_level c mask _ _ _ _ hT (by
      rw [List.length_append, List.length_take, List.length_singleton, ← lS]
      omega), tC]
  have n3 : NoBad (normRule c mask F) ([r0, r1] ++ tS ++ [r2]) := by
    refine noBad_one n2 ?_
    show normRule c mask F (r0 :: r1 :: (tS ++ [_])) = _
    rw [normRule_mid c mask F h0 h1 (by simp), midRule_behind c mask h3 (by simp)]
    show omRule c mask Fb H.pV [{ r2 with drawn := ⟨[], [], [], none⟩ }] = _
    unfold omRule
    rw [hl2]
    refine listOf_nil ?_
    rintro g ⟨⟨m, hm, hne⟩, _⟩
    have hm7 : m < 7 := by
      have : m < 7 * 1 := hm
      omega
    apply hne
    show rd (hidden Fc mask (Fb.next + m)) - (dataOf c).prodRAt _ (m / 7) (m % 7) = 0
    rw [Nat.div_eq_of_lt hm7, Nat.mod_eq_of_lt hm7, tPr m hm7, sub_self]
  have n4 : NoBad (normRule c mask F) ([r0, r1] ++ tS ++ [r2] ++ tP) := by
    refine noBad_glue n3 (fun i r hi => ?_) (products_true c mask h5 tP2)
    have hil : i < tP.length := (List.getElem?_eq_some_iff.mp hi).1
    show normRule c mask F (r0 :: r1 :: ((tS ++ [r2]) ++ (tP.take i ++ [_]))) = _
    rw [normRule_mid c mask F h0 h1 (by simp), List.append_assoc,
      midRule_behind c mask h3 (by simp)]
    show backRule c mask H.pV Fb (r2 :: (tP.take i ++ [_])) = _
    rw [backRule_tail c mask H.pV Fb h4 (by simp) (by
      rw [List.length_append, List.length_take, List.length_singleton, ← lP]
      omega)]
  have n5 : NoBad (normRule c mask F) ([r0, r1] ++ tS ++ [r2] ++ tP ++ left) := by
    refine noBad_glue n4 (fun i r _ => ?_) (noBad_none left)
    show normRule c mask F (r0 :: r1 :: (((tS ++ [r2]) ++ tP) ++ (left.take i ++ [_]))) = _
    rw [normRule_mid c mask F h0 h1 (by simp), List.append_assoc, List.append_assoc,
      midRule_behind c mask h3 (by simp)]
    show backRule c mask H.pV Fb (r2 :: (tP ++ (left.take i ++ [_]))) = _
    exact backRule_past c mask H.pV Fb (by
      rw [List.length_append, List.length_append, List.length_singleton, lP]
      omega)
  have e : rs = [r0, r1] ++ tS ++ [r2] ++ tP ++ left := by
    rw [hrs]
    simp
  rw [e]
  exact n5

end VerifiableInference.Desc.Kinds.Head.Law
