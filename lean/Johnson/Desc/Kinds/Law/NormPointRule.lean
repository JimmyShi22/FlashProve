-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormPointRule.lean.
WHAT IT DOES NOT SHOW. No soundness of a protocol. No probability and no sum of errors: how many
written challenges draw a listed element at a place is the carrier's count (CoordMeasure,
RuleErr.lean), not said here. That the reads are true, that the 26 forms are 0, that the world is a
later ledger's: premises, as in Law/NormRule.lean. That an honest run meets these premises: not
shown.
THE RULE's FORM IS ANOTHER FILE's, IMPORTED: Johnson/Desc/Sound/RuleForm.lean: cutTo, strikeLast,
NoBad (written Sound.NoBad here; HeadLaw.lean's own NoBad is its NoBadStruck, letter for letter).
WHAT IT IS. THE POINT pV OF THE NORM's FIRST ROUND, WHICH IS DRAWN IN ONE MESSAGE, AS A RULE WITH A
CEILING, ELEMENT BY ELEMENT. A front here holds the rounds in front, whole, and of the round itself
the message and THE ELEMENTS OF ITS DRAW THAT STAND IN FRONT OF THE ONE ASKED. idFam c: the 17
identities' extensions over the positions, as functions of the point: named by the cells alone.
idFam_deg: degree at most 1 in each coordinate. idFam_alive: if the cells do not hold, some member
is not identically 0. idFam_dies: at a bad point of the bridge (BadP) all members are 0.
pointRule c: at a front of one round: the bad values of the next coordinate behind the coordinates
shown (Alg/Cut.lean's cutFinF: those of the first member that is still alive), as a list of
canonical writings; elsewhere empty. pointRule_length: AT MOST ONE ELEMENT. pointRule_empty: where
the cells hold the rule is empty. point_clean: where no coordinate is in the rule's list at its
front, the point is not bad. normRuleC: that rule beside Law/NormRule.lean's normRule, which looks
at no draw of the last round. normRuleC_length: the same ceiling as normRule's. normRuleC_first,
normRuleC_later: the two rules never speak at one front. norm_blockC: norm_block WITHOUT THE
PREMISE "pV is not bad".
THE COUNTS AND THE CUT ARE CALLED, NOT TYPED AGAIN: Alg/Cut.lean (cutFinF, cutFinF_card_le,
cut_back_family_list, mem_finOf); Alg/Mle.lean (DegLE.mle, exists_mle_ne_zero, mleN_eq_mle,
num_bits); Blocks/EqN.lean (eqN_nat); Blocks/Ext.lean (ext_zero_of_forall). The library's named sets
of bad POINTS with a count (Blocks/LookupRel.lean: BadPt, BadPtFam) are sets of tuples: the form
for a carrier of tuples; this file serves a carrier that asks element by element.

-/
import Mathlib
import Alg.Cut
import Johnson.Desc.Sound.RuleForm
import Johnson.Desc.Kinds.Law.NormRule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)
open Came (val)
open Sound (cutTo strikeLast)

/-! ## A front that is cut in front of an element -/

theorem strikeLast_concat (p : List Fmt.RoundView) (r : Fmt.RoundView) :
    strikeLast (p ++ [r]) = p ++ [cutTo r 0] := by
  simp [strikeLast]

theorem strikeLast_vals (l : List Fmt.RoundView) :
    ((strikeLast l).getLast?.map fun r => r.vals.length) =
      l.getLast?.map fun r => r.vals.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton p r _ =>
    rw [strikeLast_concat]
    simp [cutTo]

/-- A rule that looks at no draw of the last round, beside any other rule: clean in the cut form
gives clean in the struck form (HeadLaw.lean's NoBad). -/
theorem noBad_of_cut {p b : List Fmt.RoundView → List E} {t : List Fmt.RoundView}
    (h : Sound.NoBad (fun g => p g ++ b (strikeLast g)) t) : NoBad b t := by
  intro i r hi x hx hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  refine h i r hi j x hj (List.mem_append_right _ ?_)
  rw [strikeLast_concat]
  exact hm

theorem cut_left {p q : List Fmt.RoundView → List E} {t : List Fmt.RoundView}
    (h : Sound.NoBad (fun g => p g ++ q g) t) : Sound.NoBad p t :=
  fun i r hi j x hj hm => h i r hi j x hj (List.mem_append_left _ hm)

variable [Sizes] [Policy] [Request] [Token]

/-! ## The family on the point -/

/-- Identity number k's extension over the positions, as a function of the point. -/
noncomputable def idFam (c : NCells) (k : Fin 17) (P : Fin lt → K) : K :=
  Blocks.ext lt ((dataOf c).idAt 0 k) (Blocks.nat P)

theorem idFam_mle (c : NCells) (k : Fin 17) :
    idFam c k = Alg.mle fun b : Fin lt → Bool => (dataOf c).idAt 0 k (Alg.num b) := by
  funext P
  rw [← Alg.mleN_eq_mle]
  unfold idFam Blocks.ext Alg.mleN
  exact Finset.sum_congr rfl fun X _ => by rw [Blocks.eqN_nat]

/-- Degree at most 1 in each coordinate. -/
theorem idFam_deg (c : NCells) (k : Fin 17) : Alg.DegLE (fun _ => 1) (idFam c k) := by
  rw [idFam_mle]
  exact Alg.DegLE.mle _

/-- ALIVE: if the cells do not hold, some member is not identically 0. -/
theorem idFam_alive (c : NCells) (h : ¬ (dataOf c).Holds) :
    ∃ (k : Fin 17) (w : Fin lt → K), idFam c k w ≠ 0 := by
  by_contra hno
  refine h fun i hi k hk t ht => ?_
  by_contra hne
  have hi0 : i = 0 := Nat.lt_one_iff.mp hi
  subst hi0
  have ht' : t < 2 ^ lt := ht
  have hu : (fun b : Fin lt → Bool => (dataOf c).idAt 0 k (Alg.num b)) ≠ 0 := by
    intro h0
    have h1 : (dataOf c).idAt 0 k (Alg.num (Alg.bits lt t)) = 0 := congrFun h0 (Alg.bits lt t)
    rw [Alg.num_bits ht'] at h1
    exact hne h1
  obtain ⟨w, hw⟩ := (Alg.exists_mle_ne_zero _).mp hu
  refine hno ⟨⟨k, hk⟩, w, ?_⟩
  rw [idFam_mle]
  exact hw

/-- DIES: at a bad point of the bridge all members are 0. -/
theorem idFam_dies (c : NCells) {P : Fin lt → K} (h : (dataOf c).BadP P) (k : Fin 17) :
    idFam c k P = 0 :=
  h.2 0 Nat.one_pos k k.2

/-- Where the cells hold every member is identically 0. -/
theorem idFam_zero (c : NCells) (h : (dataOf c).Holds) (k : Fin 17) (w : Fin lt → K) :
    idFam c k w = 0 :=
  Blocks.ext_zero_of_forall (fun X hX => h 0 Nat.one_pos k k.2 X hX) _

/-! ## The rule -/

/-- The bad values of the next coordinate behind the coordinates xs, as canonical writings. -/
noncomputable def pointList (c : NCells) (xs : List E) : List E :=
  (Alg.cutFinF (idFam c) (xs.map rd)).toList.map ofK

theorem pointList_length (c : NCells) (xs : List E) : (pointList c xs).length ≤ 1 := by
  unfold pointList
  rw [List.length_map, Finset.length_toList]
  exact Alg.cutFinF_card_le (fun k => idFam_deg c k) (fun _ => 1) (fun _ => le_refl _) _

theorem pointList_empty (c : NCells) (h : (dataOf c).Holds) (xs : List E) :
    pointList c xs = [] := by
  have e : Alg.cutFinF (idFam c) (xs.map rd) = ∅ := by
    refine Finset.not_nonempty_iff_eq_empty.mp ?_
    rintro ⟨t, ht⟩
    obtain ⟨_, m, hm, _⟩ := (Alg.mem_finOf _ _ _).1 ht
    obtain ⟨w, _, hw⟩ := hm.1
    exact hw (idFam_zero c h m w)
  unfold pointList
  rw [e, Finset.toList_empty]
  rfl

/-- **THE RULE OF THE POINT pV**: at a front of one round: behind the elements that it shows. -/
noncomputable def pointRule (c : NCells) : List Fmt.RoundView → List E
  | [r] => pointList c (r.drawn.elems.map E.ofTriple)
  | _ => []

/-- **AT MOST ONE ELEMENT, AT EVERY FRONT.** -/
theorem pointRule_length (c : NCells) (g : List Fmt.RoundView) : (pointRule c g).length ≤ 1 := by
  match g with
  | [] => simp [pointRule]
  | [r] => exact pointList_length c _
  | _ :: _ :: _ => simp [pointRule]

/-- Where the cells hold the rule is empty. -/
theorem pointRule_empty (c : NCells) (h : (dataOf c).Holds) (g : List Fmt.RoundView) :
    pointRule c g = [] := by
  match g with
  | [] => rfl
  | [r] => exact pointList_empty c h _
  | _ :: _ :: _ => rfl

/-- The point as the bridge takes it is the point of the list of what was drawn. -/
theorem tupK_drawn (es : List Fmt.Ext) :
    tupK (es.map E.ofTriple).toArray = Alg.ptOf (es.map fun x => rd (E.ofTriple x)) := by
  funext i
  show ((es.map E.ofTriple).map rd).getD i.1 0 = (es.map fun x => rd (E.ofTriple x)).getD i.1 0
  rw [List.map_map]
  rfl

/-- **Where no coordinate is in the rule's list at its front, the point is not bad.** -/
theorem point_clean (c : NCells) {F G : Fork} {r0 : Fmt.RoundView} {pV : Point}
    (h0 : drawPoint lt F [r0] = some (pV, G, []))
    (hcan : ∀ x, x ∈ r0.drawn.elems → okE (E.ofTriple x) = true)
    (hclean : ∀ j x, r0.drawn.elems[j]? = some x → E.ofTriple x ∉ pointRule c [cutTo r0 j]) :
    ¬ (dataOf c).BadP (tupK pV) := by
  unfold drawPoint at h0
  obtain ⟨y, Fx, lx, a, b⟩ := bind_some h0
  obtain ⟨hp, _, rfl⟩ := pure_some b
  obtain ⟨r, hr, hro⟩ := round_one a
  obtain rfl : r0 = r := by simpa using hr
  obtain ⟨ys, yd⟩ := y
  obtain ⟨_, _, s3, s4⟩ := Part.MaskedSum.roundOf_spec hro
  have hp' : pV = (r0.drawn.elems.map E.ofTriple).toArray := by
    rw [← hp, ← s4]
  intro hP
  rw [hp', tupK_drawn] at hP
  refine hP.1 (Alg.cut_back_family_list (fun x : Fmt.Ext => rd (E.ofTriple x)) (idFam c)
    r0.drawn.elems s3 (In := (dataOf c).Holds)
    (Out := (dataOf c).BadP (Alg.ptOf (r0.drawn.elems.map fun x => rd (E.ofTriple x))))
    (idFam_alive c) (fun h k => idFam_dies c h k) ?_ hP)
  intro xs x ys' hes
  have hj : r0.drawn.elems[xs.length]? = some x := by
    rw [hes, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have h1 := hclean xs.length x hj
  have h2 : pointRule c [cutTo r0 xs.length] =
      (Alg.cutFinF (idFam c) (xs.map fun x => rd (E.ofTriple x))).toList.map ofK := by
    show pointList c ((r0.drawn.elems.take xs.length).map E.ofTriple) = _
    rw [hes, List.take_left]
    unfold pointList
    rw [List.map_map]
    rfl
  rw [h2] at h1
  exact not_mem_of_list (hcan x (by rw [hes]; simp)) h1

/-! ## The norm's whole rule, in the cut form -/

/-- **THE RULE OF THE NORM's OWN ROUNDS, THE POINT WITH THEM.** -/
noncomputable def normRuleC (c : NCells) (mask : Nat → E) (F : Fork) (g : List Fmt.RoundView) : List E :=
  pointRule c g ++ normRule c mask F (strikeLast g)

/-- The ceiling is normRule's: at most the last message's scalars and one. -/
theorem normRuleC_length (c : NCells) (mask : Nat → E) (F : Fork) :
    Ceil (normRuleC c mask F) := by
  intro l
  unfold normRuleC
  rw [List.length_append]
  match l with
  | [] => simp [pointRule, strikeLast, normRule]
  | [r] =>
    have e : strikeLast [r] = [cutTo r 0] := strikeLast_concat [] r
    have e2 : normRule c mask F [cutTo r 0] = [] := rfl
    rw [e, e2]
    have := pointRule_length c [r]
    simp only [List.length_nil]
    omega
  | r :: a :: fr =>
    have e : pointRule c (r :: a :: fr) = [] := rfl
    have h := normRule_length c mask F (strikeLast (r :: a :: fr))
    rw [strikeLast_vals] at h
    rw [e]
    simpa using h

/-- At a front of one round: at most one element, whatever its message. -/
theorem normRuleC_first (c : NCells) (mask : Nat → E) (F : Fork) (r : Fmt.RoundView) :
    (normRuleC c mask F [r]).length ≤ 1 := by
  have e : strikeLast [r] = [cutTo r 0] := strikeLast_concat [] r
  have e2 : normRule c mask F [cutTo r 0] = [] := rfl
  unfold normRuleC
  rw [e, e2, List.append_nil]
  exact pointRule_length c [r]

/-- At a longer front the point's rule is silent: the list is normRule's. -/
theorem normRuleC_later (c : NCells) (mask : Nat → E) (F : Fork) (r a : Fmt.RoundView)
    (fr : List Fmt.RoundView) :
    normRuleC c mask F (r :: a :: fr) = normRule c mask F (strikeLast (r :: a :: fr)) := rfl

section Whole
variable [FinalNorm.In] [FinalNorm.Heard] [FinalNorm.Reads]

/-- **K6's JOINT AT THE NORM's WHOLE HEARING AND AT ONE RULE BY NAME, THE POINT WITH IT.** As
norm_block; no bad event is left as a premise of its own. -/
theorem norm_blockC (c : NCells) (mask : Nat → E) (F : Fork) (hWL : WellLaid F) (hls : ls ≤ lPd)
    (hdS : S2 ∣ d) {rs left : List Fmt.RoundView} {H : Norm.Heard} {G G' : Fork} (W : World K)
    (hcan : Canonical rs) (hhear : Norm.hear F rs = some (H, G, left)) (hL : Later G G')
    (hWs : ∀ j, W.slot j = rd (hidden G' mask j)) (hnb : Sound.NoBad (normRuleC c mask F) rs) :
    let _ : Norm.Heard := H
    NormReads W c → (∀ f, f ∈ Norm.forms → val W f = 0) →
      ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  have hP : ¬ (dataOf c).BadP (tupK H.pV) := by
    obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, Tt, hrs, h0, _⟩ :=
      norm_whole c mask F hWL hls hdS W hcan hhear hL hWs
    obtain ⟨r0, rfl⟩ := drawPoint_one h0
    refine point_clean c h0 (fun x hx => (hcan r0 (by rw [hrs]; simp)).2 x hx) fun j x hj => ?_
    exact cut_left (p := pointRule c) (q := fun g => normRule c mask F (strikeLast g)) hnb 0 r0
      (by rw [hrs]; rfl) j x hj
  exact norm_block c mask F hWL hls hdS W hcan hhear hL hWs
    (noBad_of_cut (p := pointRule c) (b := normRule c mask F) hnb) hP

end Whole

end VerifiableInference.Desc.Kinds.Head.Law
