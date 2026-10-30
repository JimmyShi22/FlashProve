-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormRule.lean.
WHAT IT DOES NOT SHOW. THE POINT pV HAS NO PLACE IN THE RULE: its lt coordinates are drawn in ONE
round, and a rule of this shape sees no coordinate of the round at whose message it stands: "pV is
not bad" (the bridge's BadP: at most lt |K|^(lt - 1) points) stays a premise of its own. That the
reads are true and the 26 forms 0: premises. No sum of the errors is taken.
WHAT IT IS. THE RULE FOR THE BAD ELEMENTS OF THE NORM's OWN ROUNDS, BY NAME, as a function of the
cells, the masks and the ledger in front: normRule: at a front that ends in the message of the nine
sums: the bridge's bad gam, as a list; inside the squares' level: squaresRule at the ledger in front
of it; at the message of the seven products: the bridge's bad om; inside the products' sumcheck:
productsRule; elsewhere empty. normRule_length: at most the last message's scalars and one.
norm_block: Law/NormHear.lean's norm_whole at that one rule.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)
open Came (val ceil_tail noBad_sub)
open Part.MaskedSum (scalars)

/-! ## A set of elements of the field, as a list of canonical writings -/

noncomputable def listOf (P : K → Prop) : List E := by
  classical exact (Finset.univ.filter P).toList.map ofK

theorem listOf_length (P : K → Prop) (n : Nat) (h : Prob.cnt P ≤ n) : (listOf P).length ≤ n := by
  classical
  unfold listOf
  rw [List.length_map, Finset.length_toList]
  unfold Prob.cnt at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  convert h

theorem not_of_listOf {P : K → Prop} {x : E} (hx : okE x = true) (h : x ∉ listOf P) :
    ¬ P (rd x) := by
  classical
  intro hp
  have := not_mem_of_list (s := Finset.univ.filter P) hx (by
    unfold listOf at h
    convert h)
  exact this (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)

variable [Sizes] [Policy] [Request] [Token]

/-- The ledger behind a message of n hidden scalars, off the message alone. -/
def laidBy (n : Nat) (F : Fork) (p : List Fmt.RoundView) : Option Fork :=
  match p with
  | [r] => (scalars r.vals).bind fun v =>
      if v.length = n then (hide v F []).map (·.2.1) else none
  | _ => none

/-- The bad gam, at the message of the nine sums. -/
noncomputable def gamRule (c : NCells) (mask : Nat → E) (F : Fork) (pV : Point)
    (p : List Fmt.RoundView) : List E :=
  match laidBy 9 F p with
  | some Fa => listOf ((dataOf c).BadG (Blocks.nat (tupK pV)) fun s =>
      rd (hidden Fa mask (F.next + s)))
  | none => []

/-- The bad om, at the message of the seven products. -/
noncomputable def omRule (c : NCells) (mask : Nat → E) (Fb : Fork) (pV : Point)
    (p : List Fmt.RoundView) : List E :=
  match laidBy 7 Fb p with
  | some Fc => listOf ((dataOf c).BadO (Blocks.nat (tupK pV)) fun n =>
      rd (hidden Fc mask (Fb.next + n)))
  | none => []

/-- The number of the level's rounds. -/
def nS (pV : Point) : Nat := (zS pV).size + 4

/-- Behind the level: the message of the seven products; then the products' sumcheck; behind that,
nothing. -/
noncomputable def backRule (c : NCells) (mask : Nat → E) (pV : Point) (Fb : Fork) :
    List Fmt.RoundView → List E
  | [] => []
  | [r2] => omRule c mask Fb pV [r2]
  | r2 :: fr =>
    match sendThenBatch 7 7 Fb [r2] with
    | none => []
    | some ((_, om), Fc, _) =>
      if fr.length ≤ pV.size + 3 then productsRule c mask Fc pV om fr else []

/-- Behind gam: the level; then backRule at the ledger behind the level. -/
noncomputable def midRule (c : NCells) (mask : Nat → E) (pV : Point) (W : Array Hid) (gam : E)
    (Fa : Fork) (fr : List Fmt.RoundView) : List E :=
  if fr.length ≤ nS pV then
    squaresRule c mask Fa pV gam ((Fa.publicPart (Norm.squaresStart W gam #[])).getD 0)
      (cvAt mask Fa W gam) fr
  else match level (zS pV) (Norm.squaresStart W gam #[]) Fa (fr.take (nS pV)) with
    | none => []
    | some (_, Fb, _) => backRule c mask pV Fb (fr.drop (nS pV))

/-- **THE RULE OF THE NORM's OWN ROUNDS.** -/
noncomputable def normRule (c : NCells) (mask : Nat → E) (F : Fork) : List Fmt.RoundView → List E
  | [] => []
  | [_] => []
  | [r0, r1] =>
    match drawPoint lt F [r0] with
    | none => []
    | some (pV, _, _) => gamRule c mask F pV [r1]
  | r0 :: r1 :: fr =>
    match drawPoint lt F [r0], sendThenBatch 9 9 F [r1] with
    | some (pV, _, _), some ((W, gam), Fa, _) => midRule c mask pV W gam Fa fr
    | _, _ => []

/-! ## The ceiling -/

theorem laidBy_vals {n : Nat} {F Fa : Fork} {p : List Fmt.RoundView} (h : laidBy n F p = some Fa) :
    ((p.getLast?.map fun r => r.vals.length).getD 0) = n := by
  unfold laidBy at h
  match p, h with
  | [r], h0 =>
    have h : ((scalars r.vals).bind fun v =>
      if v.length = n then (hide v F []).map (·.2.1) else none) = some Fa := h0
    cases hs : scalars r.vals with
    | none => rw [hs] at h; cases h
    | some v =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      by_cases hv : v.length = n
      · simp [← scalars_length _ _ hs, hv]
      · rw [if_neg hv] at h
        cases h

theorem gamRule_length (c : NCells) (mask : Nat → E) (F : Fork) (pV : Point) (p : List Fmt.RoundView) :
    (gamRule c mask F pV p).length ≤ ((p.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold gamRule
  cases hl : laidBy 9 F p with
  | none => simp
  | some Fa =>
    rw [laidBy_vals hl]
    exact le_trans (listOf_length _ 8 (D6.Bridge.cnt_BadG _ _ _)) (by omega)

theorem omRule_length (c : NCells) (mask : Nat → E) (Fb : Fork) (pV : Point) (p : List Fmt.RoundView) :
    (omRule c mask Fb pV p).length ≤ ((p.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold omRule
  cases hl : laidBy 7 Fb p with
  | none => simp
  | some Fc =>
    rw [laidBy_vals hl]
    exact le_trans (listOf_length _ 6 (D6.Bridge.cnt_BadO (dataOf c) _ _)) (by omega)

/-- The ceiling, as a word. -/
def Ceil (b : List Fmt.RoundView → List E) : Prop :=
  ∀ l, (b l).length ≤ ((l.getLast?.map fun r => r.vals.length).getD 0) + 1

theorem ceil_cons {b : List Fmt.RoundView → List E} (hb : Ceil b) (p l : List Fmt.RoundView) :
    (b l).length ≤ (((p ++ l).getLast?.map fun r => r.vals.length).getD 0) + 1 :=
  ceil_tail b hb p l

theorem backRule_length (c : NCells) (mask : Nat → E) (pV : Point) (Fb : Fork) :
    Ceil (backRule c mask pV Fb) := by
  intro l
  match l with
  | [] => simp [backRule]
  | [r2] => exact omRule_length c mask Fb pV [r2]
  | r2 :: a :: fr =>
    show (match sendThenBatch 7 7 Fb [r2] with
      | none => []
      | some ((_, om), Fc, _) =>
        if (a :: fr).length ≤ pV.size + 3 then productsRule c mask Fc pV om (a :: fr)
        else []).length ≤ _
    split
    · simp
    · split
      · exact ceil_cons (productsRule_length c mask _ _ _) [r2] (a :: fr)
      · simp

theorem midRule_length (c : NCells) (mask : Nat → E) (pV : Point) (W : Array Hid) (gam : E)
    (Fa : Fork) : Ceil (midRule c mask pV W gam Fa) := by
  intro l
  unfold midRule
  split
  · exact squaresRule_length c mask _ _ _ _ _ l
  · split
    · simp
    · rename_i _ Fb _ _
      have := ceil_cons (backRule_length c mask pV Fb) (l.take (nS pV)) (l.drop (nS pV))
      rwa [List.take_append_drop] at this

theorem normRule_length (c : NCells) (mask : Nat → E) (F : Fork) : Ceil (normRule c mask F) := by
  intro l
  match l with
  | [] => simp [normRule]
  | [_] => simp [normRule]
  | [r0, r1] =>
    show (match drawPoint lt F [r0] with
      | none => []
      | some (pV, _, _) => gamRule c mask F pV [r1]).length ≤ _
    split
    · simp
    · exact ceil_cons (gamRule_length c mask F _) [r0] [r1]
  | r0 :: r1 :: a :: fr =>
    show (match drawPoint lt F [r0], sendThenBatch 9 9 F [r1] with
      | some (pV, _, _), some ((W, gam), Fa, _) => midRule c mask pV W gam Fa (a :: fr)
      | _, _ => []).length ≤ _
    split
    · exact ceil_cons (midRule_length c mask _ _ _ _) [r0, r1] (a :: fr)
    · simp

/-! ## One round, or so many -/

theorem round_one {n k : Nat} {F G : Fork} {p : List Fmt.RoundView} {x : List E × List E}
    (h : Hear.round n k F p = some (x, G, [])) :
    ∃ r, p = [r] ∧ Part.MaskedSum.roundOf n k r = some x := by
  unfold Hear.round at h
  cases p with
  | nil => cases h
  | cons r tl =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some y =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨r, by rw [h.2.2], by rw [hr, h.1]⟩

theorem drawPoint_one {n : Nat} {F G : Fork} {p : List Fmt.RoundView} {z : Point}
    (h : drawPoint n F p = some (z, G, [])) : ∃ r, p = [r] := by
  unfold drawPoint at h
  obtain ⟨x, Fx, lx, a, b⟩ := bind_some h
  obtain ⟨_, _, rfl⟩ := pure_some b
  obtain ⟨r, hr, _⟩ := round_one a
  exact ⟨r, hr⟩

/-- A batching round is one round; it draws one element; and the ledger behind it can be read off
its message alone. -/
theorem batch_one {n rows : Nat} {F Fa : Fork} {p : List Fmt.RoundView} {A : Array Hid} {g : E}
    (h : sendThenBatch n rows F p = some ((A, g), Fa, [])) :
    ∃ r x, p = [r] ∧ r.drawn.elems = [x] ∧ E.ofTriple x = g ∧
      laidBy n F [{ r with drawn := ⟨[], [], [], none⟩ }] = some Fa := by
  unfold sendThenBatch at h
  obtain ⟨vg, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨v, gs⟩ := vg
  dsimp only at k1
  obtain ⟨A', F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨hg, rfl, rfl⟩ := need_some h3
  obtain ⟨e, rfl, rfl⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hF : F = F1 := Came.round_some h1
  subst hF
  obtain ⟨rfl, h2'⟩ := hide_some h2
  obtain ⟨r, rfl, hr⟩ := round_one h1
  obtain ⟨s1, s2, s3, s4⟩ := Part.MaskedSum.roundOf_spec hr
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp s3
  refine ⟨r, x, rfl, hx, ?_, ?_⟩
  · rw [s4, hx] at hg
    simpa using hg
  · show ((scalars r.vals).bind fun v =>
      if v.length = n then (hide v F []).map (·.2.1) else none) = some F2
    rw [s1]
    simp only [Option.bind_some]
    rw [if_pos s2, h2']
    rfl

theorem level_length {z : Point} {start : Form} {F G : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hlev : level z start F t = some (S, G, [])) : t.length = z.size + 4 := by
  unfold level at hlev
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some hlev
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨_, _, rfl⟩ := pure_some k3
  obtain ⟨_, e2, e3⟩ := Came.heardBy_cut h1
  obtain ⟨r, hr, _⟩ := round_one h2
  have := congrArg List.length (e2.symm.trans hr)
  rw [List.length_drop, List.length_singleton] at this
  omega

/-! ## The rule at a front -/

theorem normRule_mid (c : NCells) (mask : Nat → E) (F : Fork) {r0 r1 : Fmt.RoundView} {pV : Point}
    {W : Array Hid} {gam : E} {Fa : Fork} (h0 : drawPoint lt F [r0] = some (pV, F, []))
    (h1 : sendThenBatch 9 9 F [r1] = some ((W, gam), Fa, [])) {fr : List Fmt.RoundView} (hne : fr ≠ []) :
    normRule c mask F (r0 :: r1 :: fr) = midRule c mask pV W gam Fa fr := by
  cases fr with
  | nil => exact absurd rfl hne
  | cons a tl =>
    show (match drawPoint lt F [r0], sendThenBatch 9 9 F [r1] with
      | some (pV, _, _), some ((W, gam), Fa, _) => midRule c mask pV W gam Fa (a :: tl)
      | _, _ => []) = _
    rw [h0, h1]

theorem backRule_tail (c : NCells) (mask : Nat → E) (pV : Point) (Fb : Fork) {r2 : Fmt.RoundView}
    {P : Array Hid} {om : E} {Fc : Fork} (h4 : sendThenBatch 7 7 Fb [r2] = some ((P, om), Fc, []))
    {fr : List Fmt.RoundView} (hne : fr ≠ []) (hle : fr.length ≤ pV.size + 3) :
    backRule c mask pV Fb (r2 :: fr) = productsRule c mask Fc pV om fr := by
  cases fr with
  | nil => exact absurd rfl hne
  | cons a tl =>
    show (match sendThenBatch 7 7 Fb [r2] with
      | none => []
      | some ((_, om), Fc, _) =>
        if (a :: tl).length ≤ pV.size + 3 then productsRule c mask Fc pV om (a :: tl) else []) = _
    rw [h4]
    exact if_pos hle

/-! ## The law at the rule -/

section Whole
variable [FinalNorm.In] [FinalNorm.Heard] [FinalNorm.Reads]

/-- **K6's JOINT AT THE NORM's WHOLE HEARING AND AT ONE RULE BY NAME.** rs: rounds that BEGIN with
the norm's own; what lies behind them (left) is another part's. -/
theorem norm_block (c : NCells) (mask : Nat → E) (F : Fork) (hWL : WellLaid F) (hls : ls ≤ lPd)
    (hdS : S2 ∣ d) {rs left : List Fmt.RoundView} {H : Norm.Heard} {G G' : Fork} (W : World K)
    (hcan : Canonical rs) (hhear : Norm.hear F rs = some (H, G, left)) (hL : Later G G')
    (hWs : ∀ j, W.slot j = rd (hidden G' mask j)) (hnb : NoBad (normRule c mask F) rs)
    (hP : ¬ (dataOf c).BadP (tupK H.pV)) :
    let _ : Norm.Heard := H
    NormReads W c → (∀ f, f ∈ Norm.forms → val W f = 0) →
      ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, Tt, hrs, h0, h1, h3, h4, h5, hT, main⟩ :=
    norm_whole c mask F hWL hls hdS W hcan hhear hL hWs
  intro _ hreads hforms
  obtain ⟨r0, rfl⟩ := drawPoint_one h0
  obtain ⟨r1, x1, rfl, hx1, hg1, hl1⟩ := batch_one h1
  obtain ⟨r2, x2, rfl, hx2, hg2, hl2⟩ := batch_one h4
  have lS : tS.length = nS H.pV := level_length h3
  have lP : tP.length = H.pV.size + 3 := by
    obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec h5
    exact a1
  have hmidS : ∀ fr : List Fmt.RoundView, fr.length ≤ nS H.pV →
      midRule c mask H.pV H.W H.gam Fa fr =
        squaresRule c mask Fa H.pV H.gam Tt (cvAt mask Fa H.W H.gam) fr := by
    intro fr hle
    unfold midRule
    rw [if_pos hle, hT]
    rfl
  have hmidB : ∀ fr : List Fmt.RoundView, fr ≠ [] →
      midRule c mask H.pV H.W H.gam Fa (tS ++ fr) = backRule c mask H.pV Fb fr := by
    intro fr hne
    have hpos : 0 < fr.length := List.length_pos_iff.mpr hne
    unfold midRule
    rw [if_neg (by rw [List.length_append, lS]; omega), ← lS, List.take_left, List.drop_left, h3]
  -- gam
  have hG : ¬ (dataOf c).BadG (Blocks.nat (tupK H.pV))
      (fun s => rd (hidden Fa mask (F.next + s))) (rd H.gam) := by
    have h := hnb 1 r1 (by rw [hrs]; rfl) x1 (by rw [hx1]; exact List.mem_singleton.mpr rfl)
    have e : rs.take 1 = [r0] := by rw [hrs]; rfl
    rw [e, hg1] at h
    have e2 : normRule c mask F ([r0] ++ [{ r1 with drawn := ⟨[], [], [], none⟩ }]) =
        listOf ((dataOf c).BadG (Blocks.nat (tupK H.pV)) fun s =>
          rd (hidden Fa mask (F.next + s))) := by
      show (match drawPoint lt F [r0] with
        | none => []
        | some (pV, _, _) => gamRule c mask F pV [{ r1 with drawn := ⟨[], [], [], none⟩ }]) = _
      rw [h0]
      show gamRule c mask F H.pV [{ r1 with drawn := ⟨[], [], [], none⟩ }] = _
      unfold gamRule
      rw [hl1]
    rw [e2] at h
    refine not_of_listOf ?_ h
    rw [← hg1]
    exact (hcan r1 (by rw [hrs]; simp)).2 x1 (by rw [hx1]; exact List.mem_singleton.mpr rfl)
  -- the level
  have hbS : NoBad (squaresRule c mask Fa H.pV H.gam Tt (cvAt mask Fa H.W H.gam)) tS := by
    have hnb' : NoBad (normRule c mask F) ([r0, r1] ++ tS ++ ([r2] ++ (tP ++ left))) := by
      have e : [r0, r1] ++ tS ++ ([r2] ++ (tP ++ left)) = rs := by rw [hrs]; simp
      rw [e]
      exact hnb
    refine noBad_sub (fun i r hi => ?_) hnb'
    have hil : i < tS.length := (List.getElem?_eq_some_iff.mp hi).1
    show normRule c mask F (r0 :: r1 :: (tS.take i ++ [_])) = _
    rw [normRule_mid c mask F h0 h1 (by simp), hmidS _ (by
      rw [List.length_append, List.length_take, List.length_singleton, ← lS]
      omega)]
  -- om
  have hO : ¬ (dataOf c).BadO (Blocks.nat (tupK H.pV))
      (fun n => rd (hidden Fc mask (Fb.next + n))) (rd H.om) := by
    have hidx : rs[2 + tS.length]? = some r2 := by
      rw [hrs]
      show (r0 :: r1 :: (tS ++ (r2 :: (tP ++ left))))[2 + tS.length]? = _
      rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_append_right (le_refl _), Nat.sub_self]
      rfl
    have h := hnb (2 + tS.length) r2 hidx x2 (by rw [hx2]; exact List.mem_singleton.mpr rfl)
    have e : rs.take (2 + tS.length) = r0 :: r1 :: tS := by
      rw [hrs]
      show (r0 :: r1 :: (tS ++ (r2 :: (tP ++ left)))).take (2 + tS.length) = _
      rw [Nat.add_comm, List.take_succ_cons, List.take_succ_cons, List.take_left]
    rw [e, hg2] at h
    have e2 : normRule c mask F (r0 :: r1 :: tS ++ [{ r2 with drawn := ⟨[], [], [], none⟩ }]) =
        listOf ((dataOf c).BadO (Blocks.nat (tupK H.pV)) fun n =>
          rd (hidden Fc mask (Fb.next + n))) := by
      show normRule c mask F (r0 :: r1 :: (tS ++ [_])) = _
      rw [normRule_mid c mask F h0 h1 (by simp), hmidB _ (by simp)]
      show omRule c mask Fb H.pV [{ r2 with drawn := ⟨[], [], [], none⟩ }] = _
      unfold omRule
      rw [hl2]
    rw [e2] at h
    refine not_of_listOf ?_ h
    rw [← hg2]
    exact (hcan r2 (by rw [hrs]; simp)).2 x2 (by rw [hx2]; exact List.mem_singleton.mpr rfl)
  -- the sumcheck
  have hbP : NoBad (productsRule c mask Fc H.pV H.om) tP := by
    have hnb' : NoBad (normRule c mask F) ((r0 :: r1 :: tS ++ [r2]) ++ tP ++ left) := by
      have e : (r0 :: r1 :: tS ++ [r2]) ++ tP ++ left = rs := by rw [hrs]; simp
      rw [e]
      exact hnb
    refine noBad_sub (fun i r hi => ?_) hnb'
    have hil : i < tP.length := (List.getElem?_eq_some_iff.mp hi).1
    show normRule c mask F (r0 :: r1 :: ((tS ++ [r2]) ++ (tP.take i ++ [_]))) = _
    rw [normRule_mid c mask F h0 h1 (by simp), List.append_assoc, hmidB _ (by simp)]
    show backRule c mask H.pV Fb (r2 :: (tP.take i ++ [_])) = _
    rw [backRule_tail c mask H.pV Fb h4 (by simp) (by
      rw [List.length_append, List.length_take, List.length_singleton, ← lP]
      omega)]
  exact main hreads hforms hbS hbP hP hG hO

end Whole

end VerifiableInference.Desc.Kinds.Head.Law
