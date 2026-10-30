-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LevelLaw.lean: THE LAW OF HeadParts.lean's "level z start", WITH ITS LETTERS FREE: a masked sumcheck of
a sum that the prover does not send: start is the form that it must equal; two end values; a last round
"LINE" in which one element is drawn. For any point z, any form start and ANY summand Sm that is summed over
the call's variables (the further variable last) to sig (IsSum). Fixed first, as sound_hear_true fixes
them: Tt: the start's public part at the ledger in front; Cv: the start's value at the hidden scalars. There is
a rule from the front of a transcript to a short list of bad elements such that: at a hearing that returns, in a
world whose slots hold the hidden scalars at the level's own numbers and in which start is worth Cv, with the
level's own form 0, the summand at the challenges equal to the summand S0 on the end values as shown, and no bad
draw: Cv = sig: THE START FORM IS WORTH THE SUM.
THE SUMCHECK IS NOT PROVED HERE: sound_hear_true (its bad sets empty at the truth), at a call without a
lead. The proof goes as Law/SumLaw.lean's coreG.
A DEVICE OF THE RULE: the rule of Law/Bad.lean and its two bridges are typed for a first message of two scalars:
the caller's lead, then mu. A level's first message holds mu alone. modR lays one public scalar (the start's
public part, written canonically) in front of the first round's message; the level's rule is that at the
front so turned, cut to the statement's ceiling. So these bridges are called, not typed again.
THE LAST ROUND's ELEMENT has no bad value: nothing here reads it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SumLaw
import Johnson.Desc.Kinds.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E zeroE oneE addE mulE subE okE invE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open OnBytes.Desc.First.P1 (mle tot ext1 IsSum dAt)
open Part.MaskedSum (Var Call Ends Read Sent movesOf ownSlots scalars readAll shapeOk rowForm rowLaid
  row challenges leadScalars weightsOf)

/-! ## 1. The device -/

/-- One scalar laid in front of the first round's message. -/
def modR (c0 : E) : List Fmt.RoundView → List Fmt.RoundView
  | [] => []
  | r0 :: tl => { r0 with vals := .e c0.triple :: r0.vals } :: tl

theorem modR_length (c0 : E) (l : List Fmt.RoundView) : (modR c0 l).length = l.length := by
  cases l <;> rfl

theorem rd_tgt (x : E) : rd (tgt x) = rd x := by
  unfold tgt
  show Reading.gl.val _ = _
  rw [Reading.gl.add, Reading.gl.mul, Reading.gl.zero, Reading.gl.one]
  show (0 : K) + 1 * rd x = rd x
  ring

theorem okE_tgt (x : E) : okE (tgt x) = true := okE_addE _ _

theorem mul_tgt (e x : E) : mulE e (tgt (tgt x)) = mulE e x := by
  apply eq_of_rd (okE_mulE _ _) (okE_mulE _ _)
  show Reading.gl.val _ = Reading.gl.val _
  rw [Reading.gl.mul, Reading.gl.mul]
  show _ * rd (tgt (tgt x)) = _ * rd x
  rw [rd_tgt, rd_tgt]

/-- The statement's ceiling at a front. -/
def ceilOf (h : List Fmt.RoundView) : Nat := ((h.getLast?.map fun r => r.vals.length).getD 0) + 1

/-! ## 2. The ledger behind two runs of layings -/

theorem hidden_vals0 {F0 G F1 : Fork} {beta : E} {own : Nat} {vals : Array E} {n2 : Nat}
    (mask : Nat → E) (hW : WellLaid F0)
    (r2 : ({ F0 with next := n2 } : Fork).hideRun (F0.next + own) vals beta = some G)
    (r3 : G.hideRun F0.next (Array.replicate own zeroE) (subE zeroE oneE) = some F1) :
    (∀ i, i < own → rd (hidden F1 mask (F0.next + i)) = rd (mask (F0.next + i))) ∧
    (∀ j, j < vals.size → rd (hidden F1 mask (F0.next + own + j))
      = rd (F1.vp.getD (F0.next + own + j) zeroE) - rd beta * rd (mask (F0.next + own + j))) := by
  obtain ⟨w2, _, _, v2, m2⟩ := hideRun_frame (F := { F0 with next := n2 }) hW r2
  obtain ⟨_, _, _, v3, m3⟩ := hideRun_frame w2 r3
  have s3 : (Array.replicate own zeroE).size = own := Array.size_replicate
  refine ⟨?_, ?_⟩
  · intro i hi
    unfold hidden
    rw [v3, m3, if_pos (by rw [s3]; omega), if_pos (by rw [s3]; omega), rd_sub, rd_mul, rd_neg_one]
    have : (Array.replicate own zeroE).toList.getD (F0.next + i - F0.next) (0 : E) = zeroE := by
      have hi' : F0.next + i - F0.next = i := by omega
      rw [hi', Array.toList_replicate, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos hi]
      rfl
    rw [this]
    show Reading.gl.val zeroE - _ = _
    rw [Reading.gl.zero]
    ring
  · intro j hj
    unfold hidden
    rw [m3, if_neg (by rw [s3]; omega), m2, if_pos (by omega), rd_sub, rd_mul]
    have : F1.vp.getD (F0.next + own + j) (0 : E) = F1.vp.getD (F0.next + own + j) zeroE := by
      rw [v3, v3, if_neg (by rw [s3]; omega), if_neg (by rw [s3]; omega), v2, v2,
        if_pos (by omega), if_pos (by omega)]
      have hlt : F0.next + own + j - (F0.next + own) < vals.toList.length := by
        rw [Array.length_toList]; omega
      rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt]
    rw [this]

/-! ## 3. The rule -/

section Gen
variable (z : Point)

theorem shapeL : shapeOk ⟨0, vsG z, some ⟨2, 2⟩⟩ = true := shapeG z 2 (by omega)

variable (Sm : List K → K) (sig : K)
  (hS : IsSum ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
  (mask : Nat → E) (F0 : Fork) (Tt : E) (Cv : K)

/-- The number of the first end value: a level has no lead. -/
def sEndL : Nat := F0.next + ownG z 2
def hcoefL (i : Nat) : K := rd (mask (F0.next + i))

def SHL := Part.MaskedSum.sound_hear_true Reading.gl 0 (vsG z) ⟨2, 2⟩ (shapeL z)
  (hcoefL mask F0) Sm sig hS (rd Tt) Cv

def bEL : K → Finset K := Classical.choose (Classical.choose_spec (SHL z Sm sig hS mask F0 Tt Cv))
def tqL : K → K → List K → K[X] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (SHL z Sm sig hS mask F0 Tt Cv)))
def bdL : K → K → List (K[X] × K) → K[X] → Finset K :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (SHL z Sm sig hS mask F0 Tt Cv))))
def specL := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (SHL z Sm sig hS mask F0 Tt Cv))))

/-- Law/Bad.lean's rule at the sets of this call, which look at neither of its first two letters. -/
def badL1 : List Fmt.RoundView → List E :=
  bad (kG z 2).all (fun _ => Cv) (fun _ _ => bEL z Sm sig hS mask F0 Tt Cv)
    (fun _ _ => bdL z Sm sig hS mask F0 Tt Cv)

/-- **The rule.** -/
def badLv (h : List Fmt.RoundView) : List E :=
  (badL1 z Sm sig hS mask F0 Tt Cv (modR (tgt Tt) h)).take (ceilOf h)

theorem badLv_length (h : List Fmt.RoundView) : (badLv z Sm sig hS mask F0 Tt Cv h).length
    ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := List.length_take_le _ _

/-- **Empty at the truth.** -/
theorem bEL_empty (mu : K) : bEL z Sm sig hS mask F0 Tt sig mu = ∅ :=
  (specL z Sm sig hS mask F0 Tt sig).2.2.2.2.1 rfl mu

theorem bdL_empty (mu eps : K) (pre : List (K[X] × K)) :
    bdL z Sm sig hS mask F0 Tt Cv mu eps pre
      (tqL z Sm sig hS mask F0 Tt Cv mu eps (pre.map (·.2))) = ∅ :=
  (specL z Sm sig hS mask F0 Tt Cv).2.2.2.2.2.1 mu eps pre

/-- No bad draw under the level's rule: none under Law/Bad.lean's at the turned rounds. -/
theorem noBad_mod {t : List Fmt.RoundView} (hnb : NoBad (badLv z Sm sig hS mask F0 Tt Cv) t) :
    NoBad (badL1 z Sm sig hS mask F0 Tt Cv) (modR (tgt Tt) t) := by
  intro i r hi x hx
  cases t with
  | nil => simp [modR] at hi
  | cons r0 tl =>
    cases i with
    | zero =>
      have hr : r = { r0 with vals := .e (tgt Tt).triple :: r0.vals } := by
        simpa [modR] using hi.symm
      subst hr
      have h0 := hnb 0 r0 rfl x hx
      simp only [List.take_zero, List.nil_append] at h0 ⊢
      unfold badLv at h0
      -- the list at a front of one round has at most one member
      have hlen : (badL1 z Sm sig hS mask F0 Tt Cv
          (modR (tgt Tt) [{ r0 with drawn := ⟨[], [], [], none⟩ }])).length ≤ 1 := by
        unfold badL1 bad
        refine le_trans (List.length_take_le' _ _) ?_
        show ((bEL z Sm sig hS mask F0 Tt Cv _).toList.map ofK).length ≤ 1
        rw [List.length_map, Finset.length_toList]
        exact (specL z Sm sig hS mask F0 Tt Cv).2.1 _
      rw [List.take_of_length_le (le_trans hlen (by unfold ceilOf; omega))] at h0
      exact h0
    | succ i =>
      have hi' : tl[i]? = some r := by simpa [modR] using hi
      have h0 := hnb (i + 1) r (by simpa using hi') x hx
      unfold badLv at h0
      have e1 : modR (tgt Tt) ((r0 :: tl).take (i + 1) ++ [{ r with drawn := ⟨[], [], [], none⟩ }])
          = (modR (tgt Tt) (r0 :: tl)).take (i + 1) ++ [{ r with drawn := ⟨[], [], [], none⟩ }] := by
        simp [modR, List.take_succ_cons]
      have e2 : ceilOf ((r0 :: tl).take (i + 1) ++ [{ r with drawn := ⟨[], [], [], none⟩ }])
          = ceilOf ((modR (tgt Tt) (r0 :: tl)).take (i + 1)
            ++ [{ r with drawn := ⟨[], [], [], none⟩ }]) := by
        unfold ceilOf
        rw [List.getLast?_append, List.getLast?_append]
        rfl
      rw [e1, e2] at h0
      have h00 : (badL1 z Sm sig hS mask F0 Tt Cv ((modR (tgt Tt) (r0 :: tl)).take (i + 1)
            ++ [{ r with drawn := ⟨[], [], [], none⟩ }])).take
          (ceilOf ((modR (tgt Tt) (r0 :: tl)).take (i + 1)
            ++ [{ r with drawn := ⟨[], [], [], none⟩ }]))
          = badL1 z Sm sig hS mask F0 Tt Cv ((modR (tgt Tt) (r0 :: tl)).take (i + 1)
            ++ [{ r with drawn := ⟨[], [], [], none⟩ }]) :=
        List.take_of_length_le (bad_length _ _ _ _ _)
      rw [h00] at h0
      exact h0

end Gen

theorem noBad_take {bad' : List Fmt.RoundView → List E} {t : List Fmt.RoundView} (n : Nat) (h : NoBad bad' t) :
    NoBad bad' (t.take n) := by
  intro i r hi x hx
  rw [List.getElem?_take] at hi
  split at hi
  · rename_i hin
    have h0 := h i r hi x hx
    rw [List.take_take, Nat.min_eq_left (le_of_lt hin)]
    exact h0
  · cases hi

theorem canonical_take {t : List Fmt.RoundView} (n : Nat) (h : Canonical t) : Canonical (t.take n) :=
  fun r hr => h r (List.mem_of_mem_take hr)

theorem canonical_mod {c0 : E} (hc : okE c0 = true) {t : List Fmt.RoundView} (h : Canonical t) :
    Canonical (modR c0 t) := by
  cases t with
  | nil => exact h
  | cons r0 tl =>
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr'
    · refine ⟨fun x hx => ?_, (h r0 (by simp)).2⟩
      rcases List.mem_cons.1 hx with hx | hx
      · have e : x = c0.triple := by injection hx
        rw [e, E.ofTriple_triple]
        exact hc
      · exact (h r0 (by simp)).1 x hx
    · exact h r (List.mem_cons_of_mem _ hr')

theorem lead0_of_sent {r0 : Fmt.RoundView} {tl : List Fmt.RoundView} {mu eps : E} {vs : List Var}
    {e : Option Ends} (h : Sent r0 1 1 [mu] [eps]) :
    leadScalars ⟨0, vs, e⟩ (r0 :: tl) = some [] := by
  obtain ⟨h1, _, h3, _⟩ := h
  simp [leadScalars, Part.MaskedSum.firstRound, Part.MaskedSum.roundOf, h1, h3]

theorem round_some {n k : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {x : List E × List E}
    (h : Hear.round n k F rs = some (x, G, left)) : F = G := by
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.1

section Law
variable (z : Point) (Sm : List K → K) (sig : K)
  (hS : IsSum ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
  (mask : Nat → E) (F0 : Fork) (Tt : E) (Cv : K)

/-- **THE LAW OF "level z start".** -/
theorem coreL (start : Form) (hWL : WellLaid F0) {F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (W : World K)
    (hWs : ∀ j, F0.next ≤ j → j < sEndL z F0 + 2 → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t) (hlev : level z start F0 t = some (S, F1, []))
    (hT : F0.publicPart start = some Tt) (hC : vW W start = Cv) (S0 : E)
    (g1 : vW W (S.left S0) = 0)
    (gS : ∀ β : K, (∀ j, j < 2 → rd (S.end_ j).shown
        = vW W (S.end_ j).var + β * rd (mask (sEndL z F0 + j))) →
      Sm (S.r.toList.map rd ++ [β]) = rd S0)
    (hnb : NoBad (badLv z Sm sig hS mask F0 Tt Cv) t) :
    Cv = sig := by
  unfold level at hlev
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some hlev
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  have hG : G1 = G2 := round_some h2
  subst hG
  obtain ⟨e1, _, _⟩ := heardBy_cut h1
  obtain ⟨ld, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hs⟩ := heardBy_spec e1
  have hk : callOf 0 z 2 = ⟨0, vsG z, some ⟨2, 2⟩⟩ := rfl
  rw [hk] at a2 a4 hs
  obtain ⟨_, Tt', R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hfr : front = [] := List.length_eq_zero_iff.mp hfl
  subst hfr
  have hs0' : Sent r0 1 1 [R.mu] [R.eps] := hs0
  have hld : ld = [] := by
    rw [ht, lead0_of_sent hs0'] at a2
    exact (Option.some.inj a2).symm
  subst hld
  obtain ⟨run1, _⟩ := hide_unfold a3
  have hFa : Fa = F0 := by
    have h0 : ({ F0 with next := F0.next + ([] : List E).length } : Fork).hideRun F0.next
        ([] : List E).toArray oneE = some F0 := by
      simp [Fork.hideRun]
    rw [h0] at run1
    exact (Option.some.inj run1).symm
  subst hFa
  have hTt : Tt' = Tt := by
    rw [hT] at hpub
    exact (Option.some.inj hpub).symm
  subst hTt
  have hlenR : R.rounds.length = (kG z 2).all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt ((kG z 2).all.zip (R.rounds.map (·.2)))).1.length
      = ownG z 2 := by
    have hz : ((kG z 2).all.zip (R.rounds.map (·.2))).map (·.1) = (kG z 2).all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsG z ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ (kG z 2).all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allG_d z 2 _ this]; omega
  have run3 : G.hideRun Fa.next (Array.replicate (ownG z 2) zeroE) (subE zeroE oneE) = some G1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    have hlen' : (Part.MaskedSum.hidingAt ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Call).all.zip
        (R.rounds.map (·.2)))).1.length = ownG z 2 := hlen
    rw [hlen'] at h5
    exact h5
  obtain ⟨V2, V3⟩ := hidden_vals0 (own := ownG z 2) mask hWL hrun2 run3
  have hfirst : hd.first = Fa.next := by rw [hhd]
  have hsEnd : hd.sEnd = sEndL z Fa := by rw [hhd]; rfl
  rw [hsEnd] at a6
  have hend : ∀ j, j < 2 → s.end_ j
      = (⟨Aff.slot (sEndL z Fa + j), G1.vp.getD (sEndL z Fa + j) zeroE⟩ : Hid) := by
    intro j hj
    rw [hs]
    exact hiddenFrom_get a6 j hj
  have hvs : R.values.toArray.size = 2 := by
    rw [List.size_toArray]; exact hsv.2.1
  have hallLen : (kG z 2).all.length = (vsG z).length + 1 := by
    show (vsG z ++ [Var.point zeroE 3]).length = _
    simp
  have hrlen : hd.r.length = (vsG z).length + 1 := by
    rw [hhd]
    show (R.rounds.map (·.2)).length = _
    rw [List.length_map, hlenR, hallLen]
  have hbeta : hd.r.getLastD zeroE = (R.rounds.map (·.2)).getLastD zeroE := by rw [hhd]
  have hrsplit : hd.r = challenges (kG z 2) hd ++ [(R.rounds.map (·.2)).getLastD zeroE] := by
    rw [← hbeta]
    exact take_append_last hd.r (vsG z).length zeroE hrlen
  have hSr : s.r = (challenges (kG z 2) hd).toArray := by rw [hs]; rfl
  have hrl : s.r.toList.map rd = (challenges (kG z 2) hd).map rd := by rw [hSr]
  obtain ⟨_, _, _, main, _⟩ := specL z Sm sig hS mask Fa Tt' Cv
  have hleft : ∀ x, s.left x = rowForm hd x {} := by
    intro x; rw [hs]; rfl
  -- the turned rounds
  have ht2 : modR (tgt Tt') (t.take (z.size + 3))
      = { r0 with vals := .e (tgt Tt').triple :: r0.vals } :: (used ++ [rv]) := by
    rw [ht]; rfl
  have hs2 : Sent { r0 with vals := .e (tgt Tt').triple :: r0.vals } 2 1 [tgt Tt', R.mu] [R.eps] := by
    obtain ⟨b1, _, b3, b4⟩ := hs0'
    refine ⟨?_, rfl, b3, b4⟩
    show (scalars r0.vals).map (E.ofTriple (tgt Tt').triple :: ·) = _
    rw [b1, E.ofTriple_triple, Option.map_some]
  have hcan2 : Canonical (modR (tgt Tt') (t.take (z.size + 3))) :=
    canonical_mod (okE_tgt _) (canonical_take _ hcan)
  have hnb2 := noBad_mod z Sm sig hS mask Fa Tt' Cv (noBad_take (z.size + 3) hnb)
  refine main W start Fa G (t.take (z.size + 3)) hd R S0 {} G G1 (rowForm hd S0 {}) a4 hread
    ?_ hC ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hhd]; rfl
  · intro i hi
    have hi' : i < ownG z 2 := hi
    rw [hfirst, hWs _ (by omega) (by unfold sEndL; omega)]; exact V2 i hi
  · rw [row_eq, a5]; rfl
  · rw [← hleft]; exact g1
  · rw [hrsplit, List.map_append, Aff.value_empty, add_zero]
    show Sm ((challenges (kG z 2) hd).map rd ++ [rd ((R.rounds.map (·.2)).getLastD zeroE)]) = rd _
    rw [← hrl]
    apply gS
    intro j hj
    show rd (s.end_ j).shown = vW W (s.end_ j).var + _
    rw [hend j hj]
    show rd (G1.vp.getD (sEndL z Fa + j) zeroE) = vW W (Aff.slot _) + _
    rw [vW_slot, hWs _ (by unfold sEndL; omega) (by omega)]
    have hV3 := V3 j (by rw [hvs]; exact hj)
    show _ = rd (hidden G1 mask (Fa.next + ownG z 2 + j)) + _ * rd (mask (Fa.next + ownG z 2 + j))
    rw [hV3]
    show rd (G1.vp.getD (Fa.next + ownG z 2 + j) zeroE) = _
    ring
  · exact bridge_eps ht2 hs2 hcan2 hnb2 fun _ _ m => (specL z Sm sig hS mask Fa Tt' Cv).2.1 m
  · have htg : hd.target = Tt' := by rw [hhd]
    rw [htg, ← mul_tgt]
    intro i m hm
    exact bridge_rounds ht2 hs2 hvr (allG_d z 2) hcan2 hnb2
      (fun _ _ m e pre g => (specL z Sm sig hS mask Fa Tt' Cv).2.2.1 m e pre g) i m hm

end Law

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.coreL
