-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SumLaw.lean: THE LAW OF HeadParts.lean's "sumcheck z n", WITH ITS LETTERS FREE: for any point
z, any number n >= 1 of end values and ANY summand Sm that is summed over the call's variables (the further
variable last) to sig (IsSum): there is a rule from the front of a transcript to a short list of
bad elements such that: at a hearing that returns, in a world whose slots hold the hidden scalars, with the
sumcheck's own form 0, the summand at the challenges equal to the summand S0 on the end values as shown, and
no bad draw: THE CLAIMED SUM's HIDDEN SCALAR IS sig. THE WORLD IS ASKED AT THE SUMCHECK's OWN NUMBERS ALONE (from
F0.next up to sEndG + n): so a world that is read off a LATER ledger serves, if later layings keep these.
THE SUMCHECK IS NOT PROVED HERE: the law is sound_hear_true (Johnson/Desc/Part/MaskedSumTruth.lean): THE
RULE's SETS ARE CHOSEN FROM THAT LAW, WHOSE SETS ARE EMPTY AT THE TRUTH (bEG_empty, bdG_empty): so that the rule can
later be shown empty at an honest run; that is not shown here. THE
PROOF IS coreW (Law/Lemma2b.lean, the head's one sumcheck), with zt ++ halves lPd, two end values and the
product of two tables turned into letters; its bridges (Sum2b, Ledger, LedgerAt, Decode, Bad) are called as
they stand. New here: hiddenFrom at n scalars (hiddenFrom_get).
THE PREMISE gS is asked for every beta under "each end value as shown is its hidden scalar and beta times its
mask entry": the caller need not know which element beta was.
WHO USES IT: the final normalization's "normed" (Law/Normed.lean); n = 4 with a sum of products: the
normalization's "products".

-/
import Mathlib
import Johnson.Desc.Part.MaskedSumTruth
import Johnson.Desc.Kinds.Law.Lemma2b

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

theorem mapM_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    ∀ (j : Nat) (a : α), l[j]? = some a → ∃ b, f a = some b ∧ r[j]? = some b
  | [], _, _, j, a, ha => by simp at ha
  | x :: xs, r, h, j, a, ha => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some ys =>
        simp [List.mapM_cons, hx, hxs] at h
        subst h
        cases j with
        | zero =>
          simp at ha
          subst ha
          exact ⟨y, hx, rfl⟩
        | succ j => exact mapM_get f xs ys hxs j a (by simpa using ha)

/-- What hiddenFrom hands back. -/
theorem hiddenFrom_get {first n : Nat} {F : Fork} {es : Array Hid}
    (h : hiddenFrom first n F [] = some (es, F, [])) : ∀ j, j < n →
    es.getD j {} = { var := Aff.slot (first + j), shown := F.vp.getD (first + j) zeroE } := by
  intro j hj
  unfold hiddenFrom at h
  cases hm : (List.range n).mapM (fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none =>
    rw [hm] at h
    cases h
  | some l =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true] at h
    subst h
    obtain ⟨b, hb, hl⟩ := mapM_get _ _ _ hm j j (List.getElem?_range hj)
    cases hs : F.shown (first + j) with
    | none =>
      rw [hs] at hb
      cases hb
    | some x =>
      rw [hs] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      rw [← shown_some hs, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hl]
      rfl

section Gen
variable (z : Point) (n : Nat)

/-- The sumcheck's variables, its call, the number of its own scalars. -/
def vsG : List Var := z.toList.map (.point · 3)
@[inherit_doc vsG] def kG : Call := ⟨1, vsG z, some ⟨2, n⟩⟩
@[inherit_doc vsG] def ownG : Nat := ownSlots (kG z n).all

theorem kG_eq : callOf 1 z n = kG z n := rfl

theorem vsG_d : ∀ v ∈ vsG z, v.d = 3 := by
  intro v hv
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem allG_d : ∀ v ∈ (kG z n).all, v.d = 3 := by
  intro v hv
  have hm : v ∈ vsG z ++ [Var.point zeroE 3] := hv
  rcases List.mem_append.mp hm with h | h
  · exact vsG_d z v h
  · rw [List.mem_singleton] at h
    rw [h]; rfl

theorem shapeG (hn : 1 ≤ n) : shapeOk ⟨1, vsG z, some ⟨2, n⟩⟩ = true := by
  simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun v hv => ?_, by omega, hn⟩
  rw [vsG_d z v hv]; omega

/-- A hearing that returns has as many challenges as the point has coordinates. -/
theorem sum_r_size {z : Point} {n : Nat} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hsum : sumcheck z n F0 t = some (S, F1, [])) : S.r.size = z.size := by
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hSS⟩ := sumcheck_spec hsum
  rw [kG_eq] at a2 a4 hSS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsG z, some ⟨2, n⟩⟩ t = some R from hread)
  have hlenR : R.rounds.length = (kG z n).all.length := hvr.length.2
  have hallLen : (kG z n).all.length = (vsG z).length + 1 := by
    show (vsG z ++ [Var.point zeroE 3]).length = _
    simp
  have hrlen : hd.r.length = (vsG z).length + 1 := by
    rw [hhd]
    show (R.rounds.map (·.2)).length = _
    rw [List.length_map, hlenR, hallLen]
  have hv : (vsG z).length = z.size := by
    unfold vsG
    rw [List.length_map, Array.length_toList]
  rw [hSS]
  show (challenges (kG z n) hd).toArray.size = _
  rw [List.size_toArray]
  show (hd.r.take (vsG z).length).length = _
  rw [List.length_take, hrlen, hv]
  omega

variable (hn : 1 ≤ n) (Sm : List K → K) (sig : K)
  (hS : IsSum ((⟨1, vsG z, some ⟨2, n⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
  (mask : Nat → E) (F0 : Fork)

/-- The number of the first end value. -/
def sEndG : Nat := F0.next + 1 + ownG z n
def hcoefG (i : Nat) : K := rd (mask (F0.next + 1 + i))
def cvG (c0 : E) : K := rd c0 - rd (mask F0.next)

/-- The law at this call, ITS BAD SETS EMPTY AT THE TRUTH, for the two values T and Cv of the claimed
form. -/
def SHG (Tv Cv : K) := Part.MaskedSum.sound_hear_true Reading.gl 1 (vsG z) ⟨2, n⟩ (shapeG z n hn)
  (hcoefG mask F0) Sm sig hS Tv Cv

/-- The hiding polynomial's sum; the set of bad eps; the true round polynomial; a round's set of bad
challenges: that law's own, in its order. -/
def muG (Tv Cv : K) : K := Classical.choose (SHG z n hn Sm sig hS mask F0 Tv Cv)
@[inherit_doc muG] def bEG (Tv Cv : K) : K → Finset K :=
  Classical.choose (Classical.choose_spec (SHG z n hn Sm sig hS mask F0 Tv Cv))
@[inherit_doc muG] def tqG (Tv Cv : K) : K → K → List K → K[X] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (SHG z n hn Sm sig hS mask F0 Tv Cv)))
@[inherit_doc muG] def bdG (Tv Cv : K) : K → K → List (K[X] × K) → K[X] → Finset K :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (SHG z n hn Sm sig hS mask F0 Tv Cv))))

def specG (Tv Cv : K) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (SHG z n hn Sm sig hS mask F0 Tv Cv))))

/-- **Empty at the truth**: where the claimed form's value is the sum, no eps is bad. -/
theorem bEG_empty (Tv : K) (mu : K) : bEG z n hn Sm sig hS mask F0 Tv sig mu = ∅ :=
  (specG z n hn Sm sig hS mask F0 Tv sig).2.2.2.2.1 rfl mu

/-- **Empty at the truth**: at the true round polynomial no challenge is bad. -/
theorem bdG_empty (Tv Cv mu eps : K) (pre : List (K[X] × K)) :
    bdG z n hn Sm sig hS mask F0 Tv Cv mu eps pre
      (tqG z n hn Sm sig hS mask F0 Tv Cv mu eps (pre.map (·.2))) = ∅ :=
  (specG z n hn Sm sig hS mask F0 Tv Cv).2.2.2.2.2.1 mu eps pre

/-- **The rule.** -/
def badG : List Fmt.RoundView → List E :=
  bad (kG z n).all (cvG mask F0) (bEG z n hn Sm sig hS mask F0) (bdG z n hn Sm sig hS mask F0)

theorem badG_length (h : List Fmt.RoundView) : (badG z n hn Sm sig hS mask F0 h).length
    ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := bad_length _ _ _ _ h

/-- **THE LAW OF "sumcheck z n".** -/
theorem coreG (hWL : WellLaid F0) {F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (W : World K)
    (hWs : ∀ j, F0.next ≤ j → j < sEndG z n F0 + n → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t) (hsum : sumcheck z n F0 t = some (S, F1, [])) (S0 : E)
    (g1 : vW W (S.left S0) = 0)
    (gS : ∀ β : K, (∀ j, j < n → rd (S.end_ j).shown
        = vW W (S.end_ j).var + β * rd (mask (sEndG z n F0 + j))) →
      Sm (S.r.toList.map rd ++ [β]) = rd S0)
    (hnb : NoBad (badG z n hn Sm sig hS mask F0) t) :
    vW W S.claimed.var = sig := by
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hSS⟩ := sumcheck_spec hsum
  rw [kG_eq] at a2 a4 hSS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsG z, some ⟨2, n⟩⟩ t = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hld : ld = [c0] := by
    have h1 : leadScalars ⟨1, vsG z, some ⟨2, n⟩⟩ t = some ld := a2
    rw [ht, lead_of_sent hs0'] at h1
    exact (Option.some.inj h1).symm
  subst hld
  obtain ⟨run1, hcA⟩ := hide_unfold a3
  obtain ⟨_, _, nFa, _, _⟩ :=
    hideRun_frame (F := { F0 with next := F0.next + [c0].length }) hWL run1
  have hnext : Fa.next = F0.next + 1 := nFa
  have hC : cA.getD 0 {} = { var := Aff.slot F0.next, shown := c0 } := by
    rw [hcA]; simp
  rw [hC] at a4 hpub hSS
  dsimp only at a4 hpub
  have hlenR : R.rounds.length = (kG z n).all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt ((kG z n).all.zip (R.rounds.map (·.2)))).1.length
      = ownG z n := by
    have hz : ((kG z n).all.zip (R.rounds.map (·.2))).map (·.1) = (kG z n).all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsG z ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ (kG z n).all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allG_d z n _ this]; omega
  have run3 : G.hideRun (F0.next + 1) (Array.replicate (ownG z n) zeroE) (subE zeroE oneE)
      = some F1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    rw [hlen, hnext] at h5
    exact h5
  rw [hnext] at hrun2
  obtain ⟨V1, V2, V3, V4⟩ := hidden_vals (own := ownG z n) mask hWL run1 hrun2 run3
  rw [hC] at hhd
  dsimp only at hhd
  have hTt : Tt = tgt c0 := by rw [publicPart_slot hpub, V4]
  subst hTt
  have hfirst : hd.first = F0.next + 1 := by rw [hhd]; exact hnext
  have hsEnd : hd.sEnd = sEndG z n F0 := by
    rw [hhd]
    show Fa.next + ownSlots (kG z n).all = _
    rw [hnext]; rfl
  rw [hsEnd] at a6
  have hend : ∀ j, j < n → S.end_ j
      = (⟨Aff.slot (sEndG z n F0 + j), F1.vp.getD (sEndG z n F0 + j) zeroE⟩ : Hid) := by
    intro j hj
    rw [hSS]
    exact hiddenFrom_get a6 j hj
  have hvs : R.values.toArray.size = n := by
    rw [List.size_toArray]; exact hsv.2.1
  have hallLen : (kG z n).all.length = (vsG z).length + 1 := by
    show (vsG z ++ [Var.point zeroE 3]).length = _
    simp
  have hrlen : hd.r.length = (vsG z).length + 1 := by
    rw [hhd]
    show (R.rounds.map (·.2)).length = _
    rw [List.length_map, hlenR, hallLen]
  have hbeta : hd.r.getLastD zeroE = (R.rounds.map (·.2)).getLastD zeroE := by rw [hhd]
  have hrsplit : hd.r = challenges (kG z n) hd ++ [(R.rounds.map (·.2)).getLastD zeroE] := by
    rw [← hbeta]
    exact take_append_last hd.r (vsG z).length zeroE hrlen
  have hSr : S.r = (challenges (kG z n) hd).toArray := by rw [hSS]
  have hrl : S.r.toList.map rd = (challenges (kG z n) hd).map rd := by rw [hSr]
  obtain ⟨_, _, _, main, _⟩ := specG z n hn Sm sig hS mask F0 (rd (tgt c0)) (cvG mask F0 c0)
  have hleft : ∀ x, S.left x = rowForm hd x {} := by
    intro x; rw [hSS]; rfl
  have hres : cvG mask F0 c0 = sig := by
    refine main W (Aff.slot F0.next) Fa G t hd R S0 {} G F1 (rowForm hd S0 {}) a4 hread
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hhd]; rfl
    · rw [Aff.value_slot, hWs _ (le_refl _) (by unfold sEndG; omega)]; exact V1
    · intro i hi
      have hi' : i < ownG z n := hi
      rw [hfirst, hWs _ (by omega) (by unfold sEndG; omega)]; exact V2 i hi
    · rw [row_eq, a5]; rfl
    · rw [← hleft]; exact g1
    · rw [hrsplit, List.map_append, Aff.value_empty, add_zero]
      show Sm ((challenges (kG z n) hd).map rd ++ [rd ((R.rounds.map (·.2)).getLastD zeroE)]) = rd _
      rw [← hrl]
      apply gS
      intro j hj
      rw [hend j hj]
      show rd (F1.vp.getD (sEndG z n F0 + j) zeroE) = vW W (Aff.slot _) + _
      rw [vW_slot, hWs _ (by unfold sEndG; omega) (by omega)]
      have hV3 := V3 j (by rw [hvs]; exact hj)
      show _ = rd (hidden F1 mask (F0.next + 1 + ownG z n + j))
        + _ * rd (mask (F0.next + 1 + ownG z n + j))
      rw [hV3]
      show rd (F1.vp.getD (F0.next + 1 + ownG z n + j) zeroE) = _
      ring
    · exact bridge_eps ht hs0' hcan hnb fun Tv Cv m => (specG z n hn Sm sig hS mask F0 Tv Cv).2.1 m
    · have htg : hd.target = tgt c0 := by rw [hhd]
      rw [htg]
      intro i m hm
      exact bridge_rounds ht hs0' hvr (allG_d z n) hcan hnb
        (fun Tv Cv m e pre g => (specG z n hn Sm sig hS mask F0 Tv Cv).2.2.1 m e pre g) i m hm
  have hcl : S.claimed.var = Aff.slot F0.next := by rw [hSS]
  rw [hcl, vW_slot, hWs _ (le_refl _) (by unfold sEndG; omega), V1]
  exact hres

end Gen

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.coreG
