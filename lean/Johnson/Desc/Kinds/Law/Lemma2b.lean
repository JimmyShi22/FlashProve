-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Lemma2b.lean: LEMMA 2b, THE BRANCH's FORM (HeadLaw.lean: over raw rounds and
MaskedSum4.lean), FROM THE LAW OF THE MASKED SUMCHECK (MaskedSumTruth.lean: sound_hear_true;
MaskedSumProducts.lean: isSum_product). The bridges: Sum2b · Ledger · LedgerAt · Mle · Decode · Tables ·
Ends · Bad.
-/
import Mathlib
import Johnson.Desc.Part.MaskedSumTruth
import Johnson.Desc.Kinds.Law.Bad

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE invE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)
open Polynomial
open OnBytes.Desc.First.P1 (mle tot ext1 IsSum dAt)
open Part.MaskedSum (Var Call Ends Read Sent movesOf ownSlots scalars readAll shapeOk rowForm rowLaid
  row challenges leadScalars weightsOf)

theorem okE_mulE (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

/-- The caller's lead, off a first round that was read. -/
theorem lead_of_sent {r0 : Fmt.RoundView} {tl : List Fmt.RoundView} {c0 mu eps : E} {vs : List Var}
    {e : Option Ends} (h : Sent r0 2 1 [c0, mu] [eps]) :
    leadScalars ⟨1, vs, e⟩ (r0 :: tl) = some [c0] := by
  obtain ⟨h1, _, h3, _⟩ := h
  simp [leadScalars, Part.MaskedSum.firstRound, Part.MaskedSum.roundOf, h1, h3]

theorem shown_some {F : Fork} {j : Nat} {x : E} (h : F.shown j = some x) :
    x = F.vp.getD j zeroE := by
  unfold Fork.shown at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- What the ledger makes of the one slot's form. -/
theorem publicPart_slot {F : Fork} {j : Nat} {Tt : E} (h : F.publicPart (Aff.slot j) = some Tt) :
    Tt = tgt (F.vp.getD j zeroE) := by
  cases hs : F.shown j with
  | none =>
    have h' : ((F.shown j).map fun y => addE zeroE (mulE oneE y)).bind pure = some Tt := h
    rw [hs] at h'; cases h'
  | some x =>
    have h' : ((F.shown j).map fun y => addE zeroE (mulE oneE y)).bind pure = some Tt := h
    rw [hs] at h'
    rw [← shown_some hs]
    exact (Option.some.inj h').symm

/-- What `hiddenFrom` hands back, for two scalars. -/
theorem hiddenFrom_two {first : Nat} {F : Fork} {es : Array Hid}
    (h : hiddenFrom first 2 F [] = some (es, F, [])) :
    es.getD 0 {} = { var := Aff.slot first, shown := F.vp.getD first zeroE } ∧
    es.getD 1 {} = { var := Aff.slot (first + 1), shown := F.vp.getD (first + 1) zeroE } := by
  unfold hiddenFrom at h
  have hr : List.range 2 = [0, 1] := rfl
  rw [hr] at h
  cases h0 : F.shown first with
  | none => simp [List.mapM_cons, h0] at h
  | some x0 =>
    cases h1 : F.shown (first + 1) with
    | none => simp [List.mapM_cons, h0, h1] at h
    | some x1 =>
      simp only [List.mapM_cons, List.mapM_nil, Nat.add_zero, h0, h1, Option.map_some,
        Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq,
        and_true] at h
      subst h
      rw [← shown_some h0, ← shown_some h1]
      exact ⟨rfl, rfl⟩

/-- A list of n + 1 members is its first n and its last. -/
theorem take_append_last {α : Type} (l : List α) (n : Nat) (z : α) (h : l.length = n + 1) :
    l = l.take n ++ [l.getLastD z] := by
  have hne : l ≠ [] := by intro e; rw [e] at h; simp at h
  have h1 : l.getLastD z = l.getLast hne := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a as => simp [List.getLastD]
  rw [h1]
  have h2 : l.take n = l.dropLast := by rw [List.dropLast_eq_take, h]; rfl
  rw [h2, List.dropLast_append_getLast]

variable [Sizes] [Policy] [Request] [Token]

section Core
variable [FinalNorm.In] [In]

/-- The sumcheck's point. -/
def zP : Point := FinalNorm.zt ++ halves lPd
/-- Its variables. -/
def vsP : List Var := zP.toList.map (.point · 3)
/-- Its call. -/
def kP : Call := ⟨1, vsP, some ⟨2, 2⟩⟩
/-- The number of its own scalars. -/
def ownP : Nat := ownSlots kP.all

theorem kP_eq : callOf 1 zP 2 = kP := rfl

theorem vsP_d : ∀ v ∈ vsP, v.d = 3 := by
  intro v hv
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem allP_d : ∀ v ∈ kP.all, v.d = 3 := by
  intro v hv
  have hm : v ∈ vsP ++ [Var.point zeroE 3] := hv
  rcases List.mem_append.mp hm with h | h
  · exact vsP_d v h
  · rw [List.mem_singleton] at h
    rw [h]; rfl

theorem shapeP : shapeOk ⟨1, vsP, some ⟨2, 2⟩⟩ = true := by
  simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun v hv => ?_, by omega, by omega⟩
  rw [vsP_d v hv]; omega

variable (c : Cells) (mask : Nat → E) (F0 : Fork)

def sEndP : Nat := F0.next + 1 + ownP
def AtP : List Bool → K := cut lPd d (fA c)
def UtP : List Bool → K := cut lPd d (fU c)
/-- The summand, the further variable last. -/
def SmP : List K → K := fun rs =>
  mle (vsP.length + 1) (ext1 vsP.length (AtP c) (rd (mask (sEndP F0)))) rs *
    mle (vsP.length + 1) (ext1 vsP.length (UtP c) (rd (mask (sEndP F0 + 1)))) rs
def sigP : K := tot (weightsOf Reading.gl vsP) fun b => AtP c b * UtP c b
def hcoefP (i : Nat) : K := rd (mask (F0.next + 1 + i))
def cvP (c0 : E) : K := rd c0 - rd (mask F0.next)

theorem hSP : IsSum ((⟨1, vsP, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl)) (SmP c mask F0)
    (sigP c) :=
  Part.MaskedSum.isSum_product Reading.gl 1 vsP 2 (fun v hv => by rw [vsP_d v hv]) _ _ _ _

/-- The law at this call, for the two values T and Cv of the claimed form: IN THE FORM WHOSE BAD
SETS ARE EMPTY AT THE TRUTH (MaskedSumTruth.lean: sound_hear_true): the sets are chosen from it, so
that the rule below can be shown empty at an honest run: that cannot be had of sets chosen from the
bare law. -/
def SHP (Tv Cv : K) := Part.MaskedSum.sound_hear_true Reading.gl 1 vsP ⟨2, 2⟩ shapeP
  (hcoefP mask F0) (SmP c mask F0) (sigP c) (hSP c mask F0) Tv Cv

/-- The sum of the hiding polynomial. -/
def muTP (Tv Cv : K) : K := Classical.choose (SHP c mask F0 Tv Cv)
def bEP (Tv Cv : K) : K → Finset K := Classical.choose (Classical.choose_spec (SHP c mask F0 Tv Cv))
/-- The true round polynomial, for mu, eps and the challenges in front. -/
def tqP (Tv Cv : K) : K → K → List K → K[X] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (SHP c mask F0 Tv Cv)))
def bdP (Tv Cv : K) : K → K → List (K[X] × K) → K[X] → Finset K :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (SHP c mask F0 Tv Cv))))

/-- All seven clauses. -/
def specT (Tv Cv : K) := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec (SHP c mask F0 Tv Cv))))

/-- The two sizes and the law. -/
def specP (Tv Cv : K) := And.intro (specT c mask F0 Tv Cv).2.1
  (And.intro (specT c mask F0 Tv Cv).2.2.1 (specT c mask F0 Tv Cv).2.2.2.1)

/-- AT THE TRUTH NO eps IS BAD. -/
theorem bEP_empty (Tv Cv : K) (h : Cv = sigP c) (mu : K) : bEP c mask F0 Tv Cv mu = ∅ :=
  (specT c mask F0 Tv Cv).2.2.2.2.1 h mu

/-- A ROUND's SET IS EMPTY AT THE TRUE ROUND POLYNOMIAL. -/
theorem bdP_empty (Tv Cv mu eps : K) (pre : List (K[X] × K)) :
    bdP c mask F0 Tv Cv mu eps pre (tqP c mask F0 Tv Cv mu eps (pre.map (·.2))) = ∅ :=
  (specT c mask F0 Tv Cv).2.2.2.2.2.1 mu eps pre

/-- **The rule of Lemma 2b.** -/
def badP : List Fmt.RoundView → List E := bad kP.all (cvP mask F0) (bEP c mask F0) (bdP c mask F0)

/-- sigma is 2^-lPd times the true sum. -/
theorem sigP_eq (hzt : (FinalNorm.zt).size = lt) : sigP c = ((2 : K) ^ lPd)⁻¹ * rd (trueSum c) := by
  have hw : weightsOf Reading.gl vsP
      = ((FinalNorm.zt).toList.map rd ++ List.replicate lPd (2 : K)⁻¹).map fun z => (1 - z, z) := by
    unfold weightsOf vsP zP
    rw [Array.toList_append, List.map_append, List.map_append, List.map_append, ← map_rd_halves]
    simp only [List.map_map]
    rfl
  unfold sigP
  rw [hw, tot_pairs]
  exact sigma_eq c hzt

/-- **The core of Lemma 2b, read in the field, in any world that holds the hidden scalars UNDER THE
NUMBERS THAT THE SUMCHECK ITSELF LAYS** (the claimed sum's, its own, the two end values'). The
three things that are asked of the world: the sumcheck's own form has the value 0; the two end
values' variables have the values of act's and UH's tables at the challenges. -/
theorem coreW (hWL : WellLaid F0)
    (hzt : (FinalNorm.zt).size = lt) {F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (W : World K)
    (hWs : ∀ j, F0.next ≤ j → j < sEndP F0 + 2 → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t)
    (hsum : sumcheck zP 2 F0 t = some (S, F1, []))
    (g1 : vW W (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0)
    (g2 : letI : Heard := { logits := S }
      vW W (S.end_ 0).var = (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
        rd (eq rH t) * rd (eq rs k) * fA c t k)
    (g3 : letI : Heard := { logits := S }
      vW W (S.end_ 1).var = (Finset.range T).sum fun t => (Finset.range d).sum fun k =>
        rd (eq rH t) * rd (eq rs k) * fU c t k)
    (hnb : NoBad (badP c mask F0) t) :
    (2 : K) ^ lPd * vW W S.claimed.var = rd (trueSum c) := by
  letI : Heard := { logits := S }
  obtain ⟨ld, cA, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hS⟩ := sumcheck_spec hsum
  rw [kP_eq] at a2 a4 hS
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsP, some ⟨2, 2⟩⟩ t = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hld : ld = [c0] := by
    have h1 : leadScalars ⟨1, vsP, some ⟨2, 2⟩⟩ t = some ld := a2
    rw [ht, lead_of_sent hs0'] at h1
    exact (Option.some.inj h1).symm
  subst hld
  obtain ⟨run1, hcA⟩ := hide_unfold a3
  obtain ⟨_, _, nFa, _, _⟩ :=
    hideRun_frame (F := { F0 with next := F0.next + [c0].length }) hWL run1
  have hnext : Fa.next = F0.next + 1 := nFa
  have hC : cA.getD 0 {} = { var := Aff.slot F0.next, shown := c0 } := by
    rw [hcA]; simp
  rw [hC] at a4 hpub hS
  dsimp only at a4 hpub
  have hlenR : R.rounds.length = kP.all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt (kP.all.zip (R.rounds.map (·.2)))).1.length = ownP := by
    have hz : (kP.all.zip (R.rounds.map (·.2))).map (·.1) = kP.all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsP ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ kP.all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allP_d _ this]; omega
  have run3 : G.hideRun (F0.next + 1) (Array.replicate ownP zeroE) (subE zeroE oneE) = some F1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    rw [hlen, hnext] at h5
    exact h5
  rw [hnext] at hrun2
  obtain ⟨V1, V2, V3, V4⟩ := hidden_vals (own := ownP) mask hWL run1 hrun2 run3
  rw [hC] at hhd
  dsimp only at hhd
  have hTt : Tt = tgt c0 := by rw [publicPart_slot hpub, V4]
  subst hTt
  have hfirst : hd.first = F0.next + 1 := by rw [hhd]; exact hnext
  have hsEnd : hd.sEnd = sEndP F0 := by
    rw [hhd]
    show Fa.next + ownSlots kP.all = _
    rw [hnext]; rfl
  rw [hsEnd] at a6
  obtain ⟨E0, E1⟩ := hiddenFrom_two a6
  have hend0 : S.end_ 0 = { var := Aff.slot (sEndP F0), shown := F1.vp.getD (sEndP F0) zeroE } := by
    rw [hS]; exact E0
  have hend1 : S.end_ 1
      = { var := Aff.slot (sEndP F0 + 1), shown := F1.vp.getD (sEndP F0 + 1) zeroE } := by
    rw [hS]; exact E1
  have hvs : R.values.toArray.size = 2 := by
    rw [List.size_toArray]; exact hsv.2.1
  have X0 := V3 0 (by omega)
  have X1 := V3 1 (by omega)
  rw [Nat.add_zero] at X0
  have hallLen : kP.all.length = vsP.length + 1 := by
    show (vsP ++ [Var.point zeroE 3]).length = _
    simp
  have hrlen : hd.r.length = vsP.length + 1 := by
    rw [hhd]
    show (R.rounds.map (·.2)).length = _
    rw [List.length_map, hlenR, hallLen]
  have hbeta : hd.r.getLastD zeroE = (R.rounds.map (·.2)).getLastD zeroE := by rw [hhd]
  have hrsplit : hd.r = challenges kP hd ++ [(R.rounds.map (·.2)).getLastD zeroE] := by
    rw [← hbeta]
    exact take_append_last hd.r vsP.length zeroE hrlen
  have hxlen : (challenges kP hd).length = vsP.length := by
    show (hd.r.take vsP.length).length = _
    rw [List.length_take, hrlen]; omega
  have hvsl : vsP.length = lt + lPd := by
    unfold vsP zP halves
    simp [hzt]
  have hSr : (logits.r) = (challenges kP hd).toArray := by
    show S.r = _
    rw [hS]
  have hsize : (logits.r).size = lt + lPd := by
    rw [hSr, List.size_toArray, hxlen, hvsl]
  have hrl : (logits.r).toList.map rd = (challenges kP hd).map rd := by rw [hSr]
  have hA : rd (hidden F1 mask (sEndP F0))
      = mle (lt + lPd) (AtP c) ((challenges kP hd).map rd) := by
    have h3 : vW W (S.end_ 0).var = rd (hidden F1 mask (sEndP F0)) := by
      rw [hend0]
      show vW W (Aff.slot _) = _
      rw [vW_slot, hWs _ (by unfold sEndP; omega) (by omega)]
    have h4 := mle_at_r (fA c) logits.r hsize
    rw [hrl] at h4
    unfold AtP
    rw [h4, ← h3, g2]
    rfl
  have hU : rd (hidden F1 mask (sEndP F0 + 1))
      = mle (lt + lPd) (UtP c) ((challenges kP hd).map rd) := by
    have h3 : vW W (S.end_ 1).var = rd (hidden F1 mask (sEndP F0 + 1)) := by
      rw [hend1]
      show vW W (Aff.slot _) = _
      rw [vW_slot, hWs _ (by unfold sEndP; omega) (by omega)]
    have h4 := mle_at_r (fU c) logits.r hsize
    rw [hrl] at h4
    unfold UtP
    rw [h4, ← h3, g3]
    rfl
  obtain ⟨_, _, main⟩ := specP c mask F0 (rd (tgt c0)) (cvP mask F0 c0)
  have hleft : ∀ x, S.left x = rowForm hd x {} := by
    intro x; rw [hS]; rfl
  have hres : cvP mask F0 c0 = sigP c := by
    refine main W (Aff.slot F0.next) Fa G t hd R
      ((S.end_ 0).shown * (S.end_ 1).shown) {} G F1
      (rowForm hd ((S.end_ 0).shown * (S.end_ 1).shown) {}) a4 hread ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hhd]; rfl
    · rw [Aff.value_slot, hWs _ (Nat.le_refl _) (by unfold sEndP; omega)]; exact V1
    · intro i hi
      have hi' : i < ownP := hi
      rw [hfirst, hWs _ (by omega) (by unfold sEndP; omega)]; exact V2 i hi
    · rw [row_eq, a5]; rfl
    · rw [← hleft]; exact g1
    · rw [hrsplit, List.map_append, Aff.value_empty, add_zero]
      show SmP c mask F0 ((challenges kP hd).map rd ++
        [rd ((R.rounds.map (·.2)).getLastD zeroE)]) = rd _
      unfold SmP
      rw [Part.MaskedSum.product_at vsP.length _ _ _ _ _ _ (by rw [List.length_map, hxlen]), rd_mul,
        hend0, hend1, hvsl, ← hA, ← hU]
      dsimp only
      have Y0 : rd (F1.vp.getD (sEndP F0) zeroE) = rd (hidden F1 mask (sEndP F0))
          + rd ((R.rounds.map (·.2)).getLastD zeroE) * rd (mask (sEndP F0)) := by
        have := X0
        show _ = rd (hidden F1 mask (F0.next + 1 + ownP)) + _ * rd (mask (F0.next + 1 + ownP))
        rw [this]
        show rd (F1.vp.getD (F0.next + 1 + ownP) zeroE) = _
        ring
      have Y1 : rd (F1.vp.getD (sEndP F0 + 1) zeroE) = rd (hidden F1 mask (sEndP F0 + 1))
          + rd ((R.rounds.map (·.2)).getLastD zeroE) * rd (mask (sEndP F0 + 1)) := by
        have := X1
        show _ = rd (hidden F1 mask (F0.next + 1 + ownP + 1))
          + _ * rd (mask (F0.next + 1 + ownP + 1))
        rw [this]
        show rd (F1.vp.getD (F0.next + 1 + ownP + 1) zeroE) = _
        ring
      rw [Y0, Y1]
    · exact bridge_eps ht hs0' hcan hnb fun Tv Cv m => (specP c mask F0 Tv Cv).1 m
    · have htg : hd.target = tgt c0 := by rw [hhd]
      rw [htg]
      intro i m hm
      exact bridge_rounds ht hs0' hvr allP_d hcan hnb
        (fun Tv Cv m e pre g => (specP c mask F0 Tv Cv).2.1 m e pre g) i m hm
  have hcl : S.claimed.var = Aff.slot F0.next := by rw [hS]
  have h2 : ((2 : K) ^ lPd) ≠ 0 := two_pow_ne_zero _
  rw [hcl, vW_slot, hWs _ (Nat.le_refl _) (by unfold sEndP; omega), V1]
  have h3 : rd c0 - rd (mask F0.next) = ((2 : K) ^ lPd)⁻¹ * rd (trueSum c) := by
    rw [← sigP_eq c hzt]; exact hres
  rw [h3, mul_inv_cancel_left₀ h2]

/-- **The core of Lemma 2b**, the classes of the point as letters: in the world without entries, the
reads filled from the cells. -/
theorem core (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F0)
    (hzt : (FinalNorm.zt).size = lt) {F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (hcan : Canonical t)
    (hsum : sumcheck zP 2 F0 t = some (S, F1, []))
    (hf1 : atHidden F1 mask (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0)
    (hf2 : letI : Heard := { logits := S }
      letI := readsAt c
      atHidden F1 mask ((logits.end_ 0).var
        - sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k) = 0)
    (hw : letI : Heard := { logits := S }
      atHidden F1 mask forTheMerge.value.var = sumTo V fun v => sumTo d fun k =>
        forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k * ofInt (c.Wh k v))
    (hnb : NoBad (badP c mask F0) t) :
    (2 ^ lPd : E) * atHidden F1 mask S.claimed.var = trueSum c := by
  letI : Heard := { logits := S }
  have g1 : vW (worldOf F1 mask) (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0 := by
    have h1 := congrArg rd hf1
    rw [rd_atHidden, rd_zero] at h1
    exact h1
  have g2 : vW (worldOf F1 mask) (S.end_ 0).var = (Finset.range T).sum fun t =>
      (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fA c t k := by
    have h1 := congrArg rd hf2
    rw [rd_atHidden, rd_zero] at h1
    have h2 := actForm_value c (worldOf F1 mask)
    have h5 : vW (worldOf F1 mask) (logits.end_ 0).var - ((Finset.range T).sum fun t =>
        (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fA c t k) = 0 := by
      rw [← h2]; exact h1
    exact sub_eq_zero.mp h5
  have g3 : vW (worldOf F1 mask) (S.end_ 1).var = (Finset.range T).sum fun t =>
      (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fU c t k := by
    have h1 := congrArg rd hw
    rw [rd_atHidden, weights_eq c hreq hy] at h1
    exact h1
  have h := coreW c mask F0 hWL hzt (worldOf F1 mask) (fun _ _ _ => rfl) hcan hsum g1 g2 g3 hnb
  apply eq_of_rd (okE_mulE _ _) (by unfold trueSum; exact okE_sumTo _ _)
  have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
  have hm : rd (mulE (2 ^ lPd) (atHidden F1 mask S.claimed.var))
      = rd ((2 : E) ^ lPd) * rd (atHidden F1 mask S.claimed.var) := Reading.gl.mul _ _
  rw [hm, rd_pow, hr2, rd_atHidden]
  exact h

end Core

/-- **LEMMA 2b** (the branch's form). -/
theorem lemma2b : Lemma2bStatement := by
  intro _ _ _ _ c p mask F0 hreq hy hWL hzt _
  letI := p.normIn
  letI := p.headIn
  refine ⟨badP c mask F0, fun h => bad_length _ _ _ _ h, ?_⟩
  intro F1 t S _ _ hcan hsum _ _ hforms hw hnb
  exact core c mask F0 hreq hy hWL hzt hcan hsum
    (hforms _ (by simp [logitForms])) (hforms _ (by simp [logitForms])) hw hnb

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.lemma2b
