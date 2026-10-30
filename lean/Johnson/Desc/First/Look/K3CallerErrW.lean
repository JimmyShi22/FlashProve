-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerErrW.lean: THE ERRORS OF THE LOOKUP's WRITTEN ROUNDS: the least
errors that bear the proved block's (bearT, K3CallerErr.lean) are, as shares of the written rounds'
own challenge values (strings of hash blocks, with the round's test bits), AT MOST 2^-157, ROUND BY
ROUND. Statements and proofs. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. K3CallerErr.lean bounds the typed block's counts among the typed challenge sets. The rule of
composition counts a piece's errors among the WRITTEN rounds' challenge values. A written round
draws b blocks of 256 bits; at most w of its values go to one typed value, and w · |typed| ≤ (1 +
2^-128)^b · 2^(256 b) (Run.planDraws_law). The library's OnBytes.Slice.entry_pow turns a typed share
into a written one. Here it is called at each of the lookup's rounds.

Main names.
  TwRound.LW B M q c e: c · B ≤ the size that the entry says; it draws at most M elements; those
    that must not be 0 are among them. lw_entN, lw_all: at the lookup's list of entries, AT ANY
    NUMBER wk OF TEST BITS (K3CallerErr.lean's lb_entN, lb_all with two clauses more).
  nVals_repNZ, nVals_plain, sizeOf_le_nVals: a written round that holds elements alone has at least
    as many typed values as its entry's size says.
  pow_slack, num_le: (2^128 + 1)^B · 2^157 ≤ (2^128)^B · 2^158 at every B below 512 (by induction):
    the samplers' bias costs one bit.
  below_plain: one written round. bearT_below: all of them: Err.Below at 2^-157.
  lookupC_written: AT THE KIND's OWN ERRORS: for every caller whose record passes FoNums.ok, all
    written rounds ds that hold elements alone and have the entries forEnts wk h, and ε' := bearT:
    Err.Below ε' 2^-157.
  entries_forEnts, dig_written: the entries of the kind's own declared rounds (P.rounds) are
    forEnts at the setting's test bits; so at the closed caller of a link's digits.
Limits. A share is a count among all strings of hash blocks and test bits: nothing on the hash
function. Round by round: with at most 2048 rounds (lookupC_rounds) the block's written shares add
up to at most 2^-146: THAT SUM IS A RECKONING HERE, NOT A THEOREM.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerErr
import Johnson.Desc.First.Look.K3Caller
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Tie.Pv.Lookup.Forest.FoFour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 List

/-- the count times B is at most the entry's size; the entry draws at most M elements, those that
must not be 0 among them -/
def LW (B M q c : ℕ) (e : Fmt.Entry) : Prop :=
  c * B ≤ sizeOf q e ∧ e.drawE ≤ M ∧ e.drawNZ ≤ e.drawE

theorem lw_rd {B M q c k : ℕ} (wk : ℕ) (name : String) (s : ℕ) (h : c * B ≤ q ^ k) (hk : k ≤ M) :
    LW B M q c (rd wk name s k) :=
  ⟨by simpa [sizeOf, rd] using h, hk, Nat.zero_le _⟩
theorem lw_Y {B M q c : ℕ} (wk s : ℕ) (h : c * B ≤ q - 1) (hM : 1 ≤ M) :
    LW B M q c (rd wk "PSC Y" s 1 1) :=
  ⟨by simpa [sizeOf, rd] using h, hM, le_refl 1⟩
theorem lw_none (B M q : ℕ) (name : String) (s : ℕ) : LW B M q 0 (rdNone name s) :=
  ⟨by simp [sizeOf, rdNone], Nat.zero_le _, le_refl _⟩
theorem lw_one {B M q c : ℕ} (wk : ℕ) (name : String) (s : ℕ) (h : c * B ≤ q) (hM : 1 ≤ M) :
    LW B M q c (rd wk name s 1) :=
  lw_rd wk name s (by rw [pow_one]; exact h) hM

theorem lw_psc (B M q wk k g gY vals : ℕ) (hM : 1 ≤ M) (h1 : 1 * B ≤ q) (hg : g * B ≤ q)
    (hY : gY * B ≤ q - 1) :
    Forall₂ (LW B M q) (pscC k g gY) (pscN wk (replicate k g) true gY vals) := by
  unfold pscC pscN
  rw [if_pos rfl, map_replicate]
  exact f2_append (f2_append (.cons (lw_one _ _ _ h1 hM) .nil) (f2_rep (lw_one _ _ _ hg hM) k))
    (.cons (lw_Y _ _ hY hM) (.cons (lw_none _ _ _ _ _) .nil))

theorem lw_clo (B M q wk d w : ℕ) (hM : 1 ≤ M) (h1 : 1 * B ≤ q) (h2 : 2 * B ≤ q) :
    Forall₂ (LW B M q) ([1] ++ replicate d 2 ++ replicate w 1)
      (pscN wk (replicate d 2 ++ replicate w 1) false 0 0) := by
  have e : pscN wk (replicate d 2 ++ replicate w 1) false 0 0 =
      [rd wk "PSC epsilon" 1 1] ++ replicate d (rd wk "PSC round" 2 1) ++
        replicate w (rd wk "PSC round" 1 1) := by
    simp [pscN]
  rw [e]
  exact f2_append (f2_append (.cons (lw_one _ _ _ h1 hM) .nil) (f2_rep (lw_one _ _ _ h2 hM) d))
    (f2_rep (lw_one _ _ _ h1 hM) w)

theorem lw_entN (B M q wk v' d w n : ℕ) (hM : 1 ≤ M) (hwM : w + d ≤ M) (h3 : 3 * B ≤ q - 1)
    (hv : 2 ^ (v' + 1) * B ≤ q) (hw : (w + d) * B ≤ q) :
    Forall₂ (LW B M q) (epsN v' d w n q) (entN wk v' d w n) := by
  have h0 : 0 * B ≤ q := by omega
  have h1 : 1 * B ≤ q := by omega
  have h2 : 2 * B ≤ q := by omega
  have h2' : 2 * B ≤ q - 1 := by omega
  have hv1 : (2 ^ (v' + 1) - 1) * B ≤ q :=
    Nat.le_trans (Nat.mul_le_mul_right B (Nat.sub_le _ _)) hv
  have hw1 : w * B ≤ q := Nat.le_trans (Nat.mul_le_mul_right B (Nat.le_add_right w d)) hw
  have hwM1 : w ≤ M := Nat.le_trans (Nat.le_add_right w d) hwM
  unfold epsN entN
  rw [append_assoc [rd wk "LKP" 0 1]]
  refine f2_append (f2_append (f2_append (f2_append (f2_append (f2_append (f2_append
    (.cons (lw_one _ _ _ hv1 hM) .nil)
    (f2_first (lw_psc B M q wk 0 0 3 3 hM h1 h0 h3) (lw_psc B M q wk 0 0 3 2 hM h1 h0 h3) n))
    (.cons (lw_rd _ _ _ (point_lb hw1) hwM1) .nil))
    (f2_flat _ _ (fun l => f2_append (lw_psc B M q wk l 2 2 2 hM h1 h2 h2')
      (.cons (lw_one _ _ _ h1 hM) .nil)) _))
    (f2_flat _ _ (fun l => f2_append (lw_psc B M q wk (w + l) 2 2 2 hM h1 h2 h2')
      (.cons (lw_one _ _ _ h1 hM) .nil)) _))
    (lw_clo B M q wk d w hM h1 h2))
    (.cons (lw_rd _ _ _ (point_lb hw) hwM) .nil))
    (lw_psc B M q wk (w + d) 2 2 1 hM h1 h2 h2')

theorem lw_all (B M q wk v' d w n dS : ℕ) (several : Bool) (hM : 1 ≤ M) (hwM : w + d ≤ M)
    (h3 : 3 * B ≤ q - 1) (hv : 2 ^ (v' + 1) * B ≤ q) (hw : (w + d) * B ≤ q)
    (hS : 2 ^ dS * B ≤ q) :
    Forall₂ (LW B M q) (shHead several (2 ^ dS) ++ epsN v' d w n q)
      (shHead several (shiftN wk) ++ entN wk v' d w n) := by
  refine f2_append ?_ (lw_entN B M q wk v' d w n hM hwM h3 hv hw)
  cases several with
  | true => exact .cons (lw_one _ _ _ hS hM) .nil
  | false => exact .nil

end TwRound

namespace OnBytes.Slice
open Iop Prob _root_.Run TwRound
open scoped ENNReal

/-- The typed values of a run of n elements that must not be 0, and of what is drawn after them. -/
theorem nVals_repNZ (n : ℕ) (rest : List Fmt.Draw) :
    nVals (List.replicate n Fmt.Draw.elemNZ ++ rest) =
      (Fmt.Fld.two.p ^ 3 - 1) ^ n * nVals rest := by
  induction n with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ n ih =>
      show (Fmt.Fld.two.p ^ 3 - 1) * nVals (List.replicate n Fmt.Draw.elemNZ ++ rest) = _
      rw [ih]
      generalize Fmt.Fld.two.p ^ 3 - 1 = P
      rw [pow_succ, mul_comm (P ^ n) P, mul_assoc]

/-- What a written round that holds elements alone draws. -/
theorem dsOf_plain {d : _root_.Run.PQ.RD} (h : Fo.Peel.Plain d) : Fmt.dsOf d.entry d.kind =
    List.replicate (d.entry.drawE - d.entry.drawNZ) Fmt.Draw.elem ++
      (List.replicate d.entry.drawNZ Fmt.Draw.elemNZ ++ [.trits 0]) := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [h.poss, h.trits, if_neg h.notSeeds, if_neg h.notSealed, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem nVals_plain {d : _root_.Run.PQ.RD} (h : Fo.Peel.Plain d) : nVals (Fmt.dsOf d.entry d.kind) =
    Fintype.card GE ^ (d.entry.drawE - d.entry.drawNZ) *
      (Fintype.card GE - 1) ^ d.entry.drawNZ := by
  rw [dsOf_plain h, nVals_repE, nVals_repNZ, nVals_end, mul_one, card_GE]

/-- At any number q: an entry's size is at most q^(drawE - drawNZ) · (q - 1)^drawNZ. (q is a letter,
so that no step is a computation with the field's size.) -/
theorem sizeOf_le (q : ℕ) (e : Fmt.Entry) :
    TwRound.sizeOf q e ≤ q ^ (e.drawE - e.drawNZ) * (q - 1) ^ e.drawNZ := by
  unfold TwRound.sizeOf
  split
  · rename_i h0
    rw [h0, Nat.sub_zero, pow_zero, mul_one]
  · split
    · rename_i h1
      rw [h1.1, h1.2, Nat.sub_self, pow_zero, one_mul, pow_one]
    · exact Nat.zero_le _

/-- It has at least as many typed values as its entry's size says. -/
theorem sizeOf_le_nVals {d : _root_.Run.PQ.RD} (h : Fo.Peel.Plain d) :
    TwRound.sizeOf (Fintype.card GE) d.entry ≤ nVals (Fmt.dsOf d.entry d.kind) :=
  (sizeOf_le _ _).trans (le_of_eq (nVals_plain h).symm)

/-- (1 + 1/N)^B ≤ 1 + B/M as long as M + B ≤ N, without a division. -/
theorem pow_slack (N M : ℕ) : ∀ B, M + B ≤ N → (N + 1) ^ B * M ≤ N ^ B * (M + B)
  | 0, _ => by simp
  | B + 1, h => by
    have ih := pow_slack N M B (by omega)
    have h1 : M + B ≤ N := by omega
    have h2 : (N + 1) * (M + B) ≤ N * (M + (B + 1)) :=
      calc (N + 1) * (M + B) = N * (M + B) + (M + B) := by ring
        _ ≤ N * (M + B) + N := Nat.add_le_add_left h1 _
        _ = N * (M + (B + 1)) := by ring
    calc (N + 1) ^ (B + 1) * M = (N + 1) * ((N + 1) ^ B * M) := by ring
      _ ≤ (N + 1) * (N ^ B * (M + B)) := Nat.mul_le_mul_left _ ih
      _ = N ^ B * ((N + 1) * (M + B)) := by ring
      _ ≤ N ^ B * (N * (M + (B + 1))) := Nat.mul_le_mul_left _ h2
      _ = N ^ (B + 1) * (M + (B + 1)) := by ring

/-- The samplers' bias costs at most one bit at fewer than 512 blocks. -/
theorem num_le (B : ℕ) (hB : B < 512) :
    (2 ^ 128 + 1) ^ B * 1 * 2 ^ 157 ≤ (2 ^ 128) ^ B * 2 ^ 158 := by
  have h := pow_slack (2 ^ 128) 512 B
    (Nat.le_trans (by omega : 512 + B ≤ 1024) (by norm_num : 1024 ≤ 2 ^ 128))
  generalize (2 ^ 128 + 1) ^ B = X at h ⊢
  generalize (2 ^ 128) ^ B = Y at h ⊢
  have h2 : X * 512 ≤ Y * 1024 := Nat.le_trans h (Nat.mul_le_mul_left _ (by omega))
  have e1 : (2 : ℕ) ^ 157 = 512 * 2 ^ 148 := by norm_num
  have e2 : (2 : ℕ) ^ 158 = 1024 * 2 ^ 148 := by norm_num
  rw [mul_one, e1, e2, ← mul_assoc, ← mul_assoc]
  exact Nat.mul_le_mul_right _ h2

/-- **One written round**: the typed count c times the sampler's bound is at most 2^-157 of the
round's challenge values. -/
theorem below_plain {d : _root_.Run.PQ.RD} (h : Fo.Peel.Plain d) {c : ℕ}
    (hc : LW (2 ^ 158) 40 (Fintype.card GE) c d.entry) :
    ((c * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 157 * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have hlog : d.entry.logN ≤ 64 := by
    rw [h.logN]
    exact Nat.zero_le _
  have hB : (bsRound .two d.entry d.kind).b < 512 := by
    rw [(planDraws_law .two d.entry d.kind hlog).2]
    unfold Fmt.blocksFor Fmt.wordsAtMost
    rw [h.poss, h.trits, if_neg h.notSealed]
    have h1 := hc.2.1
    have h2 := hc.2.2
    omega
  refine entry_pow d hlog c 1 (2 ^ 158) _ _ 157 rfl rfl (by positivity) ?_ ?_
  · rw [one_mul]
    exact Nat.le_trans hc.1 (sizeOf_le_nVals h)
  · exact Nat.le_trans (num_le _ hB) (Nat.le_mul_of_pos_right _ (by positivity))

end OnBytes.Slice

namespace Fo.Peel
open Iop IOR Prob Cb TWhole OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run TwRound
open scoped ENNReal

/-- **All written rounds**: the least errors that bear the typed ones are at most 2^-157, round by
round, as shares of the written rounds' challenge values. -/
theorem bearT_below : ∀ (ds : List RDT) (s' : Shape) (ε : Err s') (ε' : Err (uLT (ckP .two) ds)),
    bearT ds s' ε = some ε' → (∀ d ∈ ds, Plain (toRD d)) →
    List.Forall₂ (LW (2 ^ 158) 40 (Fintype.card GE)) (errList ε) (ds.map (·.entry)) →
      Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 157)
  | [], [], _, _, _, _, _ => trivial
  | d :: ds, _ :: s', ε, ε', h, hP, hL => by
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
    have hL' : List.Forall₂ (LW (2 ^ 158) 40 (Fintype.card GE)) (ε.1 :: errList ε.2)
        (d.entry :: ds.map (·.entry)) := hL
    obtain ⟨a, b⟩ := List.forall₂_cons.1 hL'
    exact ⟨below_plain (d := toRD d) (hP d List.mem_cons_self) a,
      bearT_below ds s' ε.2 t ht (fun d' hd => hP d' (List.mem_cons_of_mem _ hd)) b⟩
  | [], _ :: _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, h, _, _ => by cases h

end Fo.Peel

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Cb.Fo TwRound
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open scoped ENNReal

/-- The lookup's counts against its entries, at any number of test bits. -/
theorem forEps_lw {h : Sh} (H : FoNums.ok h = true) (wk : ℕ) :
    List.Forall₂ (LW (2 ^ 158) 40 (Fintype.card Cb.Gl.E)) (forEps (Fintype.card Cb.Gl.E) h)
      (forEnts wk h) := by
  obtain ⟨hv, hd⟩ := ok_depths H
  have hq := gl_big
  have top : (2 : ℕ) ^ 31 * 2 ^ 158 ≤ 2 ^ 191 := by norm_num
  have pw : ∀ k, k < 32 → 2 ^ k * 2 ^ 158 ≤ Fintype.card Cb.Gl.E := fun k hk =>
    Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 31))) top) (Nat.le_of_lt hq)
  have e5 : FoNums.w = 5 := rfl
  have e : FoNums.w + h.d ≤ 36 := by omega
  exact lw_all (2 ^ 158) 40 _ wk _ _ _ _ _ _ (by norm_num) (by omega)
    (Nat.le_sub_one_of_lt (Nat.lt_of_le_of_lt (by norm_num) hq)) (pw _ hv)
    (Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_right _ e) (by norm_num : 36 * 2 ^ 158 ≤
      2 ^ 191)) (Nat.le_of_lt hq)) (pw _ hd)

/-- **At the kind's own errors**: the written rounds' least errors are at most 2^-157, round by
round. -/
theorem lookupC_written (L : List LookupCCaller) (hL : OkLookupC L) (c : LookupCCaller)
    (hc : c ∈ L) (wk : ℕ) (ds : List RDT) (hP : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = forEnts wk c.h) (ε' : Err (uLT (ckP .two) ds))
    (hb : bearT ds _ ((kLookupC L).ε c) = some ε') : Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 157) := by
  refine bearT_below ds _ _ ε' hb hP ?_
  rw [he]
  show List.Forall₂ _ (errList (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e) _
  rw [forB_eps]
  exact forEps_lw (hL c hc) wk

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model VerifiableInference.OnPublicFiles
open scoped ENNReal

/-- The entries of the kind's own declared rounds are the library's list, at the setting's test
bits. -/
theorem entries_forEnts {p : P} {h : Forest.Shape} (hs : p.shape = some h)
    (H : FoNums.ok h = true) (hN : 1 < h.NC) (hr : p.entries.isSome = true) :
    p.rounds.map (·.entry) = Cb.Fo.forEnts (p.set.workOf .field .request) h := by
  obtain ⟨es, hes⟩ := Option.isSome_iff_exists.1 hr
  rw [rounds_entries, hes]
  unfold P.entries at hes
  rw [hs] at hes
  change lookEntries p.set h = some es at hes
  unfold lookEntries at hes
  split at hes
  · rename_i Pl hf
    obtain rfl := Option.some.inj hes
    have e : OnBytes.Model.forestSize h = { v := h.v, d := h.d, shifted := true } := by
      unfold OnBytes.Model.forestSize
      rw [decide_eq_true hN]
    rw [← e] at hf
    exact (Cb.Fo.plan_forest H hf).1
  · cases hes

/-- **At the closed caller of a link's digits.** -/
theorem dig_written {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : Nat} (Ex : Iop.ExtSpec) (Wp : Type)
    (H : DigOK set x tl D rad pp) (ds : List OnBytes.Maker.RDT)
    (hP : ∀ d ∈ ds, Fo.Peel.Plain (OnBytes.Flat.toRD d))
    (he : ds.map (·.entry) = (P.ofPlace set true x).rounds.map (·.entry))
    (ε' : Iop.Err (OnBytes.Maker.uLT (_root_.Run.ckP .two) ds))
    (hb : Fo.Peel.bearT ds _ ((kLookupCR [noRider (digCaller x tl D rad Ex Wp)]).ε
      (noRider (digCaller x tl D rad Ex Wp))) = some ε') :
    Iop.Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 157) :=
  lookupC_written [digCaller x tl D rad Ex Wp] (dig_ok Ex Wp H) _ (List.mem_singleton.2 rfl) _ ds hP
    (he.trans (entries_forEnts H.shape (dig_foOk H)
      (by
        rw [(DgP.shape2_parts H.tail).2.1.nc]
        decide) H.rounds)) ε' hb

end VerifiableInference.Desc.First.Look

#print axioms TwRound.lw_all
#print axioms OnBytes.Slice.sizeOf_le_nVals
#print axioms OnBytes.Slice.num_le
#print axioms OnBytes.Slice.below_plain
#print axioms Fo.Peel.bearT_below
#print axioms VerifiableInference.OnPublicFiles.forEps_lw
#print axioms VerifiableInference.OnPublicFiles.lookupC_written
#print axioms VerifiableInference.Desc.First.Look.entries_forEnts
#print axioms VerifiableInference.Desc.First.Look.dig_written
