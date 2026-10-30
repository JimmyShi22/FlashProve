-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindCost.lean: what proof of work costs in the compiler's three bounds: exact equations,
then closed forms.

Definitions, statements (in `Compile.Batch.Cost.Spec`) and proofs.
Generic: any interface L with batches, any lawful wire Wr of L without tests (`Wr.OK`,
Iop/BatchWire.lean), any type Nn of nonces with a fixed element (the fixed nonce), any data Dg of
the honest prover's search, any three lists gT, gL, gB of numbers of test bits, one number for each
round of `L.offline` (the offline IOP), `L.link` (the link IOP) and `L.onlineBatch` (a session). No protocol
occurs here.

A round with b test bits ("grinding", proof of work): the prover's message ends in a nonce, the
verifier's message holds b further uniform bits, and the verifier rejects unless all of them are 0
(`L.grind`, Iop/BatchGrind.lean; the wire: `Wr.grind Dg ..`, Iop/GrindWire.lean).
The compiler's three bounds for rounds that may have a test (CompileK/GrindMain.lean)
are terms at the wire with tests. Here each of them is tied to the same term
at the wire without tests.

Main names:
  `Spec.alpha_work`: under `Wr.OK`,
      alphaBG (Wr.grind ..) M = alphaBG Wr M + (gFail Dg gT + gFail Dg gL + maxBatchSize · gFail Dg gB).
    `gFail`: the sum of (1 - 2^-b)^(tries) over the rounds with a test: some search of the offline
    IOP, of the drawn link, of one of the maxBatchSize slots of a session finds no nonce. (A shared search,
    which runs once, is charged maxBatchSize times: the compiler's union bound.)
  `Spec.eps_work`: epsB (Wr.grind ..) M = epsB Wr M. The formula does not move: the verifier
    evaluates the typed oracles as often as before. What moves is the number M.εs that is put in: a
    bound on every round-by-round error of the interface with tests. That number is one that `M`
    lists (the data field `LH.Nums.εs`, Iop/InteractiveOracleProof.lean): that the interface with tests is sound at
    the number that is listed for it is no statement of this file; that tie is `grindPropsK`
    (Hiop/GrindK.lean), under the hypotheses of its statement (that condition itself asks soundness
    of the parts one level down: the tie carries soundness, it does not found it).
  `Spec.zeta_work`: under `Wr.OK`,
      zetaBGen (L.grind ..) p M (hashTermsBGTot (Wr.grind ..) p) t n
        = zetaBGen L p M (hashTermsBGTot Wr p) t n + sqWork .. n.
    `sqWork` n = (searches of setup and n batches, `xGr`) · (all Fiat-Shamir evaluations of the
    honest parties, every try counted at its cap, `xFbG`) / 2^min(sFS, λ). It does not depend on
    the adversary's number t of queries: the part of ζ that is linear in t is that of the scheme
    without work.
  Guard, `Spec.zeros` (`alpha_zero`, `sqWork_zero`, `zeta_zero`): under `Wr.OK` and 1 ≤ L.maxBatchSize, at
    lists of zeros the three bounds are those of the wire without tests. (The scheme at lists of
    zeros is not the scheme without work: its wire has one block more, which nobody reads. The
    guards are on the bounds.)
  Closed forms, with the nine numbers of Top/ProgDrawClosedGr.lean (`Top.GrSums`, with
    `Top.GrSums.Of`: for each of the three protocols a bound on the tries after the first of one
    transcript, on its rounds with a test, on its sum of failure terms): `xGr_work_le`,
    `xFbG_work_le`, `sqWork_le`, `gFail_work_le`, each under the hypotheses of its statement.
  `flat`, `of_flat`: the nine numbers from five: kT, kL, kO rounds with a test at most; in each of
    them at most m tries after the first and a failure term of at most φ.

Limits: this file says nothing on any scheme: these are equations and inequalities between terms.
That `gFail` bounds the chance of a failed search, and that ζ bounds anything, is not shown here.
Every search is counted at its cap, not at its mean. No number here is a security level.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Counts
import Compile.Batch.CountsGrSumF
import Top.ProgDrawClosedGr

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cost
open Iop Compile Compile.Batch
open scoped ENNReal

variable {Nn : Type} [Inhabited Nn] {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (Wr : QueryLayout lam L)
  (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
  (gB : GBits L.onlineBatch.loc.shape) (p : Params)

/-- What work adds to the bound on privacy: searches times all tries, over 2^min(sFS, λ). -/
def sqWork (n : ℕ) : ℝ≥0∞ :=
  (xGr (Wr.grind Dg gT gL gB) p n : ℝ≥0∞) *
    (xFbG (Wr.grind Dg gT gL gB) p n : ℕ) / 2 ^ (min p.sFS lam)

/-! ## The exact equations -/

namespace Spec

/-- Under `Wr.OK`, completeness: work adds the sums of the failure terms. -/
def alpha_work : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X)
      (Wr : QueryLayout lam L) (Dg : GrData Nn) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
    Wr.OK → ∀ M : LH.Nums, alphaBG (Wr.grind Dg gT gL gB) M =
      alphaBG Wr M + (gFail Dg gT + gFail Dg gL + L.maxBatchSize * gFail Dg gB)

/-- Binding: the formula does not move. -/
def eps_work : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (M : LH.Nums),
    epsB (Wr.grind Dg gT gL gB) M = epsB Wr M

/-- Under `Wr.OK`, privacy: work adds one term, which does not depend on the adversary's number of
queries. -/
def zeta_work : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (p : Params),
    Wr.OK → ∀ (M : LH.Nums) (t n : ℕ),
      zetaBGen (L.grind Nn gT gL gB) p M (hashTermsBGTot (Wr.grind Dg gT gL gB) p) t n =
        zetaBGen L p M (hashTermsBGTot Wr p) t n + sqWork Wr Dg gT gL gB p n

/-- Guard: under `Wr.OK` and 1 ≤ L.maxBatchSize, at lists of zeros the three bounds are those of the wire
without tests. -/
def zeros : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (p : Params),
    Wr.OK → 1 ≤ L.maxBatchSize →
    ∀ M : LH.Nums,
      alphaBG (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) M = alphaBG Wr M ∧
      epsB (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) M = epsB Wr M ∧
      ∀ t n : ℕ,
        zetaBGen (L.grind Nn (GBits.zero _) (GBits.zero _) (GBits.zero _)) p M
            (hashTermsBGTot (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) p) t n =
          zetaBGen L p M (hashTermsBGTot Wr p) t n

end Spec

theorem alpha_work : Spec.alpha_work := by
  intro Nn _ I X lam L Wr Dg gT gL gB hW M
  rw [alphaBG_grind, alphaBG_of_ok hW]
  rfl

theorem eps_work : Spec.eps_work := fun _ _ _ _ _ _ Wr Dg gT gL gB M =>
  epsB_wireGrind Wr Dg gT gL gB M

theorem hashSq_work (hW : Wr.OK) (n : ℕ) :
    hashSqBG (Wr.grind Dg gT gL gB) p n = hashSqBG Wr p n + sqWork Wr Dg gT gL gB p n := by
  have e : xReq (L.grind Nn gT gL gB) n = xReq L n := rfl
  unfold hashSqBG sqWork
  rw [xTree_grind, xFb_grind, xGr_of_ok hW, e, Nat.cast_zero, zero_mul, ENNReal.zero_div, add_zero]
  abel

theorem hashTerms_work (hW : Wr.OK) (t n : ℕ) :
    hashTermsBGTot (Wr.grind Dg gT gL gB) p t n =
      hashTermsBGTot Wr p t n + sqWork Wr Dg gT gL gB p n := by
  unfold hashTermsBGTot
  rw [muB_grind, hashSq_work Wr Dg gT gL gB p hW, add_assoc]

theorem zeta_work : Spec.zeta_work := by
  intro Nn _ I X lam L Wr Dg gT gL gB p hW M t n
  have e : zetaBGen (L.grind Nn gT gL gB) p M = zetaBGen L p M := rfl
  rw [e]
  unfold zetaBGen
  rw [hashTerms_work Wr Dg gT gL gB p hW]
  abel

/-! ## Closed forms -/

variable {Wr Dg gT gL gB p}

/-- the searches of setup and n batches -/
theorem xGr_work_le {σ : Top.GrSums} (hσ : Top.GrSums.Of Dg gT gL gB σ) (hN : 1 ≤ L.maxBatchSize) (n : ℕ) :
    xGr (Wr.grind Dg gT gL gB) p n ≤ σ.sT + p.leaves * σ.sL + n * (L.maxBatchSize * σ.sO) := by
  rw [xGr_grind]
  have t1 := le_trans (gSearchL_le Dg 0 1 _ gT) (le_trans (le_of_eq (Nat.one_mul _)) hσ.sT)
  have t2 := le_trans (gSearchL_le Dg 0 1 _ gL) (le_trans (le_of_eq (Nat.one_mul _)) hσ.sL)
  have t3 := le_trans (gSearch_le Dg 0 _ hN _ L.onlineBatch.ann gB) (Nat.mul_le_mul_left _ hσ.sO)
  exact Nat.add_le_add (Nat.add_le_add t1 (Nat.mul_le_mul_left _ t2)) (Nat.mul_le_mul_left _ t3)

/-- all Fiat-Shamir evaluations of the honest parties, every try counted at its cap -/
theorem xFbG_work_le {σ : Top.GrSums} (hσ : Top.GrSums.Of Dg gT gL gB σ) (hN : 1 ≤ L.maxBatchSize) (n : ℕ) :
    xFbG (Wr.grind Dg gT gL gB) p n ≤
      xFb (L := L) p n + (σ.mT + p.leaves * σ.mL + n * (L.maxBatchSize * σ.mO)) := by
  rw [xFbG_eq, xFb_grind]
  refine Nat.add_le_add_left (le_trans (xMore_grind_le Wr Dg gT gL gB p hN n) ?_) _
  exact Nat.add_le_add (Nat.add_le_add hσ.mT (Nat.mul_le_mul_left _ hσ.mL))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hσ.mO))

/-- What work adds to ζ, closed: for every Y that is at least the count of Fiat-Shamir evaluations
without further tries (`xFb`), and every e that is at most the salt length `p.sFS` and at most λ.
(not all hypotheses are named here: see the statement below) -/
theorem sqWork_le {σ : Top.GrSums} (hσ : Top.GrSums.Of Dg gT gL gB σ) (hN : 1 ≤ L.maxBatchSize) (n Y e : ℕ)
    (h2 : xFb (L := L) p n ≤ Y) (e2 : e ≤ p.sFS) (e3 : e ≤ lam) :
    sqWork Wr Dg gT gL gB p n ≤
      (((σ.sT + p.leaves * σ.sL + n * (L.maxBatchSize * σ.sO)) *
          (Y + (σ.mT + p.leaves * σ.mL + n * (L.maxBatchSize * σ.mO))) : ℕ) : ℝ≥0∞) / 2 ^ e := by
  unfold sqWork
  rw [← Nat.cast_mul]
  exact frac_le
    (Nat.mul_le_mul (xGr_work_le hσ hN n)
      (le_trans (xFbG_work_le hσ hN n) (Nat.add_le_add_right h2 _))) (le_min e2 e3)

omit [Inhabited Nn] in
/-- What work adds to α, closed. -/
theorem gFail_work_le {σ : Top.GrSums} (hσ : Top.GrSums.Of Dg gT gL gB σ) :
    gFail Dg gT + gFail Dg gL + L.maxBatchSize * gFail Dg gB ≤ σ.qT + σ.qL + L.maxBatchSize * σ.qO :=
  add_le_add (add_le_add hσ.qT hσ.qL) (mul_le_mul' le_rfl hσ.qO)

end Compile.Batch.Cost

namespace Compile.Batch.Cost
open Iop Compile Compile.Batch
open scoped ENNReal

variable {Nn : Type}

/-! ## Lists before and after the blocks -/

/-- Nine numbers that bound the three lists (`Top.GrSums.Of`) also bound the same lists on the
shapes after verifier messages are made from blocks (`GBits.pull`). -/
theorem ofPull {Dg : GrData Nn} {sT sL sB : Shape} {gT : GBits sT} {gL : GBits sL}
    {gB : GBits sB} {σ : Top.GrSums} (h : Top.GrSums.Of Dg gT gL gB σ) (aT : Samplers sT)
    (aL : Samplers sL) (aB : Samplers sB) :
    Top.GrSums.Of Dg (gT.pull aT) (gL.pull aL) (gB.pull aB) σ where
  mT := by rw [sumMo_eq_sumF, sumF_pull, ← sumMo_eq_sumF]; exact h.mT
  mL := by rw [sumMo_eq_sumF, sumF_pull, ← sumMo_eq_sumF]; exact h.mL
  mO := by rw [sumMo_eq_sumF, sumF_pull, ← sumMo_eq_sumF]; exact h.mO
  sT := by rw [nTests_eq_sumF, sumF_pull, ← nTests_eq_sumF]; exact h.sT
  sL := by rw [nTests_eq_sumF, sumF_pull, ← nTests_eq_sumF]; exact h.sL
  sO := by rw [nTests_eq_sumF, sumF_pull, ← nTests_eq_sumF]; exact h.sO
  qT := by rw [gFail_eq_sumF, sumF_pull, ← gFail_eq_sumF]; exact h.qT
  qL := by rw [gFail_eq_sumF, sumF_pull, ← gFail_eq_sumF]; exact h.qL
  qO := by rw [gFail_eq_sumF, sumF_pull, ← gFail_eq_sumF]; exact h.qO

theorem allLe_pull {n : ℕ} :
    ∀ {s : Shape} (a : Samplers s) {g : GBits s}, g.AllLe n → (g.pull a).AllLe n
  | [], _, _, _ => trivial
  | _ :: _, (_, as), (_, _), h => ⟨h.1, allLe_pull as h.2⟩

/-! ## Five numbers in the place of nine -/

/-- The nine numbers from five: kT, kL, kO rounds with a test; m tries after the first and a failure
term φ in each. -/
def flat (kT kL kO m : ℕ) (φ : ℝ≥0∞) : Top.GrSums :=
  ⟨kT * m, kL * m, kO * m, kT, kL, kO, kT * φ, kL * φ, kO * φ⟩

/-- every round with a test has at most m tries after the first and a failure term of at most φ -/
def Capped (Dg : GrData Nn) (m : ℕ) (φ : ℝ≥0∞) : {s : Shape} → GBits s → Prop
  | [], _ => True
  | _ :: _, (b, g) => (b ≠ 0 → Dg.mo b ≤ m ∧ failBits Dg b ≤ φ) ∧ Capped Dg m φ g

theorem sumMo_le {Dg : GrData Nn} {m : ℕ} {φ : ℝ≥0∞} :
    ∀ {s : Shape} {g : GBits s}, Capped Dg m φ g → GBits.sumMo Dg s g ≤ nTests s g * m
  | [], _, _ => Nat.zero_le _
  | _ :: s, (b, g), h => by
      show (if b = 0 then 0 else Dg.mo b) + GBits.sumMo Dg s g ≤
        ((if b = 0 then 0 else 1) + nTests s g) * m
      rw [Nat.add_mul]
      refine Nat.add_le_add ?_ (sumMo_le h.2)
      by_cases hb : b = 0
      · rw [if_pos hb, if_pos hb, Nat.zero_mul]
      · rw [if_neg hb, if_neg hb, Nat.one_mul]
        exact (h.1 hb).1

theorem gFail_le {Dg : GrData Nn} {m : ℕ} {φ : ℝ≥0∞} :
    ∀ {s : Shape} {g : GBits s}, Capped Dg m φ g → gFail Dg g ≤ (nTests s g : ℝ≥0∞) * φ
  | [], _, _ => zero_le _
  | _ :: s, (b, g), h => by
      show failBits Dg b + gFail Dg g ≤ (((if b = 0 then 0 else 1) + nTests s g : ℕ) : ℝ≥0∞) * φ
      rw [Nat.cast_add, add_mul]
      refine add_le_add ?_ (gFail_le h.2)
      by_cases hb : b = 0
      · subst hb
        exact zero_le _
      · rw [if_neg hb, Nat.cast_one, one_mul]
        exact (h.1 hb).2

/-- Under the hypotheses below, the five numbers give the nine. -/
theorem of_flat {Dg : GrData Nn} {sT sL sB : Shape} {gT : GBits sT} {gL : GBits sL}
    {gB : GBits sB} {kT kL kO m : ℕ} {φ : ℝ≥0∞} (cT : Capped Dg m φ gT)
    (cL : Capped Dg m φ gL) (cB : Capped Dg m φ gB) (hT : nTests sT gT ≤ kT)
    (hL : nTests sL gL ≤ kL) (hB : nTests sB gB ≤ kO) :
    Top.GrSums.Of Dg gT gL gB (flat kT kL kO m φ) where
  mT := (sumMo_le cT).trans (Nat.mul_le_mul_right _ hT)
  mL := (sumMo_le cL).trans (Nat.mul_le_mul_right _ hL)
  mO := (sumMo_le cB).trans (Nat.mul_le_mul_right _ hB)
  sT := hT
  sL := hL
  sO := hB
  qT := (gFail_le cT).trans (mul_le_mul' (Nat.cast_le.2 hT) le_rfl)
  qL := (gFail_le cL).trans (mul_le_mul' (Nat.cast_le.2 hL) le_rfl)
  qO := (gFail_le cB).trans (mul_le_mul' (Nat.cast_le.2 hB) le_rfl)

/-! ## Guards: lists of zeros -/

theorem nTests_zero : ∀ s : Shape, nTests s (GBits.zero s) = 0
  | [] => rfl
  | _ :: s => by
      show (if (0 : ℕ) = 0 then 0 else 1) + nTests s (GBits.zero s) = 0
      rw [if_pos rfl, nTests_zero s]

theorem capped_zero (Dg : GrData Nn) (m : ℕ) (φ : ℝ≥0∞) : ∀ s : Shape, Capped Dg m φ (GBits.zero s)
  | [] => trivial
  | _ :: s => ⟨fun h => (h rfl).elim, capped_zero Dg m φ s⟩

/-- at lists of zeros all nine numbers can be 0 -/
theorem of_zero (Dg : GrData Nn) (sT sL sB : Shape) :
    Top.GrSums.Of Dg (GBits.zero sT) (GBits.zero sL)
      (GBits.zero sB) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  have h := of_flat (kT := 0) (kL := 0) (kO := 0) (capped_zero Dg 0 0 sT) (capped_zero Dg 0 0 sL)
    (capped_zero Dg 0 0 sB) (nTests_zero sT).le (nTests_zero sL).le (nTests_zero sB).le
  simpa [flat] using h

variable [Inhabited Nn] {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (Wr : QueryLayout lam L)
  (Dg : GrData Nn) (p : Params)

/-- Guard: under `Wr.OK`, at lists of zeros α is that of the wire without tests. -/
theorem alpha_zero (hW : Wr.OK) (M : LH.Nums) :
    alphaBG (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) M = alphaBG Wr M := by
  have h := gFail_work_le (L := L) (of_zero Dg L.offline.shape L.link.shape L.onlineBatch.loc.shape)
  rw [alpha_work Nn I X lam L Wr Dg _ _ _ hW]
  have h0 : gFail Dg (GBits.zero L.offline.shape) + gFail Dg (GBits.zero L.link.shape) +
        L.maxBatchSize * gFail Dg (GBits.zero L.onlineBatch.loc.shape) = 0 := by
    refine le_antisymm (h.trans (le_of_eq ?_)) (zero_le _)
    simp
  rw [h0, add_zero]

/-- Guard: for 1 ≤ L.maxBatchSize, at lists of zeros work adds nothing to ζ. -/
theorem sqWork_zero (hN : 1 ≤ L.maxBatchSize) (n : ℕ) :
    sqWork Wr Dg (GBits.zero _) (GBits.zero _) (GBits.zero _) p n = 0 := by
  have h :=
    xGr_work_le (Wr := Wr) (p := p) (of_zero Dg L.offline.shape L.link.shape L.onlineBatch.loc.shape) hN n
  have h0 : xGr (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) p n = 0 :=
    Nat.le_zero.1 (h.trans (by simp))
  unfold sqWork
  rw [h0, Nat.cast_zero, zero_mul, ENNReal.zero_div]

theorem zeta_zero (hW : Wr.OK) (hN : 1 ≤ L.maxBatchSize) (M : LH.Nums) (t n : ℕ) :
    zetaBGen (L.grind Nn (GBits.zero _) (GBits.zero _) (GBits.zero _)) p M
        (hashTermsBGTot (Wr.grind Dg (GBits.zero _) (GBits.zero _) (GBits.zero _)) p) t n =
      zetaBGen L p M (hashTermsBGTot Wr p) t n := by
  rw [zeta_work Nn I X lam L Wr Dg _ _ _ p hW, sqWork_zero Wr Dg p hN, add_zero]

theorem zeros : Spec.zeros := fun Nn _ I X lam L Wr Dg p hW hN M =>
  ⟨alpha_zero Wr Dg hW M, eps_work Nn I X lam L Wr Dg _ _ _ M, zeta_zero Wr Dg p hW hN M⟩

end Compile.Batch.Cost
