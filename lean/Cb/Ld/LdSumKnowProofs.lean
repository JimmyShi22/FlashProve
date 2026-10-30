-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumKnowProofs.lean: the proof of `Spec.ld_sum_know` (Cb/Ld/LdSumKnow.lean) (round-by-round
knowledge soundness of the zero-knowledge sumcheck that folds, the block `Y.ior` of
Cb/Ld/LdSum.lean, under the hypotheses of its statement). No axiom beyond Lean's three; no
hypothesis beyond those in the statements' own text.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The proof is by `Iop.Reduction.Know.of_badFam` (Ior/Know.lean): a family of bad sets within the
errors, and a backward step on clean transcripts (`BadFam.Clean`, Iop/Rbr.lean: no verifier message
of the transcript is bad).
  The bad sets. Round of the coefficient: the values at which some member of the list around (input
  oracles, fresh mask) meets the new claim while what is left of it without the fresh mask is no
  witness of the input statement (`ldk_round_coeff`; the new claim is affine in the coefficient:
  `SumPar.stg0_val`, Cb/Ld/LdSumClaimY.lean). Round from the stage (k' + 1, h'), with the claim S,
  the running target σ and the prover's round polynomial q: `Halving.BadAt` for the claims "S.val =
  σ" before and "q sums to σ, and (S.next γ).val = q(γ)" after (`ldh_step_cnt`; a false claim turns
  true at no more than n values: `SStg.poly`, `hev_poly`, `lds_poly`).
  The backward step. If the verifier outputs a statement, all its checks hold. The new oracles are
  the folds of all rounds in closed form (`ldx_fold_closed`), the new claim is the last stage's
  claim (`SStg.val_zero`, `SumPar.stg_end`). Then `ldh_good` round by round, from the last to the
  first, and the round of the coefficient.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumKnow
import Cb.Ld.LdHideProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop LdCode

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P)

/-- the rounds of the sumcheck that are left -/
abbrev rnds (k : ℕ) : Shape := List.replicate k (sRound E Y.Ch Y.n)

/-- On messages a round of the chain is `foldM` (Cb/Ld/LdSumClaim.lean). -/
theorem step_foldW_fst (k : ℕ) :
    ∀ (h : ℕ) (γ : E) (w : (Y.sg (k + 1) h).MR),
      ((Halving.step Y.C Y.Z Y.Zw k h).foldW γ w).1 = foldM k h γ w.1
  | 0, γ, w => by
      funext j
      rcases j with a | a <;> rfl
  | h + 1, γ, w => by
      funext j
      rcases j with a | a | a <;> rfl

theorem chPt_eq :
    ∀ (k h : ℕ) (γ : HPt (sVars E Y.n k)), stgPt Y.C Y.Z Y.Zw k h (sPt Y.n k γ) = Y.chPt k h γ
  | 0, _, _ => rfl
  | k + 1, h, γ => by
      show ((Fin.cons γ.1 (sPt Y.n k γ.2) : Fin (k + 1) → E) 0,
          stgPt Y.C Y.Z Y.Zw k (h - 1)
            (Fin.tail (Fin.cons γ.1 (sPt Y.n k γ.2) : Fin (k + 1) → E))) =
        (γ.1, Y.chPt k (h - 1) γ.2)
      rw [Fin.tail_cons, chPt_eq k (h - 1) γ.2]
      rfl

variable [Fintype E] [Fintype P]

/-- the claims of a round -/
def cBefore {k : ℕ} (h : ℕ) (S : SStg E Y.C.J Y.Z.J k) (σ : E) : (Y.sg k h).MR → Prop := fun w =>
  S.val Y.n h w.1 = σ
def cAfter {k : ℕ} (h : ℕ) (S : SStg E Y.C.J Y.Z.J (k + 1)) (σ : E)
    (q : Fin (Y.n + 1) → E) (γ : E) : (Y.sg k (h - 1)).MR → Prop :=
  fun w' => (HVar.plain E Y.n).phi q = σ ∧ (S.next γ).val Y.n (h - 1) w'.1 = hev q γ

/-- The bad sets of the rounds of the sumcheck. -/
def badR (e : ℕ) : (k h : ℕ) → (Y.sg k h).Word → SStg E Y.C.J Y.Z.J k → E → BadFam (Y.rnds k)
  | 0, _, _, _, _ => ()
  | k + 1, h, f, S, σ =>
      (fun m =>
          {c | (Halving.step Y.C Y.Z Y.Zw k h).BadAt
            e (Y.cBefore h S σ) (Y.cAfter h S σ m.2 (Y.val c)) f (Y.val c)},
        fun m c =>
          badR e k (h - 1) ((Halving.step Y.C Y.Z Y.Zw k h).fold (Y.val c) f)
            (S.next (Y.val c)) (hev m.2 (Y.val c)))

/-- what the errors of the rounds that are left require of the codes; g i is the error of the i-th
of them -/
def RErr (e : ℕ) : (k h : ℕ) → (ℕ → ℕ) → Prop
  | 0, _, _ => True
  | k + 1, h, g =>
    (∃ L b bs bw : ℕ,
      (Y.sg (k + 1) h).ListAt e L ∧
      (Y.C.il (Fin k → Bool)).MCAat e b ∧
      (0 < h →
        (Y.Z.il (Fin (h - 1) → Bool)).MCAat e bs ∧ (Y.Zw.il (Fin (h - 1) → Bool)).MCAat e bw) ∧
      (b + if 0 < h then bs + bw else 0) + L * Y.n ≤ g 0) ∧
    RErr e k (h - 1) fun j => g (j + 1)

omit [Fintype P] in
/-- Under `hS` (`S.Deg Y.n h`), a false claim turns true at no more than n values. -/
theorem spoil_le {k : ℕ} (h : ℕ) (S : SStg E Y.C.J Y.Z.J (k + 1)) (hS : S.Deg Y.n h) (σ : E)
    (q : Fin (Y.n + 1) → E) (w : (Y.sg (k + 1) h).MR) (hw : ¬ Y.cBefore h S σ w) :
    cnt (fun γ => Y.cAfter h S σ q γ ((Halving.step Y.C Y.Z Y.Zw k h).foldW γ w)) ≤ Y.n := by
  obtain ⟨p, hp, h01, hpγ⟩ := S.poly Y.n hS w.1
  obtain ⟨Q, hQ, hQe⟩ := hev_poly q
  by_cases hc : (HVar.plain E Y.n).phi q = σ
  · have hne : p.eval 0 + p.eval 1 ≠ Q.eval 0 + Q.eval 1 := by
      rw [h01, ← hQe, ← hQe, ← plain_phi E E Y.n q, hc]
      exact hw
    refine le_trans (cnt_mono fun γ hγ => ?_)
      (lds_poly E (Y.n + 1) p Q (Nat.lt_succ_of_le hp) (Nat.lt_succ_of_le hQ) hne)
    rw [hpγ γ, ← hQe γ, ← Y.step_foldW_fst k h γ w]
    exact hγ.2
  · rw [cnt_false fun γ hγ => hc hγ.1]
    exact Nat.zero_le _

theorem badR_within (d e : ℕ) (hOK : Spec.CodesOK E P Y.C Y.Z Y.Zw d e)
    (hv : Function.Injective Y.val) :
    ∀ (k h : ℕ) (g : ℕ → ℕ), Y.RErr e k h g →
      ∀ (f : (Y.sg k h).Word) (S : SStg E Y.C.J Y.Z.J k) (σ : E),
        S.Deg Y.n h → (Y.badR e k h f S σ).Within (sErr Y.n k g) := by
  intro k
  induction k with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ k ih =>
    intro h g hg f S σ hS
    obtain ⟨⟨L, b, bs, bw, hL, hb, hm, hle⟩, hrest⟩ := hg
    refine ⟨fun m => ?_, fun m c => ih (h - 1) _ hrest _ _ _ (hS.next (Y.val c))⟩
    refine le_trans ?_ hle
    refine le_trans
      (lss_cnt_val Y.Ch E Y.val hv fun γ =>
        (Halving.step Y.C Y.Z Y.Zw k h).BadAt e (Y.cBefore h S σ) (Y.cAfter h S σ m.2 γ) f γ) ?_
    exact ldh_step_cnt E P Y.C Y.Z Y.Zw k h d e L b bs bw Y.n hOK hb hm hL (Y.cBefore h S σ)
      (Y.cAfter h S σ m.2) (fun w hw => Y.spoil_le h S hS σ m.2 w hw) f

omit [Fintype E] in
/-- The rounds of the sumcheck, backwards. -/
theorem rounds_back (d e : ℕ) (hOK : Spec.CodesOK E P Y.C Y.Z Y.Zw d e) :
    ∀ (k h : ℕ) (f : (Y.sg k h).Word) (S : SStg E Y.C.J Y.Z.J k) (σ : E) (τ : Tr (Y.rnds k)),
      (Y.badR e k h f S σ).Clean τ →
      HCons (sVars E Y.n k) σ (sQ Y.n k τ.plains) (sG Y.val Y.n k τ.rho) →
      ∀ w : (Y.sg 0 (endH k h)).MR,
        (Y.sg 0 (endH k h)).Near e
          ((stgChain Y.C Y.Z Y.Zw k h).foldAll (Y.chPt k h (sG Y.val Y.n k τ.rho)) f)
          ((Y.sg 0 (endH k h)).enc w.1 w.2) →
        (SStg.nextAll Y.n k (sG Y.val Y.n k τ.rho) S).val Y.n (endH k h) w.1 =
          hFin (sVars E Y.n k) σ (sQ Y.n k τ.plains) (sG Y.val Y.n k τ.rho) →
        (Y.sg k h).Near e f
          ((Y.sg k h).enc
            ((stgChain Y.C Y.Z Y.Zw k h).backAll d (Y.chPt k h (sG Y.val Y.n k τ.rho)) f w).1
            ((stgChain Y.C Y.Z Y.Zw k h).backAll d (Y.chPt k h (sG Y.val Y.n k τ.rho)) f w).2) ∧
        S.val Y.n h
            ((stgChain Y.C Y.Z Y.Zw k h).backAll d (Y.chPt k h (sG Y.val Y.n k τ.rho)) f w).1 =
          σ := by
  intro k
  induction k with
  | zero => exact fun _ _ _ _ _ _ _ w hn hc => ⟨hn, hc⟩
  | succ k ih =>
    intro h f S σ τ hcl hcons w hn hc
    obtain ⟨m, c, τ'⟩ := τ
    obtain ⟨hc0, hcl'⟩ := hcl
    obtain ⟨hphi, hcons'⟩ := hcons
    obtain ⟨n1, c1⟩ := ih (h - 1) ((Halving.step Y.C Y.Z Y.Zw k h).fold (Y.val c) f)
      (S.next (Y.val c)) (hev m.2 (Y.val c)) τ' hcl' hcons' w hn hc
    have hg := ldh_good E P _ _ (Halving.step Y.C Y.Z Y.Zw k h) d e
      (lss_stg_laws E P Y.C Y.Z Y.Zw k (h - 1) hOK.1.1 hOK.1.2.1 hOK.1.2.2)
      (lss_stg_dist E P Y.C Y.Z Y.Zw k (h - 1) d hOK.2.1.1 hOK.2.1.2.1 hOK.2.1.2.2)
      (step_laws E P Y.C Y.Z Y.Zw d e hOK k h) hOK.2.2 (Y.cBefore h S σ)
      (Y.cAfter h S σ m.2 (Y.val c)) f (Y.val c) hc0 _ n1 ⟨hphi, c1⟩
    exact ⟨hg.1, hg.2.1⟩

/-- the error of the i-th round of the sumcheck, as Y.err has it -/
def gErr (Lst mC mS mW : ℕ → ℕ) (i : ℕ) : ℕ :=
  mC (i + 1) + (if i + 1 ≤ Y.h then mS (i + 1) + mW (i + 1) else 0) + Lst i * Y.n

theorem rErr_of (e : ℕ) (Lst mC mS mW : ℕ → ℕ) (hE : Y.ErrOK e Lst mC mS mW) :
    ∀ k' j0 : ℕ, j0 + k' = Y.k → Y.RErr e k' (Y.h - j0) fun i => Y.gErr Lst mC mS mW (j0 + i) := by
  intro k'
  induction k' with
  | zero => exact fun _ _ => trivial
  | succ k' ih =>
    intro j0 hj
    have e2 : Y.h - (j0 + 1) = Y.h - j0 - 1 := by omega
    refine ⟨⟨Lst j0, mC (j0 + 1), mS (j0 + 1), mW (j0 + 1), ?_, ?_, ?_, ?_⟩, ?_⟩
    · have h1 : (stg Y.C Y.Z Y.Zw (Y.k - j0) (Y.h - j0)).ListAt e (Lst j0) := hE.list j0 (by omega)
      have e1 : Y.k - j0 = k' + 1 := by omega
      rw [e1] at h1
      exact h1
    · have h1 := hE.mcaC (j0 + 1) (by omega) (by omega)
      have e1 : Y.k - (j0 + 1) = k' := by omega
      rw [e1] at h1
      exact h1
    · intro hpos
      have a := hE.mcaS (j0 + 1) (by omega) (by omega)
      have b := hE.mcaW (j0 + 1) (by omega) (by omega)
      rw [e2] at a b
      exact ⟨a, b⟩
    · show (mC (j0 + 1) + if 0 < Y.h - j0 then mS (j0 + 1) + mW (j0 + 1) else 0) + Lst j0 * Y.n ≤
        mC (j0 + 0 + 1) + (if j0 + 0 + 1 ≤ Y.h then mS (j0 + 0 + 1) + mW (j0 + 0 + 1) else 0) +
          Lst (j0 + 0) * Y.n
      simp only [Nat.add_zero]
      by_cases hp : 0 < Y.h - j0
      · exact le_of_eq (by rw [if_pos hp, if_pos (by omega : j0 + 1 ≤ Y.h)])
      · exact le_of_eq (by rw [if_neg hp, if_neg (by omega : ¬ j0 + 1 ≤ Y.h)])
    · have h1 := ih (j0 + 1) (by omega)
      have ef : (fun i => Y.gErr Lst mC mS mW (j0 + 1 + i)) =
          fun j => Y.gErr Lst mC mS mW (j0 + (j + 1)) :=
        funext fun i => by rw [Nat.add_assoc, Nat.add_comm 1 i]
      rw [e2, ef] at h1
      exact h1

/-! ## The round of the coefficient -/

omit [Fintype E] [Fintype P] in
theorem inM_eq (w : (Y.sg Y.k Y.h).MR) :
    Y.inM w.1 =
      (dropM (D₁ := Y.C.il (Fin Y.k → Bool)) (D₂ := Y.Z.il (Fin Y.h → Bool))
        (W := Y.Zw.il (Fin Y.h → Bool)) w).1 := by
  funext j
  cases j <;> rfl

omit [Fintype E] [Fintype P] in
theorem dropW_word0 (y : Y.Cin.Word) (z : Y.Cw.Word) :
    dropW (D₁ := Y.C.il (Fin Y.k → Bool)) (D₂ := Y.Z.il (Fin Y.h → Bool))
        (W := Y.Zw.il (Fin Y.h → Bool)) (Y.word0 y z) = y := by
  funext p
  cases p <;> rfl

/-- the claim after the round of the coefficient -/
def c0After (x : Y.Xi) (μ : E) (ε : E) : (Y.sg Y.k Y.h).MR → Prop := fun w =>
  (Y.stg0 x ε).val Y.n Y.h w.1 = μ + x.1 * ε

/-- The bad values of the coefficient, and the set of the challenges that give them. -/
def bad0E (e : ℕ) (a : Y.Xi × Y.Cin.Word) (m : Y.round0.Msg) (ε : E) : Prop :=
  ∃ w : (Y.sg Y.k Y.h).MR,
    ((Y.sg Y.k Y.h).Near e (Y.word0 a.2 m.1) ((Y.sg Y.k Y.h).enc w.1 w.2) ∧ Y.c0After a.1 m.2 ε w) ∧
    ¬ (Y.Cin.Near e (dropW (Y.word0 a.2 m.1)) (Y.Cin.enc (dropM w).1 (dropM w).2) ∧
      Y.slIn.Holds a.1 (dropM w).1)
def bad0 (e : ℕ) (a : Y.Xi × Y.Cin.Word) (m : Y.round0.Msg) : Set Y.Ch :=
  {c | Y.bad0E e a m (Y.val c)}

omit [Fintype P] in
theorem spoil0_le (x : Y.Xi) (μ : E) (w : (Y.sg Y.k Y.h).MR)
    (hw : ¬ Y.slIn.Holds x
      (dropM (D₁ := Y.C.il (Fin Y.k → Bool)) (D₂ := Y.Z.il (Fin Y.h → Bool))
        (W := Y.Zw.il (Fin Y.h → Bool)) w).1) :
    cnt (fun ε => Y.c0After x μ ε w) ≤ 1 := by
  have hne : (∑ j, Y.slIn x.2 j * Y.inM w.1 j) - x.1 ≠ 0 := by
    rw [Y.inM_eq w]
    exact sub_ne_zero.mpr hw
  refine le_trans (cnt_mono fun ε hε => ?_) (lds_affine E _ (Y.psi0 w.1 - μ) hne)
  have h1 : (Y.stg0 x ε).val Y.n Y.h w.1 = μ + x.1 * ε := hε
  rw [Y.stg0_val x ε w.1] at h1
  linear_combination h1

theorem bad0_cnt (e L : ℕ) (hv : Function.Injective Y.val) (hL : (Y.sg Y.k Y.h).ListAt e L)
    (a : Y.Xi × Y.Cin.Word) (m : Y.round0.Msg) :
    cnt (fun c => c ∈ Y.bad0 e a m) ≤ L := by
  have h1 := ldk_round_coeff E P (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool))
    (Y.Zw.il (Fin Y.h → Bool)) e L 1 hL (fun w => Y.slIn.Holds a.1 w.1) (Y.c0After a.1 m.2)
    (fun w hw => Y.spoil0_le a.1 m.2 w hw) (Y.word0 a.2 m.1)
  rw [Nat.mul_one] at h1
  exact le_trans (lss_cnt_val Y.Ch E Y.val hv (Y.bad0E e a m)) h1

/-- The bad sets of the block. -/
def bad (e : ℕ) (a : Y.Xi × Y.Cin.Word) : BadFam Y.ior.shape :=
  (fun m => Y.bad0 e a m,
    fun m c => Y.badR e Y.k Y.h (Y.word0 a.2 m.1) (Y.stg0 a.1 (Y.val c)) (m.2 + a.1.1 * Y.val c))

omit [Fintype E] [Fintype P] in
/-- The new oracles are the folds of all rounds. -/
theorem imp_eq (y : Y.Cin.Word) (τ : Tr Y.shape) :
    Y.imp y τ =
      Y.lastN.word
        ((stgChain Y.C Y.Z Y.Zw Y.k Y.h).foldAll
          (Y.chPt Y.k Y.h (Y.gam τ.rho)) (Y.word0 y τ.1.1)) := by
  rw [← Y.chPt_eq]
  exact (ldx_fold_closed E P Y.C Y.Z Y.Zw Y.k Y.h (Nat.le_add_right Y.h Y.g)
    (ldh_endH Y.k Y.h (Nat.le_add_right Y.h Y.g))
    (sPt Y.n Y.k (Y.gam τ.rho)) (Y.word0 y τ.1.1)).symm

end SumPar

theorem ld_sum_know (E P : Type) [Field E] [Fintype E] [Fintype P] : Spec.ld_sum_know E P := by
  intro Y d e Lst mC mS mW hOK hE hv hn hQ
  refine Reduction.Know.of_badFam (Y.bad e) (fun a _ => ?_) ?_
  · have hR := Y.rErr_of e Lst mC mS mW hE Y.k 0 (Nat.zero_add _)
    simp only [Nat.zero_add, Nat.sub_zero] at hR
    exact ⟨fun m => Y.bad0_cnt e (Lst 0) hv (hE.list 0 (Nat.zero_le _)) a m,
      fun m c => Y.badR_within d e hOK hv Y.k Y.h _ hR _ _ _ (Y.stg0_deg hn hQ a.1 (Y.val c))⟩
  · rintro ⟨x, y⟩ ⟨m, c, τ'⟩ b w' _ hclean hout hRB
    have hout' : (Y.out x (m, c, τ')).map (fun xo => (xo, Y.imp y (m, c, τ'))) = some b := hout
    unfold SumPar.out at hout'
    split_ifs at hout' with hH
    · obtain rfl := Option.some.inj hout'
      obtain ⟨hnear, hclaim⟩ := hRB
      have hlaws : Y.lastN.Laws := ldh_last_laws E P Y.C Y.Z Y.Zw _ _
      have hn1 : (Y.sg 0 (endH Y.k Y.h)).Near e
          ((stgChain Y.C Y.Z Y.Zw Y.k Y.h).foldAll
            (Y.chPt Y.k Y.h (sG Y.val Y.n Y.k τ'.rho)) (Y.word0 y m.1))
          ((Y.sg 0 (endH Y.k Y.h)).enc (Y.lastN.mrInv w').1 (Y.lastN.mrInv w').2) := by
        refine (ldh_rename_near E P _ _ Y.lastN hlaws e _ _).mpr ?_
        rw [hlaws.right]
        have h1 := Y.imp_eq y (m, c, τ')
        have h2 : Y.Cout.Near e (Y.imp y (m, c, τ')) (Y.Cout.enc w'.1 w'.2) := hnear
        rw [h1] at h2
        exact h2
      have hc1 : (SStg.nextAll Y.n Y.k (sG Y.val Y.n Y.k τ'.rho) (Y.stg0 x (Y.val c))).val
            Y.n (endH Y.k Y.h) (Y.lastN.mrInv w').1 =
          hFin (sVars E Y.n Y.k) (m.2 + x.1 * Y.val c)
            (sQ Y.n Y.k τ'.plains) (sG Y.val Y.n Y.k τ'.rho) := by
        rw [SStg.val_zero Y.n _ _ _ Fin.elim0]
        exact (Y.stg_end x (Y.val c) (sG Y.val Y.n Y.k τ'.rho) Fin.elim0 w'.1).trans hclaim
      obtain ⟨n0, c0⟩ := Y.rounds_back d e hOK Y.k Y.h (Y.word0 y m.1) (Y.stg0 x (Y.val c))
        (m.2 + x.1 * Y.val c) τ' hclean.2 hH _ hn1 hc1
      have h0 := not_not.mp fun hnot => hclean.1 ⟨_, ⟨n0, c0⟩, hnot⟩
      rw [Y.dropW_word0] at h0
      exact h0
    · cases hout'

end Cb
