--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Link/FoldKept.lean: THE SHARED FOLD's SECOND CORE: behind a fold of a group WITH KEPT
MEMBERS the claim is true at an honest prover's three folded messages and the kept members' own
messages. General in the stage. Beside Johnson/Prover/Link/FoldHolds.lean, which serves groups
without kept members; at V = 0 the two cores say the same.

The verifier's side. A kept member's main rows are not folded with the other rows
(OnBytes/Iop/Ground.lean, at GroupLayout). The fold hands on each kept form times one factor,
eps (1 - g_1) .. (1 - g_k) (foldKeptFactor, OnBytes/Iop/Fold.lean; foldOutput_kept,
OnBytes/Slice/BlkFoldOut.lean).
The honest side. V: the kept forms' value at the kept members' messages. It enters the sum over the
cube at the corner 0 alone: the summand gets eps V (1 - X_1) .. (1 - X_k). So round i's polynomial
gets eps V (1 - γ_1) .. (1 - γ_(i-1)) (1 - X): of what is sent, THE CONSTANT ALONE TURNS.
[Argued, proved nowhere: a strategy that is accepted at every point has no other choice: each round
polynomial, from the last one back, is fixed by the verifier's end value.]

Main names (namespace Johnson.Prover.Link).
  keptQ k a γ    the round polynomials of a times the corner's weight, in closed form
  keptQ_rounds, keptQ_causal   they are that summand's; a round's part does not hang on later draws
  foldQK         the honest round polynomials: foldQ with eps times keptQ at V
  fold_core_kept   THE CORE: the claim in front, the kept forms' value in it, is true, and the fresh
      table pairs (Pairs, FoldHolds.lean): then the claim behind is true: at every drawn
      coefficient, every drawn point and every V
  fold_turned_kept   a test that can fail: another first scalar, no drawn element 0: false
  keptVal N κ Ks   the kept forms' value at tables κ of lengths N: LETTERS
  keptVal_scale, eqk_list   the verifier's factor, read in the field
  fold_holds_kept   the same at the single rows that the description's fold returns (foldOutAt,
      Johnson/Prover/Link/FormFold.lean), their kept forms with them

By calls: honQ_rounds, summand_sum (Cb/Ld/LdSumHon.lean); HRounds.add_smul, HRounds.congr,
hSumAll_add_smul, SCausal.add_mul, plain_sum (Cb/Ld/LdSumRun.lean); runQ_rounds, runQ_inj, mid_at,
claimOf_shows (FoldHolds.lean); Alg.eqk_cons (Alg/Mle.lean); Form.entry_scale
(OnBytes/Iop/TensorLaws.lean); readE_foldKeptFactor (Johnson/Desc/First/Close/Law/InvMore.lean);
vecS_foldOutput_fits (OnBytes/Slice/BlkProxFold.lean). RECKONED HERE, NOT CALLED: the rounds of the
one new summand (keptQ_rounds, by keptQ's own recursion) and that the corner's weight sums to 1 over
the cube (sum_corner).

Limits. The claims are bare equations: stmG and stmS (OnBytes/Slice/BlkRead.lean) do not read kept
forms. κ and N are letters: THE TIE TO THE SOUNDNESS SIDE's READING of a row with kept members
(groupValue, keptWeight: Johnson/Desc/Means/) IS OWED BY THE CALLER. No member of fold_holds_kept's
premises is shown. FoldHolds.lean's limits hold here too: not every fresh table pairs; that the fold
says yes is not shown; nothing on how W is chosen. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FoldHolds
import Johnson.Desc.First.Close.Law.InvMore
import OnBytes.Iop.TensorLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb

/-! ## 1 The kept forms' term: V times the weight of the cube's corner 0 -/

/-- The weight of the corner 0 at a point with one coordinate more. -/
theorem eqk_corner_cons {k : ℕ} (x : GE) (z : Fin k → GE) :
    Alg.eqk (Fin.cons x z : Fin (k + 1) → GE) (fun _ => false) =
      (1 - x) * Alg.eqk z (fun _ => false) := by
  have h := Alg.eqk_cons x z false (fun _ => false)
  have e : (Fin.cons false (fun _ => false) : Fin (k + 1) → Bool) = fun _ => false := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  rw [e] at h
  exact h

/-- Over the cube that weight sums to 1. -/
theorem sum_corner : ∀ (k : ℕ) (c : GE),
    hSumAll (sVars GE 2 k) (fun z => c * Alg.eqk (sPt 2 k z) (fun _ => false)) = c
  | 0, c => by
      show c * Alg.eqk _ _ = c
      simp [Alg.eqk]
  | k + 1, c => by
      show (HVar.plain GE 2).sum (fun x => hSumAll (sVars GE 2 k) fun xs =>
        c * Alg.eqk (Fin.cons x (sPt 2 k xs) : Fin (k + 1) → GE) (fun _ => false)) = c
      have e : ∀ x : GE, (hSumAll (sVars GE 2 k) fun xs =>
          c * Alg.eqk (Fin.cons x (sPt 2 k xs) : Fin (k + 1) → GE) (fun _ => false)) =
          c * (1 - x) := fun x => by
        rw [← sum_corner k (c * (1 - x))]
        refine congrArg _ (funext fun xs => ?_)
        rw [eqk_corner_cons]
        ring
      rw [funext e, plain_sum]
      ring

/-- **The round polynomials of a times the corner's weight**, in closed form: round i's is
a_i (1 - X), a_i = a (1 - γ_1) .. (1 - γ_(i-1)). -/
def keptQ : (k : ℕ) → GE → HPt (sVars GE 2 k) → RIdx (sVars GE 2 k) → GE
  | 0, _, _, i => i.elim
  | _ + 1, a, _, .inl t => if t.val = 0 then a else if t.val = 1 then -a else 0
  | k + 1, a, γ, .inr i => keptQ k (a * (1 - γ.1)) γ.2 i

theorem keptQ_rounds : ∀ (k : ℕ) (a : GE) (γ : HPt (sVars GE 2 k)),
    HRounds (sVars GE 2 k) (fun z => a * Alg.eqk (sPt 2 k z) (fun _ => false)) (keptQ k a γ) γ
  | 0, _, _ => trivial
  | k + 1, a, γ => by
      refine ⟨fun x => ?_, ?_⟩
      · show hev (fun t : Fin 3 => if t.val = 0 then a else if t.val = 1 then -a else 0) x =
          hSumAll (sVars GE 2 k) fun xs =>
            a * Alg.eqk (Fin.cons x (sPt 2 k xs) : Fin (k + 1) → GE) (fun _ => false)
        have e : (fun xs : HPt (sVars GE 2 k) =>
            a * Alg.eqk (Fin.cons x (sPt 2 k xs) : Fin (k + 1) → GE) (fun _ => false)) =
            fun xs => a * (1 - x) * Alg.eqk (sPt 2 k xs) (fun _ => false) := by
          funext xs
          rw [eqk_corner_cons]
          ring
        rw [e, sum_corner]
        unfold hev
        rw [Fin.sum_univ_three]
        simp
        ring
      · refine HRounds.congr _ (fun xs => ?_) (keptQ_rounds k (a * (1 - γ.1)) γ.2)
        show a * (1 - γ.1) * Alg.eqk (sPt 2 k xs) (fun _ => false) =
          a * Alg.eqk (Fin.cons γ.1 (sPt 2 k xs) : Fin (k + 1) → GE) (fun _ => false)
        rw [eqk_corner_cons]
        ring

theorem keptQ_causal : ∀ (k : ℕ) (a : GE), SCausal 2 k (keptQ k a)
  | 0, _ => trivial
  | k + 1, a => ⟨fun _ _ _ => rfl, fun x => keptQ_causal k (a * (1 - x))⟩

/-! ## 2 The second core -/

section Field
variable (s : Sg) (n0 : ℕ) (t0 : GE) (v μ : s.cIn.J → GE) (φ : s.cFr.J → GE)
  (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε V : GE) (γ : HPt (sVars GE 2 (s.h + s.g)))

/-- **The honest round polynomials where the group has kept members.** V: the kept forms' value at
the kept members' own messages. -/
def foldQK : RIdx (sVars GE 2 (s.h + s.g)) → GE :=
  fun i => foldQ s v μ W ε γ i + ε * keptQ (s.h + s.g) V γ i

theorem foldQK_causal : SCausal 2 (s.h + s.g) (foldQK s v μ W ε V) :=
  SCausal.add_mul 2 (s.h + s.g) ε (foldQ_causal s v μ W ε) (keptQ_causal (s.h + s.g) V)

/-- **THE SECOND CORE: BEHIND A FOLD OF A GROUP WITH KEPT MEMBERS THE CLAIM IS TRUE**: at every
drawn coefficient, every drawn point and every V. -/
theorem fold_core_kept (hin : ∑ j, v j * μ j + V = t0) (hP : Pairs s n0 W φ) :
    ∑ j, midVec s n0 v ε (sPt 2 (s.h + s.g) γ) j * foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j +
        ε * Alg.eqk (sPt 2 (s.h + s.g) γ) (fun _ => false) * V =
      runQ (s.h + s.g) (hMu (sVars GE 2 (s.h + s.g)) W + ε * t0) (foldQK s v μ W ε V γ) γ := by
  have h1 := (s.par 0).honQ_rounds (le_refl 2) (μ, fun _ => 0)
    (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε γ
  have h4 := runQ_rounds _ _ _ _
    (HRounds.add_smul (sVars GE 2 (s.h + s.g)) ε h1 (keptQ_rounds (s.h + s.g) V γ))
  rw [hSumAll_add_smul, (s.par 0).summand_sum (le_refl 2), sum_corner] at h4
  have h3 : ∑ j, (s.par 0).slIn (fun x => v (.inl x), fun x => v (.inr x)) j * μ j =
      ∑ j, v j * μ j :=
    Finset.sum_congr rfl fun j _ => by rcases j with j | j <;> rfl
  rw [h3] at h4
  have e : hMu (sVars GE 2 (s.h + s.g)) W + ε * t0 =
      hMu (sVars GE 2 (s.h + s.g)) W + (∑ j, v j * μ j) * ε + ε • V := by
    rw [← hin, smul_eq_mul]
    ring
  rw [mid_at s n0 v μ φ W ε γ hP, e]
  refine Eq.trans ?_ h4.symm
  rw [smul_eq_mul]
  ring

/-- **A test that can fail**: with another first scalar, and no drawn element 0, the claim behind is
false. -/
theorem fold_turned_kept (hin : ∑ j, v j * μ j + V = t0) (hP : Pairs s n0 W φ) (σ' : GE)
    (hne : σ' ≠ hMu (sVars GE 2 (s.h + s.g)) W) (hγ : ∀ i, sPt 2 (s.h + s.g) γ i ≠ 0) :
    ∑ j, midVec s n0 v ε (sPt 2 (s.h + s.g) γ) j * foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j +
        ε * Alg.eqk (sPt 2 (s.h + s.g) γ) (fun _ => false) * V ≠
      runQ (s.h + s.g) (σ' + ε * t0) (foldQK s v μ W ε V γ) γ := fun hbad =>
  hne (add_right_cancel (runQ_inj _ _ _ _ γ hγ
    (hbad.symm.trans (fold_core_kept s n0 t0 v μ φ W ε V γ hin hP))))

end Field

/-! ## 3 At the description's own letters -/

/-- The verifier's factor on the kept forms, as the corner's weight. -/
theorem eqk_list : ∀ (k : ℕ) (g : List E), g.length = k →
    (g.map fun x => 1 - readE x).prod = Alg.eqk (readP k g) (fun _ => false)
  | 0, [], _ => by simp [Alg.eqk]
  | k + 1, x :: g, h => by
      have e : readP (k + 1) (x :: g) = (Fin.cons (readE x) (readP k g) : Fin (k + 1) → GE) := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      rw [e, eqk_corner_cons, List.map_cons, List.prod_cons,
        eqk_list k g (Nat.succ.inj h)]
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h

/-- **The kept forms' value** at the tables κ of the lengths N (by the oracle message's number). -/
def keptVal (N : ℕ → ℕ) (κ : ℕ → ℕ → GE) (Ks : Array KeptForm) : GE :=
  (Ks.toList.map fun f => ∑ i ∈ Finset.range (N f.oracle), formAt f.c i * κ f.oracle i).sum

theorem keptVal_scale (N : ℕ → ℕ) (κ : ℕ → ℕ → GE) (Ks : Array KeptForm) (t : E) :
    keptVal N κ (Ks.map fun f => { f with c := f.c.scale t }) = readE t * keptVal N κ Ks := by
  unfold keptVal
  rw [Array.toList_map, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun f _ => ?_)
  show ∑ i ∈ Finset.range (N f.oracle), formAt (f.c.scale t) i * κ f.oracle i =
    readE t * ∑ i ∈ Finset.range (N f.oracle), formAt f.c i * κ f.oracle i
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : formAt (f.c.scale t) i = formAt f.c i * readE t := Form.entry_scale rdE f.c t i
  rw [h]
  ring

section AtD
variable (s : Sg) (μ : s.cIn.J → GE) (φ : s.cFr.J → GE)
  (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (γ : HPt (sVars GE 2 (s.h + s.g)))

/-- **THE SINGLE ROWS THAT THE DESCRIPTION's FOLD RETURNS, THEIR KEPT FORMS WITH THEM, ARE
TRUE.** -/
theorem fold_holds_kept (N : ℕ → ℕ) (κ : ℕ → ℕ → GE) (S : Statement) (F : FoldShape)
    (row : GroupRow) (id : ℕ) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (hk : F.layout.k = s.h + s.g)
    (hh : F.layout.h = s.h) (hok : foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = s.Z.l)
    (hin : ∑ j, vecG s row j * μ j + keptVal N κ row.kept = readE row.target)
    (hP : Pairs s s.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR
      (foldQK s (vecG s row) μ W (readE (drawnOf rE)) (keptVal N κ row.kept) γ) γ) :
    ∑ j, vecS s (foldOutAt S F row id (rE :: rR)) j * foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j +
        keptVal N κ (foldOutAt S F row id (rE :: rR)).kept =
      readE (foldOutAt S F row id (rE :: rR)).target := by
  obtain ⟨i1, i2, i3⟩ := claimOf_shows _ rR _ γ
    (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target) hR
  have hv := ProxRun.vecS_foldOutput_fits s (spent S id) F row id (drawnOf rE) (rR.map drawnOf)
    (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) hk hh
    (by rw [List.length_map, i3]) hok hZ
  have hc := fold_core_kept s s.Z.l (readE row.target) (vecG s row) μ φ W (readE (drawnOf rE))
    (keptVal N κ row.kept) γ hin hP
  show ∑ j, vecS s (foldOutput (spent S id) F row id (drawnOf rE) (rR.map drawnOf)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))) j *
        foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j +
      keptVal N κ (row.kept.map fun f =>
        { f with c := f.c.scale (foldKeptFactor (drawnOf rE) (rR.map drawnOf)) }) =
    readE (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
  rw [hv, i2, i1, readE_maddE, hσ, keptVal_scale,
    VerifiableInference.Desc.First.Close.readE_foldKeptFactor,
    eqk_list (s.h + s.g) _ (by rw [List.length_map, i3]), i2]
  exact hc

end AtD

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.eqk_corner_cons
#print axioms Johnson.Prover.Link.sum_corner
#print axioms Johnson.Prover.Link.keptQ_rounds
#print axioms Johnson.Prover.Link.keptQ_causal
#print axioms Johnson.Prover.Link.foldQK_causal
#print axioms Johnson.Prover.Link.fold_core_kept
#print axioms Johnson.Prover.Link.fold_turned_kept
#print axioms Johnson.Prover.Link.eqk_list
#print axioms Johnson.Prover.Link.keptVal_scale
#print axioms Johnson.Prover.Link.fold_holds_kept
