--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/CodeRow.lean: kind K13, the members' batching: WHERE THE PROVER SENDS THE
SCALARS THAT Johnson/Desc/K13/Honest/MovesAtM3.lean COMPUTES, and every row on the pile is true,
THE ROW THAT `Batt.rowOf` MAKES OF WHAT THE SUMCHECK's RUN RETURNS IS TRUE. Statements with their
proofs.

Three ties between the verifier's text, which computes in the program's type E, and functions over
the field K that a reading takes E to: the verifier's running claim is `after` (`after_read`); its
form on the fresh mask entries, with its product of the challenges, is `uAt` (`walk_uAt`; both
functions: Johnson/Desc/K13/Honest/Code.lean); and the tables of a pile's rows fold to multilinear
extensions (`dotAll_tabs`, `dotAll_folds_tabs`, over Johnson/Desc/K13/Honest/Tables.lean). With
`after_sent` they give the row.
Main names:
  `step_val`, `after_read`: one round, and all rounds, of the verifier's running claim, read.
  `walk_uAt`: the verifier's walk over the hiding polynomial, read.
  `readRounds`, `ReadsCode ρ w pile fresh x h`: what was heard reads as what the prover computes.
  `code_row`: **under it, the row is true.**

Which prover. The one with code (Moves.lean, MovesAtM3.lean). The library has an honest prover of
the same sumcheck without code (`TWhole.shortHonC`, Cb/G6/Core.lean); that the two send the same is
not shown.

What is not claimed. That the rows on the pile are true: a premise, owed by the sub-protocols that
lay them. That the kind's text and sub-protocols hand on this row:
Johnson/Desc/K13/Honest/Accepts.lean. The number nR of the matrix's rows is a free parameter, as in
the kind's laws. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Tables
import Johnson.Desc.K13.Honest.SumLaw
import Johnson.Desc.K13.Honest.MovesAtM3
import Johnson.Desc.K13.Law.FitProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd)
open OnBytes.Road.Hd (sumFrom_app)
open VerifiableInference.Desc.K13.Law

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {nR k : ℕ}

/-! ## The verifier's running claim -/

omit [Fintype K] in
/-- One round: the verifier completes the two sent coefficients and evaluates at the challenge. -/
theorem step_val (a c R g : E) :
    ρ.val (Psc.polyAt ((Psc.Weight.plain 3).complete [a, c] R) g) =
      ρ.val a + (ρ.val R - 2 * ρ.val a - ρ.val c) * ρ.val g + ρ.val c * ρ.val g ^ 2 := by
  have e : Psc.polyAt ((Psc.Weight.plain 3).complete [a, c] R) g =
      addE (mulE (addE (mulE (addE (mulE zeroE g) c) g)
        (mulE (subE R (addE (addE (addE zeroE (mulE (addE oneE oneE) a)) (mulE oneE zeroE))
          (mulE oneE c))) oneE)) g) a := rfl
  rw [e]
  simp only [ρ.add, ρ.mul, ρ.sub, ρ.zero, ρ.one]
  ring

omit [Fintype K] in
/-- What was sent in the rounds, read: the first and the second element of each. -/
def readRounds (rs : List (List E × E)) : List (K × K) :=
  rs.map fun p => (ρ.val (p.1.getD 0 zeroE), ρ.val (p.1.getD 1 zeroE))

/-- A list of two members. -/
theorem two_of_len : ∀ q : List E, q.length = 2 → ∃ a c, q = [a, c]
  | [a, c], _ => ⟨a, c, rfl⟩
  | [], h => by simp only [List.length_nil] at h; omega
  | [_], h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- One round of the verifier's running claim. -/
theorem claimAfter_cons (k : ℕ) (q : List E) (g : E) (rs : List (List E × E)) (R : E) :
    Psc.claimAfter (wsOf (k + 1)) ((q, g) :: rs) R =
      Psc.claimAfter (wsOf k) rs (Psc.polyAt ((Psc.Weight.plain 3).complete q R) g) := rfl

omit [Fintype K] in
/-- One round of the reading. -/
theorem readRounds_cons (a c g : E) (rs : List (List E × E)) :
    readRounds ρ (([a, c], g) :: rs) = (ρ.val a, ρ.val c) :: readRounds ρ rs := rfl

omit [Fintype K] in
/-- **The verifier's running claim, read.** -/
theorem after_read : ∀ (k : ℕ) (rs : List (List E × E)) (c0 : E), rs.length = k →
    (∀ p ∈ rs, p.1.length = 2) →
    ρ.val (Psc.claimAfter (wsOf k) rs c0) =
      after (readRounds ρ rs) (rs.map fun p => ρ.val p.2) (ρ.val c0)
  | 0, [], _, _, _ => rfl
  | k + 1, (q, g) :: rs, c0, hl, h => by
    obtain ⟨a, c, rfl⟩ := two_of_len q (h (q, g) List.mem_cons_self)
    rw [claimAfter_cons, readRounds_cons, List.map_cons, after_cons,
      after_read k rs _ (by simp only [List.length_cons] at hl; omega)
        (fun p hp => h p (List.mem_cons_of_mem _ hp)), step_val]
  | 0, _ :: _, _, hl, _ => by simp only [List.length_cons] at hl; omega
  | _ + 1, [], _, hl, _ => by simp only [List.length_nil] at hl; omega

/-! ## The verifier's walk over the hiding polynomial -/

/-- The walk at a variable that is not the last. -/
theorem walk_cons (g : E) (y : Psc.Weight × E) (rest : List (Psc.Weight × E)) :
    Psc.hidingWalk ((Psc.Weight.plain 3, g) :: y :: rest) =
      ([mulE (Psc.hidingWalk (y :: rest)).2 g, mulE (mulE (Psc.hidingWalk (y :: rest)).2 g) g] ++
          (Psc.hidingWalk (y :: rest)).1,
        mulE (Psc.hidingWalk (y :: rest)).2 (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE)) :=
  rfl

/-- The walk at the last variable. -/
theorem walk_one (g : E) :
    Psc.hidingWalk [(Psc.Weight.plain 3, g)] =
      ([oneE, mulE oneE g, mulE (mulE oneE g) g],
        addE (mulE (addE (mulE zeroE g) oneE) g) zeroE) := rfl

omit [Fintype K] in
/-- **The verifier's form on the mask entries from number i on, with pre times its product of the
challenges, is the polynomial's value at the challenges (`uAt`, Code.lean).** -/
theorem walk_uAt (mask : ℕ → K) : ∀ (n : ℕ) (gs : List E) (i : ℕ) (pre : K), gs.length = n + 1 →
    sumFrom (fun j y => ρ.val y * mask j) i (Psc.hidingWalk ((wsOf (n + 1)).zip gs)).1 +
        pre * ρ.val (Psc.hidingWalk ((wsOf (n + 1)).zip gs)).2 =
      uAt mask (n + 1) i pre (gs.map ρ.val)
  | 0, [g], i, pre, _ => by
    have ez : (wsOf 1).zip [g] = [(Psc.Weight.plain 3, g)] := rfl
    rw [ez, walk_one]
    show (ρ.val oneE * mask i + (ρ.val (mulE oneE g) * mask (i + 1) +
        (ρ.val (mulE (mulE oneE g) g) * mask (i + 2) + 0))) +
        pre * ρ.val (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE) =
      pre * ρ.val g + mask i + mask (i + 1) * ρ.val g + mask (i + 2) * ρ.val g ^ 2
    simp only [ρ.add, ρ.mul, ρ.zero, ρ.one]
    ring
  | n + 1, g :: g' :: gs, i, pre, h => by
    have ih := walk_uAt mask n (g' :: gs) (i + 2)
      (pre * ρ.val g + mask i * ρ.val g + mask (i + 1) * ρ.val g ^ 2)
      (by simp only [List.length_cons] at h ⊢; omega)
    have ez : (wsOf (n + 1 + 1)).zip (g :: g' :: gs) =
        (Psc.Weight.plain 3, g) :: (Psc.Weight.plain 3, g') :: (wsOf n).zip gs := rfl
    have ez' : (wsOf (n + 1)).zip (g' :: gs) = (Psc.Weight.plain 3, g') :: (wsOf n).zip gs := rfl
    rw [ez'] at ih
    rw [ez, walk_cons]
    generalize Psc.hidingWalk ((Psc.Weight.plain 3, g') :: (wsOf n).zip gs) = L at ih ⊢
    show sumFrom (fun j y => ρ.val y * mask j) i ([mulE L.2 g, mulE (mulE L.2 g) g] ++ L.1) +
        pre * ρ.val (mulE L.2 (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE)) =
      uAt mask (n + 1) (i + 2) (pre * ρ.val g + mask i * ρ.val g + mask (i + 1) * ρ.val g ^ 2)
        ((g' :: gs).map ρ.val)
    rw [← ih, sumFrom_app]
    show (ρ.val (mulE L.2 g) * mask i + (ρ.val (mulE (mulE L.2 g) g) * mask (i + 1) + 0)) +
        sumFrom (fun j y => ρ.val y * mask j) (i + 2) L.1 +
        pre * ρ.val (mulE L.2 (addE (mulE (addE (mulE zeroE g) oneE) g) zeroE)) = _
    simp only [ρ.add, ρ.mul, ρ.zero, ρ.one]
    ring
  | 0, [], _, _, h => by simp only [List.length_nil] at h; omega
  | 0, _ :: _ :: _, _, _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], _, _, h => by simp only [List.length_nil] at h; omega
  | _ + 1, [_], _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-! ## The tables of a pile's rows -/

omit [Fintype K] in
/-- A list of the program's elements, read, as a point. -/
theorem ptOf_rd : ∀ (k : ℕ) (l : List E), l.length = k → ptOf k (l.map ρ.val) = rd ρ k l
  | 0, [], _ => funext fun i => i.elim0
  | k + 1, a :: l, h => by
    rw [rd_cons]
    show (Fin.cons (ρ.val a) (ptOf k (l.map ρ.val)) : Fin (k + 1) → K) = _
    rw [ptOf_rd k l (by simp only [List.length_cons] at h; omega)]
  | 0, _ :: _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], h => by simp only [List.length_nil] at h; omega

omit [Fintype K] in
/-- The sum of the products over rows that are given by a function. -/
theorem dotAll_ofFn : ∀ (n : ℕ) (F : Fin n → List K × List K),
    dotAll (List.ofFn F) = ∑ q, dotT (F q).1 (F q).2
  | 0, _ => by
    rw [List.ofFn_zero, Fin.sum_univ_zero]
    rfl
  | n + 1, F => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    show dotT _ _ + dotAll (List.ofFn fun i : Fin n => F i.succ) = _
    rw [dotAll_ofFn n]

omit [Fintype K] in
/-- Setting all variables goes row by row. -/
theorem foldsAll_ofFn {n : ℕ} : ∀ (gs : List K) (F : Fin n → List K × List K),
    foldsAll gs (List.ofFn F) = List.ofFn fun q => (foldsT gs (F q).1, foldsT gs (F q).2)
  | [], _ => rfl
  | g :: gs, F => by
    show foldsAll gs ((List.ofFn F).map fun p => (foldT g p.1, foldT g p.2)) = _
    rw [List.map_ofFn, foldsAll_ofFn gs]
    rfl

omit [Fintype K] in
/-- The first table of a row, as the table of a vector. -/
theorem first_tab (a : K) (psi : List E) (h : psi.length = k) :
    scaleT a (eqT (psi.map ρ.val)) = tabOf k fun b => a * Alg.eqk (rd ρ k psi) b := by
  rw [eqT_tabOf k _ (by rw [List.length_map, h]), scaleT_tabOf, ptOf_rd ρ k psi h]

omit [Fintype K] in
/-- The tables have 2^k entries. -/
theorem sized_tabs (w : Wit K nR k) (pile : List TensorRow) (a : K)
    (hpsi : ∀ r ∈ pile, r.psi.length = k) : Sized (tabsOf ρ w pile a) k := by
  intro p hp
  obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).1 hp
  refine ⟨?_, tabOf_length k _⟩
  show (scaleT _ (eqT _)).length = 2 ^ k
  rw [first_tab ρ _ _ (hpsi _ (List.get_mem _ _)), tabOf_length]

omit [Fintype K] in
/-- The sum of the products of the tables: the rows' tensor parts, each with its coefficient. -/
theorem dotAll_tabs (w : Wit K nR k) (pile : List TensorRow) (a : K)
    (hpsi : ∀ r ∈ pile, r.psi.length = k) :
    dotAll (tabsOf ρ w pile a) = ∑ q : Fin pile.length, a ^ (q : ℕ) *
      Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (rd ρ k (pile.get q).psi) := by
  unfold tabsOf
  rw [dotAll_ofFn]
  refine Finset.sum_congr rfl fun q _ => ?_
  show dotT (scaleT _ (eqT _)) (tabOf k _) = _
  rw [first_tab ρ _ _ (hpsi _ (List.get_mem _ _)), dotT_tabOf]
  unfold Alg.mle
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [Fintype K] in
/-- The same with all variables set. -/
theorem dotAll_folds_tabs (w : Wit K nR k) (pile : List TensorRow) (a : K) (gs : List K)
    (hg : gs.length = k) (hpsi : ∀ r ∈ pile, r.psi.length = k) :
    dotAll (foldsAll gs (tabsOf ρ w pile a)) = ∑ q : Fin pile.length, a ^ (q : ℕ) *
      Alg.eqPt (rd ρ k (pile.get q).psi) (ptOf k gs) *
      Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (ptOf k gs) := by
  unfold tabsOf
  rw [foldsAll_ofFn, dotAll_ofFn]
  refine Finset.sum_congr rfl fun q _ => ?_
  show dotT (foldsT gs (scaleT _ (eqT _))) (foldsT gs (tabOf k _)) = _
  rw [first_tab ρ _ _ (hpsi _ (List.get_mem _ _)), dot_folds k gs _ _ hg, Alg.mle_smul, Alg.mle_eqk]

/-! ## The row -/

/-- **What was heard reads as what the prover with code computes**: at the mask entries that were
taken for the hiding polynomial, the tables of the pile's rows, and the challenges that were
sampled. -/
structure ReadsCode (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot) (x : E)
    (h : Psc.Heard) : Prop where
  mu : ρ.val h.mu = sumU (fun j => w.mask (fresh.getD j default)) k
  rounds : readRounds ρ h.rounds =
    sent (fun j => w.mask (fresh.getD j default)) (ρ.val h.eps) k 0 (tabsOf ρ w pile (ρ.val x))
      (h.rounds.map fun p => ρ.val p.2)

/-- **The row that the batching hands on is true.** -/
theorem code_row (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot)
    (hf : Batt.fits k pile = true) (hrows : ∀ r ∈ pile, Holds ρ w r) (x : E) (h : Psc.Heard)
    (o : Psc.Out) (hc : ReadsCode ρ w pile fresh x h)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    Holds ρ w (Batt.rowOf pile o) := by
  obtain ⟨hl, h2, hfr, hpt, hmk, hmp, htg⟩ := Law.run_fields hf hr
  obtain ⟨-, hk, hpsi⟩ := Law.of_fits x hf
  have hch : (h.rounds.map (·.2)).length = k := by simp [hl]
  have hchK : (h.rounds.map fun p => ρ.val p.2).length = k := by simp [hl]
  have hmapK : (h.rounds.map fun p => ρ.val p.2) = (h.rounds.map (·.2)).map ρ.val := by
    rw [List.map_map]
    rfl
  have hwl : (walkOf k h).1.length ≤ fresh.length := by
    have := OnBytes.Model.Road.walk_length (wsOf k) (h.rounds.map (·.2))
      (by intro e; have := congrArg List.length e; simp at this; omega) (by simp [hl])
      (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact (by decide : 1 ≤ 3))
    rw [this, hfr]
    simp [Psc.hidingEntries, Psc.Weight.plain]
    omega
  have hz := zip_sumFrom ρ w.mask fresh (walkOf k h).1 0
    (fun j => w.mask (fresh.getD j default)) hwl (fun j _ => by rw [Nat.zero_add])
  -- the value of the claim's incoming mask form
  obtain ⟨sg, hsg⟩ : ∃ sg, sg = ∑ q : Fin pile.length,
      ρ.val x ^ (q : ℕ) * formVal ρ w.mask (pile.get q).masks := ⟨_, rfl⟩
  -- the verifier's running claim
  have hT : ρ.val (Batt.claimOf pile x).target = dotAll (tabsOf ρ w pile (ρ.val x)) + sg := by
    rw [target_val, dotAll_tabs ρ w pile _ hpsi, hsg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : lhs ρ w (pile.get q) = ρ.val (pile.get q).target := hrows _ (List.get_mem _ _)
    show _ * ρ.val (pile.get q).target = _
    rw [← hq]
    unfold lhs
    ring
  have hA := after_sent (fun j => w.mask (fresh.getD j default)) (ρ.val h.eps) k
    (tabsOf ρ w pile (ρ.val x)) (h.rounds.map fun p => ρ.val p.2) (ρ.val h.eps * sg)
    (sized_tabs ρ w pile _ hpsi) hchK
  have hR : ρ.val (Psc.claimAfter (wsOf k) h.rounds
      (addE h.mu (mulE h.eps (Batt.claimOf pile x).target))) =
      uAt (fun j => w.mask (fresh.getD j default)) k 0 (ρ.val h.eps * sg)
          (h.rounds.map fun p => ρ.val p.2) +
        ρ.val h.eps * dotAll (foldsAll (h.rounds.map fun p => ρ.val p.2)
          (tabsOf ρ w pile (ρ.val x))) := by
    rw [after_read ρ k h.rounds _ hl h2, hc.rounds, ← hA, ρ.add, ρ.mul, hT, hc.mu]
    congr 1
    unfold sumU
    ring
  -- the verifier's form on the fresh mask entries
  have hW : sumFrom (fun j y => ρ.val y * w.mask (fresh.getD j default)) 0 (walkOf k h).1 +
      ρ.val h.eps * sg * ρ.val (walkOf k h).2 =
      uAt (fun j => w.mask (fresh.getD j default)) k 0 (ρ.val h.eps * sg)
        (h.rounds.map fun p => ρ.val p.2) := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [hmapK]
    exact walk_uAt ρ _ n (h.rounds.map (·.2)) 0 _ hch
  have hG := dotAll_folds_tabs ρ w pile (ρ.val x) (h.rounds.map fun p => ρ.val p.2) hchK hpsi
  rw [hmapK, ptOf_rd ρ k _ hch, ← hmapK] at hG
  show Alg.mle (colOf w (weights ρ nR ((zipT pile o.rowMaps).flatMap fun p =>
      p.1.g.map fun t => t.scale p.2))) (rd ρ k o.point) + formVal ρ w.mask o.rowMasks =
      ρ.val o.rowTarget
  rw [hpt, hmk, htg, hmp, weights_val ρ nR pile x h.eps _ hch hpsi, mle_comb, formVal_append,
    formVal_scale, hz, ρ.mul, masks_val, ρ.sub, ρ.mul, ρ.zero, hR, ← hW, hG, ← hsg]
  have hS : ∑ q : Fin pile.length, (ρ.val h.eps * (ρ.val x ^ (q : ℕ) *
        Alg.eqPt (rd ρ k (pile.get q).psi) (rd ρ k (h.rounds.map (·.2))))) *
        Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (rd ρ k (h.rounds.map (·.2))) =
      ρ.val h.eps * ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) *
        Alg.eqPt (rd ρ k (pile.get q).psi) (rd ρ k (h.rounds.map (·.2))) *
        Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (rd ρ k (h.rounds.map (·.2))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hS]
  ring

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.step_val
#print axioms VerifiableInference.Desc.K13.Honest.two_of_len
#print axioms VerifiableInference.Desc.K13.Honest.claimAfter_cons
#print axioms VerifiableInference.Desc.K13.Honest.readRounds_cons
#print axioms VerifiableInference.Desc.K13.Honest.after_read
#print axioms VerifiableInference.Desc.K13.Honest.walk_cons
#print axioms VerifiableInference.Desc.K13.Honest.walk_one
#print axioms VerifiableInference.Desc.K13.Honest.walk_uAt
#print axioms VerifiableInference.Desc.K13.Honest.dotAll_ofFn
#print axioms VerifiableInference.Desc.K13.Honest.foldsAll_ofFn
#print axioms VerifiableInference.Desc.K13.Honest.first_tab
#print axioms VerifiableInference.Desc.K13.Honest.ptOf_rd
#print axioms VerifiableInference.Desc.K13.Honest.sized_tabs
#print axioms VerifiableInference.Desc.K13.Honest.dotAll_tabs
#print axioms VerifiableInference.Desc.K13.Honest.dotAll_folds_tabs
#print axioms VerifiableInference.Desc.K13.Honest.code_row
