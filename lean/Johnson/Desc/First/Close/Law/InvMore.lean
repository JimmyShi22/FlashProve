-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/InvMore.lean: two lemmas more on the closing of a link. Statements and
proofs.
  `fold_inv2`: `fold_inv` (Inv.lean, beside this file) with three things more: the fold's own test
    of the row's sizes held (said of foldRowOk of the program `verify-on-bytes`, with which the
    text's test agrees: Johnson/Desc/Own/FoldAgree.lean); the statement at which the output is
    made has the codes of the statement in front; it is the statement handed on.
  `readE_foldKeptFactor`: the factor of the kept rows' coefficients, read in the field:
    eps (1 - g_1) .. (1 - g_k).

-/
import Johnson.Desc.First.Close.Law.Inv
import OnBytes.Slice.BlkProxFold
import OnBytes.Slice.BlkFoldOut
import Johnson.Desc.Own.FoldAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold

/-- `fold_inv` with the two things more that the vectors' law spends: the fold's own test of the
row's sizes, and that the statement at which the output is made has the codes of the statement in
front. -/
theorem fold_inv2 {S S' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : fold S F row m es rs = .ok (out, S')) :
    ∃ (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (sum eps : E) (qs : List (E × E)) (gs : List E)
      (S2 : Statement),
      rs = rE :: rR ∧ Holds rE [sum] ∧ rE.drawn.elems = [eps.triple] ∧ RoundsHold rR qs gs ∧
      gs.length = F.layout.k ∧ foldRowOk S2 F row = true ∧ S2.codes = S.codes ∧ S' = S2 ∧
      out = foldOutput S2 F row m eps gs (claimAfter (maddE sum eps row.target) qs gs) := by
  unfold fold at h
  cases hD : foldD 0 (onSt S) F row (some m) es rs with
  | error e => rw [hD] at h; exact absurd h (by simp [Except.map])
  | ok y =>
    rw [hD] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨_, k1, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨p, k2, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at k2
      subst k2
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨d2, k5, hD⟩ := ok_bind hD
      obtain ⟨z, k3, hD⟩ := ok_bind hD
      split at hD
      · rename_i sum eps
        obtain ⟨_, k6, hD⟩ := ok_bind hD
        obtain ⟨w, k4, hD⟩ := ok_bind hD
        simp only [pure, Except.pure, Except.ok.injEq] at hD
        subst hD
        obtain ⟨a1, a2⟩ := heard_inv k3
        obtain ⟨qs, b1, b2, b3⟩ := rounds_inv eR rR _ w.1 w.2 k4
        have k1 := need_ok k1
        simp only [Bool.and_eq_true, beq_iff_eq] at k1
        have k5 := got_ok k5
        have hc : d2.st.codes = S.codes := by
          unfold Ground.spendAsMaskP at k5
          split at k5
          · rw [← Option.some.inj k5]
            rfl
          · exact absurd k5 (by simp)
        refine ⟨rE, rR, sum, eps, qs, w.1, d2.st, rfl, a1, a2, b1, by rw [b3, k1.2],
          (Own.foldRowFits_agrees d2.st F row).trans (need_ok k6), hc, rfl, ?_⟩
        show foldOutput d2.st F row m eps w.1 w.2 = _
        rw [b2]
      · exact absurd hD (by simp)
    · exact absurd hD (by simp)

/-- The factor of the kept rows' coefficients, read in the field: eps (1 - g_1) .. (1 - g_k). -/
theorem readE_foldKeptFactor : ∀ (g : List E) (eps : E),
    readE (foldKeptFactor eps g) = readE eps * (g.map fun x => 1 - readE x).prod
  | [], eps => by simp [foldKeptFactor]
  | x :: g, eps => by
    have h := readE_foldKeptFactor g (mulE eps (subE oneE x))
    unfold foldKeptFactor at h ⊢
    rw [List.foldl_cons, h, List.map_cons, List.prod_cons]
    have e1 : readE (mulE eps (subE oneE x)) = readE eps * (1 - readE x) := by
      have a := rdE.mul eps (subE oneE x)
      have b := rdE.sub oneE x
      have c := rdE.one
      simp only [rdE_val] at a b c
      rw [a, b, c]
    rw [e1]
    ring

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.fold_inv2
#print axioms VerifiableInference.Desc.First.Close.readE_foldKeptFactor
