-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsClaim.lean: the claim after the program's code switch, at the values of the two
written rounds.

OnBytes/Slice/BlkCsJoint.lean shows that the row which a run of the code switch of the program (the
Lean verifier in OnBytes/) returns, read in the field, is the claim after the library's code switch
at the seed, the answer, the positions and the element that the run has taken of the view. This file
reads these four as the library reads the two written rounds, for a run on the view of these rounds.
So the row is the claim `csNextW` of OnBytes/Slice/ChainSem.lean.

Main theorems.
 `readL_ofTriple`   a list of triples of words, taken as elements of the program and read in the
                    field.
 `csRan_claim`      the row that the run returns is `csNextW` of the program's claim before the
                    switch.

Not claimed. That the symbols which the run has read are the long symbols of the word y: it is a
hypothesis, as in BlkCsJoint.lean.
-/
import OnBytes.Slice.BlkCsJoint
import OnBytes.Slice.ChainSem

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-- A list of triples of words, taken as elements of the program and read in the field. -/
theorem readL_ofTriple (l : List Fmt.Ext3) (i : ℕ) : readL (l.map E.ofTriple) i = lst l i := by
  rw [readL_eq_lst, List.map_map]
  have e : (E.triple ∘ E.ofTriple) = id := funext fun t => E.triple_ofTriple t
  rw [e, List.map_id]

section
variable {s s' : Sg} {old : SingleRows} {nc nz gp : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The row that a run of the program's code switch returns is the claim after the switch, at the
values of the two written rounds. hr: what the two rounds send and draw. hp: the rounds that are
left for the run begin with these two. hbits: the point of the sample has as many coordinates as the
library's. hy: the symbols that the run has read are the long symbols of the word y at the drawn
positions. The other hypotheses are those of `csRan_sem` (OnBytes/Slice/BlkCsJoint.lean). -/
theorem csRan_claim (hf : CsFit s s') (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τ : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView)
    (h : CsRan old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others c c' out row lay theta
      D)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest)
    (P : CsProg s s' c.st.codes old nc nz) (hkept : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (hbits : (Send.cube c.st.codes (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape).bits
      = s'.st.na)
    (y : s.cMid.Word)
    (hy : ∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i) α =
      symS s old out.positions D.y ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i).val α) :
    stmGk s' lay.k lay.h row = csNextW hf dS dC (stmS s old) y τ := by
  -- the two rounds that the run has taken are the two written rounds
  have e : D.rS :: D.rC :: D.rest = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest :=
    h.pending.symm.trans hp
  injection e with eS e2
  injection e2 with eC _
  have elS : D.rS.drawn.elems = (rvOf dS τ.1 τ.2.1).els := by rw [eS]; rfl
  have elC : D.rC.drawn.elems = (rvOf dC τ.2.2.1 τ.2.2.2.1).els := by rw [eC]; rfl
  have poC : D.rC.drawn.poss = (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [eC]; rfl
  have seC : Fmt.M1.sentOf D.rC.vals = (rvOf dC τ.2.2.1 τ.2.2.2.1).sent := by rw [eC]; rfl
  -- as the library reads them
  obtain ⟨β, hseed, hβ⟩ := seed_read hr.nz τ.1 τ.2.1
  obtain ⟨alpha, th, xs, hrv, hxs, hans, hth, hQ⟩ := cs_read hr.cs τ.2.2.1 τ.2.2.2.1
  rw [hrv] at elC poC seC
  -- the factor of the seed
  have hbeta : β.val = readE D.beta := by
    have k := congrArg (fun l => readL l 0) h.seed
    simp only at k
    rw [readL_drop, readL_ofTriple, hbits, Nat.add_zero, elS] at k
    rw [hβ]
    exact k
  -- the point of the seed
  have hz : readP s'.st.na (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) c) =
      ptL s'.st.na ((rvOf dS τ.1 τ.2.1).els.take s'.st.na) := by
    funext i
    show readL ((D.rS.drawn.elems.map E.ofTriple).take _) i.val = lst (List.take _ _) i.val
    rw [hbits, readL_take _ _ _ i.isLt, readL_ofTriple, lst_take _ _ _ i.isLt, elS]
  -- the answer
  have halpha : readE D.alpha = (ansOf dC τ.2.2.1).getD 0 0 := by
    rw [hans, readE_def]
    rw [h.valsC] at seC
    exact congrArg toE (List.head_eq_of_cons_eq seC)
  -- the element
  have htheta : readE theta = (gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).2 := by
    have k := h.elem
    rw [elC] at k
    rw [hth, ← List.head_eq_of_cons_eq k, readE_ofTriple]
  have hsem := csRan_sem hf h P hkept hG hd0 hd1 hc
    (by rw [← h.poss, poC]; exact hxs)
    (fun x hx => by
      rw [poC] at hx
      have hx' : x ∈ (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [hrv]; exact hx
      exact hr.cs.poss_lt τ.2.2.1 τ.2.2.2.1 x hx')
    β hbeta y (gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 (fun i => by rw [poC]; exact hQ i) hy
  rw [hsem, hz, halpha, htheta, ← hseed]
  rfl

end

end OnBytes.Slice

#print axioms OnBytes.Slice.readL_ofTriple
#print axioms OnBytes.Slice.csRan_claim
