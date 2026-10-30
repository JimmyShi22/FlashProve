-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchV.lean: the values' half of a code switch out of a stage that is not the
first, as one statement: `claim_behind` (Johnson/Prover/Link/SwitchHolds.lean) with its premise on
what was read paid by `hy_stage` (Johnson/Prover/Link/HyStage.lean).

Main names (namespace `Johnson.Prover.Link`).
  `switch_V`   the claim in front is true at the three folded messages `foldMsg s μ φ γ` · what the
      switch and the batching behind it have done (`Did`) · the public premises of `did_sem` and of
      `SeatReads` · each dealt column is the written column at its own position · μ ρ φ ψ are the
      written tables' and tails' by index · the answer that the switch has taken reads as `gAns`:
      then the row behind, read in the field, is true at the new message
      `gMsg hf (foldMsg s μ φ γ) (foldTl s ρ ψ γ) fr`; γ: the fold's drawn point

Limits. Every premise is asked. That the switch says yes is inside `Did`. The first stage's tree has
another reading law. Nothing on how a tail, a mask or the free room's values are chosen. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchHolds
import Johnson.Prover.Link.HyStage

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK

/-- **The values' half of a switch out of a stage that is not the first.** -/
theorem switch_V {s s' : Sg} (hf : CsFit s s') (hs : s.Sized)
    (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) (fr : ℕ → GE)
    {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
        out row lay theta D)
    (P : CsProg s s' S.codes old nc nz) (hkeptO : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (cu : IoppStage) (L : GroupLayout) (o id n : ℕ)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (h1 : 1 ≤ s.h + s.g)
    (hL : LayAt [o] #[some 0] #[some 0] L)
    (seat : SeatP S Bk [o, id] n s.C.a (stageShapes s cu))
    (hcols : ∀ c ∈ cols, c.2.1 < 2 ^ s.C.a ∧ c.2.2 = stageColW s tabM tabZ tM tZ fM fT c.2.1)
    (μ : s.cIn.J → GE) (ρ : s.cIn.Q → GE) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hM : ∀ b j, μ (.inl (b, j)) = tabM (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val))
    (hZ : ∀ b j, μ (.inr (b, j)) = tabZ (Sz.rowNo b + 2 ^ s.h * j.val))
    (hTM : ∀ b q, ρ (.inl (b, q)) = tM (Sz.rowNo b) q.val)
    (hTZ : ∀ b q, ρ (.inr (b, q)) = tZ (Sz.rowNo b) q.val)
    (hF : ∀ b j, φ (b, j) = fM (Sz.rowNo b) j.val) (hT : ∀ b q, ψ (b, q) = fT (Sz.rowNo b) q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g)
    (hHolds : (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s old)
      (foldMsg s μ φ (readP (s.h + s.g) gamma)))
    (hans : readE D.alpha = gAns hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
      (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row)
      (gMsg hf (foldMsg s μ φ (readP (s.h + s.g) gamma))
        (foldTl s ρ ψ (readP (s.h + s.g) gamma)) fr) := by
  have hC : codeOf D.code = s.C := by
    have k := P.code
    rw [h.code] at k
    exact Option.some.inj k
  have hlog : D.code.logN = s.C.a := congrArg (·.a) hC
  exact claim_behind hf _ _ fr (laws_of_sized hs) h P hkeptO hG hd0 hd1 hc ht hx β hβ Qs hQ
    (hy_stage s tabM tabZ tM tZ fM fT hs cu L o id n h hk hh h1 hL seat hcols μ ρ φ ψ hM hZ hTM hTZ
      hF hT S₀ row₀ eps claim gamma hold hkept hγ hlog Qs hQ ht)
    hHolds hans

end Johnson.Prover.Link
