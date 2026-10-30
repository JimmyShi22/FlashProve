-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearTieL.lean: from what the routines for a layers' sub-proof have heard to the
typed side, in general: along any list of stages, and for one sumcheck.

The typed transcript of a masked sumcheck (`StgH`, OnBytes/Tie/Pv/Lay/OwnTieL.lean) asks that the
element drawn in the further variable's round does not read 0. The typed output is then a function
of the lists heard. Here: that premise is had for every sumcheck of a list of stages from one
premise on the context at the start; and the typed output of one stage holds the readings of what
the routine's record holds.

Main names:
  `BetasNz ρ l`: in each sumcheck of the list l the element of the further variable's round does
    not read 0.
  `still_nz`, `heardL_nz`: from `NzCtx ρ c` (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean) and `HeardL l c
    c'` (OnBytes/Tie/Pv/Lay/HearL.lean): `NzCtx ρ c'` and `BetasNz ρ l`, for every list of stages.
  `StgOf ρ D riders H p`: the typed data D of a stage are those of the further scalars and the
    lists heard, and its target is the record's.
  `OutIs ρ D p`: the typed output has the reading of the record's coefficient and of its running
    claim; its point is the reading of the challenges heard, then of the last element; its end
    values are D's.
  `stg_out`: `OutIs`, and the record `SumSaid` (OnBytes/Tie/Pv/Lay/SumSaid.lean), from the
    routine's record (`Ended`, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), the fit of the weights to the
    stage's variables, and the lengths.

Limits: `NzCtx` at the start is a premise. The fit of the weights and the lengths are premises of
`stg_out`. That D's end values are the readings of the values heard is not asked by `StgOf` and
not said by `OutIs`. Nothing is said on what the rows and the slots are worth.
-/
import OnBytes.Tie.Pv.Lay.HearL
import OnBytes.Tie.Pv.Lay.OwnTieL
import OnBytes.Tie.Pv.Lay.SumSaid
import OnBytes.Tie.Pv.Psc.Run.NzRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-! ### Along a list of stages -/

/-- In each sumcheck of the list the element of the further variable's round does not read 0. -/
def BetasNz : List StageL → Prop
  | [] => True
  | .sum _ _ _ H :: l => ρ.val H.beta ≠ 0 ∧ BetasNz l
  | _ :: l => BetasNz l

omit [Fintype K] in
theorem still_nz {c c' : Ctx} (h : Still c c') (hc : NzCtx ρ c) : NzCtx ρ c' := by
  obtain ⟨n, f, rfl, _⟩ := h
  exact hc

omit [Fintype K] in
/-- From a context in which the elements that are drawn by the rule that never gives 0 do not read
0: so it is behind the stages, and no sumcheck's last element reads 0. -/
theorem heardL_nz : ∀ (l : List StageL) (c c' : Ctx), NzCtx ρ c → HeardL l c c' →
    NzCtx ρ c' ∧ BetasNz ρ l
  | [], c, c', hc, h => by
    rw [show c' = c from h]
    exact ⟨hc, trivial⟩
  | .sum _ _ _ _ :: l, c, c', hc, h => by
    obtain ⟨c1, c2, a, h2⟩ := h
    obtain ⟨n1, n2⟩ := parts_nz ρ a hc
    obtain ⟨g1, g2⟩ := heardL_nz l c2 c' n2 h2
    exact ⟨g1, n1, g2⟩
  | .bat _ _ _ :: l, c, c', hc, h => by
    obtain ⟨c1, c2, c3, a1, a2, a3, h2⟩ := h
    exact heardL_nz l c3 c' (keeps_requireRows ρ _ _ _ _
      (keeps_closeOne ρ _ _ _ _ _ _ (keeps_recvEs ρ _ _ _ _ hc a1) a2) a3) h2
  | .point _ _ :: l, c, c', hc, h => by
    obtain ⟨c1, a1, h2⟩ := h
    exact heardL_nz l c1 c' (keeps_close ρ _ _ _ _ _ _ hc a1) h2
  | .line _ :: l, c, c', hc, h => by
    obtain ⟨c1, a1, h2⟩ := h
    exact heardL_nz l c1 c' (keeps_closeOne ρ _ _ _ _ _ _ hc a1) h2
  | .idle :: l, c, c', hc, h => by
    obtain ⟨c1, a1, h2⟩ := h
    exact heardL_nz l c1 c' (still_nz ρ a1 hc) h2

/-! ### One stage -/

/-- The typed data of a stage are those of what was heard (riders, H) and of the record p. -/
structure StgOf {M X : Type} {S : Stg K M X} (D : StgH ρ S) (riders : List E) (H : PscH)
    (p : OnBytes.Model.Psc) : Prop where
  r : D.r = riders
  H : D.H = H
  t : D.t = p.target

/-- The typed output of a stage is the record, read. -/
structure OutIs {M X : Type} {S : Stg K M X} (D : StgH ρ S) (p : OnBytes.Model.Psc) : Prop where
  eps : D.out.eps = ρ.val p.eps
  fin : D.out.fin = ρ.val p.claim
  pt : ∀ i : Fin S.L.S.k, S.L.Q.outPt S.L.M D.out i = ρ.val (D.H.rs.getD i.1 ([], zeroE)).2
  last : S.L.Q.outB S.L.M D.out = ρ.val D.H.beta
  vals : D.out.vals = D.v

/-- From the record of what was heard, the weights' fit and the lengths. -/
theorem stg_out {M X : Type} {S : Stg K M X} (D : StgH ρ S) {riders : List E} {H : PscH}
    {p : OnBytes.Model.Psc} {C : Aff} {τ : E} {first : ℕ} {ws : List Weight}
    (o : StgOf ρ D riders H p)
    (a : Ended p C τ H.mu H.eps first ws H.rs S.L.M.DY H.sentY H.beta)
    (hfit : Fits ρ (ws ++ [Weight.atZero (S.L.M.DY + 1)]) S.L.T.par.fmt (S.L.T.par.dat D.st)
      (S.F D.st))
    (hl : H.rs.map (·.1.length) = List.ofFn S.L.M.n) (hY : H.sentY.length = S.L.M.DY) :
    OutIs ρ D p ∧
      SumSaid ρ S.L S.F D.st p (ws ++ [Weight.atZero (S.L.M.DY + 1)]) D.H.mu D.H.rs D.H.sentY
        D.H.beta D.b D.v := by
  obtain ⟨_, rfl, ht⟩ := o
  have s := sum_said ρ S.L S.F D.st a D.b D.v hfit hl hY
  have e : D.out = sumOut ρ S.L S.F D.st p.target D.H.mu p.eps D.H.rs D.H.sentY D.H.beta D.b
      D.v := by
    unfold StgH.out
    rw [ht, a.eps]
  exact ⟨⟨by rw [e]; exact s.eps, by rw [e]; exact s.fin, fun i => by rw [e]; exact s.pt i,
    by rw [e]; exact s.last, by rw [e]; exact s.vals⟩, s⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.heardL_nz
#print axioms OnBytes.Tie.Pv.Lay.stg_out
