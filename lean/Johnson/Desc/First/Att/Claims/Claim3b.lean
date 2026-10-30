-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Claim3b.lean: kind K5, the claims are the written lists: the rest of
claim 3 (callKR, claim3), with the key forms.

Main names:
  `jP`: the record of the key forms of OnBytes/Model as the kind's, field by field. `remOf`: a plane
    claim as the kind's: the function inside ptsOfOwn (Johnson/Desc/First/Att/SeatC.lean).
  `gv_callKR`, `gv_claim3`: wherever the kind's routine returns at K, at `inOld h`, it returns the
    written value (Fo.callKRV; jP of Fo.claim3V) and has gathered just the written list (Fo.callKRT;
    Fo.claim3T).
Used of OnBytes: plain records, pure functions and definitions alone; no routine in a context and no
theorem on a run: the records Attention.Heard, PlaneClaim, PW, Joins, ACall, Shape, Table; the pure
functions Attention.sumW, keyKR, Joins.set, Joins.empty; the written values and lists Fo.linPlanesT,
callKRV, callKRT, claim3V, claim3T.
Not claimed: that a routine returns; what a form is worth.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Claim3
import Johnson.Desc.First.Att.Claims.GV2

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (TablesP ScoreT Fun1 geoOf ptsOfOwn w1Of callOf tabOf keysOf tenOf)

variable {K : ℕ}

/-- The record of OnBytes/Model of the key forms as the kind's, field by field. -/
def jP (j : Joins) : P.Runs.JoinsP := { kf := j.kf, joined := j.joined }

theorem jP_set (j : Joins) (q : ℕ) (v : Aff) : (jP j).set q v = jP (j.set q v) := rfl

theorem jP_empty (n : ℕ) : P.Runs.JoinsP.empty n = jP (Joins.empty n) := rfl

/-- The plane claim of OnBytes/Model as the kind's: the function inside ptsOfOwn. -/
def remOf (c : PlaneClaim) : P.RemP :=
  { call := c.call, z := c.z, isD := c.isD, pw := w1Of c.pw, s0 := c.s0, np := c.np }

theorem planes_inOld (h : Attention.Heard) : (inOld h).p.planes = h.planes.map remOf := rfl

/-- The sum of the pieces' weights is that of OnBytes/Model. -/
theorem sumW_w1Of (pw : Array PW) : P.Runs.sumW (w1Of pw) = sumW pw := by
  unfold P.Runs.sumW sumW w1Of
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, List.foldl_map]

theorem keyKR_remOf (pc : PlaneClaim) : P.Runs.keyKR (remOf pc) = keyKR pc := by
  unfold P.Runs.keyKR keyKR remOf
  dsimp only
  rw [sumW_w1Of]
  rfl

/-- The calls of the kind's record of numbers, with their numbers. -/
theorem calls_zip (S : Shape) :
    (geoOf S).calls.toList.zipIdx = S.calls.toList.zipIdx.map fun x => (callOf x.1, x.2) := by
  show (S.calls.map callOf).toList.zipIdx = _
  rw [Array.toList_map, List.zipIdx_map]
  rfl

theorem tab_eq (k : Table) (t : Table) : (tabOf k == tabOf t) = (k == t) := by
  cases k <;> cases t <;> rfl

theorem gv_callKR (h : Attention.Heard) (q : ℕ) :
    GV K (P.Runs.callKR (inOld h) q) (Fo.callKRV h q) (Fo.callKRT h K q) := by
  unfold P.Runs.callKR Fo.callKRV Fo.callKRT
  rw [planes_inOld, ← Array.foldlM_toList, Array.toList_map, List.foldlM_map]
  exact GV.foldlM _ (fun v pc => if pc.call == q then v + keyKR pc else v)
    (fun pc => if pc.call == q then Fo.linPlanesT h K pc ++ [] else [])
    (fun v pc => GV.ite (GV.bind (gv_linPlanes h pc)
      ((GV.pure _).cast (by rw [keyKR_remOf]) rfl)) (GV.pure _)) _ _

/-- **Claim 3 of the kind's own text: the written joins and the written list.** -/
theorem gv_claim3 (h : Attention.Heard) (j : Joins) :
    GV K (P.Runs.claim3 (inOld h) (jP j)) (jP (Fo.claim3V h j)) (Fo.claim3T h K) := by
  unfold P.Runs.claim3 Fo.claim3V Fo.claim3T
  show GV K ((geoOf h.S).calls.toList.zipIdx.foldlM _ _) _ _
  rw [calls_zip, List.foldlM_map]
  exact GV.foldlMmap jP _
    (fun (j : Joins) (x : ACall × ℕ) => if x.1.kind == .kr then j.set x.2 (Fo.callKRV h x.2) else j)
    (fun (x : ACall × ℕ) => if x.1.kind == .kr then Fo.callKRT h K x.2 ++ [] else [])
    (fun j x => GV.cast (GV.ite' (q := (x.1.kind == Table.kr) = true)
      (by rw [← tab_eq x.1.kind Table.kr]; exact Iff.rfl)
      (GV.bind (gv_callKR h x.2) (GV.pure ((jP j).set x.2 (Fo.callKRV h x.2)))) (GV.pure (jP j)))
      (apply_ite jP _ _ _).symm rfl) _ _

end K5Law
