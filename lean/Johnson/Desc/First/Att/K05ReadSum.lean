-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadSum.lean: the reading of Att/K05Read.lean at a sumcheck's stage: the
image of what the stage's
rounds hold, read in the field, is the stage's typed transcript (OnBytes/Tie/Pv/Att/OwnTie.lean:
SumH.tr).

Main names:
  `rdH`, `getD_read`: a heard round as plain data; reading commutes with "the i-th, or 0".
  `plainSp`, `plainSp_length`, `plainFit`: the specs of a plain sumcheck's variables: each sends its
    degree's scalars and
    draws one element; the further variable's element is never 0.
  `cube_img`, `plainRd`, `sum_img`: the variables' rounds; the whole stage.
  `Reads`, `reads_some`, `reads_map`, `sum_img'`: the same from any plain data that read the stage's
    rounds. What a
    values' round drew is not read: the spec there has no draw, so nothing can stand in it.

Sources: Att/K05Read.lean; Att/K5SaidAll.lean; OnBytes/Tie/Pv/Att/Tr.lean (cubeTr, lastTr, plainTr).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Read
import Johnson.Desc.First.Att.K5SaidAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Cb.Pv.Lay Johnson.L5.Layers OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel TwV OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH SumH cubeTr lastTr plainTr)

noncomputable section

/-- A heard round as plain data. -/
def rdH (h : RoundH) : List GE × List GE := (h.1.map Reading.gl.val, (h.2.getD []).map Reading.gl.val)

theorem getD_read (l : List E) (i : ℕ) : (l.map Reading.gl.val).getD i 0 = Reading.gl.val (l.getD i zeroE) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact Reading.gl.zero.symm
  | some x => rfl

/-- The specs of k cube variables, then of the further variable. -/
def plainSp : (k : ℕ) → (Fin k → ℕ) → ℕ → List Tw.RSp
  | 0, _, DY => [⟨DY, 1, true⟩]
  | k + 1, n, DY => ⟨n 0, 1, false⟩ :: plainSp k (fun i => n i.succ) DY

theorem plainSp_length : ∀ (k : ℕ) (n : Fin k → ℕ) (DY : ℕ), (plainSp k n DY).length = k + 1
  | 0, _, _ => rfl
  | k + 1, n, DY => congrArg (· + 1) (plainSp_length k (fun i => n i.succ) DY)

theorem plainFit : ∀ (k : ℕ) (n : Fin k → ℕ) (DY : ℕ),
    Tw.VFit (ldPartFmt GE k n ++ [pDummy GE DY]) (plainSp k n DY)
  | 0, _, _ => ⟨⟨rfl, rfl, fun x hx => ⟨⟨x, hx rfl⟩, rfl⟩⟩, trivial⟩
  | k + 1, n, DY => ⟨⟨rfl, rfl, fun x _ => ⟨x, rfl⟩⟩, plainFit k (fun i => n i.succ) DY⟩

theorem inv_val (f : PFmt GE) (hi : Function.Injective f.val) (c : f.Ch) : Function.invFun f.val (f.val c) = c :=
  Function.leftInverse_invFun hi c

/-- The variables' rounds, the further variable's and what stands behind. -/
theorem cube_img (DY : ℕ) (A : Type) (sh : List A) (nd : sh.Nodup) (sentY : List E) (beta : E)
    (hβ : Reading.gl.val beta ≠ 0) (v : List E) (vals : A → GE)
    (hv : Tw.valsOf sh (v.map Reading.gl.val) = vals) :
    ∀ (k : ℕ) (n : Fin k → ℕ) (rs : List (List E × E)), rs.length = k →
      img (sRounds (ldPartFmt GE k n ++ [pDummy GE DY]) ++ [pRoundV GE A])
        (plainSp k n DY ++ [⟨sh.length, 0, false⟩])
        (Rds.app (sRounds (ldPartFmt GE k n ++ [pDummy GE DY])) (plainSp k n DY)
          (rdsS _ _ (plainFit k n DY))
          (show Rds [pRoundV GE A] [⟨sh.length, 0, false⟩] from (Rd.vals sh nd, ())))
        (((rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++ [(sentY, some [beta]), (v, none)]).map rdH) =
      cubeTr Reading.gl (pDummy GE DY) [pRoundV GE A] k n rs (lastTr Reading.gl DY A sentY beta hβ vals)
  | 0, _, [], _ => by
    show ((((), fun i : Fin DY => (sentY.map Reading.gl.val).getD i.1 0),
      Function.invFun (pDummy GE DY).val ((pDummy GE DY).val ⟨Reading.gl.val beta, hβ⟩),
      (((), Tw.valsOf sh (v.map Reading.gl.val)), (), ())) :
        Tr (sRound (pDummy GE DY) :: [pRoundV GE A])) = _
    rw [inv_val (pDummy GE DY) Subtype.val_injective]
    have e1 : (fun i : Fin DY => (sentY.map Reading.gl.val).getD i.1 0) = rd Reading.gl DY sentY :=
      funext fun i => getD_read sentY i.1
    rw [e1, hv]
    rfl
  | k + 1, n, x :: rs, h => by
    have ih := cube_img DY A sh nd sentY beta hβ v vals hv k (fun i => n i.succ) rs (by simpa using h)
    show ((((), fun i : Fin (n 0) => (x.1.map Reading.gl.val).getD i.1 0),
      Function.invFun (pfCube GE (n 0)).val ((pfCube GE (n 0)).val (Reading.gl.val x.2)), _) :
        Tr (sRound (pfCube GE (n 0)) :: (sRounds (ldPartFmt GE k (fun i => n i.succ) ++ [pDummy GE DY]) ++
          [pRoundV GE A]))) = (((), rd Reading.gl (n 0) x.1), Reading.gl.val x.2, _)
    rw [inv_val (pfCube GE (n 0)) Function.injective_id]
    have e1 : (fun i : Fin (n 0) => (x.1.map Reading.gl.val).getD i.1 0) = rd Reading.gl (n 0) x.1 :=
      funext fun i => getD_read x.1 i.1
    rw [e1]
    exact congrArg (fun t => (((), rd Reading.gl (n 0) x.1), Reading.gl.val x.2, t)) ih
  | 0, _, _ :: _, h => by simp at h
  | _ + 1, _, [], h => by simp at h

/-- The reader's data of a plain sumcheck's stage. -/
def plainRd (T : PlainSc GE) (sh : List T.A) (nd : sh.Nodup) : RideRd T.our.par :=
  ⟨plainSp T.nv T.deg T.DY, plainFit T.nv T.deg T.DY, sh, nd⟩

/-- **A sumcheck's stage**: the image of what its rounds hold, read, is its typed transcript. -/
theorem sum_img {M X : Type} {S : SumL GE M X} (D : SumH Reading.gl S) (sh : List S.T.A) (nd : sh.Nodup)
    (hr : D.r.length = S.n) (hl : D.H.rs.length = S.T.nv) (hv : Tw.valsOf sh (D.H.v.map Reading.gl.val) = D.v) :
    img (shapeRN S.T.our.par S.n) _ (rideRds S.T.our.par S.n (plainRd S.T sh nd)) ((sumRounds D.r D.H).map rdH) =
      D.tr := by
  have ih := cube_img S.T.DY S.T.A sh nd D.H.sentY D.H.beta D.b D.H.v D.v hv S.T.nv S.T.deg D.H.rs hl
  have e1 : (fun i : Fin S.n => ((D.r ++ [D.H.mu]).map Reading.gl.val).getD i.1 0) = D.rd := funext fun i => by
    rw [getD_read, List.getD_append _ _ _ _ (by rw [hr]; exact i.2)]
    rfl
  have e2 : ((D.r ++ [D.H.mu]).map Reading.gl.val).getD S.n 0 = Reading.gl.val D.H.mu := by
    rw [getD_read, List.getD_append_right _ _ _ _ (by rw [hr]), hr, Nat.sub_self]
    rfl
  show ((((), (fun i : Fin S.n => ((D.r ++ [D.H.mu]).map Reading.gl.val).getD i.1 0,
      ((D.r ++ [D.H.mu]).map Reading.gl.val).getD S.n 0)), Reading.gl.val D.H.eps, _) :
        Tr (shapeRN S.T.our.par S.n)) = (((), (D.rd, Reading.gl.val D.H.mu)), Reading.gl.val D.H.eps, _)
  rw [e1, e2]
  exact congrArg (fun t => (((), (D.rd, Reading.gl.val D.H.mu)), Reading.gl.val D.H.eps, t)) ih

/-- Plain data read a heard round: what was sent; what was drawn, where the hearing says it. -/
def Reads (h : RoundH) (x : List GE × List GE) : Prop :=
  x.1 = h.1.map Reading.gl.val ∧ ∀ l, h.2 = some l → x.2 = l.map Reading.gl.val

theorem reads_some {s l : List E} {x : List GE × List GE} (h : Reads (s, some l) x) : x = rdH (s, some l) :=
  Prod.ext h.1 (h.2 l rfl)

theorem reads_map {f : List E × E → RoundH} (hf : ∀ y, ∃ s l, f y = (s, some l)) :
    ∀ {a : List (List E × E)} {p : Rounds GE}, List.Forall₂ Reads (a.map f) p → p = (a.map f).map rdH
  | [], _, .nil => rfl
  | y :: a, _, .cons (b := x) (l₂ := p) h1 h2 => by
    obtain ⟨s, l, e⟩ := hf y
    have h1' : Reads (s, some l) x := e ▸ h1
    show x :: p = rdH (f y) :: _
    rw [reads_map hf h2, e, reads_some h1']

/-- **A sumcheck's stage, from plain data that read its rounds.** What the values' round drew is not
read. -/
theorem sum_img' {M X : Type} {S : SumL GE M X} (D : SumH Reading.gl S) (sh : List S.T.A) (nd : sh.Nodup)
    (hr : D.r.length = S.n) (hl : D.H.rs.length = S.T.nv) (hv : Tw.valsOf sh (D.H.v.map Reading.gl.val) = D.v)
    {pa : Rounds GE} (hp : List.Forall₂ Reads (sumRounds D.r D.H) pa) :
    img (shapeRN S.T.our.par S.n) _ (rideRds S.T.our.par S.n (plainRd S.T sh nd)) pa = D.tr := by
  rw [← sum_img D sh nd hr hl hv]
  have hp' : List.Forall₂ Reads ((D.r ++ [D.H.mu], some [D.H.eps]) ::
      ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++ [(D.H.sentY, some [D.H.beta]), (D.H.v, none)])) pa := hp
  rcases hp' with _ | ⟨h0, h1⟩
  rename_i x0 p1
  obtain ⟨pv, pl, rfl, g1, g2⟩ := Tw.f2_split _ _ _ h1
  rcases g2 with _ | ⟨gY, g3⟩
  rename_i xY p3
  rcases g3 with _ | ⟨gV, g4⟩
  rename_i xV p4
  cases g4
  have e0 := reads_some h0
  have eV := reads_map (f := fun x : List E × E => ((x.1, some [x.2]) : RoundH)) (fun y => ⟨_, _, rfl⟩) g1
  have eY := reads_some gY
  subst e0 eV eY
  have hlen : ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta])]).length =
      (plainSp S.T.nv S.T.deg S.T.DY).length := by
    rw [plainSp_length]
    simp [hl]
  have key : ∀ xl : List GE × List GE, xl.1 = D.H.v.map Reading.gl.val →
      img (sRounds S.T.our.par.fmt ++ [pRoundV GE S.T.our.par.A]) (plainSp S.T.nv S.T.deg S.T.DY ++ [⟨sh.length, 0, false⟩])
        (Rds.app (sRounds S.T.our.par.fmt) (plainSp S.T.nv S.T.deg S.T.DY) (rdsS _ _ (plainFit S.T.nv S.T.deg S.T.DY))
          (show Rds [pRoundV GE S.T.our.par.A] [⟨sh.length, 0, false⟩] from (Rd.vals sh nd, ())))
        (((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta])]) ++ [xl]) =
      Tr.app (s := sRounds S.T.our.par.fmt) (t := [pRoundV GE S.T.our.par.A])
        (img (sRounds S.T.our.par.fmt) _ (rdsS _ _ (plainFit S.T.nv S.T.deg S.T.DY))
        ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta])]))
        ((((), Tw.valsOf sh (D.H.v.map Reading.gl.val)), (), ()) : Tr [pRoundV GE S.T.our.par.A]) := by
    intro xl hx
    rw [img_app _ _ _ _ _ _ hlen]
    show Tr.app (s := sRounds S.T.our.par.fmt) (t := [pRoundV GE S.T.our.par.A]) _
      ((((), Tw.valsOf sh xl.1), (), ()) : Tr [pRoundV GE S.T.our.par.A]) = _
    rw [hx]
  have k1 := key xV gV.1
  have k2 := key (rdH (D.H.v, none)) rfl
  show ((rdRide S.n).fm _, (rdRide S.n).g _, img (sRounds S.T.our.par.fmt ++ [pRoundV GE S.T.our.par.A]) _ _
    ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta]), xV])) =
    ((rdRide S.n).fm _, (rdRide S.n).g _, img (sRounds S.T.our.par.fmt ++ [pRoundV GE S.T.our.par.A]) _ _
      (((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++
        [(D.H.sentY, some [D.H.beta]), (D.H.v, none)]).map rdH))
  have a1 : (D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta]), xV] =
      ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta])]) ++ [xV] := by
    simp
  have a2 : ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)) ++
        [(D.H.sentY, some [D.H.beta]), (D.H.v, none)]).map rdH =
      ((D.H.rs.map fun x => ((x.1, some [x.2]) : RoundH)).map rdH ++ [rdH (D.H.sentY, some [D.H.beta])]) ++
        [rdH (D.H.v, none)] := by
    simp
  rw [a1, a2]
  exact congrArg (fun t => ((rdRide S.n).fm _, (rdRide S.n).g _, t)) (k1.trans k2.symm)

theorem sumRounds_length (r : List E) (H : PscH) : (sumRounds r H).length = H.rs.length + 3 := by
  simp [sumRounds, partsRounds]

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.sum_img
#print axioms VerifiableInference.Desc.First.Att.P.sum_img'
#print axioms VerifiableInference.Desc.First.Att.P.cube_img
