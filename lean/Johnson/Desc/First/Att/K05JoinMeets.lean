-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinMeets.lean: the join as the verifier's record has it (`qAt` and the
worth of the heard record's cEnd, Johnson/Desc/First/Att/Claims/PortJoin.lean) meets the join at the
letters made of the typed lookup's output statement (`joinLayOf`,
Johnson/Desc/First/Att/K05GuestKeysAt.lean): in worth, not letter for letter.

Why not letter for letter. The typed lookup's output statement `TX` (Cb/Ld/LdLkpTree.lean) holds the
state, the shift theta, one masked claim and rows. It does not hold alpha. The field q of a
`JoinLay` is a function of that statement, fixed in front. So the equation Q.q x0 = qAt ρ gL, which
asks that (Q.q x0).alpha is gL.alpha, read, can be met by no Q at such a statement, unless alpha
were a function of the statement (`hq_fixes_alpha`). What saves the meeting: the join's worth does
not hang on alpha (`joinVal_free`).

Definitions, statements and proofs.
Main names:
  `kfN`, `joinVal_free`: at e := `eC`, pad := the padding trees' term of `joinRhs` at α and ce := α
    - t, `joinVal` is t less the extension of the joint key vector of the constant vectors kf: no α
    on the right. By `join_identity` (OnBytes/Tie/Pv/Lookup/Ends/Join.lean) and `ext_const`
    (Blocks/Ext.lean).
  `K3Join c gL W x0 m`: what the lookup's kind has to give, in the names of its heard record: theta,
    read, is the shift in x0; e[q], read, is `eC` at the end point of x0; `emptyE` gL
    (Johnson/Road/HeadJoin.lean), read, is the padding trees' term at gL.alpha, read; the worth of
    gL.cEnd is gL.alpha, read, less the target of x0, plus the mask form of x0.
  `join_meets`: under `K3Join`, for all kf and every α, joinVal (qAt Reading.gl gL) kf (the worth of
    gL.cEnd) is joinVal at the letters `joinLayOf` c P scl α en.
  `hscl_at`: at the scales `sclOf` S the first shift of the letters' table of scales is the group's.
  `hq_fixes_alpha`: whatever Q is, two heard records that meet it letter for letter at one output
    statement have one alpha.
Premises of `join_meets`: `FoNums.ok c.h`; four calls; en carries the caller's entries into those of
P; `K3Join`.
Used: pure functions, forms and lemmas on them alone; no routine in a context: `qAt`,
`joinVal`, `joinLayOf`, `join_identity`, `ext_const`, `ok_prem`, `eC`, `zkC`, `nN`, `tauN`, `t0N`,
`jointKey`, `zext`, `val_aAdd`, `val_aConst`, `val_aSum`, `val_aSmul`, `val_aEnt`.
Limits: `K3Join` is shown for no run. No soundness of the protocol is claimed: the premises named
are not shown. Nothing on an honest prover, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortJoin
import Johnson.Desc.First.Att.K05GuestKeysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg Finset
open OnBytes OnBytes.Model
open OnBytes.Ends (eC zkC nN tauN t0N Prem jointKey join_identity)
open VerifiableInference.OnPublicFiles (LookupCCaller)

section Free
variable {K : Type} [Field K]

/-- Four values as a function of a call's number. -/
def kfN (kf : Fin 4 → K) (c : ℕ) : K := if hc : c < 4 then kf ⟨c, hc⟩ else 0

/-- **The join's worth does not hang on alpha.** -/
theorem joinVal_free {h : Forest.Shape} (hp : Prem h) (nc : h.NC = 4) (θ α : K) (pt : ℕ → K) (kf : Fin 4 → K)
    (t : K) :
    joinVal ⟨α, θ, fun q => eC h pt q.1,
        ∑ y ∈ Ico h.NT (2 ^ h.rK), Blocks.eqN h.rK h.dT pt y * (α - (tauN h 0 (t0N h 0) : K))⟩ kf (α - t) =
      t - Blocks.ext h.v (jointKey h (fun c _ => kfN kf c) θ) pt := by
  have e := join_identity hp (fun c _ => kfN kf c) θ α pt
  unfold OnBytes.Ends.joinRhs at e
  rw [nc, Finset.sum_range] at e
  have e2 : ∀ q : Fin 4, Blocks.ext (nN h q.1) (fun _ => kfN kf q.1) (zkC h pt q.1) = kf q := fun q => by
    rw [Blocks.ext_const]
    unfold kfN
    rw [dif_pos q.2]
  simp only [e2] at e
  unfold joinVal
  linear_combination (-1 : K) * e

end Free

section Meets
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))

/-- **What the lookup's kind must give for the join**, in its heard record's names. -/
structure K3Join (gL : Forest.Heard) (W : World Cb.Gl.E) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (m : c.Sg.Msg) : Prop where
  theta : Reading.gl.val gL.theta = x0.1.2
  e : ∀ q : Fin 4, Reading.gl.val (gL.e.getD q.1 zeroE) = eC c.h x0.2.1.pt q.1
  empty : Reading.gl.val (OnBytes.Road.Hd.emptyE gL) = ∑ y ∈ Ico c.h.NT (2 ^ c.h.rK),
    Blocks.eqN c.h.rK c.h.dT x0.2.1.pt y * (Reading.gl.val gL.alpha - (tauN c.h 0 (t0N c.h 0) : Cb.Gl.E))
  cEnd : gL.cEnd.value Reading.gl W =
    Reading.gl.val gL.alpha - x0.2.1.tg + ∑ i, x0.2.1.mf i * zext (c.msg₀ m) i

variable {c P}

/-- **The two joins are worth the same**, at every alpha of the typed letters. -/
theorem join_meets (ok : FoNums.ok c.h = true) (nc : c.h.NC = 4) (scl : Scl)
    (α : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Cb.Gl.E) (en : c.J₀ → P.J)
    (hen : ∀ m j, P.msg m (en j) = c.msg₀ m j) {gL : Forest.Heard} {W : World Cb.Gl.E}
    {x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)} {m : c.Sg.Msg} (J : K3Join c gL W x0 m)
    (kf : Fin 4 → Cb.Gl.E) :
    joinVal (K5Law.qAt Reading.gl gL) kf (gL.cEnd.value Reading.gl W) =
      joinVal ((joinLayOf c P scl α en).q x0) kf (((joinLayOf c P scl α en).ce x0).val (P.msg m)) := by
  have hce : ((joinLayOf c P scl α en).ce x0).val (P.msg m) =
      α x0 - (x0.2.1.tg - ∑ i, x0.2.1.mf i * zext (c.msg₀ m) i) := by
    show (aAdd (aConst (α x0 - x0.2.1.tg))
      (aSum univ fun j : c.J₀ => aSmul (x0.2.1.mf (some j)) (aEnt (en j)))).val (P.msg m) = _
    rw [val_aAdd, val_aConst, val_aSum, Fintype.sum_option]
    have e0 : x0.2.1.mf none * zext (c.msg₀ m) none = 0 := mul_zero _
    rw [e0, zero_add]
    have e1 : ∑ j : c.J₀, (aSmul (x0.2.1.mf (some j)) (aEnt (en j) : Aff Cb.Gl.E P.J)).val (P.msg m) =
        ∑ j : c.J₀, x0.2.1.mf (some j) * zext (c.msg₀ m) (some j) :=
      sum_congr rfl fun j _ => by
        rw [val_aSmul, val_aEnt, hen]
        rfl
    rw [e1]
    ring
  have hL : K5Law.qAt Reading.gl gL = ⟨Reading.gl.val gL.alpha, x0.1.2, fun q => eC c.h x0.2.1.pt q.1,
      ∑ y ∈ Ico c.h.NT (2 ^ c.h.rK), Blocks.eqN c.h.rK c.h.dT x0.2.1.pt y *
        (Reading.gl.val gL.alpha - (tauN c.h 0 (t0N c.h 0) : Cb.Gl.E))⟩ := by
    unfold K5Law.qAt
    rw [J.theta, J.empty]
    congr 1
    funext q
    exact J.e q
  have hcL : gL.cEnd.value Reading.gl W =
      Reading.gl.val gL.alpha - (x0.2.1.tg - ∑ i, x0.2.1.mf i * zext (c.msg₀ m) i) := by
    rw [J.cEnd]
    ring
  rw [hL, hcL, hce, joinVal_free (Fo.ok_prem ok) nc]
  exact (joinVal_free (Fo.ok_prem ok) nc x0.1.2 (α x0) x0.2.1.pt kf _).symm

/-- The first shift of the letters' table of scales is the group's, at the scales of the shape. -/
theorem hscl_at (S : Attention.Shape) (α : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Cb.Gl.E)
    (en : c.J₀ → P.J) :
    ((joinLayOf c P (OnBytes.Road.L5.sclOf S) α en).scl.κ 0).sh = S.cf.sh.getD 0 0 := rfl

/-- **Why the two cannot meet letter for letter**: whatever Q is, two heard records of the lookup
that meet it letter for letter at one output statement have one alpha. -/
theorem hq_fixes_alpha (Q : JoinLay P) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) {g g' : Forest.Heard}
    (h : Q.q x0 = K5Law.qAt Reading.gl g) (h' : Q.q x0 = K5Law.qAt Reading.gl g') :
    Reading.gl.val g.alpha = Reading.gl.val g'.alpha :=
  congrArg JoinPub.alpha (h.symm.trans h')

end Meets

end VerifiableInference.Desc.First.Att.P
