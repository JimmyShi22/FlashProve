-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestJoin.lean: the premise `JoinGives`
(Johnson/Desc/First/Att/K05GuestHid.lean) cut into its parts.

Definitions, statements and proofs. By `mcl_join` (OnBytes/Tie/Pv/Lookup/Ends/JoinClK.lean) and
`forA_key` (OnBytes/Tie/Pv/Lookup/Forest/FoJoinAt.lean) the lookup's out-claim on the keys is an
equation on the calls' own extensions (`joinRhs`, OnBytes/Tie/Pv/Lookup/Ends/Join.lean). The join of
an attention segment (`joinVal`, Cb/Pv/Att/End/Join.lean) is that equation where the join's letters
are the lookup's and the caller's keys are `keyVec` of the cells.
Main names:
  `JoinFits c P Q tb x m`: six clauses: there are four calls; the calls' weights e are `eC` at the
    lookup's end point; theta is the shift in the lookup's output statement; pad is the padding
    trees' term of `joinRhs`; the form ce is worth alpha, less the target, plus the mask form (the
    hidden value at the end of the key side); keys: the extension of the caller's key vector of call
    q at the lookup's point of call q is the extension of `keyVec` of the cells at the library's key
    point.
  `keysHold_iff`: under `FoNums.ok c.h` and `JoinFits`, the lookup's out-claim on the keys holds
    exactly if the join holds at the four extensions of `keyVec`.
  `joinGives_of_fits`: so `JoinGives`.
Used: pure functions and lemmas on them alone; no routine in a context: `mcl_join`,
`forA_key`, `ok_prem`, `ok_v`, `eC`, `zkC`, `nN`, `tauN`, `t0N`, `forK`, `zext`, `joinVal`,
`keyVec`, `KeysHold`.
Limits: `JoinFits` is shown for no caller. Its first five clauses say how the join's letters are
laid; the sixth speaks of the caller's L and of the agreement of the two sides' key points and
sizes. Nothing on an honest prover or on hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLkOut
import Johnson.Desc.First.Att.K05GuestHid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg Finset
open OnBytes.Ends (eC zkC nN tauN t0N mcl_join)
open VerifiableInference.OnPublicFiles (LookupCCaller)

section Join
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (Q : JoinLay P) (tb : Tables)

/-- The join's letters are the lookup's, and the caller's keys are keyVec of the cells. -/
structure JoinFits (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) : Prop where
  nc : c.h.NC = 4
  e : ∀ q : Fin 4, (Q.q x).e q = eC c.h x.2.1.pt q.1
  th : (Q.q x).theta = x.1.2
  pad : (Q.q x).pad = ∑ y ∈ Ico c.h.NT (2 ^ c.h.rK),
    Blocks.eqN c.h.rK c.h.dT x.2.1.pt y * ((Q.q x).alpha - (tauN c.h 0 (t0N c.h 0) : Cb.Gl.E))
  ce : (Q.ce x).val (P.msg m) = (Q.q x).alpha - x.2.1.tg + ∑ i, x.2.1.mf i * zext (c.msg₀ m) i
  keys : ∀ q : Fin 4, Blocks.ext (nN c.h q.1) (forK Cb.Gl.E c.L x.1.1 (zext (c.msg₀ m)) q.1)
      (zkC c.h x.2.1.pt q.1) =
    Blocks.ext (P.C.a q) (keyVec (scl := Q.scl) P.D tb (P.tOf m) q) (P.C.zC q (P.zOf x))

/-- **The lookup's out-claim on the keys is the join at the calls' vectors of looked-up values.** -/
theorem keysHold_iff (ok : FoNums.ok c.h = true) (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (m : c.Sg.Msg) (F : JoinFits c P Q tb x m) :
    KeysHold c x m ↔
      joinVal (Q.q x) (fun q => Blocks.ext (P.C.a q) (keyVec (scl := Q.scl) P.D tb (P.tOf m) q)
        (P.C.zC q (P.zOf x))) ((Q.ce x).val (P.msg m)) = 0 := by
  have h1 : KeysHold c x m ↔ OnBytes.Ends.joinRhs c.h (forK Cb.Gl.E c.L x.1.1 (zext (c.msg₀ m))) x.1.2 (Q.q x).alpha
      x.2.1.pt = (Q.q x).alpha - x.2.1.tg + ∑ i, x.2.1.mf i * zext (c.msg₀ m) i :=
    mcl_join (Fo.ok_prem ok) _ x.1.2 (Q.q x).alpha x.2.1 (zext (c.msg₀ m)) (Cb.Fo.ok_v ok).symm
      (Fo.forA_key Cb.Gl.E c.h c.L ok x.1.1 x.1.2 (zext (c.msg₀ m)))
  have h2 : OnBytes.Ends.joinRhs c.h (forK Cb.Gl.E c.L x.1.1 (zext (c.msg₀ m))) x.1.2 (Q.q x).alpha x.2.1.pt =
      ∑ q : Fin 4, (Q.q x).e q * ((Q.q x).alpha - (q.val : Cb.Gl.E) * (Q.q x).theta -
        Blocks.ext (P.C.a q) (keyVec (scl := Q.scl) P.D tb (P.tOf m) q) (P.C.zC q (P.zOf x))) +
        (Q.q x).pad := by
    unfold OnBytes.Ends.joinRhs
    rw [F.nc, Finset.sum_range, F.pad]
    congr 1
    exact Finset.sum_congr rfl fun q _ => by rw [F.e, F.th, F.keys]
  rw [h1, h2, ← F.ce]
  unfold joinVal
  exact ⟨fun e => by rw [e]; ring, fun e => by linear_combination e⟩

/-- So the premise `JoinGives` of `keys_link` follows from the six clauses. -/
theorem joinGives_of_fits (ok : FoNums.ok c.h = true) (F : ∀ x m, JoinFits c P Q tb x m) :
    JoinGives c P Q tb := fun x m h => (keysHold_iff c P Q tb ok x m (F x m)).2 h

end Join

end VerifiableInference.Desc.First.Att.P
