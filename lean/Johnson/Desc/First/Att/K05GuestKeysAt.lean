-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestKeysAt.lean: `JoinFits` (Johnson/Desc/First/Att/K05GuestJoin.lean),
and so `JoinGives`, at letters of the join that are made of the lookup's own, for any caller whose
keys are `keyVec` of cells read off its entries.

Definitions, statements and proofs.
Main names:
  `zkC_eq_zC`: the lookup's point of call q (`zkC`, OnBytes/Tie/Pv/Lookup/Ends/Join.lean) is the
    library's key point `Calls.zC` at C := `callsOf` of the lookup's shape, under the public test
    `CallsFit`. (`zk_eq_zC_of_fit`, Johnson/Road/Lane5ZkZc.lean, says the like of the verifier's
    arrays, read.)
  `joinLayOf c P scl α en`: the join's letters: alpha := α x; theta := the shift in the lookup's
    output statement; e := `eC` at the end point; pad := the padding trees' term of `joinRhs`; ce :=
    the form "alpha, less the target, plus the mask form", its entries carried into those of P by
    en.
  `joinFits_of_lay`: `JoinFits` at these letters.
  `joinGives_at`: so `JoinGives`.
Premises: `FoNums.ok c.h`; four calls; `CallsFit`; P.C = callsOf c.h; P.zOf is the lookup's end
point; en carries the caller's entries into those of P (hen); the caller's keys are `keyVec` of the
cells cellsOf (hK); these cells are those of P (hc).
Used: pure functions, forms and lemmas on them alone; no routine in a context:
`callsFit_iota`, `aConst`, `aAdd`, `aSmul`, `aSum`, `aEnt`, `val_aAdd`, `val_aConst`, `val_aSum`,
`val_aSmul`, `val_aEnt`, `eC`, `iotaN`, `tauN`, `t0N`, `forK`, `zext`, `joinGives_of_fits`.
Limits: α is a free letter: `mcl_join` (OnBytes/Tie/Pv/Lookup/Ends/JoinClK.lean) is stated for every
alpha. hen, hK and hc are shown for no caller in this file. No soundness of the protocol is claimed:
the premises named are not shown. Nothing on an honest prover or on hiding.

-/
import Johnson.Road.Lane5CallsOf
import Johnson.Desc.First.Att.K05GuestJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg Finset
open OnBytes.Ends (eC zkC nN iotaN tauN t0N)
open OnBytes.Road.L5 (callsOf CallsFit callsFit_iota)
open VerifiableInference.OnPublicFiles (LookupCCaller)

/-- **The lookup's point of a call is the library's key point.** -/
theorem zkC_eq_zC {K : Type} {S : OnBytes.Attention.Shape} {fs : OnBytes.Model.Forest.Shape} (hf : CallsFit S fs)
    (q : Fin 4) (pt : ℕ → K) : zkC fs pt q.1 = (callsOf fs).zC q pt := by
  obtain ⟨h1, h2⟩ := callsFit_iota hf q
  have hDk : (callsOf fs).Dk = fs.dT := rfl
  have hsg : (callsOf fs).sg = fs.rK := rfl
  funext i
  unfold zkC iotaN Calls.zC
  rw [h1, hDk, hsg]
  by_cases h : i < (callsOf fs).e q
  · rw [if_pos h, if_pos h]
    congr 1
    omega
  · rw [if_neg h, if_neg h]

section At
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))

/-- **The join's letters, made of the lookup's.** -/
noncomputable def joinLayOf (scl : Scl) (α : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Cb.Gl.E)
    (en : c.J₀ → P.J) : JoinLay P where
  scl := scl
  q := fun x => ⟨α x, x.1.2, fun q => eC c.h x.2.1.pt q.1,
    ∑ y ∈ Ico c.h.NT (2 ^ c.h.rK),
      Blocks.eqN c.h.rK c.h.dT x.2.1.pt y * (α x - (tauN c.h 0 (t0N c.h 0) : Cb.Gl.E))⟩
  ce := fun x => aAdd (aConst (α x - x.2.1.tg))
    (aSum univ fun j : c.J₀ => aSmul (x.2.1.mf (some j)) (aEnt (en j)))

variable {c P}

/-- **JoinFits at these letters.** -/
theorem joinFits_of_lay (scl : Scl) (α : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Cb.Gl.E)
    (en : c.J₀ → P.J) (tb : Tables) {S : OnBytes.Attention.Shape} (hf : CallsFit S c.h)
    (hC : P.C = callsOf c.h) (hz : ∀ b, P.zOf b = b.2.1.pt) (nc : c.h.NC = 4)
    (hen : ∀ m j, P.msg m (en j) = c.msg₀ m j) (cellsOf : (c.J₀ → Cb.Gl.E) → Raw → Cb.Gl.E)
    (hK : ∀ st μ (q : Fin 4) i, c.L.K st μ q.1 i = keyVec (scl := scl) P.D tb (cellsOf μ) q i)
    (hc : ∀ m, cellsOf (c.msg₀ m) = P.tOf m)
    (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) :
    JoinFits c P (joinLayOf c P scl α en) tb x m where
  nc := nc
  e := fun _ => rfl
  th := rfl
  pad := rfl
  ce := by
    show (aAdd (aConst (α x - x.2.1.tg))
      (aSum univ fun j : c.J₀ => aSmul (x.2.1.mf (some j)) (aEnt (en j)))).val (P.msg m) = _
    rw [val_aAdd, val_aConst, val_aSum, Fintype.sum_option]
    have e0 : x.2.1.mf none * zext (c.msg₀ m) none = 0 := mul_zero _
    rw [e0, zero_add]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [val_aSmul, val_aEnt, hen]
    rfl
  keys := fun q => by
    have e1 : forK Cb.Gl.E c.L x.1.1 (zext (c.msg₀ m)) q.1 =
        keyVec (scl := scl) P.D tb (P.tOf m) q := by
      funext i
      rw [← hc m]
      exact hK x.1.1 (c.msg₀ m) q i
    rw [e1, zkC_eq_zC hf q, hz x, hC]
    rfl

/-- So the premise `JoinGives` of `keys_link` holds at these letters. -/
theorem joinGives_at (ok : FoNums.ok c.h = true) (scl : Scl)
    (α : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Cb.Gl.E) (en : c.J₀ → P.J) (tb : Tables)
    {S : OnBytes.Attention.Shape} (hf : CallsFit S c.h) (hC : P.C = callsOf c.h)
    (hz : ∀ b, P.zOf b = b.2.1.pt) (nc : c.h.NC = 4) (hen : ∀ m j, P.msg m (en j) = c.msg₀ m j)
    (cellsOf : (c.J₀ → Cb.Gl.E) → Raw → Cb.Gl.E)
    (hK : ∀ st μ (q : Fin 4) i, c.L.K st μ q.1 i = keyVec (scl := scl) P.D tb (cellsOf μ) q i)
    (hc : ∀ m, cellsOf (c.msg₀ m) = P.tOf m) : JoinGives c P (joinLayOf c P scl α en) tb :=
  joinGives_of_fits c P _ tb ok fun x m => joinFits_of_lay scl α en tb hf hC hz nc hen cellsOf hK hc x m

end At

end VerifiableInference.Desc.First.Att.P
