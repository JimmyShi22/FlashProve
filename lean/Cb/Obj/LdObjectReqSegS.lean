-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqSegS.lean: the object's term of a request is OK, from `r.ZkS` and the hypotheses
named below.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves.
Statements and proofs: the analogues of `ldReqStart_goodT` (Cb/Req1/LdReqStart.lean) and `ldOS_okAt`
(Cb/Obj/LdObjectReqSeg.lean), with `r.ZkS` (Cb/Req1/LdReqS.lean: the set of fresh facts closed under
join at each segment's entry) in the place of `r.Zk`. The file imports nothing of the object's
records, so that these can import it: Cb/Obj/LdObjectTerms.lean does.

Main names:
  `Spec.ldReqStartS_goodT`: the request as one reduction from a statement without oracle messages:
    the whole bundle (`GoodT`, Ior/KnowCollGood.lean), from `r.Hyp`, `r.ZkS`.
  `Spec.ldOS_okAtS`: the object's term of a request is OK (`LdOL.ReqT.OK`, Cb/Obj/LdObjectReq.lean),
    from `EndOK`, `r.Hyp`, `r.ZkS` and the format.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqSeg
import Cb.Req1.LdReqSProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace Spec

def ldReqStartS_goodT : Prop :=
  ∀ (E Kc Xi Wi : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi),
    r.Hyp → r.ZkS → GoodT (r.F w₀) (r.FH w₀) A z.J.rels (r.Fext w₀) (r.FP w₀)

def ldOS_okAtS (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc) (Wp : Type)
      (B : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)) (pi : Wp → O.Cf.conf.PIdx)
      (r : O.ReqAt core Wp B) (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (O.jReq core)).J.E.Pos → Prop)
      (qi : Finset (O.zAt Wp B).J.E.Pos → Prop),
    O.EndOK pi B → r.Hyp → r.ZkS →
    r.chain.Fmt (O.fmtA core qφ) (O.fmtZAt B pi qi) → (O.termAt r pi w₀).OK core

end Spec

theorem ldReqStartS_goodT : Spec.ldReqStartS_goodT := fun E Kc Xi Wi E0 _ _ A z r w₀ h hz =>
  (goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2
    ⟨ldReqStart_goodB E Kc Xi Wi E0 A z r w₀ h,
      exact_pre _ _ _ _ _ _ _ _ _ _ _ _ A.rel _ _ _
        (fun p : Xi × Wi => (ldStartX E p.1, ldStartW E p.2)) ldStartE_isLocal (ldStartStep A).acc
        (ldReqS_goodT E Kc _ z r (ldStartW E w₀) h hz).exact⟩

theorem ldOS_okAtS (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOS_okAtS F E := by
  intro O Kc core Wp B pi r w₀ qφ qi hE hH hZ hF
  obtain ⟨h1, h2, h3, -⟩ := ldReqStart_fmt E Kc _ _ O.Cf.conf.Rec O.Cf.conf.PIdx O.Cf.conf.E0
    (O.jReq core) O.S _ _ B r w₀ (O.fmtA core qφ) (O.fmtZAt B pi qi) (fun _ => True) hH hF rfl
    rfl (fun _ _ => trivial)
  exact ⟨ldReqStartS_goodT E Kc _ _ O.Cf.conf.E0 (O.jReq core) (O.zAt Wp B) r w₀ hH hZ, h1, h2, h3,
    hE⟩

end Cb
