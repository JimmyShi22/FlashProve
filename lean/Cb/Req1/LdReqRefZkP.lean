-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefZkP.lean: what honest-verifier zero knowledge asks of the reference request
(`r.Zk`), beside its hypotheses.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.
The reference request r is the term `ldReqRef`, with its list L of segments and its last segment T
(Cb/Req1/LdReqRef.lean). Facts: A `MaskFact W` is a reading `kc` of witnesses of type W into a type
`Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. (Cb/Req1/LdSegFresh.lean) Wide
facts: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean); `Zk`, `After`: Cb/Req1/LdReq.lean.
Each under the hypotheses of its statement: Cb/Req1/LdReqRefZk.lean reduces `r.Zk` of the reference
request to: each reference segment's `Zk` at the facts that are fresh where it begins; the last
segment's body's; the final batching's fact. Cb/Req1/LdSegRefAllZk.lean states (the proof is in
Cb/Req1/LdSegRefAllZkProofs.lean) the `Zk` of a closed body from places and from facts in "base";
Cb/Req1/LdSegWholeZk.lean: the closing of a segment with one group asks nothing, beside its
hypotheses; Cb/Req1/LdSegCarryTen.lean: the final batching's fact follows from the wide fact of its
own masks. Here they are put together.

Main names:
  `A.ZkAt pp X`: for a closed body A and a set X of facts at its entry: `Nonempty I.C.E0.Str`, and
    there are letters (the wide reading W, the front's letters F, how the core reads the ghost κ,
    what the digits' lookup reads RdL) with: the core is the ghost; the front's conditions, among
    them on places, on numbers and on the claim Cc (`F.OK pp`); the front's blocks' facts are in X
    and quiet for what runs before; the conditions on the two late blocks (places; their wide facts
    are in X, quiet for the front; the two senders do not look).
  `L.ZkP pp base`: for the list: each segment's `A.ZkAt` at the facts that are fresh behind the
    segments before it and its entry step.
  In the three statements pp is the characteristic of E (`[CharP E pp]`).
  `Spec.ldReqRefZkP_body`: see its statement.
  `Spec.ldReqRefZkP_segs`: `L.OK pp → L.ZkP pp base → L.Zk base`.
  `Spec.ldReqRefZkP`: `r.Zk` from: `L.OK pp`, `T.OK pp`, the final batching's conditions
    (2 ≤ degree, evader, `Tie`, places); `L.ZkP` at the facts that are fresh behind the first
    sendings; `T.A.ZkAt` behind the segments and the last entry step; the wide fact of the final
    batching's own masks is fresh behind the last segment, in a reading that holds what the batching
    reads.

Limits: what is left, in words: places; "quiet" clauses; senders that do not look; and facts on
freshness at the entry of each segment, which are the matter of the sendings before it and of what
crosses a closing (Cb/Req1/LdSegSendFresh.lean, Cb/Req1/LdSegCarryClose.lean,
Cb/Req1/LdSegRefTenLook.lean: `ldSegRefX_out`): not chained from segment to segment here. (not all
hypotheses are named here: see `Spec.ldReqRefZkP`)
Terms: lean/GLOSSARY.md: reference request, segment, body, closing, sending, final batching, group,
core.
-/
import Cb.Req1.LdReqRefZk
import Cb.Req1.LdSegRefAllZkProofs
import Cb.Req1.LdSegCarryTen
import Cb.Req1.LdSegWholeZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- What zero knowledge asks of a closed body, at the facts X that are fresh at its entry, beside
its hypotheses. -/
def LdRefD.ZkAt {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)
    (pp : ℕ) (X : MaskFact A.V.Fp.s0.J.W → Prop) : Prop :=
  Nonempty I.C.E0.Str ∧
  ∃ (W : LdRefW A) (F : LdRefF A) (κ : A.Gh → Kc) (RdL : A.Xa.Q.T.Ent → Prop),
    A.Ghost κ ∧ F.OK pp ∧ A.FrontFacts F X ∧ A.Late W F RdL X

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

def ZkP (pp : ℕ) (base : MaskFact a.J.W → Prop) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.ZkP pp base ∧ S.A.ZkAt pp (S.entry.After (L.segs.After base))

end LdRefL

namespace Spec

def ldReqRefZkP_body : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
      (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh))))
      (X : MaskFact A.V.Fp.s0.J.W → Prop),
    A.OK pp → A.ZkAt pp X → (A.body St₁ fz Az).Zk X

def ldReqRefZkP_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (base : MaskFact a.J.W → Prop),
    L.OK pp → L.ZkP pp base → L.Zk base

/-- What zero knowledge asks of the reference request, beside its hypotheses. -/
def ldReqRefZkP : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    L.OK pp → T.OK pp → 2 ≤ R.n → R.Z.OK → R.Tie → R.X.Own → (∀ n, R.Rd n → Rd n) →
    L.ZkP pp (ldReqRef R first a₁ more hm b L T).base₀ →
    T.A.ZkAt pp (T.entry.After (L.segs.After (ldReqRef R first a₁ more hm b L T).base₀)) →
    T.tail.After (L.segs.After (ldReqRef R first a₁ more hm b L T).base₀)
      (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M) →
    (ldReqRef R first a₁ more hm b L T).Zk

end Spec

theorem ldReqRefZkP_body : Spec.ldReqRefZkP_body := by
  intro E Kc _ _ pp _ I A St₁ fz Az X hA ⟨hne, W, F, κ, RdL, h1, h2, h3, h4⟩
  exact ldSegRefAll_zk E Kc pp I A W F κ RdL St₁ fz Az X hA h1 h2 h3 h4

theorem ldReqRefZkP_segs : Spec.ldReqRefZkP_segs := by
  intro E Kc _ _ pp _ I a b L base
  induction L with
  | nil => intro _ _; rw [LdRefL.Zk]; trivial
  | snoc L S ih =>
      intro hO hZ
      rw [LdRefL.OK] at hO
      rw [LdRefL.ZkP] at hZ
      rw [LdRefL.Zk]
      exact ⟨ih hO.1 hZ.1,
        ldSegWholeZk_one E Kc _ S.K.R.c1 _ S.K.kinds S.l S.Qc _
          (ldReqRefZkP_body E Kc pp _ S.A S.K.St₁ S.K.fz S.K.Az _ hO.2.body hZ.2)⟩

theorem ldReqRefZkP :
    Spec.ldReqRefZkP := fun F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T Rd Rr hL hT hn hZ hTie hO hRd zL zT zB =>
  ldReqRefK_req F E Kc pp R a first a₁ more hm b L T hT hn hZ hTie hO
    (ldReqRefZkP_segs E Kc pp _ _ _ L _ hL zL)
    (ldReqRefZkP_body E Kc pp _ T.A T.St₁ T.fz T.Az _ hT.body zT) (segTen_in R.X _ Rd Rr hO hRd zB)

end Cb
