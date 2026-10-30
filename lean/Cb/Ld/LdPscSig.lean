-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscSig.lean: the zero-knowledge sumcheck for a polynomial summand between statements about
oracle messages (this file does not say zero knowledge: see Limits).

This file proves, under the hypotheses of its statements, completeness, and round-by-round knowledge
soundness on the statements with the condition "on" and for the relaxed relation of `S.over`, of the
sumcheck of Cb/Ld/LdPsc.lean where the entries that it speaks of are read off the messages of oracle
messages.
Definitions, statements and proofs: the block of Cb/Ld/LdPsc.lean in the bundle of
Cb/Ld/LdSigLift.lean, and lifted over a signature.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
S is a signature (Cb/Ld/LdSig.lean): a finite family of oracle messages, each with its code, its
sample and its radius. "msg" reads the entries m : J → E that the block's parameters name off the
tuple of messages of S (any function). A0 is any base joint on (state, further oracles, (messages,
further witness)): whatever else is claimed; it rides along.

The first three rows below are under `Y.VarsOK`, `Y.DegOK` and `Y.ValInj`, the last two under
`T.VarsOK`, `T.DegX`, `T.DegY` and `T.ValInj`.
Main names:
  `Spec.psc_goodAt`: at the base the block has the bundle `GoodAt` (Cb/Ld/LdSigLift.lean).
    `Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
    value of one type M with a further witness, the clauses of `GoodB` with two differences: a
    further clause `same` asks that, on every run, the honest prover's output witness carries the
    M-part of its input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for
    each fixed m of type M, round-by-round knowledge soundness (`Know`) on the input joint's set of
    statements and at the numbers' list of errors, as `GoodB`'s does, but between the relaxed
    relations at (m, ·) and with the extractor `ext m`. Its clauses here: strings (`point`); local
    (`isLocal`); perfectly complete (`acc`); the condition handed on (`onOut`); the messages kept
    (`same`); nothing withheld, in this sense: `pBad` = 0, `pHid` = 0, every `cov k` empty
    (`Y.nums`); and knowledge sound for each fixed tuple of messages, with the errors 1, the
    degrees, 0 (as counts of challenges, as in Cb/Ld/LdPsc.lean, "Numbers": 1 of |E|; n_j of the
    j-th challenge set; 0) and the identity as extractor.
  `Spec.psc_goodB_sig`: over S: `(Y.psc E₀).keep S.Smp S.ext` leads from `S.over` (sum claim and A0)
    to `S.over` (output rows and A0): relation = the words are the encodings, the samples are met,
    the claims hold; relaxation = the messages are the decoding with the sample, and the claims hold
    of them. All of `GoodT` but zero knowledge (`IOR.GoodB`). `GoodB` is `IOR.GoodT` without its
    clause on zero knowledge. `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is
    asked of one reduction, with its honest side, between two joints, at given numbers; among its
    clauses: completeness between the honest relations, outside sets of verifier randomness whose
    probabilities further clauses bound by the numbers; round-by-round knowledge soundness (`Know`)
    between the relaxed relations, on the input joint's set of statements, with a given extractor,
    at the numbers' list of errors; and one on honest-verifier zero knowledge.
  `Spec.psc_core_goodAt`, `Spec.psc_core_goodB_sig`: the same for `Y.core` alone (round 0 and the
    rounds of the variables; the whole block where no map is revealed), to the end claim
    (`Y.baseMid`), with the errors 1, the degrees (as counts, as above).
  `Spec.psc_our_goodB_sig`: the instance with the dummy variable, from the conditions on the
    instance; its input joint has the sum of the masked summand in k + 1 variables.
  `Spec.psc_our_goodB_true`: the same, from the true sum claim in k variables, without inner masks
    (`PscOur.baseIn`): what a caller hands over.

The order of the coefficient ε, the verifier's message of round 0 (Cb/Ld/LdPsc.lean): in `S.over`
the samples of all oracle messages of S, those that hold the block's masks among them, stand in the
carried part of the input statement: so the coefficient comes after them.
"Collision-free" stands in the field "on" of `S.over` and is carried; the proofs do not use it: the
decoder is a function of the statement on all statements.

Notation: `Y`: the parameters of the block (`PscPar E`); `T`: the parameters of the instance
(`PscOur E`); `Y.VarsOK`: φ(ψ) = 1 for every variable (`HVar.OK`, Cb/Ld/LdHide.lean); `Y.DegOK`: the
summand has the degrees of the variables; `Y.ValInj`: different challenges have different values;
`T.DegX`, `T.DegY`: the degrees of the summand, in the k variables and in the values of the revealed
maps; `Ex`, `E₀`: external oracles (`ExtSpec`); `Wp`: the type of the further witness; `Kc`: the
type into which a joint's `core` maps witnesses; `R.keep Z F`: R with a carried part (`IOR.keep`,
Ior/Frame.lean); `S.liftH`: the honest side over a signature. (`PscPar`, `PscOur`, `VarsOK`,
`DegOK`, `ValInj`, `DegX`, `DegY`: Cb/Ld/LdPsc.lean; `ExtSpec`: Iop/InteractiveOracleProof.lean; `IOR.Rels`:
Ior/Chain.lean; `Sig.liftH`: Cb/Ld/LdSigLift.lean.)

Limits: this file does not say zero knowledge (Cb/Ld/LdPscZk.lean: masked messages). It says nothing
on where masks lie, and nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPscProofsOur
import Cb.Ld.LdSigLiftProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace PscPar
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

/-- The numbers: the errors (as counts of challenges); nothing is withheld, in this sense:
`pBad` = 0, `pHid` = 0, every `cov k` empty; no oracle is sent, so every budget (`bud` is `True`).
-/
def nums (Ex : ExtSpec) (Kc : Type) : IOR.Nums Kc (Y.psc Ex) :=
  ⟨Y.err Ex, 0, 0, fun _ _ => True, fun _ => ∅⟩
def numsC (Ex : ExtSpec) (Kc : Type) : IOR.Nums Kc (Y.core Ex) :=
  ⟨Y.errC Ex, 0, 0, fun _ _ => True, fun _ => ∅⟩

end PscPar

/-- The input joint of the instance at the base: the true sum claim, in k variables; A0 rides along.
-/
def PscOur.baseIn {E : Type} [Field E] [Fintype E] (T : PscOur E) {Ex : ExtSpec}
    {Wt Kc : Type} (A0 : IOR.Rels Kc T.St Ex Wt) (msg : Wt → T.J → E) :
    IOR.Rels Kc (E × T.St) Ex Wt :=
  T.par.baseRels A0 msg Prod.snd T.SumHolds

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def psc_goodAt : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    GoodAt (Y.psc Ex) (Y.hon Ex fun w => msg w.1) (Y.baseIn A0 fun w => msg w.1)
      (Y.baseOut A0 fun w => msg w.1) (fun _ _ _ wp => wp) (Y.nums Ex Kc)
def psc_core_goodAt : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    GoodAt (Y.core Ex) (Y.honC Ex fun w => msg w.1) (Y.baseIn A0 fun w => msg w.1)
      (Y.baseMid A0 fun w => msg w.1) (fun _ _ _ wp => wp) (Y.numsC Ex Kc)

/-- The block over a signature. -/
def psc_goodB_sig : Prop :=
  ∀ (S : Sig E) (Y : PscPar E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc Y.St E₀ (S.Msg × Wp)) (msg : S.Msg → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    GoodB ((Y.psc E₀).keep S.Smp S.ext) (S.liftH (Y.hon E₀ fun w => msg w.1))
      (S.over (Y.baseIn A0 fun w => msg w.1)) (S.over (Y.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((Y.nums E₀ Kc).keep S.Smp S.ext)
def psc_core_goodB_sig : Prop :=
  ∀ (S : Sig E) (Y : PscPar E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc Y.St E₀ (S.Msg × Wp)) (msg : S.Msg → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    GoodB ((Y.core E₀).keep S.Smp S.ext) (S.liftH (Y.honC E₀ fun w => msg w.1))
      (S.over (Y.baseIn A0 fun w => msg w.1)) (S.over (Y.baseMid A0 fun w => msg w.1))
      (fun _ _ w => w) ((Y.numsC E₀ Kc).keep S.Smp S.ext)

/-- The instance with the dummy variable, over a signature. -/
def psc_our_goodB_sig : Prop :=
  ∀ (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E),
    T.VarsOK → T.DegX → T.DegY → T.ValInj →
    GoodB ((T.par.psc E₀).keep S.Smp S.ext) (S.liftH (T.par.hon E₀ fun w => msg w.1))
      (S.over (T.par.baseIn A0 fun w => msg w.1)) (S.over (T.par.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((T.par.nums E₀ Kc).keep S.Smp S.ext)

/-- The instance over a signature, from the true sum claim. -/
def psc_our_goodB_true : Prop :=
  ∀ (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E),
    T.VarsOK → T.DegX → T.DegY → T.ValInj →
    GoodB ((T.par.psc E₀).keep S.Smp S.ext) (S.liftH (T.par.hon E₀ fun w => msg w.1))
      (S.over (T.baseIn A0 fun w => msg w.1)) (S.over (T.par.baseOut A0 fun w => msg w.1))
      (fun _ _ w => w) ((T.par.nums E₀ Kc).keep S.Smp S.ext)

end Spec

section Proofs
variable (E : Type) [Field E] [Fintype E]

theorem psc_goodAt : Spec.psc_goodAt E := fun Y Ex M Wp Kc A0 msg hV hD hI =>
  { point := psc_point E Y Ex
    isLocal := psc_local E Y Ex
    acc := psc_acc_base E Y Ex (M × Wp) Kc A0 (fun w => msg w.1) hV hD
    onOut := psc_carry_base E Y Ex (M × Wp) Kc A0 (fun w => msg w.1)
    keeps := fun w x c ρ => congrArg A0.core (psc_keeps E Y Ex (M × Wp) (fun w => msg w.1) w x c ρ)
    prBad := by
      have h : (Y.hon Ex fun w : M × Wp => msg w.1).Bad = ∅ := by
        show Rho.cylFst _ ∅ ∪ Rho.cylSnd _ ∅ = ∅
        ext ρ
        simp [Rho.cylFst, Rho.cylSnd]
      rw [h]
      simp [prRho]
    cover := by
      rintro w x ρ (h | ⟨_, _, h⟩)
      · exact h
      · exact h
    prCov := fun _ => by simp [prRho, PscPar.nums]
    same := fun w x c ρ => congrArg Prod.fst (psc_keeps E Y Ex (M × Wp) (fun w => msg w.1) w x c ρ)
    know := psc_know_at E Y Ex M Wp Kc A0 msg hV hD hI }

theorem psc_core_goodAt : Spec.psc_core_goodAt E := fun Y Ex M Wp Kc A0 msg hV hD hI =>
  { point := ⟨(pRound0_point, pRounds_point Y.fmt)⟩
    isLocal := Y.core_local Ex
    acc := psc_core_acc_base E Y Ex (M × Wp) Kc A0 (fun w => msg w.1) hV hD
    onOut := (psc_copy_core E Y Ex hV hD hI).carry_base A0
    keeps := fun w x _ ρ =>
      congrArg (fun o : Y.Mid × (M × Wp) => A0.core o.2)
        (psc_run E Y Ex (M × Wp) (fun w => msg w.1) w x ρ).2.2.2
    prBad := by
      show prRho (∅ : Set (Rho (Y.core Ex).shape)) ≤ 0
      simp [prRho]
    cover := fun _ _ _ h => h
    prCov := fun _ => by simp [prRho, PscPar.numsC]
    same := fun w x _ ρ =>
      congrArg (fun o : Y.Mid × (M × Wp) => o.2.1)
        (psc_run E Y Ex (M × Wp) (fun w => msg w.1) w x ρ).2.2.2
    know := psc_core_know_at E Y Ex M Wp Kc A0 msg hV hD hI }

theorem psc_goodB_sig : Spec.psc_goodB_sig E := fun S Y E₀ Wp Kc A0 msg hV hD hI =>
  sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ (Y.psc E₀) _ _ _ _ _
    (psc_goodAt E Y E₀ S.Msg Wp Kc A0 msg hV hD hI)

theorem psc_core_goodB_sig : Spec.psc_core_goodB_sig E := fun S Y E₀ Wp Kc A0 msg hV hD hI =>
  sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ (Y.core E₀) _ _ _ _ _
    (psc_core_goodAt E Y E₀ S.Msg Wp Kc A0 msg hV hD hI)

theorem psc_our_goodB_sig : Spec.psc_our_goodB_sig E := fun S T E₀ Wp Kc A0 msg hV hX hY hI =>
  psc_goodB_sig E S T.par E₀ Wp Kc A0 msg ((psc_our_ok E T).1 hV)
    (psc_our_deg E T hX hY) ((psc_our_ok E T).2 hI)

theorem psc_our_goodB_true : Spec.psc_our_goodB_true E := fun S T E₀ Wp Kc A0 msg hV hX hY hI => by
  have e : T.SumHolds = T.par.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m).symm
  unfold PscOur.baseIn
  rw [e]
  exact psc_our_goodB_sig E S T E₀ Wp Kc A0 msg hV hX hY hI

end Proofs
end Cb
