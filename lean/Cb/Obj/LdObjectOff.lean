-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOff.lean: the two sub-protocols that are run on one encoding of the index: a
reduction that tests that the word encodes an index, and the test for linear constraints after it;
under the hypotheses of the statements, any reductions with the properties `WfT.OK`, `LinT.OK` have
what the holographic IOP requires of them.

Definitions, statements (in `Cb.Spec`) and proofs.
The offline phase is the preamble of weights-formedness, then the test for linear constraints at one
instance (`SubsR.offline`, Hiop/RecBuild.lean).
The test for linear constraints (in Hiop: the IOPP for the constraint relation) is a reduction from
the constraint relation (`ConfigurationWithOutOfDomainSample.Left.Rlin`, Hiop/RecConf.lean) to the trivial statement.
For "joint" and "tail" see the head of Cb/Obj/LdObjectLink.lean.
This file is the analogue of Cb/Obj/LdObjectReq.lean (the preamble of a request) for the two
sub-protocols of the offline phase. `O : LdOL` (Cb/Obj/LdObjectLin.lean) fixes what the preamble
leaves (`O.left`) and the first joint of the test (`O.P.j0 O.on0`).

Main names:
  `ldWfRels C core`: the first joint of weights-formedness. Its explicit part is the record, its
    oracle the encoded index, its witness the prover encoded index. Exact: `C.Rwf`; relaxed:
    `C.RwfR` (no witness is read); condition: no collision at the record's seed.
  `O.WfT Kc`, `T.OK`: any term from that joint to the oracle messages `O.S` over any last base joint
    `T.B` (the joint `(O.S.over T.B).cf`; `Sig.over`, Cb/Ld/LdSig.lean; further witness `T.Wp`, in
    which the prover encoded index is: `T.pi`): its bundle `GoodT`, its formats (`prefx`, `passes`,
    `hands`), and the three facts that tie `T.B` to `O.holds`: its exact relation gives "the index
    is the encoding of the prover encoded index, the record is that index's own and has its
    message's answers (`ConfigurationWithOutOfDomainSample.Enc`), and `O.holds`"; `O.holds` of the decoded index (the message to
    which the encoded index decodes with its record, `dcd`; it need not hold an index) gives its
    relaxed relation at a fixed further witness `T.z0`; its condition gives "no collision".
  `Spec.ldOW_object`: from `T.OK core`: `PreListR` ∧ `PreKnowR` (nothing is extracted)
    (Hiop/RecSubs.lean).
  `O.LinT`, `T.OK`: any tail of a chain from `O.P.j0 O.on0` to the trivial statement, within a bound
    `T.qi` that allows at most t positions of the encoded index.
  `Spec.ldOT_object`: from `T.OK`, `HasDist O.Cf.C₀.G O.Cf.C₀.d` (Blocks/Decode.lean) and `O.Cf.eM`
    < `O.Cf.C₀.d`: `LinListR` ∧ `LinKnowR` (by `Cb.ldObj_lin`, Cb/Obj/LdObjectTail.lean, with three
    of the four bridging facts of Cb/Obj/LdObjectLin.lean: `ldOL_rel`, `ldOL_on`, `ldOL_relR`;
    the fourth is the field `reads` of `T.OK`).
  `Spec.ldOW_fit`: the line "the preamble's budget bears what the test reads of the oracles left":
    from "the preamble's term bears what follows" at the tail's bound, if that bound is closed under
    subsets and the tail has `T'.OK`.

Limits: no term is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReq
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The first joint of weights-formedness. -/
def ldWfRels (C : ConfigurationWithOutOfDomainSample) {Kc : Type} (core : C.PIdx → Kc) : Rels Kc C.Rec C.E0 C.PIdx where
  rel  := C.Rwf
  relR := fun a _ => C.RwfR a ()
  on   := C.free
  core := core

namespace LdOL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)

/-- Any term for the preamble of weights-formedness: the data. -/
structure WfT (Kc : Type) where
  /-- the further witness at the end, where the prover encoded index is in it, a fixed value; the
  last base joint -/
  Wp  : Type
  pi  : Wp → O.Cf.conf.PIdx
  z0  : Wp
  B   : Rels Kc (O.Cl × O.Cf.conf.Rec) O.Cf.conf.E0 (O.S.Msg × Wp)
  F   : IOR O.Cf.conf.Rec O.Cf.conf.E0
    ((O.Cl × O.Cf.conf.Rec) × O.S.Smp) (O.Cf.conf.E0.prod O.S.ext)
  H   : F.Honest O.Cf.conf.PIdx (O.S.Wit × Wp)
  ext : O.Cf.conf.Rec × O.Cf.conf.E0.Str → Tr F.shape → O.S.Wit × Wp → O.Cf.conf.PIdx
  P   : Nums Kc F

namespace WfT
variable {O} {Kc : Type} (T : O.WfT Kc)

structure OK (core : O.Cf.conf.PIdx → Kc) : Prop where
  good   : GoodT T.F T.H (ldWfRels O.Cf.conf core) (O.S.over T.B).cf T.ext T.P
  prefx  : T.F.IdxPrefix
  passes : T.F.Passes id fun b => b.1.2
  hands  : T.H.Hands O.Cf.conf.Rwf id fun w => T.pi w.2
  relB   : ∀ x y w,
    T.B.rel x y w → O.Cf.conf.Enc x.2 y (T.pi w.2) ∧ O.holds x.1 x.2 (T.pi w.2).1.1 w.1
  relRB  : ∀ a m U,
    O.Cf.conf.dcd a.2 a.1.2 = some U → O.holds a.1.1 a.1.2 U m → T.B.relR a (m, T.z0)
  onB    : ∀ a, T.B.on a → ¬ O.Cf.conf.coll a.2 a.1.2.1

def wf : IOR O.Cf.conf.Rec O.Cf.conf.E0 (O.left.Xl × O.Cf.conf.Rec) O.left.El :=
  closeF T.F
def hWf : T.wf.Honest O.Cf.conf.PIdx (O.Cf.conf.PIdx × O.left.WAux) := closeH T.pi T.H
def nums : PreNums T.wf := closeN T.P

end WfT

/-- Any tail for the test at one instance: the data. -/
structure LinT where
  Q   : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone
  H   : Q.Honest O.P.W0 Unit
  ext : (O.left.Xl × O.Cf.conf.Rec) × O.left.El.Str → Tr Q.shape → Unit → O.P.W0
  N   : Nums Unit Q
  /-- the bound on what it needs of (index, oracles left) -/
  qi  : Finset O.left.El.Pos → Prop

namespace LinT
variable {O} (T : O.LinT)

open Classical in
structure OK : Prop where
  tail  : TailTr T.Q T.H (O.P.j0 O.on0) trivRels T.ext T.N T.qi
  reads : ∀ U, T.qi U → (U.filter fun p => p.isLeft).card ≤ O.t

def hLin : T.Q.Honest (O.Cf.conf.PIdx × O.left.WAux) Unit :=
  Honest.mapW T.H O.fi fun _ u => u
def nums : LinNumsR T.Q.shape := ⟨T.N.err, T.N.pBad, O.t, fun _ T' => T' = ∅⟩

end LinT
end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E]

def ldOW_object : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (T : O.WfT Kc) (core : O.Cf.conf.PIdx → Kc), T.OK core →
    PreListR O.left T.wf T.hWf id id O.Cf.conf.Rwf T.nums ∧
    PreKnowR O.left T.wf O.Cf.conf.free O.Cf.conf.RwfR (fun _ _ _ => ()) T.nums.err

def ldOT_object : Prop :=
  ∀ (O : LdOL F E) (T : O.LinT) (d0 : O.left.AMsg), HasDist O.Cf.C₀.G O.Cf.C₀.d →
    O.Cf.eM < O.Cf.C₀.d → T.OK →
    LinListR O.left T.Q T.hLin T.nums ∧ LinKnowR O.left T.Q d0 T.nums.err

open Classical in
def ldOW_fit : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (T : O.WfT Kc) (T' : O.LinT) (qa : Finset O.Cf.conf.E0.Pos → Prop),
    T.F.Bears T.P.bud qa T'.qi → (∀ U V, V ⊆ U → T'.qi U → T'.qi V) → T'.OK →
    ∀ ρ₁ ρ₂, T.nums.bud ρ₁ ((T'.Q.extReads ρ₂).biUnion (T.wf.srcO ρ₁))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E]


-- Limit: no theorem of this library states the hypothesis `T.OK core` at a concrete instance.

theorem ldOW_object : Spec.ldOW_object F E := by
  intro O Kc T core h
  exact ldClose E O.Cf.conf O.S Kc _ _ Unit O.Cl T.Wp O.holds T.F T.H
    (ldWfRels O.Cf.conf core) T.B T.ext T.P id id T.pi O.Cf.conf.RwfR (fun _ => ()) T.z0
    (fun _ _ => 0) h.good h.prefx h.passes h.hands h.relB h.relRB h.onB (fun _ _ _ hR => hR)

theorem ldOT_object : Spec.ldOT_object F E := fun O T d0 hd he h =>
  ldObj_lin O.Cf.conf O.left O.P.W0 T.Q T.H (O.P.j0 O.on0) T.ext T.N T.qi O.t O.fi
    (fun w => O.S.msgs w.2) d0 h.tail (ldOL_rel F E O) (fun a => (ldOL_on F E O a).1)
    (fun a w _ => ldOL_relR F E O hd he a w) h.reads

open Classical in
theorem ldOW_fit : Spec.ldOW_fit F E := by
  intro O Kc T T' qa hB hsub hT ρ₁ ρ₂
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ hT.tail
  have h := (hB ρ₁ _ (hsub _ _ (h9 ρ₂).2 (h9 ρ₂).1)).1
  have e : (T'.Q.extReads ρ₂).biUnion (T.wf.srcO ρ₁) = (T'.Q.extReads ρ₂).biUnion (T.F.srcO ρ₁) :=
    Finset.biUnion_congr rfl fun q _ => post_id_srcO T.F _ ρ₁ q
  show T.P.bud ρ₁ _
  rw [e]
  exact h

end
end Cb
