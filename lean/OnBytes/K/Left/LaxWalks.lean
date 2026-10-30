-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxWalks.lean: the field `walks` of `LaxDebts` (OnBytes/K/Left/Lax.lean), from a
written list of smaller facts: on the family of oracle functions, on what the format's reader said
of each opening, and on the description's forms and the chain's record of roots.

`LaxDebts.walks` asks for a way to hash a vertex, a way to write a leaf's body, two tables (which
tree has which form; which tree has which root) and six facts on them. Here the first two are
fixed: a vertex is the format's call 166 of a hash h under the configuration's digest, and a leaf's
body is `ownEnc` at the plan's salt (OnBytes/K/Left/LaxPagesOwn.lean, whose `own_emb` is one of the
six facts). The two tables stay letters.

Main names:
  `WalkParts D d₁ F c₀ c₁ o h Fm Rt`: the list, in three groups.
     On the family F and the hash h: `size`, `node`, `leafOwn`, `leafSto`.
     On what was read: `readOwn`, `readSto` (the format's reader of each opening said yes), `salts`,
       `colSto`.
     On the description and the record of roots: `forms`, `roots`, `formOf`, `rootOf`, `depthSto`,
       `rootSto`.
  `walks_of_parts`: the list gives `LaxDebts.walks`, to the letter. By `ownOkE_of_read` and
     `stoOkE_of_read` (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean).

Limits: no field of the list is shown here, nor that they can be met together. Values under one
family of oracle functions; nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Lax
import OnBytes.K.Left.LaxPagesOwn

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.EntryFill
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open _root_.Run (bytesToDig leafSalt)

variable {lg s : ℕ} (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (d₁ : Sd1 lg s)
  (F : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁)))

/-- What is owed for the walks of the openings in what was read (o), under the family F, at the
outer roots c₀, c₁. h: the format's hash as a function of number, two places, start and bytes; Fm:
"tree n of the chain has the form s"; Rt: "the chain's record has the root c for tree n". -/
structure WalkParts (c₀ c₁ : Dig 256) (o : _root_.Fmt.ChainOut)
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (Fm : ℕ → _root_.Fmt.Shape → Prop)
    (Rt : ℕ → Dig 256 → Prop) : Prop where
  /-- The hash: a call's value has the length of its number -/
  size : ∀ n t i st b, ByteArray.size (h n t i st b) = _root_.Fmt.dlen n
  /-- The family: its answer at a vertex is the format's call 166 under the configuration digest -/
  node : NodeLaw F fun l r => h 166 0 0 D.base.cfg (l ++ r)
  /-- The family: its answer at a typed leaf of an own tree that is opened is the format's leaf
  call, started with the run's value -/
  leafOwn : ∀ run, o.run = some run → ∀ op ∈ ownOps o, ∀ (x : Fin (2 ^ op.sh.a))
    (sym : Fin op.sh.W → UInt64) (salt : ByteArray), salt.size = D.base.plan.salt →
    (F TypedOracleCompiler.Compile.Batch.OracleName.leaf
        (⟨ownEnc D.base.plan.salt op.sh x sym, leafSalt run salt⟩ : LeafIn (Ls D d₁)) : Dig 256) =
      bytesToDig (leafAtH h op.sh run x.val (List.ofFn sym) salt)
  /-- The family: the same at a typed leaf of a stored table, started with the configuration's
  digest -/
  leafSto : ∀ op ∈ stoOps o, ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), x < 2 ^ op.sh.a →
    col.length = op.sh.W → salt.size = D.base.plan.salt →
    (F TypedOracleCompiler.Compile.Batch.OracleName.leaf
        (⟨(bodyS D.a D.base.plan.salt).embE (x, col), leafSalt D.base.cfg salt⟩ :
          LeafIn (Ls D d₁)) : Dig 256) =
      bytesToDig (leafAtH h op.sh D.base.cfg x col salt)
  /-- What was read: the format's reader said yes on each opening of an own tree -/
  readOwn : ∀ run, o.run = some run → ∀ op ∈ ownOps o, ReadAs h D.base.cfg run op
  /-- What was read: and on each opening of a stored table -/
  readSto : ∀ op ∈ stoOps o, ReadAs h D.base.cfg D.base.cfg op
  /-- What was read: every salt has the plan's length -/
  salts : ∀ op ∈ opsOf 1 o, ∀ sl ∈ op.out.salts, sl.size = D.base.plan.salt
  /-- What was read: a stored table's columns have the form's width -/
  colSto : ∀ op ∈ stoOps o, ∀ c ∈ op.out.cols, c.length = op.sh.W
  /-- The description: Fm holds of the rounds' trees, counted from 0 -/
  forms : FormsOn Fm 0 D.ds
  /-- The record of roots: Rt holds of the roots sent, counted from 0 -/
  roots : RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList)
  /-- The description and what was read: the form with an opening's own number is the opening's -/
  formOf : ∀ op ∈ ownOps o, ∀ n sh, Fm n sh → sh.tree = op.sh.tree → sh = op.sh
  /-- The record and what was read: the record's root for that tree is the root in which the
  opening's walk ended -/
  rootOf : ∀ op ∈ ownOps o, ∀ n sh c, Fm n sh → sh.tree = op.sh.tree → Rt n c →
    c = bytesToDig op.out.root
  /-- The description and what was read: a stored table has the description's depth -/
  depthSto : ∀ op ∈ stoOps o, op.sh.a = D.a
  /-- The outer roots and what was read: the outer root of an opening's table is the root in which
  its walk ended -/
  rootSto : ∀ op ∈ stoOps o, [c₀, c₁].getD (whichOf D op) default = bytesToDig op.out.root

/-- The list gives the field `walks` of `LaxDebts`. -/
theorem walks_of_parts {c₀ c₁ : Dig 256} {o : _root_.Fmt.ChainOut}
    {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray} {Fm : ℕ → _root_.Fmt.Shape → Prop}
    {Rt : ℕ → Dig 256 → Prop} (P : WalkParts D d₁ F c₀ c₁ o h Fm Rt) :
    ∃ (vert : ByteArray → ByteArray → ByteArray) (e1 : Enc1 (Body (Ls D d₁)))
      (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop),
    NodeLaw F vert ∧ (∀ q a, (ownES D hok).emb (.inr q) a = embLS D.C (liftT e1) D.ds q a) ∧
    FormsOn Fm 0 D.ds ∧
    (∀ run, o.run = some run → ∀ op ∈ ownOps o, OwnOkE F vert e1 run Fm Rt op) ∧
    (∀ op ∈ stoOps o,
      StoOkE F vert (bodyS D.a D.base.plan.salt).embE D.a D.base.cfg [c₀, c₁] D op) ∧
    RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList) :=
  ⟨fun l r => h 166 0 0 D.base.cfg (l ++ r), ownEnc D.base.plan.salt, Fm, Rt, P.node,
    own_emb D hok, P.forms,
    fun run hrun op hop => ownOkE_of_read P.size D.base.plan.salt (P.readOwn run hrun op hop)
      (P.formOf op hop) (P.rootOf op hop) (P.salts op (List.mem_of_mem_filter hop))
      (P.leafOwn run hrun op hop),
    fun op hop => stoOkE_of_read P.size D.base.plan.salt (P.readSto op hop) (P.depthSto op hop)
      (P.rootSto op hop) (P.colSto op hop) (P.salts op (List.mem_of_mem_filter hop))
      (P.leafSto op hop),
    P.roots⟩

end OnBytes.K.Left
