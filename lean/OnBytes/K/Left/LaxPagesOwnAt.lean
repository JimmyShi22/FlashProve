-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxPagesOwnAt.lean: an opening of a tree of the chain's own that the format's reader
has read is in order at the family that runs: the twin of `famOf_stoOk`
(OnBytes/K/Left/LaxPages.lean) for the own trees.

Main names:
  `famOf_own`: the hypothesis `hleaf` of `ownOkE_of_read` (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean) at the
    family that runs, at the bodies `ownEnc` (OnBytes/K/Left/LaxPagesOwn.lean).
  `famOf_ownOk`: `OwnOkE` from `ReadAs`.
  `hOfG_oBits`: the reader's hash here, written out: the format's hash over the oracle on bytes that
    the realised oracle on bits induces (`ho_oBits`, OnBytes/K/Left/LaxChain.lean, ties that to the
    format's own oracle).

Limits: that the reader has read the opening (`ReadAs`), that the opening's shape is an own tree of
the description, the two facts on forms and roots (`hform`, `hroot`, in `ownOkE_of_read`'s own
letters), the salts' length and the run value's length are hypotheses. Nothing on any file, on
soundness or on any hash's strength.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxPages
import OnBytes.K.Left.LaxPagesOwn

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.RowsG (hOfG)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (d₁ : Sd1 lg s)
  (hD : D.base.cfg.size = 32) (sh : OnBytes.Params.IndexShape)

/-- The reader's hash of these files, written out. -/
theorem hOfG_oBits : hOfG oBits = _root_.Fmt.HO (oB (oBits ())) := rfl

/-- The law at the leaves of an own tree, at the family that runs. f: an own tree's shape. -/
theorem famOf_own (f : _root_.Fmt.Shape) (h1 : f.stored = false)
    (hp : _root_.Fmt.leafPlace f.tree f.W (D.base.plan.salt / 8) < 2 ^ 48)
    (ha : 2 ^ f.a + 2 ^ f.a ≤ 2 ^ 64) (run : ByteArray) (hrun : run.size = 32)
    (x : Fin (2 ^ f.a)) (sym : Fin f.W → UInt64) (salt : ByteArray)
    (hs : salt.size = D.base.plan.salt) :
    (EntryRunTop.famOf D hD d₁ sh TypedOracleCompiler.Compile.Batch.OracleName.leaf
        (⟨ownEnc D.base.plan.salt f x sym, leafSalt run salt⟩ : LeafIn (Ls D d₁)) : Dig 256) =
      bytesToDig (leafAtH (hOfG oBits) f run x.val (List.ofFn sym) salt) := by
  rw [famOf_atPage]
  exact own_leaf D d₁ (EntryRunTop.cfgOf D) hD (EntryRunTop.pdOf D) (EntryRunTop.restAt D sh)
    D.base.plan.salt (EntryRunTop.backOf D d₁) oBits f h1 hp ha run hrun x sym salt hs

/-- An opening of an own tree that the format's reader has read is in order at the family that
runs. d: a round of the description of which the opening's shape is a tree. -/
theorem famOf_ownOk (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) {run : ByteArray}
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} {op : OpAt}
    (R : ReadAs (hOfG oBits) D.base.cfg run op) (h1 : op.sh.stored = false)
    (d : TypedOracleCompiler.Run.PQ.RD)
    (hd : d ∈ D.ds) (ht : op.sh ∈ d.trees)
    (hform : ∀ n f, Fm n f → f.tree = op.sh.tree → f = op.sh)
    (hroot : ∀ n f c, Fm n f → f.tree = op.sh.tree → Rt n c → c = bytesToDig op.out.root)
    (hsalt : ∀ sl ∈ op.out.salts, sl.size = D.base.plan.salt) (hrun : run.size = 32) :
    OwnOkE (EntryRunTop.famOf D hD d₁ sh) (fun l r => hOfG oBits 166 0 0 D.base.cfg (l ++ r))
      (ownEnc D.base.plan.salt) run Fm Rt op :=
  ownOkE_of_read (size_hOfG oBits) D.base.plan.salt R hform hroot hsalt
    (fun x sym salt hs => famOf_own D d₁ hD sh op.sh h1 (own_bounds D hok d hd op.sh ht).1
      (own_bounds D hok d hd op.sh ht).2 run hrun x sym salt hs)

end OnBytes.K.Left
