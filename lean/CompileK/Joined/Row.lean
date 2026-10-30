-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/Row.lean: a file's verifier, built from three interactive oracle reductions in a
row.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


Compile/Joined/Types.lean has the rounds of a file with three hash chains (`Chains`) and its
verifier over all rounds (`Desc`). Here that verifier is not given but made from a description of
each chain, so that its decision is the three chains' decisions in a row, and so that it depends on
the oracles only where it reads, if each chain does.

The form is the library's own (Ior/Ior.lean). A chain is an interactive oracle reduction over its
rounds: it reads the implicit part of its statement and its prover's oracles at declared positions,
rejects or hands on an explicit part, and hands on a new implicit part whose symbols are computed
from declared positions. So a tree that a later chain opens though an earlier chain sent it is an
oracle of the earlier chain that is handed on in the implicit part. The library composes such
reductions, carries the later chain's reads back to the earlier chain's oracles, and proves that
locality is kept (Ior/SeqProofs.lean).

Main names:
  `Stage s Xi Ei Xo Eo`: the fields of `IOR` but for the shape, which is s; `Stage.ior`.
  `Stage.ofIOR`: any `IOR` as a stage over its own shape. `Stage.cons`: a round laid in front of a
    stage, a chain's first round; `Stage.cons_isLocal`: the stage stays local.
  `Stage.tail`: a stage without its first round; `Stage.front`: with another first round; both stay
    local (`Stage.tail_isLocal`, `Stage.front_isLocal`).
  `Row G Y E`: three stages over the three chains' rounds; `Row.ior`: the three in a row.
  `Row.IsLocal`: each stage is local: one law for each chain.
  `Row.desc pre`: the file's verifier: it decides on `pre x`; `Row.desc_proto`: at `id` its protocol
    is the library's `IOR.toInteractiveOracleProof` of the row.
  `Row.desc_isLocal`: it is local, if each stage is.

Limits: the three laws of `Row.IsLocal` are owed of the description. As in the library's `IOR`, the
positions that a stage reads are a function of the verifier messages alone, not of the instance or
of the plain parts, which `Desc.reads` would allow. Nothing here says that a real file's chains have
this form. Two fields of `Stage`, `blinded` and `tie`, are carried over from `IOR` as they are; no
statement here reads them. Nothing on soundness: see OnBytes/TypedOracleCompiler/Joined/OfLinks.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.SeqProofs
import Compile.Joined.Types

set_option autoImplicit false

noncomputable section

namespace CompileK.Joined
open Iop
open _root_.Compile.Joined (Chains Desc)

/-! ## One chain -/

/-- One chain's typed description over the rounds s: the fields of an interactive oracle reduction
(`IOR`, Ior/Ior.lean, where each field is explained) but for the shape. -/
structure Stage (s : Shape) (Xi : Type) (Ei : ExtSpec) (Xo : Type) (Eo : ExtSpec) where
  blinded : OPos s → Bool
  extReads : Rho s → Finset Ei.Pos
  reads : Rho s → Finset (OPos s)
  out : Xi → Ei.Str → Tr s → Option Xo
  imp : Ei.Str → Tr s → Eo.Str
  srcE : Rho s → Eo.Pos → Finset Ei.Pos
  srcO : Rho s → Eo.Pos → Finset (OPos s)
  tie : Rho s → OPos s → Finset Ei.Pos

/-- the chain as an interactive oracle reduction; its shape is s by unfolding -/
@[reducible] def Stage.ior {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec}
    (S : Stage s Xi Ei Xo Eo) : IOR Xi Ei Xo Eo where
  shape := s
  blinded := S.blinded
  extReads := S.extReads
  reads := S.reads
  out := S.out
  imp := S.imp
  srcE := S.srcE
  srcO := S.srcO
  tie := S.tie

/-- any interactive oracle reduction is a stage over its own shape -/
def Stage.ofIOR {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) :
    Stage R.shape Xi Ei Xo Eo where
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out := R.out
  imp := R.imp
  srcE := R.srcE
  srcO := R.srcO
  tie := R.tie

theorem Stage.ofIOR_ior {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) :
    (Stage.ofIOR R).ior = R := rfl

open Classical in
/-- A round r laid in front of a stage: a chain's first round. The stage reads no position of its
oracle; it rejects where the test ok fails on the instance and the round's plain part, and else does
what it did on the later rounds. bl: the value of the field `blinded` at the positions of r. -/
def Stage.cons {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (r : Round) (bl : r.Pos → Bool)
    (ok : Xi → r.Plain → Bool) (S : Stage s Xi Ei Xo Eo) : Stage (r :: s) Xi Ei Xo Eo where
  blinded := fun p => match p with
    | .inl q => bl q
    | .inr q => S.blinded q
  extReads := fun ρ => S.extReads ρ.2
  reads := fun ρ => (S.reads ρ.2).image Sum.inr
  out := fun x y τ => if ok x τ.1.2 then S.out x y τ.2.2 else none
  imp := fun y τ => S.imp y τ.2.2
  srcE := fun ρ q => S.srcE ρ.2 q
  srcO := fun ρ q => (S.srcO ρ.2 q).image Sum.inr
  tie := fun ρ p => match p with
    | .inl _ => ∅
    | .inr q => S.tie ρ.2 q

open Classical in
/-- a round in front keeps a stage local -/
theorem Stage.cons_isLocal {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (r : Round)
    (bl : r.Pos → Bool) (ok : Xi → r.Plain → Bool) {S : Stage s Xi Ei Xo Eo}
    (h : S.ior.IsLocal) : (S.cons r bl ok).ior.IsLocal where
  out := fun x y y' τ τ' hρ hp he hr => by
    have hρ2 : τ.2.2.rho = τ'.2.2.rho := congrArg Prod.snd hρ
    have hp1 : τ.1.2 = τ'.1.2 := congrArg Prod.fst hp
    have hp2 : τ.2.2.plains = τ'.2.2.plains := congrArg Prod.snd hp
    have ho : S.out x y τ.2.2 = S.out x y' τ'.2.2 :=
      h.out x y y' τ.2.2 τ'.2.2 hρ2 hp2 he fun p hm => hr (.inr p) (Finset.mem_image_of_mem _ hm)
    show (if ok x τ.1.2 then S.out x y τ.2.2 else none) =
      if ok x τ'.1.2 then S.out x y' τ'.2.2 else none
    rw [hp1, ho]
  imp := fun y y' τ τ' q hρ hp he hr =>
    h.imp y y' τ.2.2 τ'.2.2 q (congrArg Prod.snd hρ) (congrArg Prod.snd hp) he fun p hm =>
      hr (.inr p) (Finset.mem_image_of_mem _ hm)

/-- A stage without its first round r: that round is fed its fixed message and the verifier message
c₀. For a stage that does not look at its first round. -/
def Stage.tail {r : Round} {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (c₀ : r.Chal)
    (S : Stage (r :: s) Xi Ei Xo Eo) : Stage s Xi Ei Xo Eo where
  blinded := fun p => S.blinded (.inr p)
  extReads := fun ρ => S.extReads (c₀, ρ)
  reads := fun ρ => (S.reads (c₀, ρ)).preimage Sum.inr Sum.inr_injective.injOn
  out := fun x y τ => S.out x y ((r.dOrc, r.dPlain), c₀, τ)
  imp := fun y τ => S.imp y ((r.dOrc, r.dPlain), c₀, τ)
  srcE := fun ρ q => S.srcE (c₀, ρ) q
  srcO := fun ρ q => (S.srcO (c₀, ρ) q).preimage Sum.inr Sum.inr_injective.injOn
  tie := fun ρ p => S.tie (c₀, ρ) (.inr p)

/-- a stage without its first round stays local -/
theorem Stage.tail_isLocal {r : Round} {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (c₀ : r.Chal)
    {S : Stage (r :: s) Xi Ei Xo Eo} (h : S.ior.IsLocal) : (S.tail c₀).ior.IsLocal where
  out := fun x y y' τ τ' hρ hp he hr =>
    h.out x y y' ((r.dOrc, r.dPlain), c₀, τ) ((r.dOrc, r.dPlain), c₀, τ')
      (congrArg (Prod.mk c₀) hρ) (congrArg (Prod.mk r.dPlain) hp) he fun p hm =>
        match p, hm with
        | .inl _, _ => rfl
        | .inr q, hm => hr q (show q ∈ (S.reads (c₀, τ.rho)).preimage Sum.inr
            Sum.inr_injective.injOn from Finset.mem_preimage.2 hm)
  imp := fun y y' τ τ' q hρ hp he hr =>
    h.imp y y' ((r.dOrc, r.dPlain), c₀, τ) ((r.dOrc, r.dPlain), c₀, τ') q
      (congrArg (Prod.mk c₀) hρ) (congrArg (Prod.mk r.dPlain) hp) he fun p hm =>
        match p, hm with
        | .inl _, _ => rfl
        | .inr z, hm => hr z (show z ∈ (S.srcO (c₀, τ.rho) q).preimage Sum.inr
            Sum.inr_injective.injOn from Finset.mem_preimage.2 hm)

/-- A stage with another first round: r is cut off (`Stage.tail`) and r' laid in front
(`Stage.cons`). -/
def Stage.front {r : Round} {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (c₀ : r.Chal) (r' : Round)
    (bl : r'.Pos → Bool) (ok : Xi → r'.Plain → Bool) (S : Stage (r :: s) Xi Ei Xo Eo) :
    Stage (r' :: s) Xi Ei Xo Eo :=
  (S.tail c₀).cons r' bl ok

theorem Stage.front_isLocal {r : Round} {s : Shape} {Xi Xo : Type} {Ei Eo : ExtSpec} (c₀ : r.Chal)
    (r' : Round) (bl : r'.Pos → Bool) (ok : Xi → r'.Plain → Bool) {S : Stage (r :: s) Xi Ei Xo Eo}
    (h : S.ior.IsLocal) : (S.front c₀ r' bl ok).ior.IsLocal :=
  Stage.cons_isLocal r' bl ok (Stage.tail_isLocal c₀ h)

/-! ## Three chains in a row -/

/-- A file's typed description: three chains in a row over the rounds G, from statements with an
explicit part in Y and an implicit part in E to the trivial statement. -/
structure Row (G : Chains) (Y : Type) (E : ExtSpec) where
  /-- the explicit parts that the first chain hands on -/
  X₁ : Type
  /-- the implicit parts that the first chain hands on -/
  E₁ : ExtSpec
  /-- the explicit parts that the second chain hands on -/
  X₂ : Type
  /-- the implicit parts that the second chain hands on -/
  E₂ : ExtSpec
  S₁ : Stage G.c₁ Y E X₁ E₁
  S₂ : Stage G.c₂ X₁ E₁ X₂ E₂
  S₃ : Stage G.c₃ X₂ E₂ Unit extNone

namespace Row
variable {G : Chains} {Y : Type} {E : ExtSpec} (Rw : Row G Y E)

/-- the three chains in a row, as one reduction over all rounds of the file -/
def ior : IOR Y E Unit extNone := Rw.S₁.ior.seq (Rw.S₂.ior.seq Rw.S₃.ior)

/-- **Owed of the description**: each chain's output and what it hands on depend on the oracles only
at the positions that it declares. -/
structure IsLocal : Prop where
  loc₁ : Rw.S₁.ior.IsLocal
  loc₂ : Rw.S₂.ior.IsLocal
  loc₃ : Rw.S₃.ior.IsLocal

theorem ior_isLocal (h : Rw.IsLocal) : Rw.ior.IsLocal := h.loc₁.seq (h.loc₂.seq h.loc₃)

/-- The file's verifier, made from the row: it reads what the row reads, and accepts where the row
does not reject, on the instance `pre x`. -/
def desc (pre : Y → Y) : Desc G Y E where
  blinded := Rw.ior.blinded
  extReads := fun _ ρ => Rw.ior.extReads ρ
  reads := fun _ ρ _ => Rw.ior.reads ρ
  accept := fun x y τ => (Rw.ior.out (pre x) y τ).isSome

/-- at `id` the file's protocol is the row as a protocol, in the library's sense -/
theorem desc_proto : (Rw.desc id).proto = Rw.ior.toInteractiveOracleProof := rfl

/-- the file's decision depends on the oracles only where it reads, if each chain is local -/
theorem desc_isLocal (h : Rw.IsLocal) (pre : Y → Y) : (Rw.desc pre).proto.IsLocal :=
  fun x y y' τ τ' hρ hp he hr =>
    congrArg Option.isSome ((Rw.ior_isLocal h).out (pre x) y y' τ τ' hρ hp he hr)

end Row

end CompileK.Joined
