-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/AssembleCuts.lean: at a proof string that is assembled from three chains as read,
each part that the premises "cut by cut" speak of is one chain's own. Equations.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


OnBytes/TypedOracleCompiler/Joined/Assemble.lean makes the proof string of a file from what is read for each chain
(`ChainStr`, `FileW.assemble`). OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean lists what gives a yes of the
file's verifier, chain by chain (`Cuts`), in terms of parts of the proof string. Here these parts
are computed at an assembled string. So whoever builds the string by the one file and concludes by
the other has each premise said of one `ChainStr`.

Main names:
  `op₁_eq` ... `op₃_eq`: the cuts of the openings have two names: `op₁` (YesByCuts.lean) is
    `FileW.opens₁` (Assemble.lean), and so on.
  `assemble_op₁` ... `assemble_op₃`: at an assembled string they are the chains' own openings.
  `assemble_tr₁` ... `assemble_tr₃`: the transcript that the verifier builds for a chain's rounds
    is built from that chain's plain parts and openings.
  `assemble_run₁` ... `assemble_run₃`: each chain's run is `recomputeChain` at that chain's plain parts; the
    first is handed all roots, the second those of the second and third chain, the third its own,
    if the earlier chains have taken as many roots as were read for them.
  `assemble_plains`: the plain parts of the whole, on which it depends which positions are read.

Limits: equations alone. That a chain takes as many roots as were read for it is a hypothesis of
`assemble_run₂` and `assemble_run₃`.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.Assemble
import OnBytes.TypedOracleCompiler.Joined.YesByCuts

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

namespace FileW
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)

theorem op₁_eq (π : F.Prf) : op₁ F.D π = F.opens₁ π := rfl
theorem op₂_eq (π : F.Prf) : op₂ F.D π = F.opens₂ π := rfl
theorem op₃_eq (π : F.Prf) : op₃ F.D π = F.opens₃ π := rfl

variable (salt : Bits) (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂) (k₃ : ChainStr lam G.c₃)
  (ext : E.Pos → Option (Opening lam E.Sym)) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam))
  (rsalt : Bits)

theorem assemble_op₁ :
    op₁ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₁.opens :=
  F.assemble_opens₁ salt k₁ k₂ k₃ ext rtreq slot path rsalt

theorem assemble_op₂ :
    op₂ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₂.opens :=
  F.assemble_opens₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt

theorem assemble_op₃ :
    op₃ F.D (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) = k₃.opens :=
  F.assemble_opens₃ salt k₁ k₂ k₃ ext rtreq slot path rsalt

/-- the plain parts of the whole -/
theorem assemble_plains :
    (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt).plains =
      Plains.app (s := G.c₁) (t := G.c₂ ++ G.c₃) k₁.plains
        (Plains.app (s := G.c₂) (t := G.c₃) k₂.plains k₃.plains) := rfl

theorem assemble_tr₁ (a : Out lam G.c₁) :
    tr₁ F.D F.wq (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a =
      mkTr G.c₁ G.A₁ (wire₁ F.wq) a.2.1 k₁.plains a.1 k₁.opens := by
  have h1 := F.assemble_pls₁ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  have h2 := F.assemble_op₁ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  unfold pls₁ at h1
  unfold tr₁
  rw [h1, h2]

theorem assemble_tr₂ (b : Out lam G.c₂) :
    tr₂ F.D F.wq (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) b =
      mkTr G.c₂ G.A₂ (wire₂ F.wq) b.2.1 k₂.plains b.1 k₂.opens := by
  have h1 := F.assemble_pls₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  have h2 := F.assemble_op₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  unfold pls₂ at h1
  unfold tr₂
  rw [h1, h2]

theorem assemble_tr₃ (e : Out lam G.c₃) :
    tr₃ F.D F.wq (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) e =
      mkTr G.c₃ G.A₃ (wire₃ F.wq) e.2.1 k₃.plains e.1 k₃.opens := by
  have h1 := F.assemble_pls₃ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  have h2 := F.assemble_op₃ salt k₁ k₂ k₃ ext rtreq slot path rsalt
  unfold pls₃ at h1
  unfold tr₃
  rw [h1, h2]

variable (cms : List (Dig lam)) (x : Y)

/-- the first chain's run: its own plain parts; all roots -/
theorem assemble_run₁ :
    run₁ F.t F.D F.wq F.embP F.xin cms x (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) =
      recomputeChain F.t cms (F.xin x) salt rtreq G.c₁ G.A₁ (wire₁ F.wq) (emb₁ F.t F.embP) 0 .first
        (k₁.roots ++ (k₂.roots ++ k₃.roots)) k₁.plains := by
  unfold run₁
  rw [F.assemble_pls₁ salt k₁ k₂ k₃ ext rtreq slot path rsalt]
  rfl

/-- the second chain's run, if the first has taken as many roots as were read for it -/
theorem assemble_run₂ (a : Out lam G.c₁) (h : k₁.roots.length = RootsOfChain.count G.c₁ a.2.1) :
    run₂ F.t F.D F.wq F.embP F.xin cms x (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a =
      recomputeChain F.t cms (F.xin x) salt rtreq G.c₂ G.A₂ (wire₂ F.wq) (emb₂ F.t F.embP)
        (0 + G.c₁.length) a.2.2 (k₂.roots ++ k₃.roots) k₂.plains := by
  unfold run₂
  rw [F.assemble_pls₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt,
    F.assemble_drop₁ salt k₁ k₂ k₃ ext rtreq slot path rsalt h]
  rfl

/-- the third chain's run, if the first two have taken as many roots as were read for them -/
theorem assemble_run₃ (a : Out lam G.c₁) (b : Out lam G.c₂)
    (h : k₁.roots.length = RootsOfChain.count G.c₁ a.2.1) (h' : k₂.roots.length = RootsOfChain.count G.c₂ b.2.1) :
    run₃ F.t F.D F.wq F.embP F.xin cms x (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a
        b =
      recomputeChain F.t cms (F.xin x) salt rtreq G.c₃ G.A₃ (wire₃ F.wq) (emb₃ F.t F.embP)
        (0 + G.c₁.length + G.c₂.length) b.2.2 k₃.roots k₃.plains := by
  unfold run₃
  rw [F.assemble_pls₃ salt k₁ k₂ k₃ ext rtreq slot path rsalt,
    F.assemble_drop₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt h h']
  rfl

end FileW

end TypedOracleCompiler.Joined
