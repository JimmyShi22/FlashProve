-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/WireOf.lean: the wire record of a file with three joined hash chains, made of the
wire records of its parts, and its laws from theirs.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Main names:
  `Wires lam K G`      the wire records of the front, chain 1, the joining round, chain 2, the seam
                       and chain 3
  `Wires.sh`           the wire records of all rounds of the file, in a row
  `Wires.OKG`, `Wires.sh_okg`         each part is lawful; then the whole is
  `Wires.DepthLe`, `Wires.sh_depthLe`  no tree of a part is deeper than d; then none of the whole is
  `Wires.qb`, `Wires.qb_okg`          the wire record of the file's protocol, and its laws
  `FileW.coherent`     the annotation of a written file is coherent, under `G.Laws`

Limits: that the verifier of a file opens at most `nOpen` positions, and the laws of the wire record
of the external strings, are hypotheses of `Wires.qb_okg`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Wire
import OnBytes.TypedOracleCompiler.Joined.Cut
import Compile.Joined.Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- lawful wire records in a row -/
theorem WireSB.okg_app {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B} (hW : RoundsQueryLayout.OKG s A W) (hV : RoundsQueryLayout.OKG u B V) :
    RoundsQueryLayout.OKG (s ++ u) (RoundSplits.app A B) (WireSB.app W V) :=
  (WireSB.okg_iff _).2 ⟨by rw [WireSB.fst_app]; exact hW, by rw [WireSB.snd_app]; exact hV⟩

/-- no tree deeper than d, in a row -/
theorem WireSB.depthLe_app (d : ℕ) : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    {W : RoundsQueryLayout lam K s A} {V : RoundsQueryLayout lam K u B}, RoundsQueryLayout.DepthLe d s A W →
      RoundsQueryLayout.DepthLe d u B V → RoundsQueryLayout.DepthLe d (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, WireSB.depthLe_app d hW.2 hV⟩

/-- The wire records of the parts of a file over the rounds G. -/
structure Wires (lam K : ℕ) (G : Chains) where
  /-- the front's -/
  wF : WireRB lam K G.rF (RAnn.allLocal G.rF)
  /-- chain 1's -/
  W₁ : RoundsQueryLayout lam K G.s₁ (RoundSplits.allLocal G.s₁)
  /-- the joining round's -/
  wJ : WireRB lam K G.rJ G.aJ
  /-- chain 2's -/
  W₂ : RoundsQueryLayout lam K G.s₂ (RoundSplits.const (RAnn.ofShared .sh) G.s₂)
  /-- the seam's -/
  w3 : WireRB lam K G.r3 (RAnn.allLocal G.r3)
  /-- chain 3's -/
  W₃ : RoundsQueryLayout lam K G.s₃ (RoundSplits.allLocal G.s₃)

namespace Wires
variable {G : Chains} (V : Wires lam K G)

/-- the seam and chain 3 -/
def sh₃ : RoundsQueryLayout lam K G.sh₃ G.ann₃ := (V.w3, V.W₃)
/-- the joining round, chain 2, and what follows -/
def shJ : RoundsQueryLayout lam K G.shJ G.annJ := (V.wJ, WireSB.app V.W₂ V.sh₃)
/-- The wire records of all rounds of the file. -/
def sh : RoundsQueryLayout lam K G.sh G.ann := (V.wF, WireSB.app V.W₁ V.shJ)

/-- each part's wire records are lawful -/
structure OKG : Prop where
  wF : V.wF.OKG
  W₁ : RoundsQueryLayout.OKG _ _ V.W₁
  wJ : V.wJ.OKG
  W₂ : RoundsQueryLayout.OKG _ _ V.W₂
  w3 : V.w3.OKG
  W₃ : RoundsQueryLayout.OKG _ _ V.W₃

theorem sh_okg (h : V.OKG) : RoundsQueryLayout.OKG G.sh G.ann V.sh :=
  ⟨h.wF, WireSB.okg_app h.W₁ ⟨h.wJ, WireSB.okg_app h.W₂ ⟨h.w3, h.W₃⟩⟩⟩

/-- no tree of a part is deeper than d -/
structure DepthLe (d : ℕ) : Prop where
  wF : (∀ e ∈ V.wF.depth0, e ≤ d) ∧ ∀ e ∈ V.wF.depthJ, e ≤ d
  W₁ : RoundsQueryLayout.DepthLe d _ _ V.W₁
  wJ : (∀ e ∈ V.wJ.depth0, e ≤ d) ∧ ∀ e ∈ V.wJ.depthJ, e ≤ d
  W₂ : RoundsQueryLayout.DepthLe d _ _ V.W₂
  w3 : (∀ e ∈ V.w3.depth0, e ≤ d) ∧ ∀ e ∈ V.w3.depthJ, e ≤ d
  W₃ : RoundsQueryLayout.DepthLe d _ _ V.W₃

theorem sh_depthLe {d : ℕ} (h : V.DepthLe d) : RoundsQueryLayout.DepthLe d G.sh G.ann V.sh :=
  ⟨h.wF, WireSB.depthLe_app d h.W₁ ⟨h.wJ, WireSB.depthLe_app d h.W₂ ⟨h.w3, h.W₃⟩⟩⟩

variable {Y : Type} {E : ExtSpec}

/-- The wire record of the file's protocol: the rounds' wire records, that of the external strings,
and the two numbers that bound what is opened. -/
def qb (D : Desc G Y E) (ext : WireE E) (decO : DecidableEq (OPos G.sh)) (nOpen maxDepth : ℕ) :
    ProtocolQueryLayout lam K D.batch := ⟨V.sh, ext, decO, nOpen, maxDepth⟩

theorem qb_okg (D : Desc G Y E) (ext : WireE E) (decO : DecidableEq (OPos G.sh))
    (nOpen maxDepth : ℕ) (hV : V.OKG) (he : ext.OK)
    (ho : ∀ x ρ pl, (D.reads x ρ pl).card + (D.extReads x ρ).card ≤ nOpen)
    (hd : V.DepthLe maxDepth) : (V.qb D ext decO nOpen maxDepth).OKG :=
  ⟨V.sh_okg hV, he, ho, V.sh_depthLe hd⟩

end Wires

/-- The annotation of a written file is coherent, if the joining round's is. -/
theorem FileW.coherent {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec}
    (F : FileW W G Y E) (h : G.Laws) : F.written.Q.ann.Coherent := G.ann_coherent h

end TypedOracleCompiler.Joined
