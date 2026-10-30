-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean: what is asked of the openings of a proof string, one record for
each chain's rounds and one for the external strings; and the laws of each chain's wire records.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.

"Yes, cut by cut" (`CutsAt`, OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) has twelve premises on the
openings that want no oracle: the strict format, that the forests are there, and that each check
fits, for each of the three chains and for the external strings. Each follows from conditions on
each position (OnBytes/TypedOracleCompiler/Joined/K/Openings.lean). Here these conditions are one record.

Main names:
  `Opened sMT s A W R rd f`: of the openings f at the rounds s, where rd says which positions are
    read and R holds the roots that the chain has taken: an opening stands only at a position that
    is read and whose tree has a root, with a salt of sMT bits (`only`); each position that is read
    has an opening (`all`); its path is as long as its tree is deep (`path`).
  `Opened.cuts`: then the strict format holds, the forests are there, and each check fits.
  `OpenedE`, `OpenedE.cuts`: the same for the external strings.
  `wire₁_okg` ... `wire₃_depthLe`: the laws of each chain's wire records, from those of the whole.

Limits: one direction only. Nothing on hashing.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Joined.K.Openings

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The openings at one chain's rounds -/

/-- What is asked of the openings f at the rounds s. -/
structure Opened (sMT : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (R : RootsOfChain lam s)
    (rd : OPos s → Bool) (f : (p : OPos s) → Option (Opening lam (OSym s p))) : Prop where
  /-- an opening stands only at a position that is read and whose tree has a root; its salt has
  sMT bits -/
  only : ∀ p op, f p = some op →
    rd p = true ∧ op.salt.length = sMT ∧ (treeOf s A W R p).isSome = true
  /-- each position that is read has an opening -/
  all : ∀ p, rd p = true → (f p).isSome = true
  /-- the path of an opening that is read is as long as its tree is deep -/
  path : ∀ p op d c, rd p = true → f p = some op → treeOf s A W R p = some (d, c) →
    op.path.length = d

/-- The strict format holds, the forests are there, and each check is well formed and within the
depth m. -/
theorem Opened.cuts {sMT m : ℕ} {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {R : RootsOfChain lam s}
    {rd : OPos s → Bool} {f : (p : OPos s) → Option (Opening lam (OSym s p))}
    (h : Opened sMT s A W R rd f) (hW : RoundsQueryLayout.OKG s A W) (hD : RoundsQueryLayout.DepthLe m s A W)
    (emb : (p : OPos s) → OSym s p → Body L) :
    strictSB sMT s A W R rd f = true ∧ ∃ Fs, forestsB s A W emb R rd f = some Fs ∧
      (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ m)) = true := by
  obtain ⟨Fs, hF⟩ := exists_forestsB s A W emb R rd f h.all
  exact ⟨strictSB_of sMT s A W hW R rd f h.only, Fs, hF, fit_of hW hD hF h.path⟩

/-- What is asked of the openings g of the external strings. -/
structure OpenedE (sMT m : ℕ) {E : ExtSpec} (we : WireE E) (rd : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) : Prop where
  only : ∀ p ∈ we.all, ∀ op, g p = some op → rd p = true ∧ op.salt.length = sMT
  all : ∀ p ∈ we.all, rd p = true → (g p).isSome = true
  path : ∀ p ∈ we.all, ∀ op, rd p = true → g p = some op → op.path.length = we.depth
  /-- each position's leaf number is one of its tree -/
  leaf : ∀ p, we.leaf p < 2 ^ we.depth
  /-- the trees over the external strings are within the depth -/
  depth : we.depth ≤ m

theorem OpenedE.cuts {sMT m : ℕ} {E : ExtSpec} {we : WireE E} {rd : E.Pos → Bool}
    {g : E.Pos → Option (Opening lam E.Sym)} (h : OpenedE sMT m we rd g) (emb : E.Sym → Body L)
    (cms : List (Dig lam)) :
    strictExt sMT we rd g = true ∧ ∃ Fe, forestExt we emb cms rd g = some Fe ∧
      (flatF Fe).all (fun c => c.wellFormed && decide (c.depth ≤ m)) = true := by
  obtain ⟨Fe, hF⟩ := exists_forestExt we emb cms rd g h.all
  exact ⟨strictExt_of we rd g sMT h.only, Fe, hF,
    fitExt_of we emb cms rd g hF h.depth h.leaf h.all h.path⟩

/-! ## The laws of each chain's wire records -/

section Wires
variable {G : Chains} {Y : Type} {E : ExtSpec} {D : Desc G Y E} {wq : ProtocolQueryLayout lam K D.batch}

theorem wire₁_okg (h : wq.OKG) : RoundsQueryLayout.OKG G.c₁ G.A₁ (wire₁ wq) :=
  ((WireSB.okg_iff (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃)
    wq.sh).1 h.sh).1

theorem wire₂_okg (h : wq.OKG) : RoundsQueryLayout.OKG G.c₂ G.A₂ (wire₂ wq) :=
  ((WireSB.okg_iff (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) _).1
    ((WireSB.okg_iff (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃)
      wq.sh).1 h.sh).2).1

theorem wire₃_okg (h : wq.OKG) : RoundsQueryLayout.OKG G.c₃ G.A₃ (wire₃ wq) :=
  ((WireSB.okg_iff (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) _).1
    ((WireSB.okg_iff (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃)
      wq.sh).1 h.sh).2).2

theorem wire₁_depthLe (h : wq.OKG) : RoundsQueryLayout.DepthLe wq.maxDepth G.c₁ G.A₁ (wire₁ wq) :=
  ((WireSB.depthLe_iff wq.maxDepth (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁)
    (B := RoundSplits.app G.A₂ G.A₃) wq.sh).1 h.depth).1

theorem wire₂_depthLe (h : wq.OKG) : RoundsQueryLayout.DepthLe wq.maxDepth G.c₂ G.A₂ (wire₂ wq) :=
  ((WireSB.depthLe_iff wq.maxDepth (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) _).1
    ((WireSB.depthLe_iff wq.maxDepth (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁)
      (B := RoundSplits.app G.A₂ G.A₃) wq.sh).1 h.depth).2).1

theorem wire₃_depthLe (h : wq.OKG) : RoundsQueryLayout.DepthLe wq.maxDepth G.c₃ G.A₃ (wire₃ wq) :=
  ((WireSB.depthLe_iff wq.maxDepth (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) _).1
    ((WireSB.depthLe_iff wq.maxDepth (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁)
      (B := RoundSplits.app G.A₂ G.A₃) wq.sh).1 h.depth).2).2

end Wires

end TypedOracleCompiler.Joined
