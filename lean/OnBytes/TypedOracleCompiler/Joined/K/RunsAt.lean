-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean: at a proof string that is assembled from three chains as read, the
three chains have values under fixed oracle functions, and no root is left over; and the decision of
a file that is made from three stages says yes if each stage does.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


"Yes, cut by cut" (`CutsAt`, OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) has 26 premises. Here are six
that want nothing of how typed queries are written as strings.

Main names:
  `Fits F k₁ k₂ k₃`: each component of each round has at most `maxRt` trees, and for each chain as
    many roots were read as its rounds have trees.
  `FileW.runs_at`: under `Fits` and the law of the joining round's kind: there are values a, b, e of
    the three chains (the premises `run₁`, `run₂`, `run₃`), the string holds no root beyond those
    that the chains take (`roots`), and the third chain ends with a slot value (`joined`).
  `Row.accept_app`: the premise `accept`, at a file whose verifier is made from three stages
    (`Row.desc`, CompileK/Joined/Row.lean): the decision at three transcripts in a row says yes if
    the first stage hands on a statement at the first, the second at the second on what the first
    handed on, and the third accepts at the third.

Limits: nothing on what the three values are. That the stages say yes at the transcripts that the
verifier builds is owed elsewhere.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.K.RunSome
import OnBytes.TypedOracleCompiler.Joined.AssembleCuts
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore
import OnBytes.TypedOracleCompiler.Joined.Joins
import CompileK.Joined.Row

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

section Runs
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)

/-- Each component of each round has at most `maxRt` trees, and for each chain as many roots were
read as its rounds have trees: in the first and the third chain those over the slot's components; in
the second those over both components of the joining round and over the shared components of the
later rounds. -/
structure Fits (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂) (k₃ : ChainStr lam G.c₃) :
    Prop where
  few₁ : FewJ G.c₁ G.A₁ (wire₁ F.wq)
  fewJ : (wire₂ F.wq).1.depthJ.length ≤ maxRt
  fewJ0 : (wire₂ F.wq).1.depth0.length ≤ maxRt
  few₂ : Few0 G.s₂ (RoundSplits.const (RAnn.ofShared .sh) G.s₂) (wire₂ F.wq).2
  few₃ : FewJ G.c₃ G.A₃ (wire₃ F.wq)
  len₁ : k₁.roots.length = sumJ G.c₁ G.A₁ (wire₁ F.wq)
  len₂ : k₂.roots.length = (wire₂ F.wq).1.depthJ.length +
    ((wire₂ F.wq).1.depth0.length +
      sum0 G.s₂ (RoundSplits.const (RAnn.ofShared .sh) G.s₂) (wire₂ F.wq).2)
  len₃ : k₃.roots.length = sumJ G.c₃ G.A₃ (wire₃ F.wq)

/-- **The three chains have values, no root is left over, and the third ends with a slot value.** -/
theorem FileW.runs_at (hG : G.Laws) (g : Fam (typedOracleFamily lam W.K L)) (salt : Bits)
    {k₁ : ChainStr lam G.c₁} {k₂ : ChainStr lam G.c₂} {k₃ : ChainStr lam G.c₃}
    (hk : Fits F k₁ k₂ k₃) (ext : E.Pos → Option (Opening lam E.Sym)) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (rsalt : Bits) (cms : List (Dig lam)) (x : Y) :
    ∃ a b e c,
      (run₁ F.t F.D F.wq F.embP F.xin cms x
        (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt)).det g = some a ∧
      (run₂ F.t F.D F.wq F.embP F.xin cms x
        (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a).det g = some b ∧
      (run₃ F.t F.D F.wq F.embP F.xin cms x
        (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a b).det g = some e ∧
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt).roots.length ≤
        RootsOfChain.count G.c₁ a.2.1 + (RootsOfChain.count G.c₂ b.2.1 + RootsOfChain.count G.c₃ e.2.1) ∧
      e.2.2.slotVal = some c := by
  -- the first chain
  obtain ⟨a, ha, ca⟩ := det_chainB_lo g F.t cms (F.xin x) salt rtreq G.c₁ G.A₁ (wire₁ F.wq)
    (emb₁ F.t F.embP) 0 .first (k₁.roots ++ (k₂.roots ++ k₃.roots)) k₁.plains
    (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₁) hk.few₁
    (by rw [List.length_append, hk.len₁]; exact Nat.le_add_right _ _)
  have h₁ : (run₁ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt)).det g = some a := by
    rw [F.assemble_run₁]
    exact ha
  have n₁ : k₁.roots.length = RootsOfChain.count G.c₁ a.2.1 := hk.len₁.trans ca.symm
  obtain ⟨t₁, -, r₁⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₁
  obtain ⟨-, -, ρ₁, -, hρ⟩ := run₁_ends F.t F.D F.wq F.embP F.xin cms x _ r₁
  -- the second chain
  obtain ⟨b, hb, cb⟩ := det_chainB_join g F.t cms (F.xin x) salt rtreq G.aJ
    (RoundSplits.const (RAnn.ofShared .sh) G.s₂) (wire₂ F.wq).1 (wire₂ F.wq).2 (emb₂ F.t F.embP)
    (0 + G.c₁.length) ρ₁ (k₂.roots ++ k₃.roots) k₂.plains.1 k₂.plains.2 hG.kindJ
    (RoundSplits.allKind_const .sh _ (fun _ => rfl) G.s₂) hk.fewJ hk.fewJ0 hk.few₂
    (by rw [List.length_append, hk.len₂]; exact Nat.le_add_right _ _)
  have h₂ : (run₂ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a).det g = some b := by
    rw [F.assemble_run₂ salt k₁ k₂ k₃ ext rtreq slot path rsalt cms x a n₁, hρ]
    exact hb
  have n₂ : k₂.roots.length = RootsOfChain.count G.c₂ b.2.1 := hk.len₂.trans cb.symm
  -- the third chain
  obtain ⟨e, he, ce⟩ := det_chainB_lo g F.t cms (F.xin x) salt rtreq G.c₃ G.A₃ (wire₃ F.wq)
    (emb₃ F.t F.embP) (0 + G.c₁.length + G.c₂.length) b.2.2 k₃.roots k₃.plains
    (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.c₃) hk.few₃ (le_of_eq hk.len₃.symm)
  have h₃ : (run₃ F.t F.D F.wq F.embP F.xin cms x
      (F.assemble salt k₁ k₂ k₃ ext rtreq slot path rsalt) a b).det g = some e := by
    rw [F.assemble_run₃ salt k₁ k₂ k₃ ext rtreq slot path rsalt cms x a b n₁ n₂]
    exact he
  obtain ⟨c, hc⟩ := joined_at hG h₁ h₂ h₃
  exact ⟨a, b, e, c, h₁, h₂, h₃,
    roots_of_lengths (F.assemble_roots salt k₁ k₂ k₃ ext rtreq slot path rsalt) n₁ n₂
      (hk.len₃.trans ce.symm), hc⟩

end Runs

/-- **The decision, stage by stage.** At a file whose verifier is made from three stages, the
decision at three transcripts in a row says yes if no stage rejects, each on what the stage before
it has handed on. -/
theorem _root_.CompileK.Joined.Row.accept_app {G : Chains} {Y : Type} {E : ExtSpec}
    (Rw : CompileK.Joined.Row G Y E) (pre : Y → Y) (x : Y) (y : E.Str) (τ₁ : Tr G.c₁)
    (τ₂ : Tr G.c₂) (τ₃ : Tr G.c₃) {x₁ : Rw.X₁} {x₂ : Rw.X₂}
    (h₁ : Rw.S₁.out (pre x) y τ₁ = some x₁) (h₂ : Rw.S₂.out x₁ (Rw.S₁.imp y τ₁) τ₂ = some x₂)
    (h₃ : Rw.S₃.out x₂ (Rw.S₂.imp (Rw.S₁.imp y τ₁) τ₂) τ₃ = some ()) :
    (Rw.desc pre).accept x y
      (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) τ₁ (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃)) =
      true := by
  show (Option.bind (Rw.S₁.out (pre x) y (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃)
      (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) τ₁ (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃))))
    fun x₂' => (Rw.S₂.ior.seq Rw.S₃.ior).out x₂'
      (Rw.S₁.imp y (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃)
        (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) τ₁ (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃))))
      (Tr.snd (s := G.c₁) (t := G.c₂ ++ G.c₃)
        (Tr.app (s := G.c₁) (t := G.c₂ ++ G.c₃) τ₁
          (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃)))).isSome = true
  rw [Tr.fst_app, Tr.snd_app, h₁, Option.bind_some]
  show (Option.bind (Rw.S₂.out x₁ (Rw.S₁.imp y τ₁) (Tr.fst (s := G.c₂) (t := G.c₃)
      (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃)))
    fun x₃ => Rw.S₃.out x₃ (Rw.S₂.imp (Rw.S₁.imp y τ₁) (Tr.fst (s := G.c₂) (t := G.c₃)
      (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃)))
      (Tr.snd (s := G.c₂) (t := G.c₃) (Tr.app (s := G.c₂) (t := G.c₃) τ₂ τ₃))).isSome = true
  rw [Tr.fst_app, Tr.snd_app, h₂, Option.bind_some, h₃]
  rfl

end TypedOracleCompiler.Joined
