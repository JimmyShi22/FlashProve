-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/WordCodings.lean: the word under a root, read off a log of strings, is the
same at two codings of the typed oracles that agree on the leaf and node oracles.

Why. The theorems on an arm of the verifier over one hash function (LinkAnsMaker.lean,
LinkAnsTwoStage.lean) hold for every coding m, and they speak of the word that the maker's log of
strings determines under a root: `extEnc W (singleTr m tr) cm`. Each file's arm can have a coding of
its own, so that nothing is asked of how one file's chains' labels stand to another's (the labels:
OnBytes/Params/Chains.lean). To join what the arms say, their words must be the same words.

Main names:
  `SameTrees W m m'`: the two codings write each leaf query and each node query as the same string,
    and read a block as the same answer of these two oracles.
  `singleTr_tree`: then the leaf and node entries that are read off a log of strings are the same.
  `extEnc_codings`: then the word under a root is the same.

Limits: nothing is said of how the codings treat the other oracles. No coding is given here. The
clauses of `SameTrees` are said of every query. So three codings that meet it pairwise are one code
on all leaf queries and all node queries: a file's coding is free at the Fiat-Shamir and other
oracles alone, and must write the other files' own trees' leaves as their codings do. That one code
of leaves and nodes spells the leaf and node calls of all three files and of the stored tables as
the programs do is not shown. All is said at one wiring W, so at one number of blocks: the arms that
are joined must stand at that W too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))

/-- Two codings agree on the leaf and node oracles: a query is written as the same string, and a
block is read as the same answer. -/
structure SameTrees (m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) : Prop where
  leaf : ∀ q j j', m.code OracleName.leaf q j = m'.code OracleName.leaf q j'
  node : ∀ q j j', m.code OracleName.node q j = m'.code OracleName.node q j'
  ansLeaf : ∀ r : Fin lam → Bool,
    (m.rng OracleName.leaf).symm (fun _ => r) = (m'.rng OracleName.leaf).symm fun _ => r
  ansNode : ∀ r : Fin lam → Bool,
    (m.rng OracleName.node).symm (fun _ => r) = (m'.rng OracleName.node).symm fun _ => r

variable {W}

/-- Agreement is symmetric. -/
theorem SameTrees.symm {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (h : SameTrees W m m') : SameTrees W m' m :=
  ⟨fun q j j' => (h.leaf q j' j).symm, fun q j j' => (h.node q j' j).symm,
    fun r => (h.ansLeaf r).symm, fun r => (h.ansNode r).symm⟩

/-- A string that the first coding reads as a leaf query, the second reads as that leaf query. -/
theorem SameTrees.dec_leaf (hlam : 0 < lam)
    {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam} (h : SameTrees W m m') {s : List Bool}
    {q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom OracleName.leaf} {j : Fin (m.blocks OracleName.leaf)}
    (hx : m.dec s = ⟨OracleName.leaf, q, j⟩) : ∃ j', m'.dec s = ⟨OracleName.leaf, q, j'⟩ := by
  have hs : m.code OracleName.leaf q j = s := by
    have h1 := m.code_dec s
    rw [hx] at h1
    exact h1
  refine ⟨⟨0, by rw [blocks_leaf hlam m']; exact Nat.one_pos⟩, ?_⟩
  rw [← hs, h.leaf q j ⟨0, by rw [blocks_leaf hlam m']; exact Nat.one_pos⟩]
  exact m'.dec_code _ _ _

/-- The same for a node query. -/
theorem SameTrees.dec_node (hlam : 0 < lam)
    {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam} (h : SameTrees W m m') {s : List Bool}
    {q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom OracleName.node} {j : Fin (m.blocks OracleName.node)}
    (hx : m.dec s = ⟨OracleName.node, q, j⟩) : ∃ j', m'.dec s = ⟨OracleName.node, q, j'⟩ := by
  have hs : m.code OracleName.node q j = s := by
    have h1 := m.code_dec s
    rw [hx] at h1
    exact h1
  refine ⟨⟨0, by rw [blocks_node hlam m']; exact Nat.one_pos⟩, ?_⟩
  rw [← hs, h.node q j ⟨0, by rw [blocks_node hlam m']; exact Nat.one_pos⟩]
  exact m'.dec_code _ _ _

/-- What `singleTr` makes of one entry of a log of strings, if it is a leaf or node entry. -/
def treeOf (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (e : QA (rom lam)) :
    Option (QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :=
  (if m.blocks (m.dec e.2.1).1 = 1 then
      some ⟨(m.dec e.2.1).1, (m.dec e.2.1).2.1, (m.rng (m.dec e.2.1).1).symm fun _ => e.2.2⟩
    else none).filter (isTree W)

/-- The leaf and node entries of `singleTr`, entry by entry. -/
theorem filter_singleTr (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (tr : Trace (rom lam)) : (singleTr m tr).filter (isTree W) = tr.filterMap (treeOf m) := by
  unfold singleTr treeOf
  rw [List.filter_filterMap]

/-- `treeOf` at an entry whose string encodes the point p. -/
theorem treeOf_dec (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (e : QA (rom lam))
    (p : m.Pt) (hd : m.dec e.2.1 = p) :
    treeOf m e = (if m.blocks p.1 = 1 then
        some ⟨p.1, p.2.1, (m.rng p.1).symm fun _ => e.2.2⟩
      else none).filter (isTree W) := by
  subst hd
  rfl

/-- An entry at another oracle is dropped. -/
theorem filter_not_tree (y : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hy : isTree W y = false) :
    (some y).filter (isTree W) = none := by
  simp [Option.filter, hy]

/-- The first coding's leaf or node entry is the second's. -/
theorem treeOf_le (hlam : 0 < lam) {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (h : SameTrees W m m') (e : QA (rom lam)) (x : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (hx : treeOf m e = some x) : treeOf m' e = some x := by
  rcases hd : m.dec e.2.1 with ⟨o, q, j⟩
  rw [treeOf_dec m e _ hd] at hx
  cases o with
  | leaf =>
      obtain ⟨j', hd'⟩ := h.dec_leaf hlam hd
      rw [treeOf_dec m' e _ hd']
      rw [if_pos (blocks_leaf hlam m)] at hx
      rw [if_pos (blocks_leaf hlam m')]
      show (some ⟨OracleName.leaf, q, (m'.rng OracleName.leaf).symm fun _ => e.2.2⟩ :
        Option (QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))).filter (isTree W) = some x
      rw [← h.ansLeaf e.2.2]
      exact hx
  | node =>
      obtain ⟨j', hd'⟩ := h.dec_node hlam hd
      rw [treeOf_dec m' e _ hd']
      rw [if_pos (blocks_node hlam m)] at hx
      rw [if_pos (blocks_node hlam m')]
      show (some ⟨OracleName.node, q, (m'.rng OracleName.node).symm fun _ => e.2.2⟩ :
        Option (QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))).filter (isTree W) = some x
      rw [← h.ansNode e.2.2]
      exact hx
  | _ =>
      exfalso
      split_ifs at hx
      · rw [filter_not_tree _ rfl] at hx
        cases hx
      · cases hx

/-- The two codings make the same of an entry of a log of strings. -/
theorem treeOf_eq (hlam : 0 < lam) {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (h : SameTrees W m m') (e : QA (rom lam)) : treeOf m e = treeOf m' e := by
  cases h1 : treeOf m e with
  | some x => exact (treeOf_le hlam h e x h1).symm
  | none =>
      cases h2 : treeOf m' e with
      | none => rfl
      | some x => rw [treeOf_le hlam h.symm e x h2] at h1; cases h1

/-- The leaf and node entries that are read off a log of strings are the same at two codings that
agree on these two oracles. -/
theorem singleTr_tree (hlam : 0 < lam) {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (h : SameTrees W m m') (tr : Trace (rom lam)) :
    (singleTr m tr).filter (isTree W) = (singleTr m' tr).filter (isTree W) := by
  rw [filter_singleTr, filter_singleTr]
  exact congrArg (fun f => tr.filterMap f) (funext (treeOf_eq hlam h))

/-- The word under a root, read off a log of strings, is the same at two codings that agree on the
leaf and node oracles. -/
theorem extEnc_codings (hlam : 0 < lam) {m m' : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (h : SameTrees W m m') (tr : Trace (rom lam)) (cm : Dig lam) :
    extEnc W (singleTr m tr) cm = extEnc W (singleTr m' tr) cm :=
  extEnc_congr_tree (singleTr_tree hlam h tr) cm

end TypedOracleCompiler.Compile.Batch.Cms
