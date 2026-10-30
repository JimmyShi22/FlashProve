-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean: AN HONEST COMMITTER FOR THE SCHEME WITH THE KEY
(ROOT, RECORD), AS A TERM, with what a query log holds in which it runs. AT LETTERS: any object with
records, any wire, any wire of the record. TIED TO NO PROGRAM. No prover. Nothing on completeness.

Why. The slot `commit` of an input of Johnson/Top/InnerCompiledVerifier.lean asks a program over the typed
oracles whose key is a root and a record. Some inputs lay a filler there, which binds nobody to
anything (among them Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean, and `lettersAtFullD` and `lettersAtSmallD`,
Johnson/Flat/Dec/TwoLettersAt.lean); `InnerCompilerInput.withCommitterOverTypedOracles` (Johnson/Top/BindsAtInnerSystem.lean) and
`InnerCompilerInput.withHonest` (Johnson/Prover/All/AtScheme.lean) lay the committer of this file; others
leave it a letter. Index binding wants a committer of which one can say: outside a rare event on the
hash function, the library's extractor, which decodes, with the key's record, the word that it reads
off the key's maker's log under the root, gives the committed index.

Main names (namespace `TypedOracleCompiler.Compile.Batch.Cms`). `committerLeafInput`, `committerLeafHashes`, `committerNodeHash` (the
verifier's own `hashTreeNode`), `committerTreeRoot`: the tree over a word: 2 ^ depth leaves, a symbol written as the
wire writes it (`embE`), a filling b₀ beyond the word's length, a salt a leaf; then the library's
levels (`levelsM`, Compile/MerkleM.lean). `committerAtFixedCoins`, `committerOverTypedOracles`: the committer behind its coins,
and with them: it draws the encoding's randomness and the salts, builds the tree over the encoded
index, asks the seed's two queries at the root (those of the verifier's `outOfDomainSeedIs`,
Johnson/TypedOracleCompiler/RecCompile/Seeds.lean), and gives the root with the honest record at that seed; the
prover's key holds the index, the randomness and the salts. `word_committerTreeRoot`: a typed log that holds a
run of the tree's builder, outside the Merkle hash event `EM`, spells the word: `extEnc` under the
root is the word. `Rom.runsIn_singleTr`: general, for any family of oracles and any coding: an
algorithm that asks one-block oracles alone: its run over one hash function, in a log of strings, is
a typed run in what `singleTr` reads off that log. `run_committerOverTypedOracles`: so for the committer over one
hash function at fixed coins: the tree's part is such a typed run, at the randomness and the salts
of the prover's key; the record is the honest one at some seed. `good_committerOverTypedOracles`: the heart: under
the wire's laws and hdec, outside `EM` on the three logs of the game of binding, and where the word
off the key's maker's log is the word off all three, the extractor gives the index that the run
again commits to.

How `word_committerTreeRoot` goes: the run puts every leaf's and every node's entry into the log
(`committerLeafHashes_log`, `committerTreeLevels_log`); so every leaf's path climbs to the root within the log
(`ClimbsIn`, `opensIn_of_climbsIn`, Compile/MerkleList.lean); outside the hash event what the
extractor finds under the root at that place is that leaf (`preimage_of_opensIn`,
Hash/MerklePure.lean); the wire reads the symbol back (`extEnc_apply`,
OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean). Of `QueryLayout.OKG` it spends `fits` and, through that lemma,
`prjE_emb` and `B.ext`.

Kin in the library, none of which says what stands here. `pairUp_log`, `levels_head`, `levels_log`,
`noCoin_pairUp`, `noCoin_levelsM` (OnBytes/K/Arm/TreeLog.lean) and `leavesM_log`, `word_of_commit`
(OnBytes/K/Arm/TreeCommit.lean): the same inductions for a tree's builder that asks strings of one
written coding at 256 bits; here the builder asks the typed oracles. `climbsIn_pathOf`
(Compile/Extraction.lean): for a node function that asks nothing. `withCoins_of_drawsNoCoin`
(ZKCP/WithCoinsBind.lean): `Rom.withCoins_noCoin` for the algorithms of ZKCP/Defs.lean. hdec is, to
the letter, the field `dec_enc` of `HolographicProtocol.WiredR` (Hiop/RecInterface.lean).

Limits.
- hdec, a premise of `good_committerOverTypedOracles`, says that the decoder gives every index back from its
  honest encoding and record. AT AN INDEX TYPE THAT HOLDS A MEMBER THAT THE DECODER NEVER GIVES IT
  IS FALSE: the statement is meant at a type of indices cut to those that the decoder can give.
- `singleTr` keeps the entries at one-block oracles alone. Where lam is not 0, leaves and nodes are
  one block under every coding (`blocks_leaf`, `blocks_node`,
  Johnson/TypedOracleCompiler/RecCompile/LinkAnsStay.lean). The seed's two queries go to an oracle whose answer has
  K + 1 blocks, so where K is not 0 they are not in it: nothing here says in a typed log how the
  seed was made; "some seed" in `run_committerOverTypedOracles` is any seed, and hdec is asked at every seed.
- The coins are two enumerations, letters of which no law is asked: nothing is said on how the
  randomness or the salts are distributed, NOR ON A SALT'S LENGTH. The verifiers of OnBytes/TypedOracleCompiler/
  refuse an opening whose salt has not exactly `p.sMT` bits (`strictExt`, Compile/Bcs.lean, through
  `proofHasStrictFormat`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), and no `Params` stands in this file. At an
  `sl` that gives a salt of another length at a place below the word's length, no opening of that
  place passes: there "honest" is a name alone. A statement that a verifier says yes, or on
  completeness, wants the premise that every salt of `sl` has `p.sMT` bits. Not claimed:
  anything on hiding.
- hM and he in `good_committerOverTypedOracles` are premises on logs; their price is paid elsewhere (its docstring).
- `RunsIn` asks membership alone: a log may hold several runs, with several roots; each statement
  holds of each. It has no rule for a sample: an algorithm that samples runs in no log.
- Two of the letters' types can be empty, and the statements on them then hold of nothing: the
  codings `OracleCoding …` (every string codes one point, so where `Bd` or the instances are uncountable
  there is none) and the wires of the record `OutOfDomainSampleQueryLayout …` (where the shape at its tag is empty: `pl0`).
- That a verifier says yes under a key of this committer is not shown.
- No program's committer, table, salt or commitment is spoken of.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsStay
import Compile.MerkleM
import Rom.WithCoins
import Rom.OverOneN
import Rom.SigmaExits
import Rom.AsksIn
import Rom.ExitBind
import Compile.MerkleList
import Compile.MerkleRom
import OnBytes.K.Arm.TreeWord

set_option autoImplicit false

noncomputable section

namespace Rom
open _root_.Compile

variable {lam : ℕ}

/-! ### General: from a log of strings to the typed log; coins -/

/-- Where the queries at n strings run in a log, the log holds each string's entry. -/
theorem askAll_runsIn {tr : Trace (rom lam)} :
    ∀ (n : ℕ) (g : Fin n → List Bool) (bs : Fin n → Fin lam → Bool),
      RunsIn tr (askAll lam n g) bs → ∀ j, (⟨(), g j, bs j⟩ : QA (rom lam)) ∈ tr
  | 0, _, _, _, j => j.elim0
  | n + 1, g, bs, h, j => by
    obtain ⟨r, hr, h⟩ := runsIn_query_iff.1 h
    obtain ⟨rest, hrest, h⟩ := (runsIn_bind_iff _ _ _).1 h
    obtain rfl := runsIn_pure_iff.1 h
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hr
    · exact askAll_runsIn n _ rest hrest j

/-- **An algorithm that asks one-block oracles alone: its run over one hash function, in a log of
strings, is a typed run in what `singleTr` reads off that log.** -/
theorem runsIn_singleTr {S : OSpec} {α : Type} (m : OracleCoding S lam) :
    ∀ (c : OComp S α), c.AsksIn (fun o _ => m.blocks o = 1) →
      ∀ {tr : Trace (rom lam)} {a : α}, RunsIn tr (c.overOne m) a → RunsIn (singleTr m tr) c a
  | .pure b, _, tr, a, h => by
    obtain rfl := runsIn_pure_iff.1 h
    exact RunsIn.pure _
  | .sample n k, _, tr, a, h => by cases h
  | .query o q k, hA, tr, a, h => by
    have h : RunsIn tr ((askAll lam (m.blocks o) (m.code o q)).bind fun bs =>
        (k ((m.rng o).symm bs)).overOne m) a := h
    obtain ⟨bs, hbs, h2⟩ := (runsIn_bind_iff _ _ _).1 h
    have hb : m.blocks o = 1 := hA.1
    have j₀ : Fin (m.blocks o) := ⟨0, by omega⟩
    have hc : (fun _ => bs j₀) = bs := by
      funext j
      have : j = j₀ := Fin.ext (by have := j.isLt; have := j₀.isLt; omega)
      rw [this]
    have hm := OnBytes.K.Arm.mem_singleTr m tr o q j₀ (bs j₀) hb (askAll_runsIn _ _ bs hbs j₀)
    rw [hc] at hm
    exact RunsIn.query o q k _ a hm (runsIn_singleTr m _ (hA.2 _) h2)

/-- An algorithm that samples nothing is itself, whatever number its coins are read off. -/
theorem withCoins_noCoin {S' : OSpec} {α : Type} :
    ∀ (c : OComp S' α) (coins : ℕ), c.NoCoin → c.withCoins coins = c
  | .pure _, _, _ => rfl
  | .query o q k, coins, h => congrArg (OComp.query o q)
      (funext fun r => withCoins_noCoin (k r) coins (h r))
  | .sample _ _, _, h => h.elim

end Rom

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The input of leaf j of the tree over a word y: below the word's length the symbol at j, written
as the wire writes a symbol of an encoded index; beyond it the filling b₀; the salt of j. -/
def committerLeafInput (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) (j : ℕ) :
    LeafIn (typedOracleCarrier L Bd aT aL) :=
  ⟨if h : j < L.wordLength then W.embE (y ⟨j, h⟩) else b₀, salt j⟩

/-- Ask the leaves' oracle at each input in turn. -/
def committerLeafHashes : List (LeafIn (typedOracleCarrier L Bd aT aL)) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (Dig lam))
  | [] => .pure []
  | x :: xs => (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
      (committerLeafHashes xs).bind fun us => .pure ((show Dig lam from u) :: us)

/-- Ask the nodes' oracle at two digests: the verifier's own `hashTreeNode`
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) at this wire's number of blocks. -/
abbrev committerNodeHash : Dig lam → Dig lam → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam) :=
  hashTreeNode (K := W.K) (L := typedOracleCarrier L Bd aT aL)

/-- The tree over a word: 2 ^ depth leaves, then the library's levels, the root. -/
def committerTreeRoot (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam) :=
  (committerLeafHashes W ((List.range (2 ^ W.depth)).map (committerLeafInput W b₀ y salt))).bind fun l =>
    (levelsM (committerNodeHash W) W.depth l).bind fun lv => .pure (rootOf lv)

/-- The committer behind its coins: the tree over the encoded index at the randomness r and the
salts, the seed's two queries at the root, the root with the honest record at that seed. -/
def committerAtFixedCoins (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (KeyRoot lam L × (I × L.EncodingRandomness × (ℕ → Bits))) :=
  (committerTreeRoot W b₀ (L.encodeIndex i r) salt).bind fun root =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ0 W S root)).bind fun a0 =>
      (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
        (seedQ1 W S (link (show FsAns lam W.K from a0)))).bind fun a1 =>
        .pure (⟨root, L.recOf i r (S.seed (show FsAns lam W.K from a1).1)⟩, (i, r, salt))

/-- **An honest committer for the scheme with the key (root, record), as a term.** It draws the
encoding's randomness and the salts, builds the tree over the encoded index, asks the seed's two
queries at the root, and gives the root with the honest record at that seed. The prover's key: the
index, the randomness, the salts. -/
def committerOverTypedOracles (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (KeyRoot lam L × (I × L.EncodingRandomness × (ℕ → Bits))) :=
  .sample ri.n fun a => .sample sl.n fun c => committerAtFixedCoins W S b₀ i (ri.e a) (sl.e c)

/-! ### What a log holds in which the tree's builder runs -/

variable {W}

/-- Where the leaves' queries run in a log: as many answers as inputs, and each input's entry with
its answer. -/
theorem committerLeafHashes_log {tr : Tc W} :
    ∀ (xs : List (LeafIn (typedOracleCarrier L Bd aT aL))) (out : List (Dig lam)),
      RunsIn tr (committerLeafHashes W xs) out →
      out.length = xs.length ∧ ∀ i x, xs[i]? = some x →
        (⟨OracleName.leaf, x, out.getD i default⟩ : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) ∈ tr
  | [], out, h => by
    obtain rfl := runsIn_pure_iff.1 h
    exact ⟨rfl, fun i x hx => by simp at hx⟩
  | y :: ys, out, h => by
    have h : RunsIn tr ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf y).bind
        fun u =>
        (committerLeafHashes W ys).bind fun us => .pure ((show Dig lam from u) :: us)) out := h
    obtain ⟨u, hu, h⟩ := (runsIn_bind_iff _ _ _).1 h
    obtain ⟨us, hus, h⟩ := (runsIn_bind_iff _ _ _).1 h
    obtain rfl := runsIn_pure_iff.1 h
    obtain ⟨hl, hi⟩ := committerLeafHashes_log ys us hus
    refine ⟨congrArg (· + 1) hl, fun i x hx => ?_⟩
    cases i with
    | zero =>
      obtain rfl : y = x := by simpa using hx
      exact runsIn_ask_iff.1 hu
    | succ i =>
      simpa only [List.getD_cons_succ] using hi i x (by simpa using hx)

/-- Where a node's query runs in a log, the log holds an entry that the library's pair of Merkle
oracles reads as that node. -/
theorem committerNodeHash_log {tr : Tc W} {a b c : Dig lam} (h : RunsIn tr (committerNodeHash W a b) c) :
    ∃ e ∈ tr, (pairM lam W.K (typedOracleCarrier L Bd aT aL)).node e = some ((a, b), c) := by
  refine ⟨_, runsIn_ask_iff.1 h, ?_⟩
  show nodeView (List.ofFn a, List.ofFn b) _ = _
  unfold nodeView
  simp only [digOf_ofFn]

/-- One step from a level of 2 n digests to the next: n digests, and the log holds each node. -/
theorem pairUpCommitterNodes_log {tr : Tc W} :
    ∀ (n : ℕ) (l l' : List (Dig lam)), l.length = 2 * n → RunsIn tr (pairUp (committerNodeHash W) l) l' →
      l'.length = n ∧ ∀ i, i < n → ∃ e ∈ tr, (pairM lam W.K (typedOracleCarrier L Bd aT aL)).node e =
        some ((l.getD (2 * i) default, l.getD (2 * i + 1) default), l'.getD i default)
  | 0, [], l', _, h => by
      obtain rfl : [] = l' := runsIn_pure_iff.1 h
      exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | 0, _ :: _, _, hl, _ => by simp at hl
  | n + 1, [], _, hl, _ => by simp at hl
  | n + 1, [_], _, hl, _ => by
      simp only [List.length_singleton] at hl
      omega
  | n + 1, a :: b :: t, l', hl, h => by
      have h' : RunsIn tr ((committerNodeHash W a b).bind fun c =>
          (pairUp (committerNodeHash W) t).bind fun r => OComp.pure (c :: r)) l' := h
      obtain ⟨c, hc, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl : c :: r = l' := runsIn_pure_iff.1 h3
      have ht : t.length = 2 * n := by
        simp only [List.length_cons] at hl
        omega
      obtain ⟨e1, e2⟩ := pairUpCommitterNodes_log n t r ht hr
      refine ⟨by rw [List.length_cons, e1], fun i hi => ?_⟩
      cases i with
      | zero => exact committerNodeHash_log hc
      | succ i =>
        have := e2 i (Nat.lt_of_succ_lt_succ hi)
        have x1 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
        rw [x1]
        simpa only [List.getD_cons_succ] using this

/-- The levels begin with the digests that they are built over. -/
theorem committerTreeLevels_head {tr : Tc W} :
    ∀ (d : ℕ) (l : List (Dig lam)) (lv : List (List (Dig lam))),
      RunsIn tr (levelsM (committerNodeHash W) d l) lv → ∃ ls, lv = l :: ls
  | 0, l, lv, h => ⟨[], (runsIn_pure_iff.1 h).symm⟩
  | d + 1, l, lv, h => by
      have h' : RunsIn tr ((pairUp (committerNodeHash W) l).bind fun u =>
          (levelsM (committerNodeHash W) d u).bind fun r => OComp.pure (l :: r)) lv := h
      obtain ⟨u, -, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, -, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      exact ⟨r, (runsIn_pure_iff.1 h3).symm⟩

/-- **The induction on the depth.** Where the levels over 2 ^ d digests run in a log, the path that
is read off the levels at a place j below 2 ^ d has d entries and climbs, within the log, from the
digest at j to the root. -/
theorem committerTreeLevels_log {tr : Tc W} :
    ∀ (d : ℕ) (l : List (Dig lam)) (lv : List (List (Dig lam))), l.length = 2 ^ d →
      RunsIn tr (levelsM (committerNodeHash W) d l) lv → ∀ j < 2 ^ d,
      (pathOf lv j).length = d ∧
        ClimbsIn (pairM lam W.K (typedOracleCarrier L Bd aT aL)) tr (pathOf lv j) j (l.getD j default)
          (rootOf lv)
  | 0, l, lv, hl, h, j, hj => by
      obtain rfl : [l] = lv := runsIn_pure_iff.1 h
      obtain rfl : j = 0 := by simpa using hj
      refine ⟨rfl, ?_⟩
      match l, hl with
      | [c], _ => rfl
  | d + 1, l, lv, hl, h, j, hj => by
      have h' : RunsIn tr ((pairUp (committerNodeHash W) l).bind fun u =>
          (levelsM (committerNodeHash W) d u).bind fun r => OComp.pure (l :: r)) lv := h
      obtain ⟨u, hu, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl : l :: r = lv := runsIn_pure_iff.1 h3
      obtain ⟨ls, rfl⟩ := committerTreeLevels_head d u r hr
      obtain ⟨e1, e2⟩ := pairUpCommitterNodes_log (2 ^ d) l u (by rw [hl, pow_succ, Nat.mul_comm]) hu
      have hj2 : j / 2 < 2 ^ d := by
        rw [pow_succ] at hj
        omega
      obtain ⟨i1, i2⟩ := committerTreeLevels_log d u (u :: ls) e1 hr (j / 2) hj2
      rw [pathOf_cons₂, rootOf_cons₂]
      refine ⟨by rw [List.length_cons, i1], u.getD (j / 2) default, ?_, i2⟩
      obtain ⟨e, he, hm⟩ := e2 (j / 2) hj2
      refine ⟨e, he, ?_⟩
      by_cases hb : j % 2 = 0
      · have y1 : 2 * (j / 2) = j := by omega
        rw [y1] at hm
        rw [if_pos hb, if_pos hb]
        exact hm
      · have y1 : 2 * (j / 2) = j - 1 := by omega
        have y2 : j - 1 + 1 = j := by omega
        rw [y1, y2] at hm
        rw [if_neg hb, if_neg hb]
        exact hm

variable (W)

/-- Entry i of a mapped range is f i, for i below n. -/
private theorem getElem?_map_range {β : Type} (f : ℕ → β) {n i : ℕ} (h : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  simp [h]

/-- **Under the wire's laws, a log that holds a run of the tree's builder, outside the Merkle hash
event, spells the word.** -/
theorem word_committerTreeRoot (hW : W.OKG) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) {tr : Tc W}
    (hM : ¬ EM tr) {cm : Dig lam} (h : RunsIn tr (committerTreeRoot W b₀ y salt) cm) :
    extEnc W tr cm = y := by
  unfold committerTreeRoot at h
  obtain ⟨l, hl, h⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain ⟨lv, hlv, h⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain rfl := runsIn_pure_iff.1 h
  obtain ⟨e1, e2⟩ := committerLeafHashes_log _ l hl
  rw [List.length_map, List.length_range] at e1
  funext q
  have hq : q.val < 2 ^ W.depth := lt_of_lt_of_le q.isLt hW.fits
  obtain ⟨p1, p2⟩ := committerTreeLevels_log W.depth l lv e1 hlv q.val hq
  have e3 := e2 q.val (committerLeafInput W b₀ y salt q.val) (getElem?_map_range _ hq)
  have ho := opensIn_of_climbsIn (pairM lam W.K (typedOracleCarrier L Bd aT aL)) ⟨_, e3, rfl⟩ W.depth _ _ p1
    p2
  have hp : extLeaf tr W.depth (rootOf lv) q.val = some (committerLeafInput W b₀ y salt q.val) :=
    (pairM lam W.K (typedOracleCarrier L Bd aT aL)).preimage_of_opensIn hM ho
  have hq' : q.val < L.wordLength := q.isLt
  refine extEnc_apply hW (sl := salt q.val) ?_
  rw [hp]
  unfold committerLeafInput
  rw [dif_pos hq']
  rfl

/-! ### The builder draws no coin and asks leaves and nodes alone -/

section Asks
variable (P : (o : OracleName) → domOf lam (typedOracleCarrier L Bd aT aL) o → Prop) (hl : ∀ x, P OracleName.leaf x)
  (hn : ∀ q, P OracleName.node q)

/-- The builder draws no coin: the leaves. -/
theorem noCoin_committerLeafHashes : ∀ xs : List (LeafIn (typedOracleCarrier L Bd aT aL)), (committerLeafHashes W xs).NoCoin
  | [] => trivial
  | x :: xs => by
      show ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
        (committerLeafHashes W xs).bind fun us => .pure ((show Dig lam from u) :: us)).NoCoin
      exact OComp.NoCoin.bind (fun _ => trivial) fun _ =>
        OComp.NoCoin.bind (noCoin_committerLeafHashes xs) fun _ => trivial

/-- The pairing. -/
theorem noCoin_pairUpCommitterNodes : ∀ l : List (Dig lam), (pairUp (committerNodeHash W) l).NoCoin
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => by
      show ((committerNodeHash W a b).bind fun c =>
        (pairUp (committerNodeHash W) t).bind fun r => OComp.pure (c :: r)).NoCoin
      exact OComp.NoCoin.bind (fun _ => trivial) fun _ =>
        OComp.NoCoin.bind (noCoin_pairUpCommitterNodes t) fun _ => trivial

/-- The levels. -/
theorem noCoin_committerTreeLevels : ∀ (d : ℕ) (l : List (Dig lam)), (levelsM (committerNodeHash W) d l).NoCoin
  | 0, _ => trivial
  | d + 1, l => by
      show ((pairUp (committerNodeHash W) l).bind fun u =>
        (levelsM (committerNodeHash W) d u).bind fun r => OComp.pure (l :: r)).NoCoin
      exact OComp.NoCoin.bind (noCoin_pairUpCommitterNodes W l) fun u =>
        OComp.NoCoin.bind (noCoin_committerTreeLevels d u) fun _ => trivial

/-- The tree. -/
theorem noCoin_committerTreeRoot (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeRoot W b₀ y salt).NoCoin :=
  OComp.NoCoin.bind (noCoin_committerLeafHashes W _) fun l =>
    OComp.NoCoin.bind (noCoin_committerTreeLevels W _ l) fun _ => trivial

/-- The committer behind its coins. -/
theorem noCoin_committerAtFixedCoins (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits) :
    (committerAtFixedCoins W S b₀ i r salt).NoCoin :=
  OComp.NoCoin.bind (noCoin_committerTreeRoot W _ _ _) fun _ => fun _ => fun _ => trivial

include hl in
/-- The builder asks leaves and nodes alone: the leaves. -/
theorem asksIn_committerLeafHashes : ∀ xs : List (LeafIn (typedOracleCarrier L Bd aT aL)), (committerLeafHashes W xs).AsksIn P
  | [] => trivial
  | x :: xs => by
      show ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
        (committerLeafHashes W xs).bind fun us => .pure ((show Dig lam from u) :: us)).AsksIn P
      refine OComp.AsksIn.bind (fun _ => ?_) ⟨hl x, fun _ => trivial⟩
      refine OComp.AsksIn.bind (fun _ => ?_) (asksIn_committerLeafHashes xs)
      exact trivial

include hn in
/-- The pairing. -/
theorem asksIn_pairUpCommitterNodes : ∀ l : List (Dig lam), (pairUp (committerNodeHash W) l).AsksIn P
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => by
      show ((committerNodeHash W a b).bind fun c =>
        (pairUp (committerNodeHash W) t).bind fun r => OComp.pure (c :: r)).AsksIn P
      refine OComp.AsksIn.bind (fun _ => ?_) ⟨hn _, fun _ => trivial⟩
      refine OComp.AsksIn.bind (fun _ => ?_) (asksIn_pairUpCommitterNodes t)
      exact trivial

include hn in
/-- The levels. -/
theorem asksIn_committerTreeLevels : ∀ (d : ℕ) (l : List (Dig lam)), (levelsM (committerNodeHash W) d l).AsksIn P
  | 0, _ => trivial
  | d + 1, l => by
      show ((pairUp (committerNodeHash W) l).bind fun u =>
        (levelsM (committerNodeHash W) d u).bind fun r => OComp.pure (l :: r)).AsksIn P
      refine OComp.AsksIn.bind (fun u => ?_) (asksIn_pairUpCommitterNodes W P hn l)
      refine OComp.AsksIn.bind (fun _ => ?_) (asksIn_committerTreeLevels d u)
      exact trivial

include hl hn in
/-- The tree. -/
theorem asksIn_committerTreeRoot (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeRoot W b₀ y salt).AsksIn P := by
  unfold committerTreeRoot
  refine OComp.AsksIn.bind (fun l => ?_) (asksIn_committerLeafHashes W P hl _)
  refine OComp.AsksIn.bind (fun _ => ?_) (asksIn_committerTreeLevels W P hn _ l)
  exact trivial

end Asks

/-! ### The committer over one hash function -/

/-- **What a log of strings holds in which the committer runs over one hash function, at fixed
coins, where lam is not 0**: the prover's key holds the index; the tree's part is a typed run in
what `singleTr` reads off the log, at the randomness and the salts of the prover's key; the record
is the honest one at some seed. -/
theorem run_committerOverTypedOracles (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I) (n : ℕ)
    {trV : Trace (rom lam)} {o : KeyRoot lam L × (I × L.EncodingRandomness × (ℕ → Bits))}
    (h : RunsIn trV (((committerOverTypedOracles W S ri sl b₀ i).overOne m).withCoins n) o) :
    o.2.1 = i ∧ RunsIn (singleTr m trV) (committerTreeRoot W b₀ (L.encodeIndex i o.2.2.1) o.2.2.2) o.1.cm ∧
      ∃ s, o.1.rcd = L.recOf i o.2.2.1 s := by
  rw [withCoins_overOne] at h
  have e : (committerOverTypedOracles W S ri sl b₀ i).withCoins n =
      committerAtFixedCoins W S b₀ i (ri.e ⟨n % (ri.n + 1), Nat.mod_lt _ ri.n.succ_pos⟩)
        (sl.e ⟨n / (ri.n + 1) % (sl.n + 1), Nat.mod_lt _ sl.n.succ_pos⟩) :=
    withCoins_noCoin _ _ (noCoin_committerAtFixedCoins W S _ _ _ _)
  rw [e] at h
  unfold committerAtFixedCoins at h
  rw [overOne_bind] at h
  obtain ⟨root, hroot, h⟩ := (runsIn_bind_iff _ _ _).1 h
  rw [overOne_bind] at h
  obtain ⟨a0, -, h⟩ := (runsIn_bind_iff _ _ _).1 h
  rw [overOne_bind] at h
  obtain ⟨a1, -, h⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain rfl := runsIn_pure_iff.1 h
  exact ⟨rfl, runsIn_singleTr m _
    (asksIn_committerTreeRoot W _ (fun _ => blocks_leaf hlam m) (fun _ => blocks_node hlam m) _ _ _) hroot,
    _, rfl⟩

/-- **The heart: under the wire's laws and hdec, where lam is not 0: outside the Merkle hash event
on the three logs, where the word off the key's maker's log trC is the word off all three, the
extractor gives at trC the index that the run again, in trV, commits to.** Of trC and trP nothing
else is asked. It feeds the hypothesis hgood of `binding_of_badW`
(Johnson/TypedOracleCompiler/RecCompile/OpensTwoStage.lean) at one coding: hgood's clauses on the run, on `EM` and
on the two words are h, hM and he (hgood's run gives the key alone, h both keys); its clause that
the logs hold one function's answers is not used. NEITHER hM NOR he IS FREE: together they are the
complement of that theorem's rare event `BadW`, whose probability is `word_pr_pub`'s
(Johnson/TypedOracleCompiler/RecCompile/WordPub.lean). hdec is false at an index type with a member that the decoder
never gives (the head, Limits). -/
theorem good_committerOverTypedOracles (hlam : 0 < lam) (hW : W.OKG)
    (hdec : ∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits))
    (b₀ : Bd) (i : I) (n : ℕ)
    {trC trP trV : Trace (rom lam)} {o : KeyRoot lam L × (I × L.EncodingRandomness × (ℕ → Bits))}
    (h : RunsIn trV (((committerOverTypedOracles W S ri sl b₀ i).overOne m).withCoins n) o)
    (hM : ¬ EM (singleTr m (trC ++ (trP ++ trV))))
    (he : extEnc W (singleTr m trC) o.1.cm =
      extEnc W (singleTr m (trC ++ (trP ++ trV))) o.1.cm) :
    (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W)).Ei o.1 trC = some i := by
  obtain ⟨-, ht, s, hs⟩ := run_committerOverTypedOracles W S hlam m ri sl b₀ i n h
  have hsub : singleTr m trV ⊆ singleTr m (trC ++ (trP ++ trV)) := by
    rw [singleTr_append, singleTr_append]
    exact fun e he => List.mem_append_right _ (List.mem_append_right _ he)
  show L.decodeIndex (extEnc W (singleTr m trC) o.1.cm) o.1.rcd = some i
  rw [he, word_committerTreeRoot W hW b₀ _ _ hM (ht.mono hsub), hs]
  exact hdec _ _ _

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.committerLeafHashes_log
#print axioms TypedOracleCompiler.Compile.Batch.Cms.committerNodeHash_log
#print axioms TypedOracleCompiler.Compile.Batch.Cms.pairUpCommitterNodes_log
#print axioms TypedOracleCompiler.Compile.Batch.Cms.committerTreeLevels_head
#print axioms TypedOracleCompiler.Compile.Batch.Cms.committerTreeLevels_log
#print axioms TypedOracleCompiler.Compile.Batch.Cms.word_committerTreeRoot
#print axioms Rom.askAll_runsIn
#print axioms Rom.runsIn_singleTr
#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_committerLeafHashes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_pairUpCommitterNodes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_committerTreeLevels
#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_committerTreeRoot
#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_committerAtFixedCoins
#print axioms TypedOracleCompiler.Compile.Batch.Cms.asksIn_committerLeafHashes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.asksIn_pairUpCommitterNodes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.asksIn_committerTreeLevels
#print axioms TypedOracleCompiler.Compile.Batch.Cms.asksIn_committerTreeRoot
#print axioms Rom.withCoins_noCoin
#print axioms TypedOracleCompiler.Compile.Batch.Cms.run_committerOverTypedOracles
#print axioms TypedOracleCompiler.Compile.Batch.Cms.good_committerOverTypedOracles
