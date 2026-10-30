-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/CommitterTreeKeptByProver.lean: the outer trees of the compiled prover (OnBytes/Prover/), at a table
that is committed by the library's committer behind its coins (`committerAtFixedCoins`,
Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean): under fixed oracle functions g the tree that the prover
builds again over the committer's own leaves is kept rightly, has the key's root and holds the word:
the premise `ExtAt` (OnBytes/Prover/Inv.lean) of `yes_of_prove` (OnBytes/Prover/Main.lean), at the
letters of the three compiled verifiers `verifyOfflineProof`, `verifyLinkProof`, `verifyOnlineProof` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean,
LinkAns.lean).

Why. `committerAtFixedCoins` gives the root, the record and (index, randomness, salts), not the tree's levels. A
prover that opens leaves needs them. The salts are an argument of `committerAtFixedCoins`, so it is called as it
stands at salts of any form; three theorems call it at the form that a reader of a file's bytes
lays as a leaf's typed salt (`Run.leafSalt`, Run/ParseBS.lean).

Main names (namespace `OnBytes.Prover`):
  `extAt_of_trees`   at every wire of external strings: trees built by `treeO` meet `ExtAt`, if the
                     leaves hold the symbols, with salts of sMT bits, and the roots are those of cms
  `committerTreeKeptByProver`          the one definition: the tree over a word as the prover keeps it: `treeO` over
                     the committer's leaves `committerLeafInput`: a program
  `committerLeafHashes_eq`, `root_committerTreeKeptByProver`, `cm_committerAtFixedCoins`   it asks the committer's leaves; its root is
                     `committerTreeRoot`'s value; that is the root in `committerAtFixedCoins`'s key
  `kept_at`          what the three protocols' wires share, at one place of one table
  `extAt_one`, `extAt_two`   `ExtAt` at a wire of one table, of two tables, under the wire's laws
  `extAt_key`, `extAt_session`, `extAt_link`   at the three verifiers' letters, for all salts that
                     have sMT bits at the places below the word's length
  `length_leafSalt`  32 bytes and sb bytes give 256 + 8 sb bits
  `extAt_key_core`, `extAt_session_core`, `extAt_link_core`   at `committerAtFixedCoins`'s own key and record, at
                     salts of that form
  `seedIs_committerAtFixedCoins`   the verifier's test of the seed says yes at `committerAtFixedCoins`'s key
  `noCoin_committerTreeKeptByProver`   the prover's builder has no coins

Limits. Under fixed typed oracle functions: nothing over one hash function, nothing on probability.
For every object with records and every wire with `QueryLayout.OKG`: shown at no written object. Who draws
the salts, and who gives them their first part, is not said: they are arguments. Nothing on bytes:
that the openings which the prover lays are those that a file's reader lays is not shown. No
verifier's yes follows from this file alone. Tied to no program.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Tree
import Johnson.TypedOracleCompiler.RecCompile.CommitOverTypedOracles
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import Run.ParseBS
import Run.CodingBitsLaws

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## General: at every wire of external strings -/

/-- Trees that the prover's builder makes meet `ExtAt`. -/
theorem extAt_of_trees :
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ)
    (E : ExtSpec) (we : WireE E) (embE : E.Sym → Body L) (cms : List (Dig lam)) (y : E.Str)
    (inp : ℕ → ℕ → LeafIn L),
  (∀ p, we.leaf p < 2 ^ we.depth) →
  (∀ p, (inp (we.which p) (we.leaf p)).body = embE (E.rd y p)) →
  (∀ p, (inp (we.which p) (we.leaf p)).salt.length = sMT) →
  (∀ p, ((treeO (K := K) we.depth (inp (we.which p))).det g).root =
    cms.getD (we.which p) default) →
  ExtAt g sMT we embE cms y fun k => (treeO (K := K) we.depth (inp k)).det g := by
  intro I X lam K L g sMT E we embE cms y inp hl hb hs hr
  refine ⟨fun p => (treeO_at g we.depth (inp (we.which p))).1, hr, fun p => ?_, fun p => ?_, hl⟩
  · show (((treeO (K := K) we.depth (inp (we.which p))).det g).inp (we.leaf p)).body = _
    rw [(treeO_at g we.depth (inp (we.which p))).2]
    exact hb p
  · show (((treeO (K := K) we.depth (inp (we.which p))).det g).inp (we.leaf p)).salt.length = _
    rw [(treeO_at g we.depth (inp (we.which p))).2]
    exact hs p

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-! ## The tree as the prover keeps it -/

/-- The tree over a word as the prover keeps it: the committer's own leaves (`committerLeafInput`), built by
the prover's builder. A program; it asks what `committerTreeRoot` asks. -/
def committerTreeKeptByProver (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (TreeK lam (typedOracleCarrier L Bd aT aL)) :=
  treeO W.depth (committerLeafInput W b₀ y salt)

/-- The committer's and the prover's programs for the leaves are one. -/
theorem committerLeafHashes_eq : ∀ xs : List (LeafIn (typedOracleCarrier L Bd aT aL)),
    committerLeafHashes W xs = leavesO (K := W.K) xs
  | [] => rfl
  | x :: xs => by
    show ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
      (committerLeafHashes W xs).bind fun us => OComp.pure ((show Dig lam from u) :: us)) = _
    rw [committerLeafHashes_eq xs]
    rfl

/-- Its root is the committer's. -/
theorem root_committerTreeKeptByProver :
  ∀ (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits),
  ((committerTreeKeptByProver W b₀ y salt).det g).root = (committerTreeRoot W b₀ y salt).det g := by
  intro b₀ y salt
  unfold committerTreeKeptByProver committerTreeRoot
  rw [det_treeO, OComp.det_bind, OComp.det_bind, committerLeafHashes_eq, det_leavesO, det_levelsO]
  show rootOf (levelsF (nodeAt g) W.depth ((List.range (2 ^ W.depth)).map fun j =>
      (g OracleName.leaf (committerLeafInput W b₀ y salt j) : Dig lam))) =
    rootOf (levelsF (nodeAt g) W.depth (List.map (β := Dig lam) (fun x => g OracleName.leaf x)
      ((List.range (2 ^ W.depth)).map (committerLeafInput W b₀ y salt))))
  rw [List.map_map]
  rfl

/-- The root in the key of the committer behind its coins is the tree's. -/
theorem cm_committerAtFixedCoins :
  ∀ (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits),
  ((committerAtFixedCoins W S b₀ i r salt).det g).1.cm = (committerTreeRoot W b₀ (L.encodeIndex i r) salt).det g := by
  intro b₀ i r salt
  unfold committerAtFixedCoins
  rw [OComp.det_bind, OComp.det_bind, OComp.det_bind]
  rfl

/-- What the three protocols' wires share, at one place q of one table. -/
theorem kept_at (sMT : ℕ) (hn : L.wordLength ≤ 2 ^ W.depth) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol)
    (salt : ℕ → Bits) (hs : ∀ j, j < L.wordLength → (salt j).length = sMT) (q : Fin L.wordLength) :
    ((committerTreeKeptByProver W b₀ y salt).det g).At g W.depth ∧
      ((committerTreeKeptByProver W b₀ y salt).det g).root = (committerTreeRoot W b₀ y salt).det g ∧
      (((committerTreeKeptByProver W b₀ y salt).det g).inp q.val).body = W.embE (y q) ∧
      (((committerTreeKeptByProver W b₀ y salt).det g).inp q.val).salt.length = sMT ∧ q.val < 2 ^ W.depth := by
  have hk := treeO_at g W.depth (committerLeafInput W b₀ y salt)
  have hi : ((committerTreeKeptByProver W b₀ y salt).det g).inp = committerLeafInput W b₀ y salt := hk.2
  refine ⟨hk.1, root_committerTreeKeptByProver W g b₀ y salt, ?_, ?_, lt_of_lt_of_le q.isLt hn⟩
  · rw [hi]
    show (if h : q.val < L.wordLength then W.embE (y ⟨q.val, h⟩) else b₀) = _
    exact dif_pos q.isLt
  · rw [hi]
    exact hs q.val q.isLt

/-! ## `ExtAt` at a wire of one table, and of two -/

theorem extAt_one (sMT : ℕ) (we : WireE (oneExternalString L.wordLength L.Symbol)) (hd : we.depth = W.depth)
    (hp : ∀ p, we.which p = 0 ∧ we.leaf p = p.val) (hn : L.wordLength ≤ 2 ^ W.depth) (b₀ : Bd)
    (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) (hs : ∀ j, j < L.wordLength → (salt j).length = sMT)
    (l : List (Dig lam)) :
    ExtAt g sMT we W.embE ((committerTreeRoot W b₀ y salt).det g :: l) y
      fun _ => (committerTreeKeptByProver W b₀ y salt).det g := by
  have f := fun q => kept_at W g sMT hn b₀ y salt hs q
  generalize (committerTreeKeptByProver W b₀ y salt).det g = T at f ⊢
  generalize (committerTreeRoot W b₀ y salt).det g = cm at f ⊢
  refine ⟨fun q => ?_, fun q => ?_, fun q => ?_, fun q => ?_, fun q => ?_⟩
  · show T.At g we.depth
    rw [hd]
    exact (f q).1
  · show T.root = (cm :: l).getD (we.which q) default
    rw [(hp q).1]
    exact (f q).2.1
  · show (T.inp (we.leaf q)).body = W.embE (y q)
    rw [(hp q).2]
    exact (f q).2.2.1
  · show (T.inp (we.leaf q)).salt.length = sMT
    rw [(hp q).2]
    exact (f q).2.2.2.1
  · rw [(hp q).2, hd]
    exact (f q).2.2.2.2

theorem extAt_two (sMT : ℕ) (we : WireE (twoExternalStrings L.wordLength L.Symbol)) (hd : we.depth = W.depth)
    (hl : (∀ p, we.which (.inl p) = 0 ∧ we.leaf (.inl p) = p.val) ∧
      ∀ p, we.which (.inr p) = 1 ∧ we.leaf (.inr p) = p.val)
    (hn : L.wordLength ≤ 2 ^ W.depth) (b₀ b₁ : Bd) (y y' : Fin L.wordLength → L.Symbol) (salt salt' : ℕ → Bits)
    (hs : ∀ j, j < L.wordLength → (salt j).length = sMT) (hs' : ∀ j, j < L.wordLength → (salt' j).length = sMT)
    (l : List (Dig lam)) :
    ExtAt g sMT we W.embE
      ((committerTreeRoot W b₀ y salt).det g :: (committerTreeRoot W b₁ y' salt').det g :: l) (y, y')
      fun k => if k = 0 then (committerTreeKeptByProver W b₀ y salt).det g else (committerTreeKeptByProver W b₁ y' salt').det g := by
  have f := fun q => kept_at W g sMT hn b₀ y salt hs q
  have f' := fun q => kept_at W g sMT hn b₁ y' salt' hs' q
  generalize (committerTreeKeptByProver W b₀ y salt).det g = T at f ⊢
  generalize (committerTreeKeptByProver W b₁ y' salt').det g = T' at f' ⊢
  generalize (committerTreeRoot W b₀ y salt).det g = cm at f ⊢
  generalize (committerTreeRoot W b₁ y' salt').det g = cm' at f' ⊢
  have x0 : ∀ q, (if we.which (.inl q) = 0 then T else T') = T := fun q => by
    rw [(hl.1 q).1, if_pos rfl]
  have x1 : ∀ q, (if we.which (.inr q) = 0 then T else T') = T' := fun q => by
    rw [(hl.2 q).1, if_neg Nat.one_ne_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (q | q)
    · show (if we.which (.inl q) = 0 then T else T').At g we.depth
      rw [x0, hd]
      exact (f q).1
    · show (if we.which (.inr q) = 0 then T else T').At g we.depth
      rw [x1, hd]
      exact (f' q).1
  · rintro (q | q)
    · show (if we.which (.inl q) = 0 then T else T').root =
        (cm :: cm' :: l).getD (we.which (.inl q)) default
      rw [x0, (hl.1 q).1]
      exact (f q).2.1
    · show (if we.which (.inr q) = 0 then T else T').root =
        (cm :: cm' :: l).getD (we.which (.inr q)) default
      rw [x1, (hl.2 q).1]
      exact (f' q).2.1
  · rintro (q | q)
    · show ((if we.which (.inl q) = 0 then T else T').inp (we.leaf (.inl q))).body = W.embE (y q)
      rw [x0, (hl.1 q).2]
      exact (f q).2.2.1
    · show ((if we.which (.inr q) = 0 then T else T').inp (we.leaf (.inr q))).body = W.embE (y' q)
      rw [x1, (hl.2 q).2]
      exact (f' q).2.2.1
  · rintro (q | q)
    · show ((if we.which (.inl q) = 0 then T else T').inp (we.leaf (.inl q))).salt.length = sMT
      rw [x0, (hl.1 q).2]
      exact (f q).2.2.2.1
    · show ((if we.which (.inr q) = 0 then T else T').inp (we.leaf (.inr q))).salt.length = sMT
      rw [x1, (hl.2 q).2]
      exact (f' q).2.2.2.1
  · rintro (q | q)
    · rw [(hl.1 q).2, hd]
      exact (f q).2.2.2.2
    · rw [(hl.2 q).2, hd]
      exact (f' q).2.2.2.2

/-! ## At the three verifiers' letters -/

/-- At the key's protocol: the letters of `verifyOfflineProof`. -/
theorem extAt_key :
  ∀ (sMT : ℕ) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) (an : L.OutOfDomainAnswer),
  W.OKG → (∀ j, j < L.wordLength → (salt j).length = sMT) →
  ExtAt g sMT (wTC W).ext W.embE (cmsTA cA ((committerTreeRoot W b₀ y salt).det g) an) y
    fun _ => (committerTreeKeptByProver W b₀ y salt).det g :=
  fun sMT b₀ y salt an hW hs =>
    extAt_one W g sMT (wTC W).ext hW.extDepth.1 hW.extT hW.fits b₀ y salt hs (cA an)

/-- At the session's protocol: the letters of `verifyOnlineProof`. -/
theorem extAt_session :
  ∀ (sMT : ℕ) (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) (an : L.OutOfDomainAnswer),
  W.OKG → (∀ j, j < L.wordLength → (salt j).length = sMT) →
  ExtAt g sMT (wBC W).ext W.embE (cmsBA cA ((committerTreeRoot W b₀ y salt).det g) an) y
    fun _ => (committerTreeKeptByProver W b₀ y salt).det g :=
  fun sMT b₀ y salt an hW hs =>
    extAt_one W g sMT (wBC W).ext hW.extDepth.2.2 hW.extB hW.fits b₀ y salt hs
      ((committerTreeRoot W b₀ y salt).det g :: cA an)

/-- At Link: the letters of `verifyLinkProof`: two tables. -/
theorem extAt_link :
  ∀ (sMT : ℕ) (b₀ b₁ : Bd) (y y' : Fin L.wordLength → L.Symbol) (salt salt' : ℕ → Bits)
    (an an' : L.OutOfDomainAnswer),
  W.OKG → (∀ j, j < L.wordLength → (salt j).length = sMT) → (∀ j, j < L.wordLength → (salt' j).length = sMT) →
  ExtAt g sMT (wLC W).ext W.embE
    (cmsLA cA ((committerTreeRoot W b₀ y salt).det g) ((committerTreeRoot W b₁ y' salt').det g) an an') (y, y')
    fun k => if k = 0 then (committerTreeKeptByProver W b₀ y salt).det g else (committerTreeKeptByProver W b₁ y' salt').det g :=
  fun sMT b₀ b₁ y y' salt salt' an an' hW hs hs' =>
    extAt_two W g sMT (wLC W).ext hW.extDepth.2.1 hW.extL hW.fits b₀ b₁ y y' salt salt' hs hs'
      (cA an ++ cA an')

/-! ## At the committer's own key, at salts of the form that a file's reader lays -/

/-- The length of the typed salt that a file's reader lays. -/
theorem length_leafSalt :
  ∀ (c s : ByteArray) (sb : ℕ), c.size = 32 → s.size = sb →
  (_root_.Run.leafSalt c s).length = 256 + 8 * sb := by
  intro c s sb hc hs
  have h : (_root_.Run.leafSalt c s).length = 8 * c.size + 8 * s.size := by
    unfold _root_.Run.leafSalt
    rw [List.length_append, _root_.Run.length_bytesToBits, _root_.Run.length_bytesToBits]
  omega

/-- **At the key file**: the committer behind its coins, called as it stands; the list and the word
are `verifyOfflineProof`'s at that key. -/
theorem extAt_key_core :
  ∀ (sb : ℕ) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (c : ByteArray) (s : ℕ → ByteArray),
  W.OKG → c.size = 32 → (∀ j, j < L.wordLength → (s j).size = sb) →
  ExtAt g (256 + 8 * sb) (wTC W).ext W.embE
    (cmsTA cA ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.cm
      ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.rcd.2) (L.encodeIndex i r)
    fun _ => (committerTreeKeptByProver W b₀ (L.encodeIndex i r) fun j => _root_.Run.leafSalt c (s j)).det g := by
  intro sb b₀ i r c s hW hc hs
  rw [cm_committerAtFixedCoins]
  exact extAt_key W cA g (256 + 8 * sb) b₀ (L.encodeIndex i r) _ _ hW
    fun j hj => length_leafSalt c (s j) sb hc (hs j hj)

/-- **At the proof file**: the session reads under one key's root; the list and the word are `verifyOnlineProof`'s
at that key. -/
theorem extAt_session_core :
  ∀ (sb : ℕ) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (c : ByteArray) (s : ℕ → ByteArray),
  W.OKG → c.size = 32 → (∀ j, j < L.wordLength → (s j).size = sb) →
  ExtAt g (256 + 8 * sb) (wBC W).ext W.embE
    (cmsBA cA ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.cm
      ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.rcd.2) (L.encodeIndex i r)
    fun _ => (committerTreeKeptByProver W b₀ (L.encodeIndex i r) fun j => _root_.Run.leafSalt c (s j)).det g := by
  intro sb b₀ i r c s hW hc hs
  rw [cm_committerAtFixedCoins]
  exact extAt_session W cA g (256 + 8 * sb) b₀ (L.encodeIndex i r) _ _ hW
    fun j hj => length_leafSalt c (s j) sb hc (hs j hj)

/-- **At the copy's file**: two keys of that committer. -/
theorem extAt_link_core :
  ∀ (sb : ℕ) (b₀ : Bd) (i i' : I) (r r' : L.EncodingRandomness) (c : ByteArray)
    (s s' : ℕ → ByteArray),
  W.OKG → c.size = 32 → (∀ j, j < L.wordLength → (s j).size = sb) → (∀ j, j < L.wordLength → (s' j).size = sb) →
  ExtAt g (256 + 8 * sb) (wLC W).ext W.embE
    (cmsLA cA ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.cm
      ((committerAtFixedCoins W S b₀ i' r' fun j => _root_.Run.leafSalt c (s' j)).det g).1.cm
      ((committerAtFixedCoins W S b₀ i r fun j => _root_.Run.leafSalt c (s j)).det g).1.rcd.2
      ((committerAtFixedCoins W S b₀ i' r' fun j => _root_.Run.leafSalt c (s' j)).det g).1.rcd.2)
    (L.encodeIndex i r, L.encodeIndex i' r')
    fun k => if k = 0 then (committerTreeKeptByProver W b₀ (L.encodeIndex i r) fun j => _root_.Run.leafSalt c (s j)).det g
      else (committerTreeKeptByProver W b₀ (L.encodeIndex i' r') fun j => _root_.Run.leafSalt c (s' j)).det g := by
  intro sb b₀ i i' r r' c s s' hW hc hs hs'
  rw [cm_committerAtFixedCoins, cm_committerAtFixedCoins]
  exact extAt_link W cA g (256 + 8 * sb) b₀ b₀ (L.encodeIndex i r) (L.encodeIndex i' r') _ _ _ _ hW
    (fun j hj => length_leafSalt c (s j) sb hc (hs j hj))
    fun j hj => length_leafSalt c (s' j) sb hc (hs' j hj)

/-- The verifier's test of the seed says yes at the committer's key. -/
theorem seedIs_committerAtFixedCoins :
  ∀ (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (salt : ℕ → Bits),
  (outOfDomainSeedIs W S ((committerAtFixedCoins W S b₀ i r salt).det g).1.cm
    ((committerAtFixedCoins W S b₀ i r salt).det g).1.rcd.1).det g = true := by
  intro b₀ i r salt
  have h : ((committerAtFixedCoins W S b₀ i r salt).det g).1.rcd.1 =
      S.seed (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from
        (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
          (seedQ1 W S (TypedOracleCompiler.Compile.Batch.link
            (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from
              (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
                (seedQ0 W S ((committerTreeRoot W b₀ (L.encodeIndex i r) salt).det g))).det g)))).det g).1 := by
    unfold committerAtFixedCoins
    rw [OComp.det_bind, OComp.det_bind, OComp.det_bind]
    rfl
  rw [cm_committerAtFixedCoins, h]
  unfold outOfDomainSeedIs
  rw [OComp.det_bind, OComp.det_bind]
  exact @decide_eq_true _ (S.decS _ _) rfl

/-- The prover's builder has no coins. -/
theorem noCoin_committerTreeKeptByProver :
  ∀ (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits), (committerTreeKeptByProver W b₀ y salt).NoCoin :=
  fun _ _ _ => (noCoin_leavesO _).bind fun l => (noCoin_committerTreeLevels W _ l).bind fun _ => trivial

end OnBytes.Prover
