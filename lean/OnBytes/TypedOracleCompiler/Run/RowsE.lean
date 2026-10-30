-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/RowsE.lean: FROM STRINGS TO VALUES AT AN ENTRY's PAGE: the row laws of the entry's
typed chain and of the seeds' chain, at the family that the page `EntryPage.implE` makes of ONE
oracle:
what that family answers at a typed query IS what the format's chain gives at the hash made of the
same oracle.

WHY. OnBytes/TypedOracleCompiler/Run/EntryPage.lean says of each kind of typed query which STRING it has. The tie
from the port's yes on an entry file to the typed verifier's yes compares VALUES: the family
`readBlocks (implE …) g` against the hash `Fmt.HO (oB (g ()))`. OnBytes/TypedOracleCompiler/Run/RowsG.lean has the
step from strings to values for every page; here it is taken at the entry's equations.

 - `famE` := `RowsG.famG` at the entry's page; `famE_is`: it is `readBlocks (implE …) g`, by
 unfolding; - `rowE_first`: the tail of the answer at the first typed query (two outer roots, both
   tables' answers beside dd) is the library's `Fmt.firstValueW` at the hash, at the pins' label and
   digest, on the two tables' items;
 - `rowE_block`: the written round k, at its own plain part: EVERY typed block j is the format's
   block number `blockTo (ordOf d) K j` of the round's row;
 - `rowE_round` : PQ.Row … (OnBytes/TypedOracleCompiler/Run/ChainFrom.lean), at a round that has work or is
   not sealed; `rowE_at` : PQ.RowAt …: the same in the form in which the chain's walk takes a
   round's law: for all chain values of 256 bits, as many roots as the round has trees, a nonce
   below 2 ^ 64;
 - `rowE_sealTail`: at a sealed round without work the tail is the row's block 1;
 - `rowE_vertex`: a vertex: the library's `Fmt.vertexW` at the hash; `rowE_leaf`: a leaf whose
   string the code of leaves writes as a call's;
 - `seedsPageE`: the law `SeedsPage` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean) at `implE`, at the name
   "the root's bytes, then the pins' fixed bytes", for EVERY root; `seedsPageE_key`: at a key's
   name, if the key's root is cm's bytes and the pins' fixed bytes are those of the key's shape and
   configuration: in the very letters of `entry_chain_seed` and `entry_run_seeds`
   (OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean).

Main definition: `famE`.
Main theorems: `rowE_first`, `rowE_block`, `rowE_round`, `rowE_at`, `rowE_vertex`, `seedsPageE`,
`seedsPageE_key`.

WHAT IS NOT SAID. THE LAW BY RECURSION ALONG THE ROUNDS' DATA (ChainFrom.lean's `PQ.RowEnd`) IS NOT
HERE: it is stated at plain parts under the annotation `Twin.allLo`, the entry's interface has
`RoundSplits.allLocal`, and the two are not one by unfolding at a variable list
(OnBytes/TypedOracleCompiler/Run/PageEBack.lean: `pbl_is`): here each round is taken by its number. `rowE_at` asks
that the round has as many trees as root items. That the compiled verifier asks these queries. No
domain of the format's hash is asked: equations at EVERY g.
What the heads of EntryPage.lean and RowsG.lean do not say. Nothing on soundness. The sibling is a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPage
import OnBytes.TypedOracleCompiler.Run.RowsG

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.RowsE
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG
open TypedOracleCompiler.Run.PlainIn
open TypedOracleCompiler.Run.KeyPageRounds (ordOf)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (dd : Sd) (K : ℕ) (V : Leaves (Le D early e))
  (back : StrCode (AllPts 256 K (Le D early e))) (g : Fam (rom 256))

/-- The typed family that the entry's page makes of the one oracle. -/
def famE : Fam (typedOracleFamily 256 K (Le D early e)) := famG (pageE P dd K V back) g

/-- It is the family read out of g through the page. -/
theorem famE_is : famE P dd K V back g = readBlocks (implE P dd K V back) g := rfl

/-! ## The link's chain -/

/-- THE FIRST QUERY, AS A VALUE: the tail is the link's chain's first value. -/
theorem rowE_first (r₀ r₁ : Dig 256) (a₀ a₁ : List T3) (salt : List Bool)
    (h₀ : a₀.length < 2 ^ 32) (h₁ : a₁.length < 2 ^ 32) (hl : salt = [] ∨ salt.length = 256) :
    (famE P dd K V back g (.fb .link)
        ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], p0E D early e⟩ :
        (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (Id.run (_root_.Fmt.firstValueW (m := Id) (hOfG g) P.l (digToBytes P.pd)
        (_root_.Fmt.tableItem "the first table" (digToBytes r₀) a₀ ++
          _root_.Fmt.tableItem "the further table" (digToBytes r₁) a₁)
        ByteArray.empty (runOf salt))) :=
  first_of_code (pageE P dd K V back) g .link _ P.l _ _ _ _
    (implE_first P dd K V back r₀ r₁ a₀ a₁ salt h₀ h₁ hl)

/-- EVERY TYPED BLOCK OF A WRITTEN ROUND's ANSWER IS A BLOCK OF THE FORMAT's ROW. -/
theorem rowE_block (hK : K < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true)
    (j : Fin (K + 1)) :
    g () ((implE P dd K V back).code (.fb .link)
        ⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩ j) =
      bytesToDig (_root_.Fmt.blockW (hOfG g) P.l (bitsToBytes ρ) (k.val + 1)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
          (GPlain.old (b := (D.ds.get k).entry.work) z))
        (D.ds.get k).kind (D.ds.get k).entry.work
        (GPlain.nonce (b := (D.ds.get k).entry.work) z)
        (blockTo (ordOf (D.ds.get k)) K j).val) :=
  blk_of_code (pageE P dd K V back) g .link _ j P.l _ _ _ _ _ _ _
    (implE_round P dd K V back hK k hi hw ρ hρ rt z hok j)

/-- The order of blocks is the format's own for the round's work, at a round that has work or is not
sealed. -/
theorem ordOf_plain (d : PQ.RD) (h : d.entry.work ≠ 0 ∨ d.kind ≠ .sealed) :
    ordOf d = decide (d.entry.work ≠ 0) := by
  unfold ordOf
  rcases h with h | h
  · rw [decide_eq_true h]
    rfl
  · rw [decide_eq_false h, Bool.or_false]

/-- THE ROW OF A WRITTEN ROUND (ChainFrom.lean's `PQ.Row`), at a round that has work or is not
sealed. -/
theorem rowE_round (hK : K < 2 ^ 48) (h1 : 0 < K) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256)
    (hs : (D.ds.get k).entry.work ≠ 0 ∨ (D.ds.get k).kind ≠ .sealed) (ρ : Bits)
    (hρ : ρ.length = 256) (rt : List (Dig 256)) (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true) :
    PQ.Row (oB (g ())) K P.l (bitsToBytes ρ) (k.val + 1)
      (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
        (GPlain.old (b := (D.ds.get k).entry.work) z))
      (D.ds.get k).kind (D.ds.get k).entry.work (GPlain.nonce (b := (D.ds.get k).entry.work) z)
      (famE P dd K V back g (.fb .link) ⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩) :=
  row_of_codes (pageE P dd K V back) g .link _ P.l _ _ _ _ _ _ fun j => by
    rw [blockNo_eq _ K j (Or.inl h1), ← ordOf_plain _ hs]
    exact implE_round P dd K V back hK k hi hw ρ hρ rt z hok j

/-- At a sealed round without work the tail is the row's block 1. -/
theorem rowE_sealTail (hK : K < 2 ^ 48) (h1 : 0 < K) (k : Fin D.ds.length)
    (hi : k.val + 1 < 2 ^ 64) (hw : (D.ds.get k).entry.work < 256)
    (hs : (D.ds.get k).kind = .sealed) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true) :
    (famE P dd K V back g (.fb .link) ⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩ :
        (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (_root_.Fmt.blockW (hOfG g) P.l (bitsToBytes ρ) (k.val + 1)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
          (GPlain.old (b := (D.ds.get k).entry.work) z))
        (D.ds.get k).kind (D.ds.get k).entry.work
        (GPlain.nonce (b := (D.ds.get k).entry.work) z) 1) := by
  have ho : ordOf (D.ds.get k) = true := by
    unfold ordOf
    rw [decide_eq_true hs, Bool.or_true]
  have hb : (blockTo true K (Fin.last K)).val = 1 := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    show (if _h : (Fin.last (K' + 1)).val = K' + 1 then (⟨1, by omega⟩ : Fin (K' + 1 + 1))
      else if _h0 : (Fin.last (K' + 1)).val = 0 then ⟨0, by omega⟩
      else ⟨(Fin.last (K' + 1)).val + 1, by omega⟩).val = 1
    rw [dif_pos (Fin.val_last _)]
  have h := rowE_block P dd K V back g hK k hi hw ρ hρ rt z hok (Fin.last K)
  rw [ho, hb] at h
  exact h

/-- A round's test holds, if there are as many roots as root items and the nonce fits its word. -/
theorem okRound_true : ∀ (w : ℕ) (l : List _root_.Fmt.Item) (rt : List (Dig 256))
    (p : GPlain ℕ w (_root_.Run.PQ.PlainOf l)), rt.length = _root_.Fmt.countItem .root l →
    GPlain.nonce (b := w) p < 2 ^ 64 → PQ.okRound w l rt p = true
  | 0, l, rt, _, h, _ => PQ.toRoots_isSome l rt h
  | w + 1, l, rt, (p : _root_.Run.PQ.PlainOf l × ℕ), h, hn => by
      have hn' : p.2 < 2 ^ 64 := hn
      show ((PQ.toRoots l rt).isSome && decide (p.2 < 2 ^ 64)) = true
      rw [PQ.toRoots_isSome l rt h, decide_eq_true hn']
      rfl

end TypedOracleCompiler.Run.RowsE

namespace TypedOracleCompiler.Run.RowsE
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG
open TypedOracleCompiler.Run.PlainIn
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (dd : Sd)

/-- THE ROW LAW AT ONE WRITTEN ROUND (ChainFrom.lean's `PQ.RowAt`), at K + 1 blocks of a verifier's
message: the typed round and the format's index are k + 1; the head is in the later rounds' format;
the way of the round's own plain part is the page's `inE`. -/
theorem rowE_at (K : ℕ) (V : Leaves (Le D early e))
    (back : StrCode (AllPts 256 (K + 1) (Le D early e))) (g : Fam (rom 256))
    (hK : K + 1 < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256)
    (hs : (D.ds.get k).entry.work ≠ 0 ∨ (D.ds.get k).kind ≠ .sealed)
    (hr : (D.ds.get k).trees.length = _root_.Fmt.countItem .root (D.ds.get k).items) :
    PQ.RowAt (fun _ : Unit => Le D early e) D.C K (famE P dd (K + 1) V back g) .link (oB (g ())) P.l
      (fun ρ => .f2 none ρ) (D.ds.get k) (inE D early e k) (k.val + 1) (k.val + 1) :=
  fun ρ rt pl hρ hrt hno =>
    rowE_round P dd (K + 1) V back g hK (Nat.succ_pos K) k hi hw hs ρ hρ rt pl
      (okRound_true _ _ _ _ (hrt.trans hr) hno)

variable (K : ℕ) (V : Leaves (Le D early e)) (back : StrCode (AllPts 256 K (Le D early e)))
  (g : Fam (rom 256))

/-! ## Vertices and leaves -/

/-- A VERTEX, AS A VALUE: the library's vertex at the hash. -/
theorem rowE_vertex (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) :
    (famE P dd K V back g .node (l, r) : Dig 256) =
      bytesToDig (Id.run (_root_.Fmt.vertexW (m := Id) (hOfG g) P.cfg (bitsToBytes l)
        (bitsToBytes r))) :=
  node_of_code (pageE P dd K V back) g (l, r) 166 0 0 P.cfg _ (by decide)
    (implE_vertex P dd K V back l r hl hr 0)

/-- A LEAF, AS A VALUE, where the code of leaves writes the string of a call. -/
theorem rowE_leaf (q : LeafIn (Le D early e)) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162)
    (h : V.lf.put q = some (bytesToBits (_root_.Fmt.oStr 0 n t i st bs))) :
    (famE P dd K V back g .leaf q : Dig 256) = bytesToDig (hOfG g n t i st bs) :=
  leaf_of_code (pageE P dd K V back) g q n t i st bs hn (implE_leaf P dd K V back q _ h 0)

/-! ## The seeds' chain -/

/-- THE LAW ON AN IMPLEMENTATION AT THE SEEDS' TAG HOLDS AT THE ENTRY's PAGE, at the name "the
root's bytes, then the pins' fixed bytes", for every root. -/
theorem seedsPageE (hK : K < 2 ^ 48) (cm : Dig 256) (hr : P.rest.size < 2 ^ 32) :
    SeedsPage (implE P dd K V back) .test (digToBytes cm ++ P.rest)
      (q0S (L := Le D early e) .test D.C e _ id [cm]) (q1S (L := Le D early e) .test D.C e _ id) :=
  seedsPage_of_codes (pageE P dd K V back) .test _ _ _ (implE_seedFirst P dd K V back cm hr)
    fun ρ i => by
      have h := implE_seedRound P dd K V back hK (List.ofFn ρ) List.length_ofFn i.castSucc
      rw [SeedRound.blockNo_cast] at h
      exact h

/-- At a key's name, if the key's root is cm's bytes and the pins' fixed bytes are those of the
key's shape and configuration. -/
theorem seedsPageE_key (hK : K < 2 ^ 48) (cm : Dig 256) (k : OnBytes.Tie.IdKey)
    (hroot : k.2.2.root = digToBytes cm)
    (hrest : P.rest = FirstName.restOf k.2.1 k.1.code.logN k.1.code.ell k.1.code.r k.1.v
      k.1.answers k.1.saltBytes) (hr : P.rest.size < 2 ^ 32) :
    SeedsPage (implE P dd K V back) .test (OnBytes.Key.nameOf k.1 k.2.1 k.2.2)
      (q0S (L := Le D early e) .test D.C e _ id [cm])
          (q1S (L := Le D early e) .test D.C e _ id) := by
  have h := seedsPageE P dd K V back hK cm hr
  rw [nameOf_tableName, FirstName.tableName_eq, hroot, ← hrest]
  exact h

end TypedOracleCompiler.Run.RowsE
