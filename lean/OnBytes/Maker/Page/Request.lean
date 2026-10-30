-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Request.lean: the rows of the page (OnBytes/Maker/Page/Frame.lean) for the tree
that binds a batch's requests: what the typed oracle functions `gJ P O` answer at a vertex and at a
leaf of that tree; and the format's hash over a function on strings, in the library's own name.

A leaf query of the request tree is typed as one string of bits: the 256 bits of the slot's closing
value, and behind them `rsOf d place salt`: the salt's bits and one word, the leaf's index
2^d + place.

Main names.
  `hO_eq_HO`: `hO O` (OnBytes/Maker/Page/Trees.lean) is the library's `Fmt.HO O` at every number but
    162. `nodeIs_HO`: `NodeIs (gJ P O) (Fmt.HO O) P.cfg`.
  `ofFn_bytesToDig`: the bits of a digest made of 32 bytes are these bytes' bits.
  `words32`: 32 bytes, cut into four words and written again, are these bytes.
  `gJ_rnode`, `rnodeAt_gJ`: the answer at a vertex, for every O: the call 178 at the page's cfg.
  `rsOf`, `rleafCall_at`, `gJ_rleaf`: the call and the answer at a leaf, for every O: the call 173.
  `dom178`, `dom173`: these two calls lie in the domain of the format's hash (`Fmt.hDom`).
  `nodeCoded_oracle`, `leafCoded_oracle`: `NodeCoded` and `LeafCoded`
    (OnBytes/TypedOracleCompiler/Joined/K/Request.lean) at `gJ P Fmt.oracle`, the format's realised oracle.

What the last two ask. The page's cfg has 32 bytes. For the leaves: the page's `sR` is a salt's
length as the format has it (`Fmt.saltLenOK`: 40, 48, 56 or 64 bytes), and the tree's depth is below
63.

Limits: identities of computations. `gJ P O` is a function of the typed query, no one-to-one coding.
The realised oracle answers as the format's hash inside that hash's domain alone (`Fmt.HO_oracle`):
so the last two are said at the calls of these two rows, which lie in it. One page has one cfg.
Nothing on soundness.


-/
import OnBytes.Maker.Page.Trees
import OnBytes.TypedOracleCompiler.Joined.K.Request
import Fmt.Rules1Only
import Fmt.Rules5Fast
import Run.OpenDomProofs

set_option autoImplicit false

namespace OnBytes.Maker.Page
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- `hO O` is the library's hash over a function, at every number but 162. -/
theorem hO_eq_HO (O : ByteArray → ByteArray) (n place ix : ℕ) (start bytes : ByteArray)
    (hn : n ≠ 162) : hO O n place ix start bytes = Fmt.HO O n place ix start bytes := by
  unfold hO Fmt.HO
  rw [if_neg hn]

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The vertices, at the library's hash over O. -/
theorem nodeIs_HO (P : PageJ L K) (O : ByteArray → ByteArray) :
    NodeIs (gJ P O) (Fmt.HO O) P.cfg := by
  intro l r hl hr
  rw [nodeIs_gJ P O l r hl hr, hO_eq_HO O 166 0 0 _ _ (by decide)]

/-- The bits of a digest made of 32 bytes are these bytes' bits. -/
theorem ofFn_bytesToDig (b : ByteArray) (h : b.size = 32) :
    List.ofFn (bytesToDig b) = bytesToBits b := by
  rw [TieTree.bytesToDig_eq]
  exact ofFn_digOf _ (by rw [length_bytesToBits, h])

/-- 32 bytes, cut into four words and written again. -/
theorem words32 (c : ByteArray) (h : c.size = 32) :
    Fmt.colBytes ((List.range 4).map fun i => Fmt.wordAt c (8 * i)) = c := by
  have e : List.range 4 = [0, 1, 2, 3] := rfl
  unfold Fmt.colBytes
  rw [e]
  simp only [List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil]
  rw [Fmt.u64_wordAt c (8 * 0) (by omega), Fmt.u64_wordAt c (8 * 1) (by omega),
    Fmt.u64_wordAt c (8 * 2) (by omega), Fmt.u64_wordAt c (8 * 3) (by omega)]
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_empty,
    Array.append_empty, Array.extract_append_extract]
  norm_num
  exact Or.inr (le_of_eq h)

/-! ## The vertices of the request tree -/

theorem gJ_rnode (P : PageJ L K) (O : ByteArray → ByteArray) (q : Bits × Bits) :
    gJ P O OracleName.rnode q = bytesToDig (hO O 178 0 0 P.cfg (bitsToBytes q.1 ++ bitsToBytes q.2)) := rfl

theorem rnodeAt_gJ (P : PageJ L K) (O : ByteArray → ByteArray) (u v : Dig 256) :
    TypedOracleCompiler.Joined.rnodeAt (gJ P O) u v =
      bytesToDig (hO O 178 0 0 P.cfg (digToBytes u ++ digToBytes v)) := by
  unfold TypedOracleCompiler.Joined.rnodeAt digToBytes
  generalize List.ofFn u = a
  generalize List.ofFn v = b
  exact gJ_rnode P O (a, b)

/-- A vertex of the request tree lies in the hash's domain (as `Run.domVertex`,
Run/OpenDomProofs.lean, under the number 178). -/
theorem dom178 (cfg l r : ByteArray) (hc : cfg.size = 32) (hl : l.size = 32) (hr : r.size = 32) :
    Fmt.hDom 178 0 0 cfg (l ++ r) = true := by
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    ByteArray.size_append, hl, hr]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, Or.inr trivial⟩, by decide⟩, by decide⟩, hc⟩,
      Or.inl (by decide)⟩,
    Fmt.leafOK_other _ _ _ rfl⟩

/-- `NodeCoded` at the page and the format's realised oracle. -/
theorem nodeCoded_oracle (P : PageJ L K) (hc : P.cfg.size = 32) :
    TypedOracleCompiler.Joined.K.NodeCoded (gJ P Fmt.oracle) P.cfg := by
  intro x y hx hy
  rw [rnodeAt_gJ, digToBytes_bytesToDig x hx, digToBytes_bytesToDig y hy,
    hO_eq_HO Fmt.oracle 178 0 0 _ _ (by decide),
    Fmt.HO_oracle _ _ _ _ _ (dom178 P.cfg x y hc hx hy)]
  rfl

/-! ## The leaves of the request tree -/

/-- What stands behind the closing value in a typed leaf query: the salt's bits, and the word of the
leaf's index. -/
def rsOf (d place : ℕ) (salt : ByteArray) : Bits :=
  bytesToBits salt ++ bytesToBits (Fmt.u64n (2 ^ d + place))

/-- The page's call at a leaf of the request tree. -/
theorem rleafCall_at (cfg : ByteArray) (d place : ℕ) (closing salt : ByteArray)
    (hc : closing.size = 32) (hi : 2 ^ d + place < 2 ^ 64) :
    rleafCall cfg salt.size (List.ofFn (bytesToDig closing) ++ rsOf d place salt) =
      some ⟨0, 173, Fmt.leafPlace 0 4 (salt.size / 8), 2 ^ d + place, cfg, closing ++ salt⟩ := by
  have lw : (bytesToBits (Fmt.u64n (2 ^ d + place))).length = 64 := by
    rw [length_bytesToBits]; rfl
  have e : List.ofFn (bytesToDig closing) ++ rsOf d place salt =
      bytesToBits (closing ++ salt) ++ bytesToBits (Fmt.u64n (2 ^ d + place)) := by
    unfold rsOf
    rw [ofFn_bytesToDig closing hc, bytesToBits_append, List.append_assoc]
  have l1 : (bytesToBits (closing ++ salt)).length = 256 + 8 * salt.size := by
    rw [length_bytesToBits, ByteArray.size_append, hc]
    omega
  rw [e]
  unfold rleafCall
  rw [if_pos (by rw [List.length_append, l1, lw]), List.drop_left' l1, List.take_left' l1,
    bitsToBytes_bytesToBits, bitsToBytes_bytesToBits]
  have w := wordOf_u64n (2 ^ d + place) hi
  unfold wordOf at w
  rw [bitsToBytes_bytesToBits] at w
  rw [w]

/-- What `gJ P O` answers there. -/
theorem gJ_rleaf (P : PageJ L K) (O : ByteArray → ByteArray) (d place : ℕ)
    (closing salt : ByteArray) (hc : closing.size = 32) (hs : salt.size = P.sR)
    (hi : 2 ^ d + place < 2 ^ 64) :
    gJ P O OracleName.rleaf (List.ofFn (bytesToDig closing) ++ rsOf d place salt) =
      bytesToDig (hO O 173 (Fmt.leafPlace 0 4 (salt.size / 8)) (2 ^ d + place) P.cfg
        (closing ++ salt)) := by
  show ansJ O ((rleafCall P.cfg P.sR _).map strOf) = _
  rw [← hs, rleafCall_at P.cfg d place closing salt hc hi]
  rfl

/-- A leaf under the number 173, as `Fmt.leafW` spells it at the tree's number 0, lies in the hash's
domain (as `Run.domLeaf`, Run/OpenDomProofs.lean, which has the numbers 164 and 174). -/
theorem dom173 (idx : ℕ) (start : ByteArray) (col : List UInt64) (salt : ByteArray)
    (hi : idx < 2 ^ 63) (hs : start.size = 32) (hW1 : 1 ≤ col.length) (hW : col.length < 2 ^ 24)
    (hsalt : Fmt.saltLenOK salt.size = true) :
    Fmt.hDom 173 (Fmt.leafPlace 0 col.length (salt.size / 8)) idx start
      (Fmt.leafBytes col salt) = true := by
  simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsalt
  have ht : (0 : ℕ) < 2 ^ 16 := by decide
  have h8 : 8 * (salt.size / 8) = salt.size := by omega
  have hb : (Fmt.leafBytes col salt).size ≤ 2 ^ 32 - 144 := by
    have := size_leafBytes col salt; omega
  have hlt : Fmt.leafPlace 0 col.length (salt.size / 8) < 2 ^ 48 :=
    Fmt.leafPlace_lt _ _ _ ht hW (by omega)
  have hok : ∀ n, (!(n == 173 || n == 174) || (0 : ℕ) == 0) = true →
      Fmt.leafOK n (Fmt.leafPlace 0 col.length (salt.size / 8)) (Fmt.leafBytes col salt) =
        true := by
    intro n hn
    unfold Fmt.leafOK
    rw [Fmt.placeW_leafPlace _ _ _ ht hW, Fmt.placeS_leafPlace _ _ _ ht hW,
      Fmt.placeTree_leafPlace _ _ _ ht, h8, hn]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
    refine Or.inr ⟨⟨⟨⟨hW1, by omega⟩, by omega⟩, size_leafBytes' col salt⟩, ?_⟩
    have := Fmt.extract_mid (Fmt.colBytes col)
      (Fmt.zeroBytes (Fmt.fillLen col.length salt.size)) salt
    rw [size_colBytes, Fmt.size_zeros] at this
    exact congrArg ByteArray.data this
  simp only [Fmt.hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, hlt⟩, Or.inl (by decide)⟩, ?_⟩, hb⟩, hs⟩, Or.inl (by decide)⟩,
    hok 173 rfl⟩
  simp only [Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨⟨hi, Or.inl (by decide)⟩, Or.inl (by decide)⟩

/-- `LeafCoded` at the page and the format's realised oracle. -/
theorem leafCoded_oracle (P : PageJ L K) (d : ℕ) (hd : d < 63) (hc : P.cfg.size = 32)
    (hR : Fmt.saltLenOK P.sR = true) :
    TypedOracleCompiler.Joined.K.LeafCoded (gJ P Fmt.oracle) d P.cfg P.sR (rsOf d) := by
  intro place closing salt hp hcl hs
  have h1 : (2 : ℕ) ^ d ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) (by omega)
  have hR' : Fmt.saltLenOK salt.size = true := by rw [hs]; exact hR
  have hle : salt.size ≤ 64 := by
    simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hR'
    exact hR'.2
  have l4 : ((List.range 4).map fun i => Fmt.wordAt closing (8 * i)).length = 4 := rfl
  have hf : Fmt.fillLen 4 salt.size = 0 := by
    unfold Fmt.fillLen
    rw [if_pos (by omega)]
  have z : Fmt.zeroBytes 0 = ByteArray.empty := rfl
  have eb : closing ++ salt =
      Fmt.leafBytes ((List.range 4).map fun i => Fmt.wordAt closing (8 * i)) salt := by
    unfold Fmt.leafBytes
    rw [words32 closing hcl, l4, hf, z, ByteArray.append_empty]
  have hdm := dom173 (2 ^ d + place) P.cfg ((List.range 4).map fun i => Fmt.wordAt closing (8 * i))
    salt (by omega) hc (by rw [l4]; decide) (by rw [l4]; decide) hR'
  rw [l4] at hdm
  rw [gJ_rleaf P Fmt.oracle d place closing salt hcl hs (by omega), eb,
    hO_eq_HO Fmt.oracle 173 _ _ _ _ (by decide), Fmt.HO_oracle _ _ _ _ _ hdm]
  rfl

end OnBytes.Maker.Page
