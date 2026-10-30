-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ChainRow.lean: under the hypotheses below, the typed answer to a round's chain query is the
format page's row of blocks of that round. For a function O on the format's strings, the answer is
at the typed oracle functions that O induces, and the row is at the hash over O: generic in all
data.

Theorems and proofs. The file is about the hash chain from which a verifier's messages are drawn.
The typed answer to a chain query has K blocks of 256 bits and the chain value; `famP`
(Run/CodingFnThin.lean) gives it, `famB` gives it as bytes. The row of blocks of a round is
`Fmt.blockW` (Fmt/Rules5Row.lean): block b is half b mod 2 of call b div 2. `blockNo w K j`
(Run/CodingFn.lean) says which block of the row the typed block j is; w is the round's number of
bits of work, and typed block K is the chain value.

The statements on `famB` and `famP` hold for every O whose answers have 32 bytes (`hO`), every
interface, spellings D (`PageD`, Run/CodingFn.lean: what the format hashes for typed data), number
of blocks K, round i + 1. The chain query is ⟨i + 1, .f2 none ρ, rt, pl⟩, put to the chain oracle
`.fb tg` of the tag tg for which D is given. `kind` (`Fmt.Kind`, Fmt/Plan.lean: what a round's
verifier message consists of) has the number D.kind (i + 1) (`hk`).

The page: an edition not in this repository (R5.2, R5.4); its section 5 stands in a second edition,
whose list of changed lines has one further rule there (R5.7) and changes neither; both have one and
the same text at the other editions compared by program; not held against the page that ships.

Main names:
  `blockW_HO`: a block of the page's row at the hash over O (Fmt/Rules23.lean: `HO`).
  `blockNo_last`, `blockNo_test`, `blockNo_msg0`, `blockNo_msgW`, `blockNo_le`: where the typed
    blocks stand in the page's row: the chain value at (first block of the verifier's message) - 1.
  `famB_row`, `famB_fetch`: the typed blocks as bytes.
  `famP_row`: the typed answer of `famP`, as bytes.

Notation:
  `Lf`: the interface behind a function of `Unit` (why: Run/CodingFnThin.lean, the head);
  `tg`: which compiled protocol: `test`, `link` or `onl` (`Tag`, Compile/Oracles.lean);
  `⟨i + 1, .f2 none ρ, rt, pl⟩`: a chain query's fields `round`, `head`, `rt`, `plain` (`FbIn`,
    Compile/Batch/Oracles.lean);
  `.f2 xl ρ`: a `Head`'s format where this round and the one before are local (`Head.f2`);
  `xl` (here `none`): the whole instance in the round `BatchProtocol.late`, nothing in every other round;
  `ρ`: the chain's value when i rounds are done, as bits (`Chain.rho`, Fmt/Rules5.lean);
  `rt`: the query's root, none if the component has no tree (`FbIn.rt`);
  `pl`: the plain part of one component of a round's prover message (`PlainPart`).

Limits: this file says nothing on round 0. It says nothing on the test bits and the draw:
Run/PageIsChain.lean. It says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFnThin
import Fmt.Rules5Row
import Fmt.Rules1Laws
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

theorem extract_l (x y : ByteArray) (n : ℕ) (h : x.size = n) : (x ++ y).extract 0 n = x := by
  have e := _root_.Fmt.extract_mid ByteArray.empty x y
  rw [ByteArray.empty_append] at e
  subst h
  simpa using e

theorem extract_r (x y : ByteArray) (n m : ℕ) (h : x.size = n) (h' : n + y.size = m) :
    (x ++ y).extract n m = y := by
  have e := _root_.Fmt.extract_mid x y ByteArray.empty
  rw [ByteArray.append_empty] at e
  subst h
  subst h'
  exact e

/-- A block of the page's row, at the hash over a function O on the format's strings whose answers
have 32 bytes: O at the string of its half of its call. -/
theorem blockW_HO (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (lab : ℕ)
    (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind) (w nonce b : ℕ) :
    _root_.Fmt.blockW (_root_.Fmt.HO O) lab rho i msg kind w nonce b =
      O (_root_.Fmt.oStr (UInt8.ofNat (b % 2)) 162 lab i rho
          (msg ++ _root_.Fmt.tail kind w nonce (b / 2))) := by
  have e : _root_.Fmt.callW (m := Id) (_root_.Fmt.HO O) lab rho i msg kind w nonce (b / 2) =
      O (_root_.Fmt.oStr 0 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce (b / 2))) ++
        O (_root_.Fmt.oStr 1 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce (b / 2))) := rfl
  unfold _root_.Fmt.blockW
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [h]
    exact extract_l _ _ 32 (hO _)
  · rw [h]
    exact extract_r _ _ 32 64 (hO _) (by rw [hO])

theorem roundBytes_tail (msg : ByteArray) (kind : _root_.Fmt.Kind) (w c nonce : ℕ) :
    roundBytes msg kind.num w c nonce = msg ++ _root_.Fmt.tail kind w nonce c := by
  unfold roundBytes _root_.Fmt.tail
  rw [ByteArray.append_assoc]

/-! ## Where the typed blocks stand in the page's row -/

theorem blockNo_last (w K : ℕ) : blockNo w K (Fin.last K) = _root_.Fmt.firstBlock w - 1 := by
  unfold blockNo _root_.Fmt.firstBlock
  rw [if_pos (Fin.val_last K)]
  split <;> rfl

/-- without work: typed block k is block k of the verifier's message, for k < K -/
theorem blockNo_msg0 (K : ℕ) (k : Fin K) :
    blockNo 0 K k.castSucc = _root_.Fmt.firstBlock 0 + k.val := by
  unfold blockNo _root_.Fmt.firstBlock
  rw [if_neg (by simp; omega), if_pos rfl, if_pos rfl]
  simp
  omega

/-- with work (`hw`), if 0 < K (`hK`): typed block 0 is the test block -/
theorem blockNo_test (w K : ℕ) (hw : w ≠ 0) (hK : 0 < K) :
    blockNo w K (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) = 0 := by
  unfold blockNo
  rw [if_neg (by show ¬ 0 = K; omega), if_neg hw, if_pos rfl]

/-- with work (`hw`), if k + 1 < K (`hk`): typed block k + 1 is block k of the verifier's message -/
theorem blockNo_msgW (w K k : ℕ) (hw : w ≠ 0) (hk : k + 1 < K) :
    blockNo w K (⟨k + 1, by omega⟩ : Fin (K + 1)) = _root_.Fmt.firstBlock w + k := by
  unfold blockNo _root_.Fmt.firstBlock
  rw [if_neg (by show ¬ k + 1 = K; omega), if_neg hw,
    if_neg (by show ¬ k + 1 = 0; omega), if_neg hw]
  show k + 1 + 1 = 2 + k
  omega

theorem blockNo_le (w K : ℕ) (j : Fin (K + 1)) : blockNo w K j ≤ K + 1 := by
  unfold blockNo
  have := j.isLt
  split
  · split <;> omega
  · split
    · omega
    · split <;> omega

variable {I X : Type} (Lf : Unit → BatchProtocol I X) {tg : Tag}

/-- Under `hO` and `hk` (the head tells them), the typed blocks of a round's chain answer are the
page's blocks, at the places that `blockNo` names. -/
theorem famB_row (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (D : PageD (Lf ()) tg)
    (K : ℕ) (i : ℕ) (ρ : List Bool) (rt : Option (Dig 256))
    (pl : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg)) (kind : _root_.Fmt.Kind)
    (hk : kind.num = D.kind (i + 1)) (j : Fin (K + 1)) :
    (famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg)).getD
        j.val ByteArray.empty =
      _root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
        (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1))
        (D.nonce (i + 1) pl) (blockNo (D.work (i + 1)) K j) := by
  have e : famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg) =
      Array.ofFn (n := K + 1) fun j =>
        bytesP O (fbCallP Lf D K (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg) j) := by
    simp only [famB, castTag_self]
    rfl
  rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt,
    blockW_HO O hO, ← roundBytes_tail, hk]
  rfl

/-- the same against what the page fetches, if it fetches more blocks than the place's number
(`hn`) -/
theorem famB_fetch (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (D : PageD (Lf ()) tg)
    (K : ℕ) (i : ℕ) (ρ : List Bool) (rt : Option (Dig 256))
    (pl : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg)) (kind : _root_.Fmt.Kind)
    (hk : kind.num = D.kind (i + 1)) (j : Fin (K + 1)) (n : ℕ)
    (hn : blockNo (D.work (i + 1)) K j < n) :
    (famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg)).getD
        j.val ByteArray.empty =
      (_root_.Fmt.fetchW (m := Id) (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
          (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl) n).getD
        (blockNo (D.work (i + 1)) K j) ByteArray.empty := by
  rw [famB_row Lf O hO D K i ρ rt pl kind hk j, _root_.Fmt.fetchW_getD _ _ _ _ _ _ _ _ n _ hn]

theorem size_blockW_HO (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32) (lab : ℕ)
    (rho : ByteArray) (i : ℕ) (msg : ByteArray) (kind : _root_.Fmt.Kind) (w nonce b : ℕ) :
    (_root_.Fmt.blockW (_root_.Fmt.HO O) lab rho i msg kind w nonce b).size = 32 := by
  rw [blockW_HO O hO]
  exact hO _

theorem digToBytes_digS (b : ByteArray) (h : b.size = 32) : digToBytes (digS b) = b := by
  rw [digS_eq]
  exact TieTree.dig_bytes b h

/-- Under `hO` and `hk` (the head tells them), the typed answer of `famP` to a round's chain query,
as bytes, is the page's row: the K blocks of the verifier's side, and the chain value. -/
theorem famP_row (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32)
    (D : PageD (Lf ()) tg) (K : ℕ) (i : ℕ) (ρ : List Bool)
    (rt : Option (Dig 256)) (pl : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg))
    (kind : _root_.Fmt.Kind) (hk : kind.num = D.kind (i + 1)) :
    (∀ k : Fin K,
      digToBytes ((famP Lf O D K (.fb tg)
            (⟨i + 1, .f2 none ρ, rt,
              pl⟩ : FbIn 256 (Lf ()) tg) : (Fin K → Dig 256) × Dig 256).1 k) =
        _root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
          (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
          (blockNo (D.work (i + 1)) K k.castSucc)) ∧
    digToBytes ((famP Lf O D K (.fb tg)
          (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg) : (Fin K → Dig 256) × Dig 256).2) =
      _root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
        (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
        (_root_.Fmt.firstBlock (D.work (i + 1)) - 1) := by
  refine ⟨fun k => ?_, ?_⟩
  · show digToBytes
        (digS ((famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg)).getD
            k.castSucc.val ByteArray.empty)) = _
    rw [famB_row Lf O hO D K i ρ rt pl kind hk k.castSucc]
    exact digToBytes_digS _ (size_blockW_HO O hO _ _ _ _ _ _ _ _)
  · show digToBytes
        (digS ((famB Lf O D K (.fb tg) (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 (Lf ()) tg)).getD
            (Fin.last K).val ByteArray.empty)) = _
    rw [famB_row Lf O hO D K i ρ rt pl kind hk (Fin.last K), blockNo_last]
    exact digToBytes_digS _ (size_blockW_HO O hO _ _ _ _ _ _ _ _)

end Run
