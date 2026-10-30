-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/KeyPageRounds.lean: at the page of a key's judge, the typed query of EVERY written
round of the three chains, at every block, has `Fmt.oStr` of one half of a hash under 162, on the
sibling's spelling of the round's message (`PQ.bytesL`) and then the format's tail (`Fmt.tail`): the
condition of `KeyPage.implK_round` is met.

`KeyPage.implK_round` (OnBytes/TypedOracleCompiler/Run/KeyPage.lean) asks that `rcG` writes, at the round, the bits
of a message's bytes and of a nonce's word. OnBytes/TypedOracleCompiler/Run/PlainIn.lean says that `rcG` at a
written round's own plain part writes what the round's own code `PQ.pRound` writes. The sibling says
what that is: where the roots fit the round's items and the nonce fits a word (`PQ.okRound`,
OnBytes/TypedOracleCompiler/Run/PageQFits.lean) it writes (`pRound_some`), and what it writes is the bits of
`bytesL` of the roots' bytes, the items and the plain part, then of the nonce's word (`pRound_fit`,
OnBytes/TypedOracleCompiler/Run/PlanQSpell.lean). This file joins the three. The sibling is a second form of
the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `pRound_eq`: `PQ.pRound`'s string, as an equation, under `PQ.okRound`;
 - `roundBytes_tail`: the library's `roundBytes` is the message and then the format's `Fmt.tail`;
 - `kind_lt`: a kind's number is below 256;
 - `implK_roundAt`: at a typed round i where the written round d stands (`rdAt G i = some d`), for a
   plain part at which `rcG` writes what d's own code writes at z: the page's string at every block;
 - `implK_round₁`, `implK_round₂`, `implK_round₃`: so at round k of the first, second, third
   stretch, at the plain part `inR₁`, `inR₂`, `inR₃` of z: the hash under 162 with the pins' first,
   second, third label and the index k + 1. Asked each time: `okRound`; work below 256; the index
   below 2 ^ 64; K below 2 ^ 48; a chain value of 256 bits.

Main theorems: `pRound_eq`, `roundBytes_tail`, `implK_roundAt`, `implK_round₁`, `implK_round₂`,
`implK_round₃`.

Not claimed. b, the block's number in the row, is by the order `KeyRanges.ordAt`: at a sealed round
without work the typed tail is the row's block 1 and the typed block 0 the row's block 0: what that
costs is said in OnBytes/TypedOracleCompiler/Run/Chain162G.lean's head. At a sealed round WITH work, which the
format page does not admit (R5.3: a seal has w = 0; nothing here asks that rule of G's rounds), the
seal would be the row's block 2 and the typed tail block 1: the equations would hold, but the next
seam's typed query would then hold the chain's next value, not the seal, and `KeyPage.implK_173`,
`implK_first3` would not be the format's calls (`KeyRanges.SealsPlain` shuts such a round out).
`Fmt.oStr` is total: that a call lies in the format's domain is not asked. That `PQ.bytesL` is the
message that a program's reader hashes is tied by no theorem. `PQ.okRound` at a chain's own query
wants as many roots as the round's items name: that a round's list of trees has that length is asked
of G by no file. That a chain of the compiled verifier asks these queries. Nothing on soundness. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.KeyPage
import OnBytes.TypedOracleCompiler.Run.PageQFits

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.KeyPageRounds
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.KeyFb TypedOracleCompiler.Run.KeyPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PlainAt
open TypedOracleCompiler.Run.PlainIn TypedOracleCompiler.Run.KeyRanges
open TypedOracleCompiler.Run.FirstAnswers (T3)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- What a written round's own code writes, as an equation: the bits of the message's bytes,
then of the nonce's word; where the roots fit the items and the nonce fits a word. -/
theorem pRound_eq (w : ℕ) (l : List _root_.Fmt.Item) (rt : List (Dig 256))
    (p : GPlain ℕ w (PlainOf l))
    (h : PQ.okRound w l rt p = true) :
    (PQ.pRound w l).put (rt, p) =
      some (bytesToBits (PQ.bytesL (rt.map digToBytes) l (GPlain.old (b := w) p)) ++
        bytesToBits (_root_.Fmt.u64n (GPlain.nonce (b := w) p))) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (PQ.pRound_some w l rt p h)
  rw [hs, PQ.pRound_fit w l rt p s hs]

/-- The library's `roundBytes` is the message and then the format's tail (Fmt/Rules5.lean: the
word of kind, work and call; the nonce's word). -/
theorem roundBytes_tail (msg : ByteArray) (k : _root_.Fmt.Kind) (w j n : ℕ) :
    roundBytes msg k.num w j n = msg ++ _root_.Fmt.tail k w n j := by
  unfold roundBytes _root_.Fmt.tail
  rw [ByteArray.append_assoc]

/-- A kind's number is below 256. -/
theorem kind_lt (k : _root_.Fmt.Kind) : k.num < 256 := by
  cases k <;> decide

variable {Sd : Type} {G : Stretches}
  {dec : List T3 × Sd → PQ.View → PQ.View → PQ.View → Bool} {d : Sd} {e : _root_.Fmt.Entry}
  (P : Pins G dec d e) (K : ℕ) (V : Leaves (Lk G dec d e))
  (back : StrCode (AllPts 256 K (Lk G dec d e)))

/-- The order of blocks at a written round: the typed tail is the row's block 1 where the round has
work or is sealed. -/
def ordOf (r : PQ.RD) : Bool := decide (r.entry.work ≠ 0) || decide (r.kind = .sealed)

/-- The page's string at a typed round where the written round r stands, for a plain part at
which `rcG` writes what r's own code writes at z. -/
theorem implK_roundAt (hK : K < 2 ^ 48) (i : ℕ) (r : PQ.RD) (hr : rdAt G i = some r)
    (hi : (threeOf G P.l₁ P.l₂ P.l₃).idx i < 2 ^ 64) (hw : r.entry.work < 256) (ρ : Bits)
    (hρ : ρ.length = 256) (rt : List (Dig 256)) (pl : PBa G.sh) (z : PlainD r)
    (hput : (rcG G i).put (rt, pl) = (PQ.pRound r.entry.work r.items).put (rt, z))
    (hok : PQ.okRound r.entry.work r.items rt z = true) (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .onl) ⟨i, .f2 none ρ, rt, pl⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordOf r) K j).val % 2)) 162
        ((threeOf G P.l₁ P.l₂ P.l₃).lab i) ((threeOf G P.l₁ P.l₂ P.l₃).idx i) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) r.items (GPlain.old (b := r.entry.work) z) ++
          _root_.Fmt.tail r.kind r.entry.work (GPlain.nonce (b := r.entry.work) z)
            ((blockTo (ordOf r) K j).val / 2))) := by
  have ek : kindAt G i = r.kind.num := by unfold kindAt; rw [hr]; rfl
  have ew : workAt G i = r.entry.work := by unfold workAt; rw [hr]; rfl
  have eo : ordAt G i = ordOf r := by unfold ordAt; rw [hr]; rfl
  have ho : (threeOf G P.l₁ P.l₂ P.l₃).on i = true := by rw [on_iff, hr]; rfl
  have h := implK_round P K V back hK i ho hi (by rw [ek]; exact kind_lt _) (by rw [ew]; exact hw)
    ρ hρ rt pl _ _ (hput.trans (pRound_eq _ _ rt z hok)) j
  rw [ek, ew, eo, roundBytes_tail] at h
  exact h

/-- Round k of the first chain: the hash under 162 with the first label and the index k + 1. -/
theorem implK_round₁ (hK : K < 2 ^ 48) (k : Fin G.ds₁.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (G.ds₁.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (G.ds₁.get k))
    (hok : PQ.okRound (G.ds₁.get k).entry.work (G.ds₁.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .onl) ⟨k.val + 1, .f2 none ρ, rt, inR₁ G k z⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordOf (G.ds₁.get k)) K j).val % 2)) 162
        P.l₁ (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (G.ds₁.get k).items
            (GPlain.old (b := (G.ds₁.get k).entry.work) z) ++
          _root_.Fmt.tail (G.ds₁.get k).kind (G.ds₁.get k).entry.work
            (GPlain.nonce (b := (G.ds₁.get k).entry.work) z)
            ((blockTo (ordOf (G.ds₁.get k)) K j).val / 2))) := by
  have hl := lab_idx₁ G P.l₁ P.l₂ P.l₃ k
  have h := implK_roundAt P K V back hK (k.val + 1) (G.ds₁.get k) (rdAt₁ G k)
    (by rw [hl.2]; exact hi) hw ρ hρ rt (inR₁ G k z) z (rcG_at₁ G k rt z) hok j
  rw [hl.1, hl.2] at h
  exact h

/-- Round k of the second chain: the hash under 162 with the second label and the index
k + 1. -/
theorem implK_round₂ (hK : K < 2 ^ 48) (k : Fin G.ds₂.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (G.ds₂.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (G.ds₂.get k))
    (hok : PQ.okRound (G.ds₂.get k).entry.work (G.ds₂.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .onl)
        ⟨G.ds₁.length + (k.val + 2) + 1, .f2 none ρ, rt, inR₂ G k z⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordOf (G.ds₂.get k)) K j).val % 2)) 162
        P.l₂ (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (G.ds₂.get k).items
            (GPlain.old (b := (G.ds₂.get k).entry.work) z) ++
          _root_.Fmt.tail (G.ds₂.get k).kind (G.ds₂.get k).entry.work
            (GPlain.nonce (b := (G.ds₂.get k).entry.work) z)
            ((blockTo (ordOf (G.ds₂.get k)) K j).val / 2))) := by
  have hl := lab_idx₂ G P.l₁ P.l₂ P.l₃ k
  have h := implK_roundAt P K V back hK _ (G.ds₂.get k) (rdAt₂ G k)
    (by rw [hl.2]; exact hi) hw ρ hρ rt (inR₂ G k z) z (rcG_at₂ G k rt z) hok j
  rw [hl.1, hl.2] at h
  exact h

/-- Round k of the third chain: the hash under 162 with the third label and the index k + 1. -/
theorem implK_round₃ (hK : K < 2 ^ 48) (k : Fin G.ds₃.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (G.ds₃.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (G.ds₃.get k))
    (hok : PQ.okRound (G.ds₃.get k).entry.work (G.ds₃.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (implK P K V back).code (.fb .onl)
        ⟨G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1, .f2 none ρ, rt, inR₃ G k z⟩ j =
      bytesToBits (_root_.Fmt.oStr (UInt8.ofNat ((blockTo (ordOf (G.ds₃.get k)) K j).val % 2)) 162
        P.l₃ (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (G.ds₃.get k).items
            (GPlain.old (b := (G.ds₃.get k).entry.work) z) ++
          _root_.Fmt.tail (G.ds₃.get k).kind (G.ds₃.get k).entry.work
            (GPlain.nonce (b := (G.ds₃.get k).entry.work) z)
            ((blockTo (ordOf (G.ds₃.get k)) K j).val / 2))) := by
  have hl := lab_idx₃ G P.l₁ P.l₂ P.l₃ k
  have h := implK_roundAt P K V back hK _ (G.ds₃.get k) (rdAt₃ G k)
    (by rw [hl.2]; exact hi) hw ρ hρ rt (inR₃ G k z) z (rcG_at₃ G k rt z) hok j
  rw [hl.1, hl.2] at h
  exact h

end TypedOracleCompiler.Run.KeyPageRounds
