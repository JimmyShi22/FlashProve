-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/SeedWide.lean: the string of the seed's second typed query, for a number K of
blocks below 2^49. Two statements with proofs. No definition.
Why. `secondPS_put` (OnBytes/TypedOracleCompiler/Run/SeedRound.lean) and `fbSeeds_q1`
(OnBytes/TypedOracleCompiler/Run/SeedPoints.lean) say what string the code of the seed's second query writes, and
ask K < 2^48. The description's own number of blocks is known to be below 2^49 alone. What the code
itself tests is the number of the CALL, which is half the block's number, so the same strings are
written up to 2^49.
  `secondPS_put_wide`: `secondPS_put` with K < 2^49. Its proof is that theorem's own, line for line:
    the two steps that use the bound bear the weaker one.
  `fbSeeds_q1_wide`: `fbSeeds_q1` with K < 2^49, through it.
Limits. Equations between strings of this library's own terms. Nothing on any hash function, on any
program, on soundness, on a binding of the commitment (the opening form, `BindsWith`), on
correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.SeedPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Spell
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.PutSome
open TypedOracleCompiler.Run.SeedRound TypedOracleCompiler.Run.SeedPoints
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

section Round
variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (tg : Tag) (p1 : PlainPart (shapeOf L tg) (annOf L tg))
  (isP1 : PlainPart (shapeOf L tg) (annOf L tg) → Bool) (hp : ∀ p, isP1 p = true ↔ p = p1)

/-- `secondPS_put` for K below 2 ^ 49: what the code tests is the number of the CALL, which is half
the block's number. -/
theorem secondPS_put_wide (K : ℕ) (hK : K < 2 ^ 49) (ρ : List Bool) (hρ : ρ.length = 256)
    (j : Fin (K + 1)) :
    (secondPS L tg p1 isP1 hp K).put (⟨1, .f2 none ρ, [], p1⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes ρ)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)))) := by
  have hb : (blockTo (decide ((0 : ℕ) ≠ 0)) K j).val = blockNo 0 K j :=
    (blockNo_eq 0 K j (Or.inr rfl)).symm
  have hle := blockNo_le K j
  have ht : toTup (chainDS L tg p1 isP1 hp) K ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j) =
      some (decide (blockNo 0 K j % 2 = 1), ρ, 1, (([], p1), blockNo 0 K j / 2)) := by
    show some (decide ((blockTo (decide ((0 : ℕ) ≠ 0)) K j).val % 2 = 1), ρ, 0 + 1,
      (([], p1), (blockTo (decide ((0 : ℕ) ≠ 0)) K j).val / 2)) = _
    rw [hb]
  have hw : (pKwc _root_.Fmt.Kind.seeds.num 0).put (blockNo 0 K j / 2) =
      some (bytesToBits (_root_.Fmt.u64n (3 + 256 * 0 + 65536 * (blockNo 0 K j / 2)))) := by
    show (kwcTo 3 0 (blockNo 0 K j / 2)).bind pWord.put = _
    unfold kwcTo
    rw [if_pos ⟨by norm_num, by norm_num, by omega⟩]
    exact if_pos (by omega)
  have hr : (rcS L tg p1 isP1 hp 1).put ([], p1) = some word0 :=
    if_pos ⟨rfl, rfl, (hp p1).2 rfl⟩
  have hw1 : pWord.put 1 = some (bytesToBits (_root_.Fmt.u64n 1)) := by
    show (if (1 : ℕ) < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n 1)) else none) = _
    exact if_pos (by norm_num)
  have h5 := ins_some (rcS L tg p1 isP1 hp 1) (pKwc _root_.Fmt.Kind.seeds.num 0) 64 64
    (pKwc_len _ _) (rcS_len L tg p1 isP1 hp 1) ([], p1) (blockNo 0 K j / 2) _ _ hr hw
  have h4 := cons_some pWord 64 pWord_len
    (fun i => ((chainDS L tg p1 isP1 hp).rc i).ins
      (pKwc ((chainDS L tg p1 isP1 hp).kind i) ((chainDS L tg p1 isP1 hp).work i)) 64 64
      (pKwc_len _ _) ((chainDS L tg p1 isP1 hp).hrc i)) 1 (([], p1), blockNo 0 K j / 2) _ _
    hw1 h5
  have h3 :=
    pre_some (bytesToBits (_root_.Fmt.u64n (162 + 65536 * _root_.Fmt.recordLabel))) _ _ _ h4
  have h2 := cons_some (pBits 256) 256 (pBits_len 256) (fun _ => PCode.pre
    (bytesToBits (_root_.Fmt.u64n (162 + 65536 * _root_.Fmt.recordLabel))) _) ρ _ _ _
    (if_pos hρ : (pBits 256).put ρ = some ρ) h3
  have h1 := pre_some mid32 _ _ _ h2
  have h0 := cons_some pHalf 8 pHalf_len (fun _ => PCode.pre mid32 _)
    (decide (blockNo 0 K j % 2 = 1)) _ _ _ rfl h1
  have e0 : (secondPS L tg p1 isP1 hp K).put ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j) =
      (toTup (chainDS L tg p1 isP1 hp) K ((⟨1, .f2 none ρ, [], p1⟩ : FbIn 256 L tg), j)).bind
        (pTup (chainDS L tg p1 isP1 hp)).put := rfl
  rw [e0, ht]
  refine Eq.trans h0 (congrArg some ?_)
  rw [oStr64_bits _ _ _ _ _ (size_bitsToBytes ρ 32 hρ),
    bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩), ← half_bits]
  have hl : word0.length = 64 := by
    unfold word0
    rw [length_bytesToBits]
    rfl
  have et : bytesToBits (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)) =
      bytesToBits (_root_.Fmt.u64n (3 + 256 * 0 + 65536 * (blockNo 0 K j / 2))) ++ word0 := by
    rw [ByteArray.empty_append]
    unfold _root_.Fmt.tail word0
    rw [bytesToBits_append]
    rfl
  rw [et, hl, Nat.sub_self, List.take_zero, List.drop_zero, List.nil_append]

end Round

section Points
variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (p0 p1 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 isP1 : PlainPart (shapeOf L t) (annOf L t) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (K : ℕ)

/-- `fbSeeds_q1` for K below 2 ^ 49. -/
theorem fbSeeds_q1_wide (hK : K < 2 ^ 49) (v : Bits) (hv : v.length = 256) (j : Fin (K + 1)) :
    (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q1 L t p1 v, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)))) := by
  unfold fbSeeds
  rw [split_false _ _ (fun x : FbIn 256 L t × Fin (K + 1) => decide (x.1.round = 1)) _
    (q1 L t p1 v, j) rfl]
  show (sel1 L t p1 isP1 K _).bind _ = _
  rw [sel1_q1 L t p1 isP1 K ((hp1 p1).2 rfl) v j]
  exact secondPS_put_wide L t p1 isP1 hp1 K hK v hv j

end Points
end Bind.Spell

#print axioms Bind.Spell.secondPS_put_wide
#print axioms Bind.Spell.fbSeeds_q1_wide
