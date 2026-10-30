-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/TieIdBytes.lean: small facts on bytes, digits and bits for the step on the
commitment ID at every hash function.

A user types the commitment ID as 64 digits of base 16. The typed side has 256 bits. The digest of
the three public files is one call of the format's hash. Here: how the program reads the digits that
the format writes; that 256 bits come back from their 32 bytes; and that, with any function g in the
place of the hash, the twin's digest of the public files is g's answer at one written string.

Main names (namespace `OnBytes.K.Arm`):
  `bytesToDig_digToBytes`: 256 bits, as 32 bytes, as 256 bits, are themselves.
  `idAsked_ofList`: the program reads 64 signs, each a digit or a letter from a to f, as themselves.
  `idAsked_hex`: so it reads the digits that the format writes for 32 bytes.
  `commit_of_asked`: if the program reads the digits of the 256 bits cm as the digits of the bytes
    b, then b, as 256 bits, is cm.
  `digest_at`: at every function g, the twin's digest of three public files over g, as 256 bits, is
    g's answer at `s0Of` of these files (Johnson/Top/Pub/PubStrings.lean): the first question of the
    public algorithm `pub2` (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean).
What is proved and how. `hexDigits_low` is 256 cases, evaluated in Lean's kernel, as `unByte_hex`
(OnBytes/Tie/IdKey.lean) is. `idAsked_ofList` follows the proof of `idAsked_idem`
(OnBytes/K/Oracle/SpineOptions.lean). `digest_at` holds by unfolding and the first fact.
What is not claimed. Nothing on a run of a program; no probability; nothing on soundness.
`digest_at` is an equation between values: that a program asks that string in a run is not said. It
speaks of the format's hash over a function g, at files of every length: the format's own hash is
that form at its own oracle only within the format's bound on lengths (`Fmt.HO_oracle` asks
`Fmt.hDom`), which is not asked here. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.SpineOptions
import OnBytes.Tie.IdKey
import OnBytes.ChecksWithHashAsArgument.M.Params.Configure
import Johnson.Top.IdKeyCode
import Johnson.Top.Pub.PubStrings
import Run.CodingPage160
import Run.OCompM

set_option autoImplicit false

namespace OnBytes.K.Arm

open _root_.Run (bytesToDig digToBytes oB)
open _root_.Iop (Dig)
open OnBytes.Model.Verify (idAsked)
open OnBytes.K.Arm.Pub (s0Of)

/-- 256 bits, as 32 bytes, as 256 bits, are themselves. -/
theorem bytesToDig_digToBytes (d : Dig 256) : bytesToDig (digToBytes d) = d :=
  VerifiableInference.Rec.digToBytes_injective
    (_root_.Run.digToBytes_bytesToDig _ (_root_.Run.size_digToBytes d))

/-- A digit, or a letter from a to f. -/
def lowB (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The two digits that the format writes for a byte are such signs: 256 cases, evaluated in Lean's
kernel. -/
theorem hexDigits_low (x : UInt8) :
    lowB (Fmt.hexDigit (x >>> 4)) = true ∧ lowB (Fmt.hexDigit (x &&& 15)) = true := by
  have key : ∀ n, n < 256 → lowB (Fmt.hexDigit (UInt8.ofNat n >>> 4)) = true ∧
      lowB (Fmt.hexDigit (UInt8.ofNat n &&& 15)) = true := by decide +kernel
  have h := key x.toNat x.toNat_lt
  rwa [UInt8.ofNat_toNat] at h

/-- The digits of a list of bytes, as `Fmt.hex` writes them. -/
def hexL (l : List UInt8) : List Char :=
  l.flatMap fun (x : UInt8) => [Fmt.hexDigit (x >>> 4), Fmt.hexDigit (x &&& 15)]

/-- Two digits a byte. -/
theorem length_hexL : ∀ l : List UInt8, (hexL l).length = 2 * l.length
  | [] => rfl
  | x :: l => by
    have ih := length_hexL l
    unfold hexL at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

/-- Each is a digit or a letter from a to f. -/
theorem low_hexL (l : List UInt8) (c : Char) (h : c ∈ hexL l) : lowB c = true := by
  unfold hexL at h
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 h
  rcases List.mem_cons.1 hx with rfl | hx
  · exact (hexDigits_low x).1
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact (hexDigits_low x).2
    · cases hx

/-- The program reads 64 signs, each a digit or a letter from a to f, as themselves. -/
theorem idAsked_ofList (L : List Char) (hl : L.length = 64) (hd : ∀ c ∈ L, lowB c = true) :
    idAsked (String.ofList L) = some (String.ofList L) := by
  have hm : (L.map fun c => if ('A' ≤ c && c ≤ 'F') = true then c.toLower else c) = L := by
    conv => rhs; rw [← List.map_id L]
    refine List.map_congr_left fun c hc => ?_
    rw [OnBytes.K.Oracle.lower_keeps c (hd c hc)]
    rfl
  have hc : (L.length == OnBytes.Model.Stages.hexW &&
      L.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true := by
    rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    exact ⟨hl, hd⟩
  unfold idAsked
  dsimp only
  rw [String.toList_ofList, hm]
  rw [if_pos hc]

/-- The program reads the digits that the format writes for 32 bytes as themselves. -/
theorem idAsked_hex (b : ByteArray) (hb : b.size = 32) :
    idAsked (Fmt.hex b) = some (Fmt.hex b) := by
  have hl : (hexL b.data.toList).length = 64 := by
    rw [length_hexL, Array.length_toList, ByteArray.size_data, hb]
  exact idAsked_ofList (hexL b.data.toList) hl (low_hexL _)

/-- If the program reads the digits of the 256 bits cm as the digits of the bytes b, then b, as 256
bits, is cm. -/
theorem commit_of_asked (cm : Dig 256) (b : ByteArray)
    (h : idAsked (Fmt.hex (digToBytes cm)) = some (Fmt.hex b)) : bytesToDig b = cm := by
  rw [idAsked_hex _ (_root_.Run.size_digToBytes cm)] at h
  rw [← OnBytes.Tie.hex_inj (Option.some.inj h), bytesToDig_digToBytes]

/-- **At every function g the twin's digest of three public files over g, as 256 bits, is g's answer
at one written string.** -/
theorem digest_at (g : ZKCP.Oracle 256) (pol lay KL : ByteArray) :
    bytesToDig (OnBytes.TwoPort.M.Params.configurationDigest (m := Id) (Fmt.HO (oB g))
      [pol, lay, KL]) = g (s0Of pol lay KL) := by
  unfold OnBytes.TwoPort.M.Params.configurationDigest Fmt.configDigestW Fmt.HO
  rw [if_neg (by decide)]
  exact bytesToDig_digToBytes _

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.bytesToDig_digToBytes
#print axioms OnBytes.K.Arm.idAsked_hex
#print axioms OnBytes.K.Arm.commit_of_asked
#print axioms OnBytes.K.Arm.digest_at
