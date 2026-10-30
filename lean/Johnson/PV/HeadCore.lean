-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/HeadCore.lean: **THE TWO PUBLIC READINGS THROUGH THE O THAT IS HANDED IN**: THE CORE, FOR
  BOTH SIZES (general in the entry's typed ground G₀): turnAt HOLDS THE LENGTHS FIRST (turnAt_is:
  the same function); ALL ELSE WAS CUT OUT
  OF Johnson/PV/HeadSmall.lean (a text that is not part of this tree) TO THE LETTER,
  SO THAT RunPure CAN IMPORT IT: it imports no RunPure.
  cStr Z · parStr b          the two calls' strings, as bytes: Fmt.oStr 0 169 0 2 | 1 Fmt.zero32 …:
    s0Of | sParOf ARE THEIR BITS (cStr_bits | parStr_bits := rfl)
  **cThru O Z := O (cStr Z)** · **sevenThru O G₀ Z c := (par7 G₀ Z.pol Z.KL Z.lay c).map fun b => O
    (parStr b)**
  hashOf_oStr · **cThru_hash | sevenThru_hash**: bytesToDig of them IS hashOf O at the
    strings s0Of | sParOf. No premise.
  turnAt t O · eightStr      FOR CONTROLS: O with one bit of its answer turned at one string alone;
    the eight public strings in the order in which they are asked.
WHAT DOES NOT GO THROUGH O: the plan's data · what of par7's parameter bytes the planner makes by
  the format's SECOND HASH FUNCTION · sp's item (five of its groups are digests under that hash:
  another function than the oracle: no query as the format stands; a letter at most). No soundness.


-/
import OnBytes.K.Served
import Johnson.Top.PreThreePub
import Johnson.Top.Pub.PubMany
import Run.ParserHashProofs
import Johnson.Top.Fire.Code.FastFamProbe

set_option autoImplicit false

namespace PV.Head
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.K.Arm.Pub (par7 s0Of sParOf)
open _root_.Run (bytesToBits bytesToDig toBytes)

/-- The string of the call that hashes the three public files. -/
def cStr (Z : OnBytes.K.Pub) : ByteArray := Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [Z.pol,
    Z.lay, Z.KL])

/-- The string of the call that hashes a chain's parameter bytes. -/
def parStr (b : ByteArray) : ByteArray := Fmt.oStr 0 169 0 1 Fmt.zero32 b

theorem cStr_bits (Z : OnBytes.K.Pub) : bytesToBits (cStr Z) = s0Of Z.pol Z.lay Z.KL := rfl
theorem parStr_bits (b : ByteArray) : bytesToBits (parStr b) = sParOf b := rfl

/-- **The digest of the three public files, through O.** -/
def cThru (O : ByteArray → ByteArray) (Z : OnBytes.K.Pub) : ByteArray := O (cStr Z)

/-- **The seven further digests, through O**, at the bytes c. -/
def sevenThru (O : ByteArray → ByteArray) (G₀ : OnBytes.Tie.EntryGround) (Z : OnBytes.K.Pub) (c :
    ByteArray) : List ByteArray :=
  (par7 G₀ Z.pol Z.KL Z.lay c).map fun b => O (parStr b)

/-- At the bits of a call's string the hash function made of O answers O at the string. -/
theorem hashOf_oStr (O : ByteArray → ByteArray) (n t i : ℕ) (st bs : ByteArray) :
    hashOf O (bytesToBits (Fmt.oStr 0 n t i st bs)) = bytesToDig (O (Fmt.oStr 0 n t i st bs)) := by
  show bytesToDig (O (toBytes (bytesToBits (Fmt.oStr 0 n t i st bs)))) = _
  rw [_root_.Run.toBytes_plain _ (_root_.Run.plain_oStr 0 n t i st bs (Or.inl rfl)),
      _root_.Run.bitsToBytes_bytesToBits]

/-- **It is what the first public string is answered.** -/
theorem cThru_hash (O : ByteArray → ByteArray) (Z : OnBytes.K.Pub) :
    hashOf O (s0Of Z.pol Z.lay Z.KL) = bytesToDig (cThru O Z) := hashOf_oStr O 169 0 2 _ _

/-- **They are what the seven further public strings are answered.** -/
theorem sevenThru_hash (O : ByteArray → ByteArray) (G₀ : OnBytes.Tie.EntryGround) (Z :
    OnBytes.K.Pub) (c : ByteArray) :
    ((par7 G₀ Z.pol Z.KL Z.lay c).map sParOf).map (hashOf O) = (sevenThru O G₀ Z c).map bytesToDig
        := by
  unfold sevenThru
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun b _ => hashOf_oStr O 169 0 1 _ b

/-- FOR CONTROLS: O with one bit of its answer turned at the string t alone. (The lengths are held
  first: `.data` lays a byte string out as an array of boxed bytes at every call: at a t of a
  megabyte that cost every call of O a megabyte's walk.) -/
def turnAt (t : ByteArray) (O : ByteArray → ByteArray) (s : ByteArray) : ByteArray :=
  if s.size == t.size && s.data == t.data then
    let a := O s
    if 0 < a.size then a.set! 0 (a.get! 0 ^^^ 1) else a
  else O s

/-- It is the same function as without the test on the lengths: that test turns no value. -/
theorem turnAt_is (t : ByteArray) (O : ByteArray → ByteArray) (s : ByteArray) :
    turnAt t O s = if s.data == t.data then
      (let a := O s
       if 0 < a.size then a.set! 0 (a.get! 0 ^^^ 1) else a)
    else O s := by
  unfold turnAt
  by_cases h : (s.data == t.data) = true
  · have e : s.data = t.data := by simpa using h
    have z : (s.size == t.size) = true := by
      show (s.data.size == t.data.size) = true
      rw [e]; simp
    rw [z, Bool.true_and]
  · have h' : (s.data == t.data) = false := by simpa using h
    rw [h', Bool.and_false]

/-- The eight public strings, in the order in which they are asked: the configuration's, then the
  seven chains' at the bytes c. -/
def eightStr (G₀ : OnBytes.Tie.EntryGround) (Z : OnBytes.K.Pub) (c : ByteArray) : List ByteArray :=
  cStr Z :: (par7 G₀ Z.pol Z.KL Z.lay c).map parStr

end PV.Head

#print axioms PV.Head.cThru_hash
#print axioms PV.Head.sevenThru_hash
#print axioms PV.Head.turnAt_is
