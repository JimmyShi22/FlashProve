-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RawWalks.lean: the raw string that `partChain` reads, written out place by place
as walks in a log; and which strings of the
log such a walk reads, and as what.

`Part.toO_byWalks` (OnBytes/Slice/ByWalks.lean) says that a part's raw string is some `mk` of what
some `sym` makes of the leaves that walks find. Here `mk` and `sym` are unfolded for the checker of
a chain with stored tables: the wiring's way of building a string puts (0, no word) where there is
no symbol; the reading keeps the stored symbol in a leaf, whatever the salt and whatever place is
written in the symbol: it is not held against j; the match of symbols is the identity.



Main theorems.
 `partChain_raw_walks`  for every description: below 2^a the stored symbol in the leaf that the walk
                        finds at leaf number j of the perfect tree of depth a, or (0, no word);
                        nothing from 2^a on.




 `look_node`, `look_stored`   for every page: the strings that the look reads as a vertex on two
                        digests; the strings in which it finds a stored symbol.
 `look_stored_page`     the second at the encoding of any description, written out to the format's
                        codes.




 `look_stored_call`, `look_stored_no2`   THE SAME AS STRINGS OF THE FORMAT'S CALL NUMBER 174, for
                        every description: in the string of that call from the configuration digest
                        on a column, its fill and a salt of the format's length the look finds
                        (place, column); and a string that does not begin with the byte 2, and in
                        which it finds y, is such a string.
                        With `stored_call_bits`.

What is not claimed. That a walk finds anything. A walk takes, under a digest, the FIRST string of
the log with that answer which the look reads as a vertex or a leaf: in a log in which two strings
have one answer it may pass by another. The look finds stored symbols also in strings behind the
byte 2, which are no call of the format (`look_stored`'s second case). Nothing on who wrote the log.
Which strings are read as a leaf that holds no stored symbol is not written. No probability.
No statement on a hash function.
-/
import OnBytes.Slice.FineAt
import OnBytes.Slice.ByWalks
import OnBytes.Slice.SameStoredAt

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (xdOf withinX bareStatement)

section
variable {γ : Type} (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
  (dec : View → Bool) (hw : withinX S0 = true)
  (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
  (m : OracleCoding (spec 256 (WkAny (xdOf S0 stm) dec).K ((xdOf S0 stm).L dec)) 256)
  (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))

/-- **The raw string that `partChain` reads, place by place, written out as walks**: below 2^a, with
a the stored tables' depth, the stored symbol in the leaf that the walk of the look through m finds
at leaf number j of the perfect tree of depth a under the root, and (0, no word) where the walk
finds no leaf or the leaf holds no stored symbol; nothing from 2^a on. Asked: one block for a leaf's
and a vertex's answer in m, taken as it is. -/
theorem partChain_raw_walks (h : OneBlock m) (σ : Trace (rom 256)) (cm : Dig 256) (j : ℕ) :
    (partChain S0 stm dec hw Lg εs m pre).raw σ cm j =
      if j < 2 ^ (xdOf S0 stm).a then
        some ((((lookOf m).walk σ (posOf (xdOf S0 stm).a j) cm).bind storedSym).getD (0, []))
      else none := by
  have hb := (Part.toO_byWalks (partChain S0 stm dec hw Lg εs m pre) h
    (Reading.wide_byLeaves (ext_ok_any (xdOf S0 stm) dec))).raw_eq σ cm
  have hr : (partChain S0 stm dec hw Lg εs m pre).raw σ cm =
      (partChain S0 stm dec hw Lg εs m pre).toO.raw σ cm := rfl
  rw [hr, hb]
  show (if hj : j < 2 ^ (xdOf S0 stm).a then _ else none) = _
  by_cases hj : j < 2 ^ (xdOf S0 stm).a
  · rw [dif_pos hj, if_pos hj]
    show some (((((lookOf m).walk σ (posOf (xdOf S0 stm).a j) cm).bind fun q =>
        (storedSym q).map (Equiv.refl SgX)).map (Equiv.refl SgX).symm).getD (0, [])) = _
    generalize (lookOf m).walk σ (posOf (xdOf S0 stm).a j) cm = w
    cases w with
    | none => rfl
    | some q =>
      show some ((((storedSym q).map (Equiv.refl SgX)).map (Equiv.refl SgX).symm).getD (0, [])) =
        some ((storedSym q).getD (0, []))
      cases storedSym q <;> rfl
  · rw [dif_neg hj, if_neg hj]

end

/-! ## Which strings a look through the encoding reads, and as what -/

section
variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : Tie.PageCX L K tg)

/-- **The strings that the look through the encoding reads as vertices**: the strings of the call
number 166, from the page's configuration digest, on two digests. -/
theorem look_node (s : List Bool) (x : Dig 256 × Dig 256) :
    (lookOf (Tie.theImplX C)).node s = some x ↔
      s = hdr 0 166 0 0 C.cfg ++ (List.ofFn x.1 ++ List.ofFn x.2) := by
  have hw := pNode_put C.cfg (List.ofFn x.1) (List.ofFn x.2) List.length_ofFn List.length_ofFn
  rw [lookOf_node, inv_iff_code]
  constructor
  · rintro ⟨k, hk⟩
    rw [hk, Tie.theImplX_node C _ _ hw k]
  · intro h
    exact ⟨(0 : Fin 1), h.trans (Tie.theImplX_node C _ _ hw 0).symm⟩

/-- **The strings in which it finds the stored symbol y**: for some salt, what the code of the call
number 174 writes of y and that salt, where it writes; else the byte 2 and the total code's
string. -/
theorem look_stored (s : List Bool) (y : L.Symbol) :
    ((lookOf (Tie.theImplX C)).leaf s).bind storedSym = some y ↔
      ∃ salt : Bits, s = ((Tie.pStoredLeaf C).put ⟨some (.inl y), salt⟩).getD
        (bitsOfByte 2 ++ C.back.put (.inl (.inl ⟨some (.inl y), salt⟩))) := by
  constructor
  · intro h
    obtain ⟨q, hq, hy⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨k, hk⟩ := (inv_iff_code (Tie.theImplX C) s Batch.OracleName.leaf q).1
      ((lookOf_leaf (Tie.theImplX C) s q).1 hq)
    rw [(storedSym_eq_some q y).1 hy] at hk
    exact ⟨q.salt, hk.trans (code_stored C y q.salt k)⟩
  · rintro ⟨salt, hs⟩
    have h2 : (lookOf (Tie.theImplX C)).leaf s = some ⟨some (.inl y), salt⟩ :=
      (lookOf_leaf (Tie.theImplX C) s ⟨some (.inl y), salt⟩).2
        ((inv_iff_code (Tie.theImplX C) s Batch.OracleName.leaf ⟨some (.inl y), salt⟩).2
          ⟨(0 : Fin 1), hs.trans (code_stored C y salt 0).symm⟩)
    rw [h2]
    rfl

end

/-- **The strings in which the look through the encoding of a description finds the stored symbol
y**, written out to the format's codes: for some salt: the string of the call number 174 from the
description's configuration digest, where the first 256 bits of the salt are that digest, the salt
has the format's length and the code of stored symbols writes y; else the byte 2, the marks "real
point", "leaf", "some", "left", the serial form of y and that of the salt. -/
theorem look_stored_page (D : XD) (dec : View → Bool) (pd : Dig 256) (K : ℕ)
    (hcfg : D.base.cfg.size = 32) (V : Tie.StmInv D) (s : List Bool) (y : SgX) :
    ((lookOf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V))).leaf s).bind storedSym =
        some y ↔ ∃ salt : Bits, s =
      ((if bitsToBytes (salt.take 256) == D.base.cfg then
          if salt.length = 256 + 8 * D.base.plan.salt then
            ((Tie.pStored D.a D.base.plan.salt).put y).map fun m =>
              pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))
          else none
        else none).getD (bitsOfByte 2 ++ false :: false :: true :: false ::
          ((Ser.prod Ser.natG (Ser.list serW)).put y ++ serBits.put salt))) :=
  look_stored (Tie.pageXPd (D := D) dec pd K hcfg V) s y

/-! ## The same as strings of the format's call number 174 -/

/-- **In the string of the format's call number 174, from the description's configuration digest, on
a column, its fill and a salt of the format's length, the look finds (place, column).** The call:
tree's place 0 with the numbers of the column's and the salt's words; index 2^a + place; start the
configuration digest; bytes `Fmt.leafBytes` of column and salt (the arguments of `Fmt.leafW` at the
number 174 and the tree 0, Fmt/Rules7.lean: by reading). Asked: `Tie.storedOK`, which asks 2^a +
place below 2^64, not place below 2^a: the place may be 2^a or more; then the index is that of no
leaf of a tree of depth a. -/
theorem look_stored_call (D : XD) (dec : View → Bool) (pd : Dig 256) (K : ℕ)
    (hcfg : D.base.cfg.size = 32) (V : Tie.StmInv D) (y : SgX) (sl : ByteArray)
    (hs : sl.size = D.base.plan.salt) (hy : Tie.storedOK D.a D.base.plan.salt y) :
    ((lookOf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V))).leaf
      (bytesToBits (Fmt.oStr 0 174 (Fmt.leafPlace 0 y.2.length (D.base.plan.salt / 8))
        (2 ^ D.a + y.1) D.base.cfg (Fmt.leafBytes y.2 sl)))).bind storedSym = some y := by
  have l1 : (bytesToBits D.base.cfg).length = 256 := by rw [length_bytesToBits, hcfg]
  have t1 : (bytesToBits D.base.cfg ++ bytesToBits sl).take 256 = bytesToBits D.base.cfg := by
    rw [← l1, List.take_left]
  have d1 : (bytesToBits D.base.cfg ++ bytesToBits sl).drop 256 = bytesToBits sl := by
    rw [← l1, List.drop_left]
  have e := Tie.implX_stored_string (D := D) dec pd K hcfg V y
    (bytesToBits D.base.cfg ++ bytesToBits sl)
    (by rw [t1, bitsToBytes_bytesToBits]; exact bytes_beq_self _)
    (by rw [List.length_append, l1, length_bytesToBits, hs]) hy 0
  rw [d1, bitsToBytes_bytesToBits] at e
  have h2 := (lookOf_leaf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V)) _
    ⟨some (.inl y), bytesToBits D.base.cfg ++ bytesToBits sl⟩).2
    ((inv_iff_code (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V)) _ Batch.OracleName.leaf
      ⟨some (.inl y), bytesToBits D.base.cfg ++ bytesToBits sl⟩).2 ⟨(0 : Fin 1), e.symm⟩)
  rw [h2]
  rfl

/-- **A string that does not begin with the byte 2, and in which the look finds y, is such a
string.** -/
theorem look_stored_no2 (D : XD) (dec : View → Bool) (pd : Dig 256) (K : ℕ)
    (hcfg : D.base.cfg.size = 32) (V : Tie.StmInv D) (s : List Bool) (y : SgX)
    (h : ((lookOf (Tie.theImplX (Tie.pageXPd (D := D) dec pd K hcfg V))).leaf s).bind storedSym =
      some y) (h2 : ¬ bitsOfByte 2 <+: s) :
    ∃ sl : ByteArray, sl.size = D.base.plan.salt ∧ Tie.storedOK D.a D.base.plan.salt y ∧
      s = bytesToBits (Fmt.oStr 0 174 (Fmt.leafPlace 0 y.2.length (D.base.plan.salt / 8))
        (2 ^ D.a + y.1) D.base.cfg (Fmt.leafBytes y.2 sl)) := by
  obtain ⟨salt, hs⟩ := (look_stored (Tie.pageXPd (D := D) dec pd K hcfg V) s y).1 h
  cases hp : (Tie.pStoredLeaf (Tie.pageXPd (D := D) dec pd K hcfg V)).put
      ⟨some (.inl y), salt⟩ with
  | none =>
    rw [hp] at hs
    exact absurd ⟨_, hs.symm⟩ h2
  | some u =>
    rw [hp] at hs
    obtain ⟨y', m, hb, hc, hl, hm, -⟩ := Tie.pLeafS_put _ _ _ _ u hp
    have hy' : y' = y := by
      have hb' : (some (Sum.inl y) : Option _) = some (Sum.inl y') := hb
      exact (Sum.inl.inj (Option.some.inj hb')).symm
    rw [hy'] at hm
    have hl' : salt.length = 256 + 8 * D.base.plan.salt := hl
    have e2 : (salt.drop 256).length = 8 * D.base.plan.salt := by
      rw [List.length_drop, hl']
      omega
    have ok := (Tie.pStored_put _ _ y m hm).1
    refine ⟨bitsToBytes (salt.drop 256), size_bitsToBytes _ _ e2, ok, ?_⟩
    rw [← Tie.implX_stored_string (D := D) dec pd K hcfg V y salt hc hl' ok 0,
      Tie.theImplX_stored _ _ u hp 0]
    exact hs

/-- The string of the format's call number 174 from a start c of 32 bytes on a column, its fill and
a salt of n bytes, in the pieces in which the code of stored leaves writes it. -/
theorem stored_call_bits (c : ByteArray) (hc : c.size = 32) (a n : ℕ) (y : SgX) (sl : ByteArray)
    (hs : sl.size = n) :
    bytesToBits (Fmt.oStr 0 174 (Fmt.leafPlace 0 y.2.length (n / 8)) (2 ^ a + y.1) c
        (Fmt.leafBytes y.2 sl)) =
      pre33 ++ (bytesToBits c ++ (Tie.storedStr a n y ++ bytesToBits sl)) := by
  rw [oStr32_bits _ _ _ _ _ (by decide) hc]
  unfold Tie.storedStr Fmt.leafBytes
  rw [hs, bytesToBits_append (_ ++ _), List.append_assoc]

end OnBytes.Slice

#print axioms OnBytes.Slice.partChain_raw_walks
#print axioms OnBytes.Slice.look_node
#print axioms OnBytes.Slice.look_stored
#print axioms OnBytes.Slice.look_stored_page
#print axioms OnBytes.Slice.look_stored_call
#print axioms OnBytes.Slice.look_stored_no2
#print axioms OnBytes.Slice.stored_call_bits
