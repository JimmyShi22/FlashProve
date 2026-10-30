-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesRaw.lean: THE ONE WRITTEN READING of the raw string under a root off a log,
said by strings alone, general in the configuration digest, the tree's depth and the salt's length.

`Three.rawU` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) is the reading in which "fine" is said, and the reading
that every file's part must read off a log in which no two strings have one answer. Here it is
written with no typed oracle, no implementation and no description of a protocol in its text: two
kinds of strings (`nodeStr`, `leafStr`), a look that reads these and no others (`lookZ`), and the
walks of that look in the perfect tree of depth a (`rawBy`).

Main definitions.
 `nodeStr c x`          the string of a vertex on two digests: the format's call number 166 from the
                        configuration digest c.
 `leafStr c a n y salt` the string of a stored leaf that holds the symbol y = (place, column), with
                        a typed salt: where the salt begins with the bits of c, has 256 + 8 n bits,
                        and the code of the call number 174 writes y at the depth a: that call's
                        string; ELSE the byte 2, four marks, and the serial forms of y and the salt.
 `lookZ c a n`          the look that reads these strings, and no others.
 `mkZ a`, `rawBy c a n` the raw string: 2^a places; at place j what the walk to leaf number j
                        finds, or (0, no word).
Main theorems.
 `nodeStr_inj`, `leafStr_sym`   a string is the string of at most one vertex and holds at most one
                        symbol.
 `lookZ_node`, `lookZ_leaf`     which strings the look reads, and as what: two equivalences.
 `leafStr_call`        at a salt of n bytes behind c, and a symbol that passes `Tie.storedOK`, the
                        leaf's string IS the string of the format's call number 174.
 `lookZ_call169`, `rawBy_offSet`   it does not see the entries at strings of calls number 169.
 `rawBy_hasLen`        it has exactly 2^a places.
 `rawBy_of_walks`, `PartO.ByWalks.raw_eq_rawBy`   A READING MADE OF THE WALKS OF A LOOK THAT AGREES
                        WITH `lookZ` IS `rawBy`, off a log in which no two strings have one answer.

What is not claimed. That a walk finds anything: under a root of which the log holds nothing the
reading is a table of (0, no word). A walk takes, under a digest, the FIRST entry of the log with
that answer whose string the look reads: in a log in which two strings have one answer it may pass
by another. THE STRINGS BEHIND THE BYTE 2 ARE NO CALLS OF THE FORMAT: they stand here because an
implementation is a total code, which must write every typed leaf somewhere, and all parts must
read one raw string. That a call's string lies in the domain of the format's hash: the code's test
is wider (an empty column; a salt of other than 5 to 8 words). "Nothing is found" and "(0, no word)
is found" are read alike. The place written in a symbol is not held against the leaf's number. That
any part's reading is `rawBy`. No probability. Nothing on any hash function.

-/
import OnBytes.Slice.WalkOff
import OnBytes.Tie.Page174

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open _root_.Iop Rom _root_.Run Compile
open _root_.Run.PQ (SgX serW bytes_beq_self)

/-! ## The two kinds of strings -/

/-- **The string of a vertex on two digests**: the format's call number 166, first half, tree 0,
index 0, from the configuration digest c, on the 512 bits of the two digests. -/
def nodeStr (c : ByteArray) (x : Dig 256 × Dig 256) : List Bool :=
  hdr 0 166 0 0 c ++ (List.ofFn x.1 ++ List.ofFn x.2)

/-- The string behind the byte 2 of a stored leaf: the byte 2, four marks, the serial form of the
symbol and that of the typed salt. No call of the format. -/
def spareStr (y : SgX) (salt : Bits) : List Bool :=
  bitsOfByte 2 ++ false :: false :: true :: false ::
    ((Ser.prod Ser.natG (Ser.list serW)).put y ++ serBits.put salt)

/-- The string of the format's call number 174 for a stored leaf, where there is one: the typed salt
begins with the bits of c and has 256 + 8 n bits, and the code of stored symbols at the depth a and
n bytes of salt writes y. The 33 constant bytes; the salt's first 256 bits (the call's start); the
label, the column and its fill; the salt's last 8 n bits. -/
def callStr (c : ByteArray) (a n : ℕ) (y : SgX) (salt : Bits) : Option (List Bool) :=
  if bitsToBytes (salt.take 256) == c then
    if salt.length = 256 + 8 * n then
      ((Tie.pStored a n).put y).map fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256))
    else none
  else none

/-- **The string of a stored leaf that holds the symbol y, with a typed salt**: the call's string
where there is one, else the string behind the byte 2. -/
def leafStr (c : ByteArray) (a n : ℕ) (y : SgX) (salt : Bits) : List Bool :=
  (callStr c a n y salt).getD (spareStr y salt)

/-- A string is the string of at most one vertex. -/
theorem nodeStr_inj (c : ByteArray) {x x' : Dig 256 × Dig 256}
    (h : nodeStr c x = nodeStr c x') : x = x' := by
  have h1 := List.append_cancel_left h
  have h2 := List.append_inj h1 (by rw [List.length_ofFn, List.length_ofFn])
  exact Prod.ext (List.ofFn_injective h2.1) (List.ofFn_injective h2.2)

/-- What the call's string is, where there is one. -/
theorem callStr_some (c : ByteArray) (a n : ℕ) (y : SgX) (salt : Bits) (u : List Bool)
    (h : callStr c a n y salt = some u) :
    (bitsToBytes (salt.take 256) == c) = true ∧ salt.length = 256 + 8 * n ∧
      ∃ m, (Tie.pStored a n).put y = some m ∧
        u = pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)) := by
  unfold callStr at h
  by_cases hc : (bitsToBytes (salt.take 256) == c) = true
  · rw [if_pos hc] at h
    by_cases hl : salt.length = 256 + 8 * n
    · rw [if_pos hl] at h
      obtain ⟨m, hm, hu⟩ := Option.map_eq_some_iff.1 h
      exact ⟨hc, hl, m, hm, hu.symm⟩
    · rw [if_neg hl] at h
      cases h
  · rw [if_neg hc] at h
    cases h

/-- A leaf's string is the call's string or the string behind the byte 2. -/
theorem leafStr_cases (c : ByteArray) (a n : ℕ) (y : SgX) (salt : Bits) :
    callStr c a n y salt = some (leafStr c a n y salt) ∨
      leafStr c a n y salt = spareStr y salt := by
  unfold leafStr
  cases callStr c a n y salt with
  | none => exact Or.inr rfl
  | some u => exact Or.inl rfl

/-- A call's string does not begin with the byte 2. -/
theorem callStr_no2 (c : ByteArray) (a n : ℕ) (y : SgX) (salt : Bits) (u : List Bool)
    (h : callStr c a n y salt = some u) : ¬ bitsOfByte 2 <+: u := by
  obtain ⟨-, -, m, -, rfl⟩ := callStr_some c a n y salt u h
  exact pre33_not_prefix 2 (by decide) _

/-- Two calls' strings that are one string hold one symbol. -/
theorem callStr_sym (c : ByteArray) (a n : ℕ) {y y' : SgX} {salt salt' : Bits} {u : List Bool}
    (h : callStr c a n y salt = some u) (h' : callStr c a n y' salt' = some u) : y = y' := by
  obtain ⟨-, hl, m, hm, hu⟩ := callStr_some c a n y salt u h
  obtain ⟨-, hl', m', hm', hu'⟩ := callStr_some c a n y' salt' u h'
  have e1 := List.append_cancel_left (hu.symm.trans hu')
  have e2 := (List.append_inj e1 (by
    rw [List.length_take, List.length_take, hl, hl'])).2
  have e3 := (List.append_inj' e2 (by
    rw [List.length_drop, List.length_drop, hl, hl'])).1
  rw [e3] at hm
  exact (Tie.pStored a n).inj hm hm'

/-- Two strings behind the byte 2 that are one string hold one symbol. -/
theorem spareStr_sym {y y' : SgX} {salt salt' : Bits} (h : spareStr y salt = spareStr y' salt') :
    y = y' := by
  have h1 := List.append_cancel_left h
  have h2 : (Ser.prod Ser.natG (Ser.list serW)).put y ++ serBits.put salt =
      (Ser.prod Ser.natG (Ser.list serW)).put y' ++ serBits.put salt' := by
    injection h1 with _ h1
    injection h1 with _ h1
    injection h1 with _ h1
    injection h1 with _ h1
  have h3 := congrArg (Ser.prod Ser.natG (Ser.list serW)).get h2
  rw [Ser.get_put, Ser.get_put] at h3
  exact congrArg Prod.fst (Option.some.inj h3)

/-- **A string holds at most one stored symbol.** -/
theorem leafStr_sym (c : ByteArray) (a n : ℕ) {y y' : SgX} {salt salt' : Bits}
    (h : leafStr c a n y salt = leafStr c a n y' salt') : y = y' := by
  rcases leafStr_cases c a n y salt with h1 | h1
  · rcases leafStr_cases c a n y' salt' with h2 | h2
    · rw [← h] at h2
      exact callStr_sym c a n h1 h2
    · exact absurd ⟨_, (h.trans h2).symm⟩ (callStr_no2 c a n y salt _ h1)
  · rcases leafStr_cases c a n y' salt' with h2 | h2
    · exact absurd ⟨_, (h.symm.trans h1).symm⟩ (callStr_no2 c a n y' salt' _ h2)
    · exact spareStr_sym (h1.symm.trans (h.trans h2))

/-! ## The look -/

/-- The thing with a property, if there is one; else nothing. (Some thing with it, if there are
several.) -/
noncomputable def theOne {α : Type} (p : α → Prop) : Option α :=
  @dite _ (∃ x, p x) (Classical.propDecidable _) (fun h => some h.choose) fun _ => none

/-- If at most one thing has the property, it is that thing. -/
theorem theOne_iff {α : Type} (p : α → Prop) (h1 : ∀ x x', p x → p x' → x = x') (x : α) :
    theOne p = some x ↔ p x := by
  unfold theOne
  constructor
  · intro h
    by_cases he : ∃ x, p x
    · rw [dif_pos he] at h
      rw [← Option.some.inj h]
      exact he.choose_spec
    · rw [dif_neg he] at h
      cases h
  · intro h
    have he : ∃ x, p x := ⟨x, h⟩
    rw [dif_pos he]
    exact congrArg some (h1 _ _ he.choose_spec h)

/-- **The look by strings**: a string is read as the vertex whose string it is, and as the stored
symbol of which, with some salt, it is the leaf's string. All other strings are read as nothing. -/
noncomputable def lookZ (c : ByteArray) (a n : ℕ) : Look 256 SgX where
  node := fun s => theOne fun x => s = nodeStr c x
  leaf := fun s => theOne fun y => ∃ salt, s = leafStr c a n y salt

/-- **Which strings it reads as vertices.** -/
theorem lookZ_node (c : ByteArray) (a n : ℕ) (s : List Bool) (x : Dig 256 × Dig 256) :
    (lookZ c a n).node s = some x ↔ s = nodeStr c x :=
  theOne_iff _ (fun _ _ h h' => nodeStr_inj c (h.symm.trans h')) x

/-- **In which strings it finds the stored symbol y.** -/
theorem lookZ_leaf (c : ByteArray) (a n : ℕ) (s : List Bool) (y : SgX) :
    (lookZ c a n).leaf s = some y ↔ ∃ salt, s = leafStr c a n y salt :=
  theOne_iff _ (fun _ _ h h' => by
    obtain ⟨salt, e⟩ := h
    obtain ⟨salt', e'⟩ := h'
    exact leafStr_sym c a n (e.symm.trans e')) y

/-- **At a salt of n bytes behind a digest of 32 bytes, and a symbol that passes the test of the
code, the leaf's string is the string of the format's call number 174**: tree's place 0 with the
numbers of the column's and the salt's words; index 2^a + place; start c; the column, its fill and
the salt. -/
theorem leafStr_call (c : ByteArray) (hc : c.size = 32) (a n : ℕ) (y : SgX) (sl : ByteArray)
    (hs : sl.size = n) (hy : Tie.storedOK a n y) :
    leafStr c a n y (bytesToBits c ++ bytesToBits sl) =
      bytesToBits (Fmt.oStr 0 174 (Fmt.leafPlace 0 y.2.length (n / 8)) (2 ^ a + y.1) c
        (Fmt.leafBytes y.2 sl)) := by
  have l1 : (bytesToBits c).length = 256 := by rw [length_bytesToBits, hc]
  have t1 : (bytesToBits c ++ bytesToBits sl).take 256 = bytesToBits c := by
    rw [← l1, List.take_left]
  have d1 : (bytesToBits c ++ bytesToBits sl).drop 256 = bytesToBits sl := by
    rw [← l1, List.drop_left]
  unfold leafStr callStr
  rw [t1, d1, bitsToBytes_bytesToBits, if_pos (bytes_beq_self c),
    if_pos (by rw [List.length_append, l1, length_bytesToBits, hs]), Tie.pStored_some a n y hy]
  show pre33 ++ (bytesToBits c ++ (Tie.storedStr a n y ++ bytesToBits sl)) = _
  rw [oStr32_bits _ _ _ _ _ (by decide) hc]
  unfold Tie.storedStr Fmt.leafBytes
  rw [hs, bytesToBits_append (_ ++ _), List.append_assoc]

/-! ## Strings of calls with the number 169 -/

/-- The tag of the string of a call with the number 169, and its first byte. -/
theorem call169_facts (s : List Bool) (hs : IsCall169 s) :
    tag16 s = t169 ∧ ¬ bitsOfByte 2 <+: s := by
  obtain ⟨half, t, i, st, bs, hh, hst, rfl⟩ := hs
  rw [oStr_bits half 169 t i st bs]
  have n2 : (2 : UInt8) ≠ half := by rcases hh with rfl | rfl <;> decide
  exact ⟨(tag16_hdr half 169 t i st hst (bytesToBits bs)).trans (Tie.tag_low 169 t),
    hdr_not_prefix 2 half n2 _ _ _ _ _⟩

/-- **The look reads no string of a call with the number 169**, at a digest of 32 bytes. -/
theorem lookZ_call169 (c : ByteArray) (hc : c.size = 32) (a n : ℕ) (s : List Bool)
    (hs : IsCall169 s) : (lookZ c a n).node s = none ∧ (lookZ c a n).leaf s = none := by
  obtain ⟨ht, h2⟩ := call169_facts s hs
  obtain ⟨-, -, -, d6, d7⟩ := t169_differs
  constructor
  · cases hx : (lookZ c a n).node s with
    | none => rfl
    | some x =>
      have e := (lookZ_node c a n s x).1 hx
      rw [e] at ht
      unfold nodeStr at ht
      rw [tag16_hdr 0 166 0 0 c hc] at ht
      exact absurd ((Tie.tag_low 166 0).symm.trans ht).symm d6
  · cases hy : (lookZ c a n).leaf s with
    | none => rfl
    | some y =>
      obtain ⟨salt, e⟩ := (lookZ_leaf c a n s y).1 hy
      rcases leafStr_cases c a n y salt with h1 | h1
      · obtain ⟨-, hl, m, hm, hu⟩ := callStr_some c a n y salt _ h1
        rw [e, hu, tag16_pre33 _ m _ (by rw [List.length_take, hl]; omega)
          (Tie.pStored_tag a n y m hm).1, (Tie.pStored_tag a n y m hm).2] at ht
        exact absurd ht.symm d7
      · exact absurd ⟨_, (e.trans h1).symm⟩ h2

/-! ## The raw string -/

/-- How a raw string is made of what is found at each place: 2^a places; (0, no word) where nothing
is found. -/
def mkZ (a : ℕ) (f : ℕ → Option SgX) : Raw SgX :=
  fun j => if j < 2 ^ a then some ((f j).getD (0, [])) else none

/-- **THE ONE WRITTEN READING, at a configuration digest c, a depth a and salts of n bytes**: at
each of the 2^a places the stored symbol that the walk of `lookZ c a n` finds at leaf number j of
the perfect tree of depth a under the root cm in the log σ; (0, no word) where it finds none;
nothing from 2^a on. At a c that has not 32 bytes: the raw string without a place. -/
noncomputable def rawBy (c : ByteArray) (a n : ℕ) (σ : Trace (rom 256)) (cm : Dig 256) :
    Raw SgX :=
  if c.size = 32 then mkZ a fun j => (lookZ c a n).walk σ (posOf a j) cm else fun _ => none

/-- At a digest of 32 bytes it has exactly 2^a places. -/
theorem rawBy_hasLen (c : ByteArray) (hc : c.size = 32) (a n : ℕ) (σ : Trace (rom 256))
    (cm : Dig 256) : Raw.HasLen (rawBy c a n σ cm) (2 ^ a) := by
  intro j
  unfold rawBy mkZ
  rw [if_pos hc]
  by_cases hj : j < 2 ^ a
  · rw [if_pos hj]
    exact ⟨fun h => (by cases h), fun h => absurd hj (Nat.not_lt.2 h)⟩
  · rw [if_neg hj]
    exact ⟨fun _ => Nat.not_lt.1 hj, fun _ => rfl⟩

/-- **It does not see the entries at strings of calls with the number 169.** No condition on c or
on the log. -/
theorem rawBy_offSet (c : ByteArray) (a n : ℕ) (S : Finset (List Bool))
    (hS : ∀ s ∈ S, IsCall169 s) (σ : Trace (rom 256)) (cm : Dig 256) :
    rawBy c a n (offSet S σ) cm = rawBy c a n σ cm := by
  unfold rawBy
  by_cases hc : c.size = 32
  · rw [if_pos hc, if_pos hc]
    refine congrArg (mkZ a) (funext fun j => ?_)
    exact walk_offSet _ S (fun s hs => (lookZ_call169 c hc a n s (hS s hs)).1)
      (fun s hs => (lookZ_call169 c hc a n s (hS s hs)).2) σ _ cm
  · rw [if_neg hc, if_neg hc]

/-- Binding with "some" changes nothing. -/
theorem bind_some_self {α : Type} (x : Option α) : x.bind some = x := by
  cases x <;> rfl

/-- **What is made in the same way of the walks of a look that agrees with `lookZ` is `rawBy`**, off
a log in which no two strings have one answer. Asked of the look k with `sym`: it reads the same
strings as the same vertices; string by string, what `sym` makes of its leaf is the stored symbol
that `lookZ` finds. -/
theorem rawBy_of_walks {Lf : Type} (k : Look 256 Lf) (sym : Lf → Option SgX) (c : ByteArray)
    (hc : c.size = 32) (a n : ℕ) (hn : ∀ s, k.node s = (lookZ c a n).node s)
    (hl : ∀ s, (k.leaf s).bind sym = (lookZ c a n).leaf s) (σ : Trace (rom 256))
    (hσ : NoClash σ) (cm : Dig 256) :
    (mkZ a fun j => (k.walk σ (posOf a j) cm).bind sym) = rawBy c a n σ cm := by
  unfold rawBy
  rw [if_pos hc]
  refine congrArg (mkZ a) (funext fun j => ?_)
  have h := walk_same k (lookZ c a n) sym some hn
    (fun s => by rw [hl s, bind_some_self]) σ hσ (posOf a j) cm
  rw [h, bind_some_self]

/-- **A part whose reading is so made reads `rawBy`**, off a log in which no two strings have one
answer. -/
theorem _root_.OnBytes.Slice.PartO.ByWalks.raw_eq_rawBy {γ Lf : Type} {s : PartO 256 γ SgX}
    {k : Look 256 Lf} {sym : Lf → Option SgX} {a : ℕ}
    (h : s.ByWalks k (posOf a) (fun _ => sym) (mkZ a)) (c : ByteArray) (hc : c.size = 32) (n : ℕ)
    (hn : ∀ x, k.node x = (lookZ c a n).node x)
    (hl : ∀ x, (k.leaf x).bind sym = (lookZ c a n).leaf x) (σ : Trace (rom 256))
    (hσ : NoClash σ) (cm : Dig 256) : s.raw σ cm = rawBy c a n σ cm := by
  rw [h.raw_eq]
  exact rawBy_of_walks k sym c hc a n hn hl σ hσ cm

end OnBytes.Slice.Shapes

#print axioms OnBytes.Slice.Shapes.leafStr_sym
#print axioms OnBytes.Slice.Shapes.lookZ_node
#print axioms OnBytes.Slice.Shapes.lookZ_leaf
#print axioms OnBytes.Slice.Shapes.leafStr_call
#print axioms OnBytes.Slice.Shapes.lookZ_call169
#print axioms OnBytes.Slice.Shapes.rawBy_offSet
#print axioms OnBytes.Slice.Shapes.rawBy_of_walks
#print axioms OnBytes.Slice.PartO.ByWalks.raw_eq_rawBy
