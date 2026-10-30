-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedStrings.lean: the strings at which the seeds of a stored table's record are asked
for: they are pairwise different; two starts have no string in common; one string of a name belongs
to one name, and one name to one shape, one configuration digest and one root.

The seed under an oracle g is a function of g's answers at the strings `blockStr ρ0 j` of the seeds'
round, where ρ0 is g's answer at `seedFirst name` (`seedUnder_eq`, OnBytes/Slice/SeedRow.lean).
Whoever wants these answers to be independent needs the strings to be different. By the laws of the
format's strings (`oStr_inj`, Fmt/Rules23Laws.lean; `firstBytes_inj`, Fmt/Rules4Laws.lean;
`oStr_number`, OnBytes/Tie/DigestPoint.lean).

Main theorems.
 `blockStr_dom`         the data of a call of the seeds' round are in the domain of the format's
                        hash, at a start of 32 bytes.
 `tail_inj`, `blockStr_inj`   at one start of 32 bytes the strings of two different blocks are
                        different, below 2^48 blocks.
 `blockStr_start`       TWO STARTS, TWO STRINGS: at two different starts of 32 bytes, whatever the
                        blocks' numbers.
 `seedFirst_ne_blockStr`   the string of the table's name is none of them, at any start: its call
                        has the number 160, theirs 162.
 `seedFirst_inj`, `nameOf_inj`, `seedFirst_key`   ONE STRING, ONE NAME, ONE ROOT: `seedFirst` is one
                        to one on names of at most 2^31 bytes; within `idOk` two keys with one name
                        have one shape, one configuration digest and one root. With
                        `size_seedBytes`.
 `idOk_of_firstId`, `seedFirst_firstId`   the first key of a digest in a log is within `idOk`; so
                        the same of two first keys.
 `mem_seedRest`         the strings that `askSeed` asks behind the first are the strings of the
                        blocks 0, 1, .., 2 `seedCalls` - 1.

What is not claimed. THE ANSWERS ARE NOT IN THE NAME: two keys with one name may have different
answers. BEYOND 2^49 BLOCKS THE STRINGS ARE NOT PAIRWISE DIFFERENT: the call's number is written,
behind a factor 2^16, modulo 2^64, so the calls c and c + 2^48 have one string; `blockStr_inj` stops
at 2^48 blocks; the law over g (OnBytes/Slice/SeedOracle.lean) has a bound on the number of blocks.
NO PROBABILITY HERE: that g's answers at these strings are uniform, for one name fixed beforehand:
OnBytes/Slice/SeedOracle.lean; the strings of the round depend on g's answer at the name's string,
and can be asked before it at starts of a committer's choice. Nothing on any hash function.

-/
import OnBytes.Slice.SeedRow
import OnBytes.Tie.IdKey
import Fmt.Rules23Laws
import Fmt.Rules5Fast
import Fmt.Rules4Laws
import Run.LaxDomProofs

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run

/-- The data of a call of the seeds' round are in the domain of the format's hash, at a start of 32
bytes. -/
theorem blockStr_dom (ρ0 : ByteArray) (h0 : ρ0.size = 32) (c : ℕ) :
    Fmt.hDom 162 Fmt.recordLabel 1 ρ0 (ByteArray.empty ++ Fmt.tail .seeds 0 0 c) = true := by
  have hs : (ByteArray.empty ++ Fmt.tail .seeds 0 0 c).size = 16 := by
    rw [ByteArray.size_append, Fmt.size_tail]
    rfl
  have h1 : Fmt.hasStart 162 = true := by decide
  have h2 : Fmt.leafOK 162 Fmt.recordLabel (ByteArray.empty ++ Fmt.tail .seeds 0 0 c) = true := by
    have hl : Fmt.isLeaf 162 = false := by decide
    unfold Fmt.leafOK
    rw [hl]
    rfl
  unfold Fmt.hDom
  rw [hs, h0, h1, h2, Bool.true_or]
  decide

/-- What stands behind the message in two calls of the seeds' round is different, below 2^47
calls. -/
theorem tail_inj (c c' : ℕ) (hc : c < 2 ^ 47) (hc' : c' < 2 ^ 47)
    (h : Fmt.tail .seeds 0 0 c = Fmt.tail .seeds 0 0 c') : c = c' := by
  unfold Fmt.tail at h
  have e := congrArg (fun x : ByteArray => x.extract 0 8) h
  simp only [extract_l _ _ 8 (Fmt.size_u64n _)] at e
  have hk : Fmt.Kind.seeds.num < 256 := by decide
  have := Tie.u64n_inj (by omega) (by omega) e
  omega

/-- **THE STRINGS OF THE BLOCKS OF THE SEEDS' ROUND ARE PAIRWISE DIFFERENT**, at one start of 32
bytes, below 2^48 blocks. -/
theorem blockStr_inj (ρ0 : ByteArray) (h0 : ρ0.size = 32) (j j' : ℕ) (hj : j < 2 ^ 48)
    (hj' : j' < 2 ^ 48) (h : blockStr ρ0 j = blockStr ρ0 j') : j = j' := by
  have two : ∀ n : ℕ, UInt8.ofNat (n % 2) = 0 ∨ UInt8.ofNat (n % 2) = 1 := fun n => by
    rcases Nat.mod_two_eq_zero_or_one n with e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨a1, -, -, -, -, a6⟩ := Fmt.oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ (two j) (two j')
    (blockStr_dom ρ0 h0 (j / 2)) (blockStr_dom ρ0 h0 (j' / 2)) h
  rw [ByteArray.empty_append, ByteArray.empty_append] at a6
  have e2 := tail_inj (j / 2) (j' / 2) (by omega) (by omega) a6
  have e1 : j % 2 = j' % 2 := by
    rcases Nat.mod_two_eq_zero_or_one j with x | x <;>
      rcases Nat.mod_two_eq_zero_or_one j' with y | y <;> rw [x, y] at a1 ⊢
    · exact absurd a1 (by decide)
    · exact absurd a1 (by decide)
  omega

/-- **The string of the table's name is none of them**: its call has the number 160, theirs 162. -/
theorem seedFirst_ne_blockStr (name ρ0 : ByteArray) (j : ℕ) : seedFirst name ≠ blockStr ρ0 j := by
  intro h
  have e := congrArg (fun x => (Fmt.wordAt x 65).toNat % 65536) h
  simp only [seedFirst, blockStr, Tie.oStr_number] at e
  exact absurd e (by decide)

/-- **Two starts, two strings**: the strings of blocks at two different starts of 32 bytes are
different, whatever the blocks' numbers. -/
theorem blockStr_start (ρ0 ρ0' : ByteArray) (h0 : ρ0.size = 32) (h0' : ρ0'.size = 32) (j j' : ℕ)
    (h : blockStr ρ0 j = blockStr ρ0' j') : ρ0 = ρ0' := by
  have two : ∀ n : ℕ, UInt8.ofNat (n % 2) = 0 ∨ UInt8.ofNat (n % 2) = 1 := fun n => by
    rcases Nat.mod_two_eq_zero_or_one n with e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (Fmt.oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ (two j) (two j')
    (blockStr_dom ρ0 h0 (j / 2)) (blockStr_dom ρ0' h0' (j' / 2)) h).2.2.2.2.1

/-! ## One string, one name, one root -/

/-- What is hashed for the first value of the seeds' chain has 56 bytes more than the name. -/
theorem size_seedBytes (name : ByteArray) :
    (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none).size = name.size + 56 := by
  unfold Fmt.firstBytes
  simp only [ByteArray.size_append, Fmt.size_u64n]
  show 32 + 8 + name.size + 8 + 0 + 8 = name.size + 56
  omega

/-- **One string, one name**: `seedFirst` is one to one on names of at most 2^31 bytes. -/
theorem seedFirst_inj (name name' : ByteArray) (hn : name.size ≤ 2 ^ 31)
    (hn' : name'.size ≤ 2 ^ 31) (h : seedFirst name = seedFirst name') : name = name' := by
  have dom : ∀ x : ByteArray, x.size ≤ 2 ^ 31 → Fmt.hDom 160 0 Fmt.recordLabel Fmt.zero32
      (Fmt.firstBytes Fmt.zero32 x ByteArray.empty none) = true := fun x hx =>
    dom0 160 Fmt.recordLabel _ (by decide) (by decide) (by decide) (by
      rw [size_seedBytes]
      omega)
  have e := (Fmt.oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) (dom name hn)
    (dom name' hn') h).2.2.2.2.2
  exact (Fmt.firstBytes_inj _ _ _ _ _ _ _ _
    ⟨rfl, by show name.size < 2 ^ 64; omega, by show ByteArray.empty.size < 2 ^ 64; decide,
      fun _ hr => by cases hr⟩
    ⟨rfl, by show name'.size < 2 ^ 64; omega, by show ByteArray.empty.size < 2 ^ 64; decide,
      fun _ hr => by cases hr⟩ e).2.1

/-- **One name, one shape, one digest, one root**: within `idOk`, two keys with one name have the
same shape, the same configuration digest and the same root. (Their answers may differ: the answers
are not in the name.) -/
theorem nameOf_inj {k k' : Tie.IdKey} (h : Tie.idOk k = true) (h' : Tie.idOk k' = true)
    (e : Key.nameOf k.1 k.2.1 k.2.2 = Key.nameOf k'.1 k'.2.1 k'.2.2) :
    k.1 = k'.1 ∧ k.2.1 = k'.2.1 ∧ k.2.2.root = k'.2.2.root := by
  unfold Tie.idOk at h h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, ac⟩, ar⟩, -⟩ := h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, bc⟩, br⟩, -⟩ := h'
  obtain ⟨s, cfg, t⟩ := k
  obtain ⟨s', cfg', t'⟩ := k'
  dsimp only at a1 a2 a3 a4 a5 a6 ac ar b1 b2 b3 b4 b5 b6 bc br e ⊢
  unfold Key.nameOf Fmt.tableName at e
  obtain ⟨n5, m6⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) e
  obtain ⟨n4, m5⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n5
  obtain ⟨n3, m4⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n4
  obtain ⟨n2, m3⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n3
  obtain ⟨n1, m2⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, Fmt.size_u64n, ac, ar, bc, br]) n2
  obtain ⟨n0, m1⟩ := Fmt.append_cancel _ _ _ _ (by
    simp only [ByteArray.size_append, ac, ar, bc, br]) n1
  obtain ⟨eR, eC⟩ := Fmt.append_cancel _ _ _ _ (by rw [ar, br]) n0
  have c1 := Tie.u64n_inj a1 b1 m1
  have c2 := Tie.u64n_inj a2 b2 m2
  have c3 := Tie.u64n_inj a3 b3 m3
  have c4 := Tie.u64n_inj a4 b4 m4
  have c5 := Tie.u64n_inj a5 b5 m5
  have c6 := Tie.u64n_inj a6 b6 m6
  obtain ⟨⟨x1, x2, x3⟩, x4, x5, x6⟩ := s
  obtain ⟨⟨y1, y2, y3⟩, y4, y5, y6⟩ := s'
  dsimp only at c1 c2 c3 c4 c5 c6
  subst c1 c2 c3 c4 c5 c6
  exact ⟨rfl, eC, eR⟩

/-- **ONE STRING, ONE NAME, ONE ROOT**: within `idOk`, two keys whose names have one string have the
same shape, the same configuration digest and the same root. -/
theorem seedFirst_key {k k' : Tie.IdKey} (h : Tie.idOk k = true) (h' : Tie.idOk k' = true)
    (e : seedFirst (Key.nameOf k.1 k.2.1 k.2.2) = seedFirst (Key.nameOf k'.1 k'.2.1 k'.2.2)) :
    k.1 = k'.1 ∧ k.2.1 = k'.2.1 ∧ k.2.2.root = k'.2.2.root := by
  have sz : ∀ x : Tie.IdKey, Tie.idOk x = true → (Key.nameOf x.1 x.2.1 x.2.2).size ≤ 2 ^ 31 :=
    fun x hx => by
      unfold Tie.idOk at hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      unfold Key.nameOf
      rw [Tie.size_tableName, hx.1.2, hx.1.1.2]
      decide
  exact nameOf_inj h h' (seedFirst_inj _ _ (sz k h) (sz k' h') e)

/-- **The first key of a digest in a log is within `idOk`**: `firstId` gives only keys that have a
code. -/
theorem idOk_of_firstId (d : ZKCP.Digest 256) (σ : Rom.Trace (Rom.rom 256)) (k : Tie.IdKey)
    (h : Tie.firstId d σ = some k) : Tie.idOk k = true := by
  unfold Tie.firstId at h
  obtain ⟨e, -, he⟩ := List.exists_of_findSome?_eq_some h
  split at he
  · have hc := (Tie.idRead_iff k _).1 he
    unfold Tie.idCode at hc
    by_contra hn
    rw [if_neg hn] at hc
    cases hc
  · cases he

/-- So two first keys whose names have one string have the same shape, the same configuration digest
and the same root. -/
theorem seedFirst_firstId (d d' : ZKCP.Digest 256) (σ σ' : Rom.Trace (Rom.rom 256))
    (k k' : Tie.IdKey) (h : Tie.firstId d σ = some k) (h' : Tie.firstId d' σ' = some k')
    (e : seedFirst (Key.nameOf k.1 k.2.1 k.2.2) = seedFirst (Key.nameOf k'.1 k'.2.1 k'.2.2)) :
    k.1 = k'.1 ∧ k.2.1 = k'.2.1 ∧ k.2.2.root = k'.2.2.root :=
  seedFirst_key (idOk_of_firstId d σ k h) (idOk_of_firstId d' σ' k' h') e

/-- **The strings that `askSeed` asks behind the first (`seedRest`, OnBytes/Slice/SeedAsked.lean)
are the strings of the blocks 0, 1, .., 2 `seedCalls` - 1.** -/
theorem mem_seedRest (ρ0 : ByteArray) (lg s : ℕ) (x : ByteArray) :
    x ∈ seedRest ρ0 lg s ↔ ∃ j, j < 2 * seedCalls lg s ∧ x = blockStr ρ0 j := by
  unfold seedRest
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hx⟩
    have hc' := List.mem_range.1 hc
    rcases List.mem_cons.1 hx with rfl | hx'
    · refine ⟨2 * c, by omega, ?_⟩
      unfold blockStr
      rw [Nat.mul_mod_right, Nat.mul_div_cancel_left c (by decide)]
      rfl
    · rw [List.mem_singleton.1 hx']
      refine ⟨2 * c + 1, by omega, ?_⟩
      unfold blockStr
      rw [show (2 * c + 1) % 2 = 1 by omega, show (2 * c + 1) / 2 = c by omega]
      rfl
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j / 2, List.mem_range.2 (by omega), ?_⟩
    unfold blockStr
    rcases Nat.mod_two_eq_zero_or_one j with e | e <;> rw [e]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

end OnBytes.Slice

#print axioms OnBytes.Slice.blockStr_dom
#print axioms OnBytes.Slice.tail_inj
#print axioms OnBytes.Slice.blockStr_inj
#print axioms OnBytes.Slice.seedFirst_ne_blockStr
#print axioms OnBytes.Slice.blockStr_start
#print axioms OnBytes.Slice.size_seedBytes
#print axioms OnBytes.Slice.seedFirst_inj
#print axioms OnBytes.Slice.nameOf_inj
#print axioms OnBytes.Slice.seedFirst_key
#print axioms OnBytes.Slice.idOk_of_firstId
#print axioms OnBytes.Slice.seedFirst_firstId
#print axioms OnBytes.Slice.mem_seedRest
