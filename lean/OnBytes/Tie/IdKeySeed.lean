-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdKeySeed.lean: the commitment ID's string with the record's seed and the further public
digests in it, as the code of a key: no bit string is the code of two keys. No hypothesis; a key has
a code only within `idOkS`.

What this file states. OnBytes/Tie/IdKey.lean has a shorter string under the call number 179: the
configuration's digest, the table's name, the record's answers. The commitment ID's string (R4.11)
also holds the record's seed, as a list of field elements in front of the answers, and a list of
further public digests behind them: cfg ++ text name ++ list ext seed ++ list ext answers ++ list id
told. The three lists carry their number in front as a word, and a further digest is 32 bare bytes:
so the parts cannot slide. `IdKeyS` is what enters the ID: an `IdKey` (shape, digest, table), the
seed, the further digests. `publishedBytesS` are the bytes; `idCodeS` is the code.
`idCodeS_oneToOne`: `ZKCP.CodeIsOneToOne idCodeS`. `idAtS` is the ID with a function O on byte
strings in the place of the hash's oracle: it is O's value at the key's string (`idAtS_eq`), and at
the function that an oracle on bit strings induces it is the library's digest of the key under
`idCodeS` (`idAtS_oB`).

Under which hypotheses. `idBytesS_inj`: within `idOkS`, equal bytes come from equal keys.
`idAtS_oB`: within `idOkS`. A key outside `idOkS` has no code.

What it does not show. A statement on strings. `publishedBytesS` is written here; that it is
`Fmt.publishedBytes` is shown in OnBytes/Tie/IdKeySeedFmt.lean. That the programs spell the ID's
string so is not said here. Nothing says that the seed in a key is the one that the hash function
gives at the table's name, or that a further digest is the digest of anything. No probability. For
proofs only; the program does not import this file.


-/
import OnBytes.Tie.IdKey

set_option autoImplicit false

namespace OnBytes.Tie

/-- What enters a commitment ID: shape, digest and table; the record's seed as a list of field
elements; the further public digests. -/
structure IdKeyS where
  base : IdKey
  seed : List E
  told : List ByteArray

/-- What stands behind the table's name: the seed, the answers, the told digests. -/
def tailS (x : List (UInt64 × UInt64 × UInt64) × List (UInt64 × UInt64 × UInt64) × List ByteArray) :
    ByteArray :=
  Fmt.pair (Fmt.list Fmt.ext) (Fmt.pair (Fmt.list Fmt.ext) (Fmt.list id)) x

/-- The bytes that the ID is the hash of. -/
def publishedBytesS (cfg name : ByteArray) (seed answers : List (UInt64 × UInt64 × UInt64))
    (told : List ByteArray) : ByteArray :=
  cfg ++ Fmt.text name ++ tailS (seed, answers, told)

/-- Written flat. -/
theorem publishedBytesS_eq (cfg name : ByteArray) (seed answers : List (UInt64 × UInt64 × UInt64))
    (told : List ByteArray) :
    publishedBytesS cfg name seed answers told =
      cfg ++ Fmt.text name ++ Fmt.list Fmt.ext seed ++ Fmt.list Fmt.ext answers ++
        Fmt.list id told := by
  unfold publishedBytesS tailS Fmt.pair
  simp only [ByteArray.append_assoc]

/-- The bytes at a key. -/
def idBytesS (k : IdKeyS) : ByteArray :=
  publishedBytesS k.base.2.1 (Key.nameOf k.base.1 k.base.2.1 k.base.2.2) (k.seed.map E.triple)
    (k.base.2.2.answers.map E.triple) k.told

/-- The keys that have a code: as `idOk`, with the bound on the longer bytes; and each told digest
has 32 bytes. -/
def idOkS (k : IdKeyS) : Bool :=
  decide (k.base.1.code.logN < 2 ^ 64) && decide (k.base.1.code.ell < 2 ^ 64) &&
    decide (k.base.1.code.r < 2 ^ 64) && decide (k.base.1.v < 2 ^ 64) &&
    decide (k.base.1.answers < 2 ^ 64) && decide (k.base.1.saltBytes < 2 ^ 64) &&
    decide (k.base.2.1.size = 32) && decide (k.base.2.2.root.size = 32) &&
    decide ((idBytesS k).size ≤ 2 ^ 32 - 144) && decide (∀ b ∈ k.told, b.size = 32)

/-- The string at which an oracle is asked for the ID. -/
def idStrS (k : IdKeyS) : ByteArray := Fmt.oStr 0 179 0 0 Fmt.zero32 (idBytesS k)

/-- The code of a key, as a bit string; none outside `idOkS`. -/
def idCodeS (k : IdKeyS) : Option ZKCP.Str :=
  if idOkS k then some (Run.bytesToBits (idStrS k)) else none

/-- A spelling that a reader undoes is one to one. -/
theorem undoes_inj {α : Type} {r : Fmt.Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (u : Fmt.Undoes r sp ok) {x y : α} (hx : ok x) (hy : ok y) (h : sp x = sp y) : x = y := by
  have a := u x hx ByteArray.empty ByteArray.empty
  have b := u y hy ByteArray.empty ByteArray.empty
  rw [h, b] at a
  exact (congrArg (·.1) (Option.some.inj a)).symm

/-- A reader undoes what stands behind the name. -/
theorem undoes_tailS :
    Fmt.Undoes
      (Fmt.rdPair (Fmt.rdList (Fmt.rdPair Fmt.rdWord (Fmt.rdPair Fmt.rdWord Fmt.rdWord)))
        (Fmt.rdPair (Fmt.rdList (Fmt.rdPair Fmt.rdWord (Fmt.rdPair Fmt.rdWord Fmt.rdWord)))
          (Fmt.rdList Fmt.rdDigest))) tailS
      fun x => (x.1.length < 2 ^ 64 ∧ ∀ e ∈ x.1, True) ∧
        (x.2.1.length < 2 ^ 64 ∧ ∀ e ∈ x.2.1, True) ∧
        x.2.2.length < 2 ^ 64 ∧ ∀ b ∈ x.2.2, b.size = 32 := by
  have hp : ∀ x : UInt64 × UInt64 × UInt64, True → 1 ≤ (Fmt.ext x).size := by
    intro x _
    unfold Fmt.ext
    simp only [ByteArray.size_append, Fmt.size_u64]
    omega
  have ht : ∀ b : ByteArray, b.size = 32 → 1 ≤ (id b).size := by
    intro b hb
    simp only [id, hb]
    omega
  exact Fmt.undoes_pair (Fmt.undoes_list undoes_ext3 hp)
    (Fmt.undoes_pair (Fmt.undoes_list undoes_ext3 hp) (Fmt.undoes_list Fmt.undoes_digest ht))

/-- The number of a list's entries is at most the size of its spelling, if no entry is spelled by
nothing. -/
theorem length_le_list {α : Type} {sp : α → ByteArray} (l : List α)
    (h : ∀ x ∈ l, 1 ≤ (sp x).size) : l.length ≤ (Fmt.list sp l).size := by
  have h1 := Fmt.length_le_cat (sp := sp) l h
  unfold Fmt.list
  rw [ByteArray.size_append]
  omega

/-- Within `idOkS`, equal bytes come from equal keys. -/
theorem idBytesS_inj {k k' : IdKeyS} (h : idOkS k = true) (h' : idOkS k' = true)
    (e : idBytesS k = idBytesS k') : k = k' := by
  unfold idOkS at h h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, ac⟩, ar⟩, az⟩, at32⟩ := h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, bc⟩, br⟩, bz⟩, bt32⟩ := h'
  -- sizes of the three parts behind the name
  have sz : ∀ q : IdKeyS, (Fmt.list Fmt.ext (q.seed.map E.triple)).size +
      (Fmt.list Fmt.ext (q.base.2.2.answers.map E.triple)).size +
      (Fmt.list id q.told).size ≤ (idBytesS q).size := by
    intro q
    unfold idBytesS
    rw [publishedBytesS_eq]
    simp only [ByteArray.size_append]
    omega
  have hpe : ∀ (l : List (UInt64 × UInt64 × UInt64)), ∀ x ∈ l, 1 ≤ (Fmt.ext x).size := by
    intro l x _
    unfold Fmt.ext
    simp only [ByteArray.size_append, Fmt.size_u64]
    omega
  have okOf : ∀ q : IdKeyS, (idBytesS q).size ≤ 2 ^ 32 - 144 → (∀ b ∈ q.told, b.size = 32) →
      (((q.seed.map E.triple).length < 2 ^ 64 ∧ ∀ e ∈ q.seed.map E.triple, True) ∧
        ((q.base.2.2.answers.map E.triple).length < 2 ^ 64 ∧
          ∀ e ∈ q.base.2.2.answers.map E.triple, True) ∧
        q.told.length < 2 ^ 64 ∧ ∀ b ∈ q.told, b.size = 32) := by
    intro q hq h32
    have s := sz q
    have l1 := length_le_list (sp := Fmt.ext) (q.seed.map E.triple) (hpe _)
    have l2 := length_le_list (sp := Fmt.ext) (q.base.2.2.answers.map E.triple) (hpe _)
    have l3 := length_le_list (sp := id) q.told (fun x hx => by simp only [id, h32 x hx]; omega)
    exact ⟨⟨by omega, fun _ _ => trivial⟩, ⟨by omega, fun _ _ => trivial⟩, by omega, h32⟩
  have hn : (Key.nameOf k.base.1 k.base.2.1 k.base.2.2).size =
      (Key.nameOf k'.base.1 k'.base.2.1 k'.base.2.2).size := by
    unfold Key.nameOf
    rw [size_tableName, size_tableName, ac, ar, bc, br]
  have e0 := e
  unfold idBytesS publishedBytesS at e0
  obtain ⟨e1, eT⟩ := Fmt.append_cancel _ _ _ _ (by
    unfold Fmt.text
    simp only [ByteArray.size_append, Fmt.size_u64n, hn, ac, bc]) e0
  have eq3 := undoes_inj undoes_tailS (okOf k az at32) (okOf k' bz bt32) eT
  have eS : k.seed.map E.triple = k'.seed.map E.triple := congrArg (·.1) eq3
  have eA : k.base.2.2.answers.map E.triple = k'.base.2.2.answers.map E.triple :=
    congrArg (·.2.1) eq3
  have eD : k.told = k'.told := congrArg (·.2.2) eq3
  -- the shorter string's bytes agree, and its keys are within its bound
  have old : ∀ q : IdKey, idBytes q = q.2.1 ++ Fmt.text (Key.nameOf q.1 q.2.1 q.2.2) ++
      Fmt.list Fmt.ext (q.2.2.answers.map E.triple) := fun _ => rfl
  have eB : idBytes k.base = idBytes k'.base := by
    rw [old, old, e1, eA]
  have szB : ∀ q : IdKeyS, (idBytes q.base).size ≤ (idBytesS q).size := by
    intro q
    rw [old]
    unfold idBytesS
    rw [publishedBytesS_eq]
    simp only [ByteArray.size_append]
    omega
  have okB : idOk k.base = true := by
    unfold idOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, ac⟩, ar⟩, le_trans (szB k) az⟩
  have okB' : idOk k'.base = true := by
    unfold idOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, bc⟩, br⟩, le_trans (szB k') bz⟩
  have eBase : k.base = k'.base := idBytes_inj okB okB' eB
  have eSeed : k.seed = k'.seed :=
    List.map_injective_iff.2 (fun _ _ hxy => triple_inj hxy) eS
  obtain ⟨b, s, d⟩ := k
  obtain ⟨b', s', d'⟩ := k'
  dsimp only at eBase eSeed eD
  subst eBase eSeed eD
  rfl

/-- Within `idOkS` the call 179 on the bytes is in the domain of the format's hash. -/
theorem idOkS_dom {k : IdKeyS} (h : idOkS k = true) :
    Fmt.hDom 179 0 0 Fmt.zero32 (idBytesS k) = true := by
  unfold idOkS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Run.dom0 179 0 (idBytesS k) (by decide) (by decide) (by decide) h.1.2

/-- **No bit string is the code of two keys.** -/
theorem idCodeS_oneToOne : ZKCP.CodeIsOneToOne idCodeS := by
  intro k k' c hk hk'
  unfold idCodeS at hk hk'
  split at hk
  · rename_i h
    split at hk'
    · rename_i h'
      have e : Run.bytesToBits (idStrS k) = Run.bytesToBits (idStrS k') :=
        (Option.some.inj hk).trans (Option.some.inj hk').symm
      have e2 := Run.bytesToBits_inj e
      unfold idStrS at e2
      exact idBytesS_inj h h' (Fmt.oStr_inj 0 0 179 179 0 0 0 0 _ _ _ _ (Or.inl rfl) (Or.inl rfl)
        (idOkS_dom h) (idOkS_dom h') e2).2.2.2.2.2
    · cases hk'
  · cases hk

/-- The ID with a function O on byte strings in the place of the hash's oracle. -/
def idAtS (O : ByteArray → ByteArray) (k : IdKeyS) : ByteArray :=
  Fmt.HO O 179 0 0 Fmt.zero32 (idBytesS k)

/-- The ID at O is the value of O at the key's string. -/
theorem idAtS_eq (O : ByteArray → ByteArray) (k : IdKeyS) : idAtS O k = O (idStrS k) := by
  unfold idAtS Fmt.HO idStrS
  rw [if_neg (by decide)]

/-- Within `idOkS`, the ID at the function that an oracle f on bit strings induces on byte strings
is, as bytes, the library's digest of the key under f at `idCodeS`. -/
theorem idAtS_oB (f : ZKCP.Oracle 256) {k : IdKeyS} (h : idOkS k = true) :
    idAtS (Run.oB f) k = Run.digToBytes (ZKCP.digestUnder f idCodeS k) := by
  rw [idAtS_eq]
  unfold Run.oB ZKCP.digestUnder idCodeS
  rw [if_pos h]
  rfl

end OnBytes.Tie

#print axioms OnBytes.Tie.idBytesS_inj
#print axioms OnBytes.Tie.idCodeS_oneToOne
#print axioms OnBytes.Tie.idAtS_oB
