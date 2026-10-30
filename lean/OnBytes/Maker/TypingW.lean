-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingW.lean: the typing of a whole file: from what the shipped verifier's reader
returns for the three chains of a key file or a proof file to the proof string of the one joined
protocol that OnBytes/Maker/Whole.lean makes of the file.

The proof string is the compiler's `OneProtocolProof` over wire records with lists of trees
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) at `(wholeDesc ..).batch`. It is laid together as
OnBytes/TypedOracleCompiler/Joined/Assemble.lean lays three chains' strings together: the roots in a row, the plain
parts in a row, the openings by the sender's position. Each stretch is typed by
OnBytes/Maker/TypingT.lean.

What the caller gives beside the reading: the plain parts of the three silent rounds (front, joining
round, seam); the tables of all openings of the file, keyed by the tree's number over the whole file
(an opening in a tree that a later chain takes over stands under the sender's number); the openings
of the stored table; the salt and the siblings of the leaf in the binding tree.

Main definitions.
  `str₁`, `str₂`, `str₃`: what is read for each chain (`ChainStr`): its roots, its plain parts with
    its silent first round's, its openings: none at the silent round; at the stretch the look-up of
    `opensT`, from the number of trees that the stretches before have sent.
  `rsOf`: what the string lays behind the slot's value in the binding tree's leaf: the salt, then
    the leaf's index (the number of leaves plus the place) as one word; `rsOf_inj`, `index_inj`: it
    is one-to-one in depth, place and salt, where the index is below 2 ^ 64. Whoever spells the
    typed query on that leaf as a string has to read this layout: salt first, then the index.
  `toBPrfW`: the proof string; nothing if the first chain has no run's value or a stretch's plain
    parts do not type.
Main theorems, by unfolding: `toBPrfW_roots`, `toBPrfW_rtreq`; `toBPrfW_assemble`: a value is
`FileW.assemble` of the three, at every written file whose verifier is `wholeDesc ..`.

What is not said. That the compiled verifier accepts this string where the shipped verifier says
yes. That the views which the protocol forms of the transcript made from it are the reader's views.
Nothing on soundness.


-/
import OnBytes.Maker.TypingT
import OnBytes.Maker.WholeLaws
import OnBytes.TypedOracleCompiler.Joined.Assemble
import OnBytes.Proof.Tail
import Run.CodingBitsLaws
import Run.PageXSpare

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (opensApp ChainStr FileW)

section
variable {TF TJ T3 : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- The openings behind a silent round: none at the round itself. -/
def behind {T : Type} (t : T) {s : Shape}
    (f : (p : OPos s) → Option (Opening 256 (OSym s p))) :
    (p : OPos (plainRound T t :: s)) → Option (Opening 256 (OSym (plainRound T t :: s) p))
  | .inl e => e.elim
  | .inr q => f q

/-- What is read for the first chain: its roots, the front's plain part and the first stretch's, the
openings at its positions. tabs: the tables of all openings of the file, keyed by the tree's number
over the whole file. os: the chain's rounds as read, the seal among them (it sends no root). -/
def str₁ (pF : TF) (pl₁ : Plains (uLT C D.ds₁)) (tabs : List (ℕ × List (ℕ × Row3)))
    (os : List Fmt.RoundOut) : ChainStr 256 (chainsOf C D tF tJ t3).c₁ :=
  ⟨rootsT os, (pF, pl₁), behind tF (opensT C D.ds₁ 0 tabs)⟩

/-- What is read for the second chain. -/
def str₂ (pJ : TJ) (pl₂ : Plains (uLT C D.ds₂)) (tabs : List (ℕ × List (ℕ × Row3)))
    (os : List Fmt.RoundOut) : ChainStr 256 (chainsOf C D tF tJ t3).c₂ :=
  ⟨rootsT os, (pJ, pl₂), behind tJ (opensT C D.ds₂ D.t₁ tabs)⟩

/-- What is read for the third chain. -/
def str₃ (p3 : T3) (pl₃ : Plains (uLT C D.ds₃)) (tabs : List (ℕ × List (ℕ × Row3)))
    (os : List Fmt.RoundOut) : ChainStr 256 (chainsOf C D tF tJ t3).c₃ :=
  ⟨rootsT os, (p3, pl₃), behind t3 (opensT C D.ds₃ (D.t₁ + D.t₂) tabs)⟩

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- What stands behind the slot's value in the binding tree's leaf: the salt's bits, then the leaf's
index as one word of 64 bits in the byte format's spelling (`Fmt.u64n`). The index is the number of
the tree's leaves plus the place, as in the leaf's label in the byte format: so the string tells the
tree's depth too, and a key file's leaf (depth 0) and a proof file's are two strings. -/
def rsOf (index : ℕ) (salt : ByteArray) : List Bool :=
  bytesToBits salt ++ bytesToBits (Fmt.u64n index)

/-- The index tells depth and place. -/
theorem index_inj {d e p q : ℕ} (hp : p < 2 ^ d) (hq : q < 2 ^ e) (h : 2 ^ d + p = 2 ^ e + q) :
    d = e ∧ p = q := by
  have key : ∀ {d e p q : ℕ}, p < 2 ^ d → 2 ^ d + p = 2 ^ e + q → ¬ d < e := by
    intro d e p q hp h hlt
    have h2 : 2 ^ (d + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) hlt
    rw [Nat.pow_succ] at h2
    omega
  have hde : d = e := by
    rcases Nat.lt_trichotomy d e with h1 | h1 | h1
    · exact absurd h1 (key hp h)
    · exact h1
    · exact absurd h1 (key hq h.symm)
  subst hde
  exact ⟨rfl, by omega⟩

/-- It is one-to-one on indices below 2 ^ 64. Above, the word holds the index modulo 2 ^ 64. -/
theorem rsOf_inj {p q : ℕ} {s t : ByteArray} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (h : rsOf p s = rsOf q t) : p = q ∧ s = t := by
  unfold rsOf at h
  have hl := congrArg List.length h
  rw [List.length_append, List.length_append, length_u64n, length_u64n] at hl
  obtain ⟨h1, h2⟩ := List.append_inj h (by omega)
  exact ⟨bits_u64n_inj hp hq h2, bytesToBits_inj h1⟩

/-- **The typing of a whole file.** r: the three chains as read. The first stretch is the first
chain without its last round, the seal. salt, path: the salt and the siblings of the leaf in the
binding tree. -/
def toBPrfW (pF : TF) (pJ : TJ) (p3 : T3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ D.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead) :
    Option (OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) :=
  match r.first.out.run, plainsT C D.ds₁ r.first.out.rounds.toList.dropLast,
      plainsT C D.ds₂ r.shared.out.rounds.toList, plainsT C D.ds₃ r.second.out.rounds.toList with
  | some run₁, some pl₁, some pl₂, some pl₃ =>
    let k₁ := str₁ C D tF tJ t3 pF pl₁ tabs r.first.out.rounds.toList
    let k₂ := str₂ C D tF tJ t3 pJ pl₂ tabs r.shared.out.rounds.toList
    let k₃ := str₃ C D tF tJ t3 p3 pl₃ tabs r.second.out.rounds.toList
    some
      { salt := bytesToBits run₁
        roots := k₁.roots ++ (k₂.roots ++ k₃.roots)
        plains := Plains.app (s := (chainsOf C D tF tJ t3).c₁)
          (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) k₁.plains
          (Plains.app (s := (chainsOf C D tF tJ t3).c₂) (t := (chainsOf C D tF tJ t3).c₃)
            k₂.plains k₃.plains)
        opens := opensApp (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) k₁.opens
          (opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
            k₂.opens k₃.opens)
        ext := ext
        rtreq := bytesToDig r.place.root
        slot := r.place.place
        path := path.map bytesToDig
        rsalt := rsOf (r.place.places + r.place.place) salt }
  | _, _, _, _ => none

theorem toBPrfW_roots (pF : TF) (pJ : TJ) (p3 : T3) (tabs ext salt path) (r : Proof.TailRead) (π)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π) :
    π.roots = rootsT r.first.out.rounds.toList ++
      (rootsT r.shared.out.rounds.toList ++ rootsT r.second.out.rounds.toList) := by
  unfold toBPrfW at h
  split at h
  · cases h
    rfl
  · cases h

theorem toBPrfW_rtreq (pF : TF) (pJ : TJ) (p3 : T3) (tabs ext salt path) (r : Proof.TailRead) (π)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π) :
    π.rtreq = bytesToDig r.place.root := by
  unfold toBPrfW at h
  split at h
  · cases h
    rfl
  · cases h

/-- **A value is the assembly of the three chains' strings**, at every written file whose verifier
is this description's. -/
theorem toBPrfW_assemble {I X : Type} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X}
    {Wb : TypedOracleCompiler.Iop.QueryLayout 256 L} (t) (wq) (embS) (embP) (xin) (embE)
    (pF : TF) (pJ : TJ) (p3 : T3) (tabs ext salt path) (r : Proof.TailRead) (π)
    (h : toBPrfW C D tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π) :
    ∃ run₁ pl₁ pl₂ pl₃, r.first.out.run = some run₁ ∧
      plainsT C D.ds₁ r.first.out.rounds.toList.dropLast = some pl₁ ∧
      plainsT C D.ds₂ r.shared.out.rounds.toList = some pl₂ ∧
      plainsT C D.ds₃ r.second.out.rounds.toList = some pl₃ ∧
      π = FileW.assemble (W := Wb)
        ⟨wholeDesc C D tF tJ t3 silent run, t, wq, embS, embP, xin, embE⟩ (bytesToBits run₁)
        (str₁ C D tF tJ t3 pF pl₁ tabs r.first.out.rounds.toList)
        (str₂ C D tF tJ t3 pJ pl₂ tabs r.shared.out.rounds.toList)
        (str₃ C D tF tJ t3 p3 pl₃ tabs r.second.out.rounds.toList) ext
        (bytesToDig r.place.root) r.place.place (path.map bytesToDig)
        (rsOf (r.place.places + r.place.place) salt) := by
  unfold toBPrfW at h
  split at h
  · rename_i run₁ pl₁ pl₂ pl₃ h1 h2 h3 h4
    cases h
    exact ⟨run₁, pl₁, pl₂, pl₃, h1, h2, h3, h4, rfl⟩
  · cases h

end

end OnBytes.Maker
