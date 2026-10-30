-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesPatch.lean: from an oracle O to O with another function's values put at some
strings (`patch O f`, OnBytes/TypedOracleCompiler/Slice/Shapes.lean): what of the verifier on bytes does not move,
if f is silent at the strings that are read.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed. So piece `Three.LinkId` of the tie named below
(OnBytes/TypedOracleCompiler/Slice/Shapes.lean) is not what a run of the Lean program gives: the program compares
the user's ID with `Key.commitmentId` (OnBytes/Key/Table.lean), the hash of the rule's string, and
`LinkId` at such an ID asks one answer of the hash at two different strings (`idCode_ne`,
Johnson/TypedOracleCompiler/Top/IdStringsApart.lean). By reading the definitions; no theorem says so.

Why. The tie "where the program returns 0, the verifier on bytes says yes" is aimed at one hash: the
format's realised oracle, with the second hash function's value at the string of a request. What is
known of the program is known at the format's oracle. `Three.VerifyB` hangs on its hash through five
things: its values at the public strings, the ID's string, two keys' records, three checkers'
values, and their logs. This file carries each of the five from O to `patch O f`.

Main definitions.
 `IsSeedStr s`         s is a string of the chain on which a table's seeds are drawn: the string of
                       a table's name, or of a block of the seeds' round at some start.
 `Quiet f`             f is silent at these, at the strings of calls with the number 169 and at
                       every key's string.
Main theorems.
 `blocksUnder_patch`, `seedUnder_patch`, `recUAt_patch`   A KEY'S RECORD DOES NOT MOVE.
 `Three.pub₀_patch`, `pub₁_patch`; `Three.At.pub_patch`   THE PUBLIC VALUES DO NOT MOVE.
 `id_patch`            THE ID'S STRING IS NOT PATCHED.
 `det_patch`, `ownLog_patch`   a checker whose own log under O holds no string at which f speaks
                       has under `patch O f` the value and the log that it has under O.
 `Three.At.linkId_patch`, `linkK_patch`, `linkE_patch`, `linkF_patch`, `clashB_patch`   so the four
                       pieces of the tie, and "the files show a clash", go over.
 `Three.At.linkK_or_patch`, `linkE_or_patch`   the key's (the entry's) piece, OR A CLASH IN ITS
                       OWN CHECKER'S LOG, goes over, with nothing asked of the other checkers.
 `quiet_of_codeOld`, `quiet_call`, `quiet_byte2`   a function that speaks at the strings of requests
                       alone (`codeOld`, OnBytes/Slice/CodeOfRequestDigest.lean) is quiet; it is silent at
                       every call under another number than 177, and behind the byte 2.

What is not claimed. A checker whose typing asks the oracle nothing (a plain function of the files,
then the typed verifier) needs nothing of this file. That any checker's log holds no patched string:
a hypothesis, owed for each file's part. (The proof file's checker is meant to ask at a request's
string: for it the hypothesis fails, and its piece is owed at the patched oracle itself.) No `Three`
is given. Nothing on the program. No probability. Nothing on any hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesAt
import OnBytes.Slice.DetLog
import OnBytes.Slice.CodeOfRequestDigest

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open _root_.Iop Rom _root_.Run
open OnBytes.Tie (IdKey idCode firstId)

/-- Where f is silent the patched oracle has the oracle's own value. -/
theorem patch_none (O : Fam (rom 256)) (f : List Bool → Option (Dig 256)) (s : List Bool)
    (h : f s = none) : patch O f () s = O () s := by
  unfold patch
  rw [h]
  rfl

/-- Where f speaks the patched oracle has f's value. -/
theorem patch_some (O : Fam (rom 256)) (f : List Bool → Option (Dig 256)) (s : List Bool)
    (x : Dig 256) (h : f s = some x) : patch O f () s = x := by
  unfold patch
  rw [h]
  rfl

/-! ## A key's record -/

/-- A string of the chain on which a table's seeds are drawn: the string of a table's name (a
call number 160), or the string of a block of the seeds' round at some start (a call number 162).
Any name, any start, any block. -/
def IsSeedStr (s : List Bool) : Prop :=
  (∃ name, s = bytesToBits (seedFirst name)) ∨ ∃ ρ0 j, s = bytesToBits (blockStr ρ0 j)

/-- The blocks that the draw reads do not move, if f is silent at the strings of the seeds'
chain. -/
theorem blocksUnder_patch (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, IsSeedStr s → f s = none) (name : ByteArray) (b : ℕ) :
    blocksUnder (patch O f) name b = blocksUnder O name b := by
  funext i
  unfold blocksUnder oB
  rw [patch_none O f _ (hf _ (Or.inl ⟨name, rfl⟩)), patch_none O f _ (hf _ (Or.inr ⟨_, _, rfl⟩))]

/-- Nor do the seeds of a key's table. -/
theorem seedUnder_patch (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, IsSeedStr s → f s = none) (lg s : ℕ) (k : IdKey) :
    seedUnder lg s k (patch O f) = seedUnder lg s k O := by
  rw [seedUnder_eq, seedUnder_eq, blocksUnder_patch O f hf]

/-- A KEY'S RECORD UNDER THE ORACLE DOES NOT MOVE, if f is silent at the strings of the seeds'
chain. -/
theorem recUAt_patch (z : Size) (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, IsSeedStr s → f s = none) (k : IdKey) :
    recUAt z (patch O f) k = recUAt z O k := by
  unfold recUAt
  rw [seedUnder_patch O f hf]

/-! ## The public values and the ID's string -/

section
variable {D : DecR} {Xi : Type} (Θ : Three D Xi)

/-- The values at the first public strings do not move, if f is silent there. -/
theorem Three.pub₀_patch (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (hf : ∀ s ∈ Θ.S₀, f s = none) : Θ.pub₀ (patch O f) = Θ.pub₀ O := by
  funext s
  unfold Three.pub₀ cutT own
  by_cases hs : s ∈ Θ.S₀
  · rw [if_pos hs, if_pos hs, patch_none O f s (hf s hs)]
  · rw [if_neg hs, if_neg hs]

/-- Nor do the values at the public strings that hang on these, if f is silent at both. -/
theorem Three.pub₁_patch (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (hf₀ : ∀ s ∈ Θ.S₀, f s = none) (hf₁ : ∀ s ∈ Θ.S₁ (Θ.pub₀ O), f s = none) :
    Θ.pub₁ (patch O f) = Θ.pub₁ O := by
  unfold Three.pub₁
  rw [Θ.pub₀_patch O f hf₀]
  funext s
  unfold cutT own
  by_cases hs : s ∈ Θ.S₁ (Θ.pub₀ O)
  · rw [if_pos hs, if_pos hs, patch_none O f s (hf₁ s hs)]
  · rw [if_neg hs, if_neg hs]

end

/-- f is silent at the strings through which the verifier on bytes reads its hash beside its
checkers' runs: the seeds' chain, the calls with the number 169, the keys' strings. -/
structure Quiet (f : List Bool → Option (Dig 256)) : Prop where
  /-- at no string of the seeds' chain -/
  seeds : ∀ s, IsSeedStr s → f s = none
  /-- at no string of a call with the number 169 -/
  pub : ∀ s, IsCall169 s → f s = none
  /-- at no key's string -/
  ids : ∀ k s, idCode k = some s → f s = none

/-- THE ID'S STRING IS NOT PATCHED. -/
theorem id_patch (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)} (hf : Quiet f) (k : IdKey)
    (s : List Bool) (hs : idCode k = some s) : patch O f () s = O () s :=
  patch_none O f s (hf.ids k s hs)

/-! ## A checker's value and log -/

/-- An algorithm whose log under O holds no string at which f speaks has one value under O and
under the patched oracle. -/
theorem det_patch {α : Type} (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (c : OComp (rom 256) α) (h : ∀ e ∈ (c.withTrace.det O).2, f e.2.1 = none) :
    c.det (patch O f) = c.det O :=
  det_eq_of_log O (patch O f) c fun e he =>
    (patch_none O f e.2.1 (h e he)).trans (log_ans O c e he).symm

/-- And one log. -/
theorem log_patch {α : Type} (O : Fam (rom 256)) (f : List Bool → Option (Dig 256))
    (c : OComp (rom 256) α) (h : ∀ e ∈ (c.withTrace.det O).2, f e.2.1 = none) :
    (c.withTrace.det (patch O f)).2 = (c.withTrace.det O).2 :=
  log_eq_of_log O (patch O f) c fun e he =>
    (patch_none O f e.2.1 (h e he)).trans (log_ans O c e he).symm

/-- The same of a part's checker's own log. -/
theorem ownLog_patch {γ Sg : Type} (s : PartO 256 γ Sg) (O : Fam (rom 256))
    (f : List Bool → Option (Dig 256)) (x : γ) (h : ∀ e ∈ s.ownLog O x, f e.2.1 = none) :
    s.ownLog (patch O f) x = s.ownLog O x :=
  log_patch O f (s.chk x) h

/-! ## The four pieces of the tie -/

namespace Three.At
variable {z : Size} {Xi : Type} {Θ : Three z.D Xi}

/-- THE PUBLIC VALUES DO NOT MOVE, at three parts whose public strings are strings of calls with
the number 169. -/
theorem pub_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) : Θ.pub₀ (patch O f) = Θ.pub₀ O ∧ Θ.pub₁ (patch O f) = Θ.pub₁ O :=
  ⟨Θ.pub₀_patch O f fun s hs => hf.pub s (h.pub₀ s hs),
    Θ.pub₁_patch O f (fun s hs => hf.pub s (h.pub₀ s hs)) fun s hs => hf.pub s (h.pub₁ _ s hs)⟩

/-- The piece for the ID and the two plain readers goes over. -/
theorem linkId_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (id : ZKCP.Digest 256) (d : Files) (a : Three.Hand)
    (hl : Θ.LinkId O id d a) : Θ.LinkId (patch O f) id d a := by
  obtain ⟨k0, k1, s, hs, hid⟩ := hl
  unfold Three.LinkId
  rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
  exact ⟨k0, k1, s, hs, (id_patch O hf _ s hs).trans hid⟩

/-- The key file's piece goes over, if its checker's own log under O holds no string at which f
speaks. -/
theorem linkK_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files) (a : Three.Hand)
    (hq : ∀ e ∈ (Θ.K (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hl : Θ.LinkK O d a) : Θ.LinkK (patch O f) d a := by
  obtain ⟨oK, c, r, u⟩ := hl
  unfold Three.LinkK
  rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
  refine ⟨oK, (det_patch O f _ hq).trans c, r, ?_⟩
  rw [h.recU] at u ⊢
  rw [recUAt_patch z O f hf.seeds]
  exact u

/-- The entry file's piece likewise. -/
theorem linkE_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files) (a : Three.Hand)
    (hq : ∀ e ∈ (Θ.E (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hl : Θ.LinkE O d a) : Θ.LinkE (patch O f) d a := by
  obtain ⟨oE, c, r, u0, u1⟩ := hl
  unfold Three.LinkE
  rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
  refine ⟨oE, (det_patch O f _ hq).trans c, r, ?_, ?_⟩
  · rw [h.recU] at u0 ⊢
    rw [recUAt_patch z O f hf.seeds]
    exact u0
  · rw [h.recU] at u1 ⊢
    rw [recUAt_patch z O f hf.seeds]
    exact u1

/-- The proof file's piece likewise. (A checker that asks at a patched string does not meet the
hypothesis on the log.) -/
theorem linkF_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files) (a : Three.Hand)
    (hq : ∀ e ∈ (Θ.F (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hl : Θ.LinkF O d a) : Θ.LinkF (patch O f) d a := by
  obtain ⟨oF, c, r, u, x⟩ := hl
  unfold Three.LinkF
  rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
  refine ⟨oF, (det_patch O f _ hq).trans c, r, ?_, x⟩
  rw [h.recU] at u ⊢
  rw [recUAt_patch z O f hf.seeds]
  exact u

/-- The key file's piece, or a clash in ITS OWN checker's log, goes over: to the piece, or to
"the files themselves show a clash", under the patched oracle. Nothing is asked of the two other
checkers. -/
theorem linkK_or_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files) (a : Three.Hand)
    (hq : ∀ e ∈ (Θ.K (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hl : Θ.LinkK O d a ∨ ¬ NoClash ((Θ.K (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d)) :
    Θ.LinkK (patch O f) d a ∨
      Θ.ClashB (Θ.pub₀ (patch O f)) (Θ.pub₁ (patch O f)) (patch O f) d := by
  rcases hl with hl | hc
  · exact Or.inl (h.linkK_patch O hf d a hq hl)
  · refine Or.inr ?_
    rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
    exact Or.inl (by rw [ownLog_patch _ O f d hq]; exact hc)

/-- The entry file's piece, or a clash in ITS OWN checker's log, goes over likewise. -/
theorem linkE_or_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files) (a : Three.Hand)
    (hq : ∀ e ∈ (Θ.E (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hl : Θ.LinkE O d a ∨ ¬ NoClash ((Θ.E (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d)) :
    Θ.LinkE (patch O f) d a ∨
      Θ.ClashB (Θ.pub₀ (patch O f)) (Θ.pub₁ (patch O f)) (patch O f) d := by
  rcases hl with hl | hc
  · exact Or.inl (h.linkE_patch O hf d a hq hl)
  · refine Or.inr ?_
    rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
    exact Or.inr (Or.inl (by rw [ownLog_patch _ O f d hq]; exact hc))

/-- "The files themselves show a clash" is one thing under both oracles, if none of the three
checkers' own logs under O holds a string at which f speaks. (The proof file's checker is meant to
ask at a patched string: then the third hypothesis fails, and this says nothing. For the key's and
the entry's pieces: `linkK_or_patch`, `linkE_or_patch`.) -/
theorem clashB_patch (h : Θ.At z) (O : Fam (rom 256)) {f : List Bool → Option (Dig 256)}
    (hf : Quiet f) (d : Files)
    (hK : ∀ e ∈ (Θ.K (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hE : ∀ e ∈ (Θ.E (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none)
    (hF : ∀ e ∈ (Θ.F (Θ.pub₀ O) (Θ.pub₁ O)).ownLog O d, f e.2.1 = none) :
    Θ.ClashB (Θ.pub₀ (patch O f)) (Θ.pub₁ (patch O f)) (patch O f) d ↔
      Θ.ClashB (Θ.pub₀ O) (Θ.pub₁ O) O d := by
  rw [(h.pub_patch O hf).1, (h.pub_patch O hf).2]
  unfold Three.ClashB
  rw [ownLog_patch _ O f d hK, ownLog_patch _ O f d hE, ownLog_patch _ O f d hF]

end Three.At

/-! ## The strings of requests -/

/-- A function that speaks at the strings of requests alone is silent at the string of every call
under a number that is not 177 modulo 65536: either half, any tree number, index, start and
bytes. m: the zero bytes behind the request. -/
theorem quiet_call (m : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld m w) {n : ℕ} (hn : n % 65536 ≠ 177) (half : UInt8)
    (t i : ℕ) (st bs : ByteArray) : f (bytesToBits (Fmt.oStr half n t i st bs)) = none := by
  by_contra hne
  obtain ⟨w, e⟩ := hf _ hne
  exact codeOld_ne_oStr m w hn half t i st bs e.symm

/-- And at every string that begins with the byte 2. -/
theorem quiet_byte2 (m : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld m w) (s : List Bool) (h2 : bitsOfByte 2 <+: s) :
    f s = none := by
  by_contra hne
  obtain ⟨w, rfl⟩ := hf s hne
  unfold codeOld at h2
  rw [oStr_bits] at h2
  exact hdr_not_prefix 2 0 (by decide) _ _ _ _ _ h2

/-- A function that speaks at the strings of requests alone is quiet: such a string is the
spelling of a call under the number 177; the seeds' chain has the numbers 160 and 162, the public
strings 169, a key's string 179. n: the zero bytes behind the request. -/
theorem quiet_of_codeOld (n : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld n w) : Quiet f where
  seeds := fun s hs => by
    by_contra hne
    obtain ⟨w, rfl⟩ := hf s hne
    rcases hs with ⟨name, e⟩ | ⟨ρ0, j, e⟩
    · exact codeOld_ne_oStr n w (n := 160) (by decide) _ _ _ _ _ e
    · exact codeOld_ne_oStr n w (n := 162) (by decide) _ _ _ _ _ e
  pub := fun s hs => by
    by_contra hne
    obtain ⟨w, rfl⟩ := hf s hne
    obtain ⟨half, t, i, st, bs, -, -, e⟩ := hs
    exact codeOld_ne_oStr n w (n := 169) (by decide) _ _ _ _ _ e
  ids := fun k s hs => by
    by_contra hne
    obtain ⟨w, rfl⟩ := hf s hne
    exact Tie.idCode_ne_call (n := 177) (by decide) _ _ _ _ _ k hs

end OnBytes.Slice.Shapes
