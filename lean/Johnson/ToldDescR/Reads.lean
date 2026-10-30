-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/ToldDescR/Reads.lean: WHAT THE PROOF FILE's DESCRIPTION
READS OF AN INSTANCE BEFORE THE FIRST ROUND.

Why. Two fields of the list of what is left of the proof file's hypothesis on soundness
(`ProofPlainOwedAtF`, Johnson/Flat/Dec/ProofPlainAtF.lean: pubEarly · one) ask that the public part
of an instance does not read the reply, and that the shared chain's first state reads of the
instance the table's key alone. Both are read off the description's make here, for every
description that `ProofFile.onlineDescription` makes, whatever the three public files and the letter for the
format's second hash function are.
Main names.
  `ReadsKeyAlone F`          the two laws, said of a description over `ProofFile.Inst`
  `ok_of_bind_ok`            where `Except.bind` says ok, both its parts did
  `pureZ_make`               what `onlineDescriptionFromPublicPart` makes is `fileDescBy` at the seat's own two later chains
  `laterShared_start`        the shared seat that the ride lays starts from the key alone
  `readsKeyAlone_fileDescBy` the two laws at `fileDescBy`, from that law of the shared seat
  `readsKeyAlone_descPure`   **the two laws at every description that `onlineDescription` makes**
Called lemmas. That `onlineDescription`'s yes is `onlineDescriptionFromPublicPart`'s at the road's public part and the ride's seat, and
what `onlineDescriptionFromPublicPart`'s yes says of F, are lemmas of `onlineDescription`'s own files
(`ProofFile.Law.descPure_made`, Johnson/Desc/ProofFile/Law/MakerPublic.lean; `pureZ_ok` and `pureTail_ok`,
Law/PureMade.lean): called here; `pureZ_make` is a short form of the last two.
Limits. Nothing is said on whether `onlineDescription` makes a description at given files (where it refuses,
the last theorem says nothing). Nothing on what the blocks read later: a block is handed the state,
and the first chain's first state does hold the request's words. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace ToldDesc
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First
open ProofFile

/-- The public part of an instance is a function of `Inst.pub`, and the shared chain's first state
is a function of the table's key. -/
structure ReadsKeyAlone (F : FileDescription ProofFile.Inst) : Prop where
  pub : ∀ a b : ProofFile.Inst, a.pub = b.pub → F.pub a = F.pub b
  shared : ∀ a b : ProofFile.Inst, a.pub.key = b.pub.key → F.start₂ (F.pub a) = F.start₂ (F.pub b)

/-- Where `Except.bind` says ok, its first part said ok, and its second part did at that value. -/
theorem ok_of_bind_ok {ε : Type u} {α : Type v} {β : Type w} {a : Except ε α}
    {f : α → Except ε β} {y : β} (h : a.bind f = .ok y) : ∃ x, a = .ok x ∧ f x = .ok y := by
  cases a with
  | error e =>
    have h' : (Except.error e : Except ε β) = Except.ok y := h
    cases h'
  | ok x => exact ⟨x, rfl, h⟩

/-- What `onlineDescriptionFromPublicPart` makes is `fileDescBy` at the seat's own shared and second chain, at the seat's own
letter for the second hash function. This is a short form of
`ProofFile.Law.pureZ_ok` and `pureTail_ok` (Johnson/Desc/ProofFile/Law/PureMade.lean), called here:
they say more (the base, both lists empty, the chain by `chainBy`). -/
theorem pureZ_make {Z : ProofFile.Pub} {T : PureSeat} {F : FileDescription ProofFile.Inst} (h : onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ A B c, T.shared = some A ∧ T.second = some B ∧
      F = fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c := by
  obtain ⟨_, -, -, -, ht⟩ := ProofFile.Law.pureZ_ok h
  obtain ⟨_, c, A, B, -, -, hA, hB, hE⟩ := ProofFile.Law.pureTail_ok ht
  exact ⟨A, B, c, hA, hB, hE⟩

/-- The shared seat that the ride lays starts from the key alone: its `start` is
`fun x => first P.codes x.key` (Johnson/Desc/ProofFile/Lot/K14Seat.lean; seated by K14SeatAtZ.lean). -/
theorem laterShared_start {Z : ProofFile.Pub} {A : SharedSeat} (h : laterShared Z = some A)
    (p q : InstPub) (hk : p.key = q.key) : A.start p = A.start q := by
  unfold laterShared Desc.K14.sharedSeatAt at h
  split at h
  · cases h
    obtain ⟨r₁, k₁⟩ := p
    obtain ⟨r₂, k₂⟩ := q
    have h' : k₁ = k₂ := hk
    subst h'
    rfl
  · cases h

/-- The two laws at `fileDescBy`, where the shared seat starts from the key alone. -/
theorem readsKeyAlone_fileDescBy {σ : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub)
    (A : SharedSeat) (B : SecondSeat) (get : σ → S) (start : InstPub → σ) (c : Chain σ ProofFile.Cl)
    (hA : ∀ p q : InstPub, p.key = q.key → A.start p = A.start q) :
    ReadsKeyAlone (fileDescBy o mk Z A B get start c) :=
  ⟨fun _ _ h => h, fun a b h => hA a.pub b.pub h⟩

/-- **The two laws at every description that `onlineDescription` makes.** -/
theorem readsKeyAlone_descPure {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) : ReadsKeyAlone F := by
  obtain ⟨Z, -, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, hA, -, rfl⟩ := pureZ_make h
  have hA' : laterShared Z = some A := hA
  exact readsKeyAlone_fileDescBy _ _ Z A B _ _ c (laterShared_start hA')

end ToldDesc

#print axioms ToldDesc.ok_of_bind_ok
#print axioms ToldDesc.pureZ_make
#print axioms ToldDesc.laterShared_start
#print axioms ToldDesc.readsKeyAlone_fileDescBy
#print axioms ToldDesc.readsKeyAlone_descPure
