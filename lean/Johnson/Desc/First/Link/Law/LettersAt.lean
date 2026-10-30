-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LettersAt.lean: AT THE TABLE's ONE ACCESSOR (`tabAt`,
Johnson/Desc/First/Batch/Law/AtTable.lean) THE WITNESS's TABLES ARE THE SAME FUNCTION IN FRONT OF
AND BEHIND EACH OF THE LAW's THREE PIECES: the law's premises htabb, htabq and htab (LinkOwes.lean:
`OwesLetters`); and the frame's move behind the batching leaves the book (LinkTable.lean:
`TableOwes.hbook₂`). Theorems.

Why. The accessor reads the verifier's state through its book of commitment trees and through the
statement's numbers of row bits, where the batching kind's lens finds its part. The batching and the
frame's sub-protocol behind it leave the statement and the book (`Rb`); the one equation takes mask
entries and adds an open row: neither turns a number of bits.

What is said.
  `tab_of_rb`: `Rb`, with a part in front and behind, gives one function. `parts_batch`: at an
    accepting step of the batching a part is there in front and behind. `htabb_at`: **htabb**, from
    `TwoBlocks`. `htabq_at`: **htabq**, from `TwoBlocks` and «a part is there» at the two
    conditions. `htab_at`: **htab**, at a piece that holds a block each of whose accepting steps is
    the one equation's. `hbook2_at`: **hbook₂**, from the runs' share at the book.

Limits. `TwoBlocks` and the runs' share are LinkAtSort.lean's (the sort's Take; the lookup's one
sentence). htabq_at takes «a part is there» behind the frame's sub-protocol from the condition
there, through the law's own h12 and hs2. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.First.Batch.Law.TableTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run.PQ (CK)

/-- Rb, with a part in front and behind, gives one function. -/
theorem tab_of_rb (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s s' : S) (R : Rb s s')
    (h : (atS.get? s).isSome = true) (h' : (atS.get? s').isSome = true) :
    tabAt own rd s' = tabAt own rd s := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 h'
  refine tabAt_same own rd s s' a a' ha ha' ?_ R.book
  rw [(part_reads s a ha).2, (part_reads s' a' ha').2, R.st]
  exact SameBits.refl _

/-- At an accepting step of the batching a part is there in front and behind. -/
theorem parts_batch (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) :
    (atS.get? s).isSome = true ∧ (atS.get? s').isSome = true := by
  obtain ⟨r, x, a, o, cls, _, _, ha, _, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, _, hq, _, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  obtain ⟨b', hb', _⟩ := atS_reads e { q with F := G } (by rw [hq]; rfl)
  exact ⟨by rw [ha]; rfl, by rw [hb']; rfl⟩

variable {W : Type} {C : CK} {F : Frame}

/-- **htabb.** -/
theorem htabb_at (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (L : Link S Claim) (pp : Where)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (T : TwoBlocks L pp) (pb : Piece C F S Claim W) (hpb : pb.b = below L.batchB) :
    ∀ (a : S × F.E.Str) τ b' (w : W), pb.ior.red.out a τ = some b' →
      tabAt own (rdW w) b'.1 = tabAt own (rdW w) a.1 := by
  intro a τ b' w hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨h1, h2⟩ := parts_batch L pp hb₁ _ _ _ _ _ j hstep
  exact tab_of_rb own (rdW w) a.1 b'.1 (T.1 _ _ _ _ _ j hstep).1 h1 h2

/-- **htabq.** -/
theorem htabq_at (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (L : Link S Claim) (pp : Where)
    (T : TwoBlocks L pp) (pq : Piece C F S Claim W) (hpq : pq.b = below L.behindB)
    (on1 on2 : S × F.E.Str → Prop) (hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true)
    (h12 : ∀ b τ c, on1 b → pq.ior.red.out b τ = some c → on2 c)
    (hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true) :
    ∀ a τ b' (w : W), on1 a → pq.ior.red.out a τ = some b' →
      tabAt own (rdW w) b'.1 = tabAt own (rdW w) a.1 := by
  intro a τ b' w ha hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact tab_of_rb own (rdW w) a.1 b'.1 (T.2 _ _ _ _ _ j hstep).1 (hs1 a ha)
    (hs2 b' (h12 a τ b' ha hout))

/-- **htab.** -/
theorem htab_at (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim W) (hpe : pe.b = below b₃) :
    ∀ (a : S × F.E.Str) τ b' (w : W), pe.ior.red.out a τ = some b' →
      tabAt own (rdW w) b'.1 = tabAt own (rdW w) a.1 := by
  intro a τ b' w hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨a0, out, ha0, hdoor, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ hs)
  obtain ⟨n, q, G, row, d1, _, _, _, hrow, hd, _, _⟩ := door_parts _ _ _ _ _ out hdoor
  obtain ⟨a1, ha1, _, _, e3⟩ :=
    atS_reads a.1 { a0 with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha0])
  rw [← hs'] at ha1
  have hst : a1.d.st = out.d.st := e3
  refine tabAt_same own (rdW w) a.1 b'.1 a0 a1 ha0 ha1 ?_ (by rw [hs', book_set])
  rw [hst, hd]
  exact (asRow_bits _ _ _ _ _ _ hrow).trans (withRow_bits _ _ _)

/-- **hbook₂**: the frame's move behind the batching leaves the book. -/
theorem hbook2_at {α : Type} (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      e₁.book = e.book) :
    ∀ m ∈ (moves₂ (α := α) L).map (·.move), MoveBook m := by
  intro m hm
  obtain rfl : m = .quiet L.runBehind := by simpa [moves₂] using hm
  exact runBehind_keep (·.book) L hk

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.htabb_at
#print axioms VerifiableInference.Desc.LinkJoin.htabq_at
#print axioms VerifiableInference.Desc.LinkJoin.htab_at
#print axioms VerifiableInference.Desc.LinkJoin.hbook2_at
