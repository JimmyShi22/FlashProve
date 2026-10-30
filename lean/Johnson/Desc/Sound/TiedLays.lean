-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedLays.lean: THE TIE AT A SEAT FOR A ROW WHOSE EXTRACTOR LAYS. A rule over
letters; nothing in it names a kind. NO RESULT ON THE PROTOCOL.

Why. `tiedBy_of_part` (TiedLift.lean) and `tiedBy_of_seat` (TiedSeat.lean) serve the rows at which
the table's extractor lays nothing (hE). At the rows that lay (a message, a pad, the token) the
extractor reads the two statements, the public part with them.

What is said. E: the map that a description's piece bears as its extractor (the table's, at its
border). `atPub E z`: E read at the record alone, the public part a letter z.
  `tiedBy_liftAtE`: `TiedBy` at the piece p over the record with the extractor e z, FOR EVERY VALUE
    z OF THE PUBLIC PART, gives `TiedBy` at the lifted piece whose extractor reads z off the
    statement.
  `withMap_is_liftAtE`: a description's piece whose block is b₀ lifted, with ANY map E as its
    extractor, IS that lifted piece at e z := the extractor of ⟨b₀, …⟩ with the map `atPub E z`.
  **`tiedBy_of_partE`**, **`tiedBy_of_seatE`**: the forms for a given piece: as the two elder
    theorems, WITHOUT hE: the kind's law and ties are stated at ⟨below B', …⟩.withMap (atPub E z).

  `atPub_extQAt`: at the table's own extractor `atPub E z` IS that extractor at the
    kinds' reader fun s => (z, s): by unfolding.

Limits. A KIND AT A ROW THAT LAYS HAS ITS LAW AT ITS OWN EXTRACTOR: to stand at the piece with the
table's it still owes "at every yes my extractor is the table's" (`goodIn_withMap`'s premise,
ReExt.lean): THE debt of these rows; this file cannot give it. "For every z": also at public parts
that no run reaches. A carriage: the premises are met by no block here. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedSeat
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {P Cl W : Type} {C : CK} {F : Frame}

/-- The map E read at the record alone, the public part a letter. -/
def atPub (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) (z : P) :
    First.S × F.E.Str → First.S × F.E.Str → W → W :=
  fun a b w => E ((z, a.1), a.2) ((z, b.1), b.2) w

/-- What a piece with a map as its extractor extracts, written with the option's fold. -/
theorem withMap_ext_eq {S : Type} (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (w : W) :
    (p.withMap E).ext a τ w = (p.ior.red.out a τ).elim w fun b => E a b w := by
  cases h : p.ior.red.out a τ with
  | some b => exact withMap_ext p E a τ b w h
  | none =>
    show (p.withMap E).ext a τ w = w
    unfold Piece.withMap
    dsimp only
    split
    · rename_i b hb
      exact nomatch h.symm.trans hb
    · rfl

/-- A yes of the lifted piece is a yes of the piece at the record; the public part is laid back. -/
theorem out_liftAtE (p : Piece C F First.S Cl W)
    (e : P → First.S × F.E.Str → Iop.Tr (uLT C p.ds) → W → W) (a b : (P × First.S) × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds))
    (h : (p.liftAt Prod.snd (fun t s => (t.1, s)) Prod.fst e).ior.red.out a τ = some b) :
    ∃ x, p.ior.red.out (a.1.2, a.2) τ = some x ∧ b = ((a.1.1, x.1), x.2) := by
  have e' := liftOut (P × First.S) First.S Cl W C F Prod.snd (fun t s => (t.1, s)) p
    (fun _ _ => rfl) (fun _ _ _ => rfl) a τ
  have h' : (p.lift Prod.snd fun t s => (t.1, s)).ior.red.out a τ = some b := h
  rw [e'] at h'
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨x, hx, rfl⟩

section
variable (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)

/-- **THE TIES PASS THE LIFT OVER THE PUBLIC PART, THE EXTRACTOR READING IT.** -/
theorem tiedBy_liftAtE (p : Piece C F First.S Cl W)
    (e : P → First.S × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedBy N Mg links ps (fun s => (z, s)) k (p.withExt (e z)) (o z) (o' z) (R z)
      (R' z)) :
    TiedBy N Mg links ps (fun a => a) k (p.liftAt Prod.snd (fun t s => (t.1, s)) Prod.fst e)
      (fun a => o a.1.1 (a.1.2, a.2)) (fun a => o' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  refine ⟨liftGoodInExt (P × First.S) First.S P Cl W C F Prod.snd (fun t s => (t.1, s)) Prod.fst p
      e o o' R R' (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun z => (H z).1),
    fun a ha hm => (H a.1.1).2.1 (a.1.2, a.2) ha hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a τ b ha hm hb ho
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.1 (a.1.2, a.2) τ x ha hm hx ho
  · intro a τ b w ha hm hb ho hw
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.1 (a.1.2, a.2) τ x w ha hm hx ho hw
  · intro a τ b w ha hm hb ho hw hr
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.1 (a.1.2, a.2) τ x w ha hm hx ho hw hr
  · intro a τ b w i ha hm hb hon hall hi hin
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.1 (a.1.2, a.2) τ x w i ha hm hx hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.1 (a.1.2, a.2) τ x hx hm
  · intro a τ b hb hd
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.2 (a.1.2, a.2) τ x hx hd

end

/-- A description's piece whose block is b₀ lifted, with any map as its extractor, IS the lifted
piece whose extractor is that map read at the record. -/
theorem withMap_is_liftAtE (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) :
    q.withMap E = (⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C F First.S Cl W).liftAt Prod.snd (fun t s => (t.1, s)) Prod.fst
        fun z => ((⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece C F First.S Cl W).withMap (atPub E z)).ext := by
  obtain ⟨bq, base, ds, back, ext, err⟩ := q
  dsimp only at hq
  subst hq
  have he : (Piece.withMap (⟨b₀.lift Prod.snd fun t s => (t.1, s), base, ds, back, ext, err⟩ :
      Piece C F (P × First.S) Cl W) E).ext = fun a τ w =>
      ((⟨b₀, base, ds, back, fun _ _ w => w, err⟩ : Piece C F First.S Cl W).withMap
        (atPub E a.1.1)).ext (a.1.2, a.2) τ w := by
    funext a τ w
    have e' := liftOut (P × First.S) First.S Cl W C F Prod.snd (fun t s => (t.1, s))
      (⟨b₀, base, ds, back, fun _ _ w => w, err⟩ : Piece C F First.S Cl W)
      (fun _ _ => rfl) (fun _ _ _ => rfl) a τ
    have e2 : (⟨b₀.lift Prod.snd fun t s => (t.1, s), base, ds, back, ext, err⟩ :
        Piece C F (P × First.S) Cl W).ior.red.out a τ =
        ((⟨b₀, base, ds, back, fun _ _ w => w, err⟩ : Piece C F First.S Cl W).ior.red.out
          (a.1.2, a.2) τ).map fun b => ((a.1.1, b.1), b.2) := e'
    rw [withMap_ext_eq, withMap_ext_eq, e2]
    cases (⟨b₀, base, ds, back, fun _ _ w => w, err⟩ : Piece C F First.S Cl W).ior.red.out
      (a.1.2, a.2) τ <;> rfl
  show (⟨_, base, ds, back, (Piece.withMap ⟨_, base, ds, back, ext, err⟩ E).ext, err⟩ :
    Piece C F (P × First.S) Cl W) = _
  rw [he]
  rfl

/-- **THE FORM FOR A GIVEN PIECE OF A DESCRIPTION's ROW, AT ANY MAP.** -/
theorem tiedBy_of_partE (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedBy N Mg links ps (fun s => (z, s)) k
      ((⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C F First.S Cl W).withMap
        (atPub E z)) (o z) (o' z) (R z) (R' z)) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  rw [withMap_is_liftAtE q b₀ hq E]
  exact tiedBy_liftAtE N Mg links ps k _ _ o o' R R' H

/-- **A BLOCK AT A SEAT IS TIED, WHATEVER ITS KIND, ALSO WHERE ITS ROW LAYS.** tie: LEFT TO THE
KIND's FILES: the tie at the table's own words at the piece over the carried record that holds
`below B` and bears the table's extractor read at the record, for every value z of the public part.
(The seat's two facts on B stand with the kind's files: they may spend them.) -/
theorem tiedBy_of_seatE (links : List ModelPart) (ps : List Place) (k : ℕ) (Bst B : Block First.S Cl)
    (q : Piece C F (P × First.S) Cl W) (hS : SeatOf Bst B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (N : Numbers) (Mg : Meaning P W)
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (tie : SeatOf Bst B → ∀ z : P, TiedBy N Mg links ps (fun s => (z, s)) k
      ((⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C F First.S Cl W).withMap (atPub E z))
      (onQ N Mg links ps (fun s => (z, s)) k) (onQ N Mg links ps (fun s => (z, s)) (k + 1))
      (relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k))
      (relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k))) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (onQ N Mg links ps (fun a => a) k)
      (onQ N Mg links ps (fun a => a) (k + 1)) (relAt (meansQ N Mg fun a => a) (insQ links ps k))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps k)) :=
  tiedBy_of_partE N Mg links ps k q (below B) hq E
    (fun z => onQ N Mg links ps (fun s => (z, s)) k)
    (fun z => onQ N Mg links ps (fun s => (z, s)) (k + 1))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k)) (tie hS)

open Cb Johnson.Pack OnBytes.Slice in
/-- **THE TABLE's EXTRACTOR READ AT THE RECORD IS THE TABLE's EXTRACTOR AT THE KINDS' READER**:
it reads its two statements through `get` alone: so what `tiedBy_of_seatE` asks of a
kind's files stands in their own words: the table's extractor at get := fun s => (z, s). -/
theorem atPub_extQAt (cs : OnBytes.Codes) {Xi Cells Tok : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × First.S → Tok) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (z : P) :
    atPub (F := F) (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun a => a) k) z =
      extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun s => (z, s)) k := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.withMap_ext_eq
#print axioms VerifiableInference.Desc.Sound.out_liftAtE
#print axioms VerifiableInference.Desc.Sound.atPub_extQAt
#print axioms VerifiableInference.Desc.Sound.tiedBy_liftAtE
#print axioms VerifiableInference.Desc.Sound.withMap_is_liftAtE
#print axioms VerifiableInference.Desc.Sound.tiedBy_of_partE
#print axioms VerifiableInference.Desc.Sound.tiedBy_of_seatE
