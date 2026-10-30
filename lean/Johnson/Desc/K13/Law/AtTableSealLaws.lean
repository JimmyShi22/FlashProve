-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealLaws.lean: WHAT A KIND's FILES OWE AT A SEAT (SeatLaws,
Johnson/Desc/Sound/TiedSeat.lean), AT THE FIRST CHAIN's LAST BLOCK (First.firstEnd). Two theorems: a
joining of Johnson/Desc/K13/Law/AtTableSeal.lean with the table's files' rule.

OBJECT. First.firstEnd piece front; every block B' that narrows it (SeatOf), read strictly (below).
USER. tiedBy_of_seatLaws | tied_of_alone | KindTied (the table's files'): seal_seatLaws ends in
SeatLaws links ps k q N Mg (First.firstEnd piece front), to the letter.
LETTERS. The table's own; q: the description's piece at k: of it base, ds, back, err alone are read.
FIELD. first_chain_knows_means (Johnson/Goal/Skeleton/ProofFile.lean), through eachTied_of_kinds.

Main names:
  narrow_same     a yes of the strict reading of a block that narrows the seal returns the record.
  seal_seatLaws   **the four**: the block's own law at the table's words (seal_own) · what rides
    (seal_rides) · a mark stays · "decodes" rides.
What is not claimed. RowSeal and FillSeal are premises: as Johnson/Desc/K13/Law/AtTableSeal.lean
says. That the description seats that block at k: not here. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSeal
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ openAfter SeatOf
  SeatLaws below below_narrows)

section
variable {Pp Cl W : Type} {C : PQ.CK} {Fr : Frame}

/-- A yes of the strict reading of a block that narrows the seal returns the record. -/
theorem narrow_same (piece : ℕ) (front : List (Block S Cl)) (B' : Block S Cl)
    (hS : SeatOf (First.firstEnd piece front) B') (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (err : Err (uLT C ds)) (a : S × Fr.E.Str) (τ : Tr (uLT C ds)) (b : S × Fr.E.Str)
    (hb : (⟨below B', base, ds, back, fun _ _ w => w, err⟩ :
      Piece C Fr S Cl W).ior.red.out a τ = some b) : b.1 = a.1 := by
  obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
  exact Keeps.chainEnd_same _ _ _ _ _ (hS.1.2 _ _ _ _ ((below_narrows B').2 _ _ _ _ hdec))

/-- **WHAT K13's FILES OWE AT THE SEAL's SEAT.** -/
theorem seal_seatLaws (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (Pp × S) Cl W) (N : Numbers) (Mg : Meaning Pp W) (piece : ℕ)
    (front : List (Block S Cl)) (p : Place) (hT : RowSeal N Mg.more links ps k p)
    (hF : FillSeal N Mg q.base (openAt links ps k)
      fun i => openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i ∧
        ¬ insQ links ps k i) :
    SeatLaws links ps k q N Mg (First.firstEnd piece front) := by
  have hs : ∀ B', SeatOf (First.firstEnd piece front) B' → ∀ (z : Pp) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Cl W).ior.red.out a τ = some b →
      (fun s : S => (z, s)) b.1 = (fun s : S => (z, s)) a.1 := fun B' hS z a τ b hb => by
    show (z, b.1) = (z, a.1)
    rw [narrow_same piece front B' hS q.base q.ds q.back q.err a τ b hb]
  refine ⟨fun B' hS z => seal_own N Mg links ps _ k
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W) p _ hT hF
      (hs B' hS z),
    fun B' hS z a τ b w i _ _ hb _ hall hi hin =>
      seal_rides N Mg links ps _ k
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W) hF
        (hs B' hS z) a τ b w i hb hall hi hin,
    fun B' hS a τ b hb hm => ?_, fun B' hS z a τ b hb hd => ?_⟩
  · rw [narrow_same piece front B' hS q.base q.ds q.back q.err a τ b hb]
    exact hm
  · rw [narrow_same piece front B' hS q.base q.ds q.back q.err a τ b hb]
    exact hF.decodes _ _ _ (sameBelow_out _ hb) hd

end

end VerifiableInference.Desc.K13.Law
