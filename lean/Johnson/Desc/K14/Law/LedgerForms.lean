-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerForms.lean: THE JOINT BETWEEN A DESCRIPTION's ROW OF PIECES AND THE ONE
TERM (share_row, Johnson/Desc/K14/Law/LedgerRow.lean). share_row speaks of pieces in given forms:
they hold, in the wrap, blocks that decide as the kind's; the two sendings have two written rounds,
"LOC" and "LIN zeta" one; nothing is put behind. HERE THESE FORMS ARE HAD BY PROOF at any row of
twelve pieces that (i) holds the blocks of the shared chain (chainOf c Q [t9, t10] last).retype,
carried to the description's type of claims as the one base's fold lays it, as a description's
pieces do (the equation b₂ of OfDesc, Johnson/Desc/Sound/DescThree.lean) and (ii) is tiled (Tiled,
Johnson/Desc/Sound/ChainRule.lean). And THE KIND K14's OWN ERRORS ARE A TERM.

  piece_eta1, piece_eta2   a piece that holds heldW b, with one | two rounds and nothing put behind,
                  is pc1 | pc2 of its own data.
  retype_as       a block carried to another type of claims decides as the block.
  row_forms       **the forms.**
  last_exact      the shared chain's own last block, carried and in the flat list's wrap, is exact
                  for the end's test.
  errZero, ownDs, ownK   **the kind's own errors**: the four written counts at 2, 4, 5, 7; ZERO at
                  3, 6, 8, 11; a letter at every other number. ownK_two … ownK_seven: by rfl.
What is not claimed. That a file's description has that chain as its shared chain (the fold's text;
at the seat: piece_at_the_fold). Nothing on the rounds' data. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRow
import Johnson.Desc.K14.Law.FlatRetype
import Johnson.Desc.K14.Law.RoundsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.ChainEnd (untestedL Exact chainEnd_exact)
open VerifiableInference.Desc.K1 (seedMaps)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-- A piece that holds a block in the wrap, at one round, with nothing put behind. -/
theorem piece_eta1 (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (b : Block St Cl) (hb
    : x.b = heldW b) (hk : x.back = []) (hl : x.ds.length = 1) :
    ∃ d ex er, x = pc1 b x.base d ex er := by
  obtain ⟨xb, base, ds, back, ext, err⟩ := x
  dsimp only at hb hk hl
  obtain ⟨d, rfl⟩ := List.length_eq_one_iff.1 hl
  subst hb hk
  exact ⟨d, ext, err, rfl⟩

/-- The like at two rounds. -/
theorem piece_eta2 (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (b : Block St Cl) (hb
    : x.b = heldW b) (hk : x.back = []) (hl : x.ds.length = 2) :
    ∃ d₁ d₂ ex er, x = pc2 b x.base d₁ d₂ ex er := by
  obtain ⟨xb, base, ds, back, ext, err⟩ := x
  dsimp only at hb hk hl
  obtain ⟨d₁, d₂, rfl⟩ := List.length_eq_two.1 hl
  subst hb hk
  exact ⟨d₁, d₂, ext, err, rfl⟩

/-- A block carried to another type of claims decides as the block. -/
theorem retype_as (b : Block St Unit) : DecidesAs (b.retype (Cl' := Cl)) b := fun _ _ _ => rfl

/-- **The forms that the one term asks, at a description's row of pieces**: the shared chain carried
    to
the description's type of claims, as the one base's fold lays it. -/
theorem row_forms (c : Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 t9 t10 : Block St
    Unit)
    (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (f pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hmap : (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]).map (·.b) =
      (((chainOf c Q [t9, t10] last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s)))
    (ht : Tiled f [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) :
    (∃ d₁ d₂ ex er, x2 = pc2 b2.retype x2.base d₁ d₂ ex er) ∧ x3.b = heldW b3.retype ∧
      (∃ d ex er, x4 = pc1 b4.retype x4.base d ex er) ∧
      (∃ d₁ d₂ ex er, x5 = pc2 b5.retype x5.base d₁ d₂ ex er) ∧
      x6.b = heldW b6.retype ∧ (∃ d ex er, x7 = pc1 b7.retype x7.base d ex er) ∧
      x8.b = heldW b8.retype ∧
      x11.b = heldW (bareOf (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10])).retype) ∧
      Tiled x2 [x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
  have g := piece_retype_at (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) c Q b1 b2 b3 b4 b5
    b6 b7 b8 [t9, t10] last hbl hmap
  obtain ⟨q2, e2, h2⟩ := g 1 b2 rfl
  obtain ⟨q3, e3, h3⟩ := g 2 b3 rfl
  obtain ⟨q4, e4, h4⟩ := g 3 b4 rfl
  obtain ⟨q5, e5, h5⟩ := g 4 b5 rfl
  obtain ⟨q6, e6, h6⟩ := g 5 b6 rfl
  obtain ⟨q7, e7, h7⟩ := g 6 b7 rfl
  obtain ⟨q8, e8, h8⟩ := g 7 b8 rfl
  obtain rfl : x2 = q2 := Option.some.inj e2
  obtain rfl : x3 = q3 := Option.some.inj e3
  obtain rfl : x4 = q4 := Option.some.inj e4
  obtain rfl : x5 = q5 := Option.some.inj e5
  obtain rfl : x6 = q6 := Option.some.inj e6
  obtain rfl : x7 = q7 := Option.some.inj e7
  obtain rfl : x8 = q8 := Option.some.inj e8
  have hc : chainOf c Q [t9, t10] last =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10]
        last := last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10]) } := by
    simp [chainOf, blocksOr, hbl]
  have h11 : x11.b =
      heldW (bareOf (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10])).retype) := by
    rw [hc] at hmap
    exact Option.some.inj (congrArg (fun L => L[11]?) hmap)
  obtain ⟨-, -, -, -, -, -, -, -, ht2⟩ := ht
  have hcn := rounds_counts Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcn
  obtain ⟨-, c2, -, c4, c5, -, c7, -⟩ := hcn
  have ht2' := ht2
  obtain ⟨o2, -, k2, -, -, -, -, -, o4, -, k4, -, o5, -, k5, -, -, -, -, -, o7, -, k7, -⟩ := ht2'
  have len : ∀ (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (b : Block St Unit) (n :
      ℕ), x.b = heldW b.retype → x.back = [] →
      x.Owed → b.rounds.length = n → x.ds.length = n := by
    intro x b n hb hk ho hn
    have h := ho.1
    rw [hk, hb] at h
    have h' : x.ds.length + 0 = b.rounds.length := h
    omega
  exact ⟨piece_eta2 x2 _ h2 k2 (len x2 b2 2 h2 k2 o2 c2), h3,
    piece_eta1 x4 _ h4 k4 (len x4 b4 1 h4 k4 o4 c4), piece_eta2 x5 _ h5 k5 (len x5 b5 2 h5 k5 o5
        c5),
    h6, piece_eta1 x7 _ h7 k7 (len x7 b7 1 h7 k7 o7 c7), h8, h11, ht2⟩

/-- The shared chain's own last block, carried and in the flat list's wrap, is exact for the end's
test. -/
theorem last_exact (front : List (Block St Unit)) :
    Exact (fun d : St => untestedL d.st)
      (bareOf ((VerifiableInference.Desc.K12.Seat.last front).retype (Cl' := Cl))) :=
  fun s rs gs s' => chainEnd_exact (Cl := Unit) 2 11 true (front.flatMap (·.rounds))
    (fun d : St => untestedL d.st) s rs gs s'

/-- No error at any round. -/
def errZero : (s : Iop.Shape) → Err s
  | [] => ()
  | _ :: s => (0, errZero s)

/-- The kind's own errors, by the block's number and its stretch's rounds. (At 2, 4, 5, 7 with
    another
number of rounds than row_forms gives: zero; no clause is stated there.) -/
def ownDs (c2 e2 logN n e4 c5 e5 kRow e7 : ℕ) : (k : ℕ) → (ds : List RDT) → Err (uLT (ckP .two) ds)
  | 2, [d₁, d₂] => (seedMaps d₁ d₂ c2).err ((e2, ()) : ℕ × Unit)
  | 4, [d] => (posMaps d logN n).err ((e4, ()) : ℕ × Unit)
  | 5, [d₁, d₂] => (seedMaps d₁ d₂ c5).err ((e5, ()) : ℕ × Unit)
  | 7, [d] => (vecMaps d kRow).err ((e7, ()) : ℕ × Unit)
  | _, _ => errZero _

/-- **The kind's own errors**: a letter at the two proximity tests and in front of block 2. -/
def ownK (c2 e2 logN n e4 c5 e5 kRow e7 : ℕ)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) :
    OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT) := fun k x =>
  if k < 2 ∨ k = 9 ∨ k = 10 then rest k x else ownDs c2 e2 logN n e4 c5 e5 kRow e7 k x.ds

section
variable (c2 e2 logN n e4 c5 e5 kRow e7 : ℕ)
  (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (b : Block St Cl) (base : ℕ)

theorem ownK_two (d₁ d₂ : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells
        Tok MsgT)
    (er : Err (uLT (ckP .two) [d₁, d₂])) :
    ownK c2 e2 logN n e4 c5 e5 kRow e7 rest 2 (pc2 b base d₁ d₂ ex er) =
      (seedMaps d₁ d₂ c2).err ((e2, ()) : ℕ × Unit) := rfl

theorem ownK_four (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok
        MsgT)
    (er : Err (uLT (ckP .two) [d])) :
    ownK c2 e2 logN n e4 c5 e5 kRow e7 rest 4 (pc1 b base d ex er) =
      (posMaps d logN n).err ((e4, ()) : ℕ × Unit) := rfl

theorem ownK_five (d₁ d₂ : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells
        Tok MsgT)
    (er : Err (uLT (ckP .two) [d₁, d₂])) :
    ownK c2 e2 logN n e4 c5 e5 kRow e7 rest 5 (pc2 b base d₁ d₂ ex er) =
      (seedMaps d₁ d₂ c5).err ((e5, ()) : ℕ × Unit) := rfl

theorem ownK_seven (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok
        MsgT)
    (er : Err (uLT (ckP .two) [d])) :
    ownK c2 e2 logN n e4 c5 e5 kRow e7 rest 7 (pc1 b base d ex er) =
      (vecMaps d kRow).err ((e7, ()) : ℕ × Unit) := rfl

end

end Desc.K14.Law

#print axioms Desc.K14.Law.row_forms
#print axioms Desc.K14.Law.last_exact
#print axioms Desc.K14.Law.ownK_two
#print axioms Desc.K14.Law.ownK_seven
