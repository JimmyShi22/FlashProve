-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerLettersOfCut.lean: THE LETTERS OF THE LEDGER's ROW EXIST: a row of pieces
that holds the shared chain's blocks as a description's pieces do, and is tiled, IS f :: PT :: MM
in the forms in which the ledger's tops spell it (ledger_at_cap, ledger_whole;
ledger_whole_by_make's premises hpf, hlf: Johnson/Desc/K14/Law/LedgerByMakeTop.lean).

  letters_of_row   at any front piece f and list l: l = seatedPiece b1 … :: [pc2 b2.retype …, x3,
                   pc1 b4.retype …, pc2 b5.retype …, x6, pc1 b7.retype …, x8, x9, x10, x11].
  letters_of_cut   so at the maker's cut Tt of a description's data: Tt.l₂ has that form (f :=
                   Tt.p₂).
HOW. The length by the equation's two lengths · eleven_of_length
(Johnson/Desc/K14/Law/LedgerRowByMake.lean) · the pieces 2, 4, 5, 7 by row_forms
(Johnson/Desc/K14/Law/LedgerForms.lean) · the piece at "LIN point" in the same way: it holds
b1.retype in the wrap (piece_retype_at), nothing is put behind it and it is owed one round (the
tiling; rounds_counts), so it is pc1 b1.retype … (piece_eta1), which is seatedPiece b1 … by rfl ·
at the cut: row_of_cut (Johnson/Desc/K14/Law/LedgerRowOfCut.lean).
ONE PREMISE THAT THE USER DOES NOT BEAR: htl : tests.length = 2. There tests is a free list, and its
length follows from hlf's twelve letters (tests_two); here the letters are what is sought, so the
length is asked. At the seat tests is a list of two by its make.
What is not claimed. Which letters they are. That a description has that chain. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerRowOfCut
import Johnson.Desc.K14.Law.LedgerRowByMake
import Johnson.Desc.K14.Law.LedgerFormsAll
import Johnson.Desc.Sound.PointSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- **The letters, at a row.** -/
theorem letters_of_row {P₁ Cl Cells Tok : Type} {Fr : Frame} (c : Model.Verify.Chains) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (htl : tests.length = 2)
    (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
    (hps : (f :: l).map (·.b) =
      (((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s)))
    (ht : Tiled f l) :
    ∃ (base : ℕ) (d : RDT)
      (ext : (P₁ × St) × Fr.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 d22 : RDT)
      (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er2 : Err (uLT (ckP .two) [d21, d22]))
      (x3 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (base4 : ℕ) (d4 : RDT)
      (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT)
      (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er5 : Err (uLT (ckP .two) [d51, d52]))
      (x6 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (base7 : ℕ) (d7 : RDT)
      (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er7 : Err (uLT (ckP .two) [d7]))
      (x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)),
      l = seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err
        ::
        [pc2 b2.retype base2 d21 d22 ex2 er2, x3, pc1 b4.retype base4 d4 ex4 er4,
          pc2 b5.retype base5 d51 d52 ex5 er5, x6, pc1 b7.retype base7 d7 ex7 er7, x8, x9, x10,
          x11] := by
  obtain ⟨t9, t10, rfl⟩ := List.length_eq_two.1 htl
  have hl : l.length = 11 := by
    have h := congrArg List.length hps
    rw [chainOf_eq c Q b1 b2 b3 b4 b5 b6 b7 b8 [t9, t10] last hbl] at h
    simp [VerifiableInference.Desc.Chain.retype, VerifiableInference.Desc.Chain.blocksInOrder] at h
    omega
  obtain ⟨pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, rfl⟩ := eleven_of_length l hl
  obtain ⟨⟨d21, d22, ex2, er2, e2⟩, -, ⟨d4, ex4, er4, e4⟩, ⟨d51, d52, ex5, er5, e5⟩, -,
    ⟨d7, ex7, er7, e7⟩, -, -, -⟩ := row_forms c Q b1 b2 b3 b4 b5 b6 b7 b8 t9 t10 last hbl f pt x2
      x3 x4 x5 x6 x7 x8 x9 x10 x11 hps ht
  obtain ⟨q1, e1, h1⟩ := piece_retype_at (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) c Q
    b1 b2 b3 b4 b5 b6 b7 b8 [t9, t10] last hbl hps 0 b1 rfl
  obtain rfl : pt = q1 := Option.some.inj e1
  have hcn := rounds_counts Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcn
  obtain ⟨c1, -⟩ := hcn
  obtain ⟨-, -, -, -, o1, -, k1, -⟩ := ht
  have hlen : pt.ds.length = 1 := by
    have h := o1.1
    rw [k1, h1] at h
    have h' : pt.ds.length + 0 = b1.rounds.length := h
    omega
  obtain ⟨d, ext, err, e0⟩ := piece_eta1 pt _ h1 k1 hlen
  refine ⟨pt.base, d, ext, err, x2.base, d21, d22, ex2, er2, x3, x4.base, d4, ex4, er4, x5.base,
    d51, d52, ex5, er5, x6, x7.base, d7, ex7, er7, x8, x9, x10, x11, ?_⟩
  have e0' : pt = seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 pt.base
      d ext err := e0
  exact congrArg₂ List.cons e0' (congrArg₂ List.cons e2 (congrArg (List.cons x3)
    (congrArg₂ List.cons e4 (congrArg₂ List.cons e5 (congrArg (List.cons x6)
      (congrArg (fun z => z :: [x8, x9, x10, x11]) e7))))))

/-- **The letters, at the maker's cut**: hlf's letters exist (hpf: f := Tt.p₂). -/
theorem letters_of_cut {XiF P₁ Cl Cells Tok : Type} (Fd : FileDescription XiF) (fileN : String)
    (Dw : WholeD) {Yt S₁t S₃t X₁t X₂t : Type}
    (Tt : Three (ckP .two) Dw (allOf Dw) Yt S₁t (P₁ × St) S₃t X₁t X₂t Cl (Wit Cells Tok MsgT))
    (ch : Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (htl : tests.length = 2)
    (hDw : Fd.data fileN = .ok Dw) (hsl : Fd.sealLast = true)
    (b₁t : Block S₁t Cl) (l₁t : List (Block S₁t Cl)) (b₂t : Block (P₁ × St) Cl)
    (l₂t : List (Block (P₁ × St) Cl)) (b₃t : Block S₃t Cl) (l₃t : List (Block S₃t Cl))
    (rest₁t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₁ Tt.ft₁) S₁t (Wit Cells Tok MsgT) ds)
    (rest₂t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) (Wit Cells Tok MsgT) ds)
    (rest₃t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₃ Tt.ft₃) S₃t (Wit Cells Tok MsgT) ds)
    (rS : Fmt.RoundView) (g₁ : (b₁t :: l₁t).map (·.rounds) = Fd.first.blocksInOrder.map (·.rounds))
    (g₂ : (b₂t :: l₂t).map (·.rounds) = Fd.shared.blocksInOrder.map (·.rounds))
    (g₃ : (b₃t :: l₃t).map (·.rounds) = Fd.second.blocksInOrder.map (·.rounds))
    (hcut : Tt.IsCut b₁t l₁t b₂t l₂t b₃t l₃t rest₁t rest₂t rest₃t rS) (hcp : AtCap rest₂t)
    (hrow : b₂t :: l₂t = (((chainOf ch Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s))) :
    ∃ (base : ℕ) (d : RDT)
      (ext : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Tr (uLT (ckP .two) [d]) →
        Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 d22 : RDT)
      (ex2 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d21,
        d22]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er2 : Err (uLT (ckP .two) [d21, d22]))
      (x3 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) Cl (Wit Cells Tok
        MsgT)) (base4 : ℕ) (d4 : RDT)
      (ex4 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d4])
        → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT)
      (ex5 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d51,
        d52]) → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er5 : Err (uLT (ckP .two) [d51, d52]))
      (x6 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) Cl (Wit Cells Tok
        MsgT)) (base7 : ℕ) (d7 : RDT)
      (ex7 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d7])
        → Wit Cells Tok MsgT →
        Wit Cells Tok MsgT)
      (er7 : Err (uLT (ckP .two) [d7]))
      (x8 x9 x10 x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) Cl (Wit
        Cells Tok MsgT)),
      Tt.l₂ = seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂
        Tt.ft₂)) (P₁ := P₁) b1 base d ext err ::
        [pc2 b2.retype base2 d21 d22 ex2 er2, x3, pc1 b4.retype base4 d4 ex4 er4,
          pc2 b5.retype base5 d51 d52 ex5 er5, x6, pc1 b7.retype base7 d7 ex7 er7, x8, x9, x10,
          x11] := by
  obtain ⟨q1, q2, -⟩ := row_of_cut Fd fileN Dw hDw hsl Tt b₁t l₁t b₂t l₂t b₃t l₃t rest₁t rest₂t
    rest₃t rS g₁ g₂ g₃ hcut hcp
  exact letters_of_row ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl htl Tt.p₂ Tt.l₂ (q1.trans hrow)
    q2

end Desc.K14.Law

#print axioms Desc.K14.Law.letters_of_row
#print axioms Desc.K14.Law.letters_of_cut
