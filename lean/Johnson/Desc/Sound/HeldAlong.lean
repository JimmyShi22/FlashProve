-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/HeldAlong.lean: "held" AT THE TOP STATEMENTS' CONFIGURATION's OWN held: where that configuration keeps a matrix ("in range", then the matrix: OnBytes/Slice/ConfOf.lean), it is, entry for entry, the matrix by numbers of which the law of the shared chain's block 1 speaks (HeldTie, Johnson/Desc/K13/Law/HeldTab.lean). One definition, four
theorems. A joint build of files of Johnson/Desc/Sound/ and Johnson/Desc/K14/Law/.

K14's files have the tie at a held of their own text (heldIf over cellsAt, Johnson/Desc/K14/Law/HeldRangeSpec.lean: heldTie_range, HeldRange.lean) and left one equation: that their cellsAt IS the library's cellsOf (Johnson/Flat/Claims.lean) at data whose sizes are the shape's.
  cells_one: that equation, over decROfS and N := ⟨matrixRows, kLo⟩: rfl · held_one: so the configuration's held there IS heldIf at the cut index.plain and the library's test of range: rfl.
  matN D N: a matrix of the library's type, by numbers; 0 outside.
  heldTie_along: **HeldTie AT heldAlong e (claimsLedgerOnAt D₀ N pp req) R AND matN D₀ N**, at every data D₀ that are decROfS of the shape (a VARIABLE: the equation is taken away by substitution) and N = ⟨matrixRows, kLo⟩. One premise on the shape: matrixRows * 2 ^ kLo ≤ index.plain.
  heldTie_full: **the same at heldFull: the release's configuration at the written sizes**, under
    one premise more: the equation h on the plan's table's shape.

Limits. N = ⟨p.S.matrixRows, p.S.kLo⟩ is a premise: that the configuration's two numbers are the plan's: public, shown by nobody here. The premise on the shape is a clause of the shape's own conditions (by report a yes of block 1 gives it). NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DataAlong
import Johnson.Desc.K14.Law.HeldRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Desc.Plain
open VerifiableInference.OnPublicFiles (kcReq)

/-- K14's files' matrix of a decoded table (cellsAt) is the library's, at data off the shape. -/
theorem cells_one (p : Par) (err eM : Nat)
    (U : (ixOf2 p.S.fold err eM (rankLib p.S.fold)).Row × Fin p.S.fold.index.code.ell → GE) :
    cellsAt p err eM (rankLib p.S.fold) p.S.fold.index.plain U =
      cellsOf (decROfS p.S.fold eM) ⟨p.S.matrixRows, p.S.kLo⟩ U := rfl

/-- So the configuration's own held is K14's files' heldIf, at the library's test of range. -/
theorem held_one {X : Type} (p : Par) (err eM : Nat) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref)
    (R : (decROfS p.S.fold eM).RelationsAndEncoding
      (claimsLedgerOnAt (decROfS p.S.fold eM) ⟨p.S.matrixRows, p.S.kLo⟩ pp req)) :
    (DecR.configurationOfStoredTable (claimsLedgerOnAt (decROfS p.S.fold eM) ⟨p.S.matrixRows, p.S.kLo⟩ pp req) R).held =
      heldIf p err eM (rankLib p.S.fold) p.S.fold.index.plain VerifiableInference.OnPublicFiles.Flat.InRange := rfl

/-- A matrix of the library's type, by numbers; 0 outside. -/
def matN (D : DecR) (N : MatrixNums) (M : Cells D N) (y c : Nat) : GE :=
  if h : y < N.rows ∧ c < 2 ^ (N.kLo + D.v) then M ⟨y, h.1⟩ ⟨c, h.2⟩ else 0

/-- **"held" at the configuration's own held, carried along the equation of data.** -/
theorem heldTie_along {X : Type} (p : Par) (err eM : Nat) {D₀ : DecR} (e : decROfS p.S.fold eM = D₀)
    (N : MatrixNums) (hN : N = ⟨p.S.matrixRows, p.S.kLo⟩) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) (R : D₀.RelationsAndEncoding (claimsLedgerOnAt D₀ N pp req))
    (hcut : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.plain) :
    HeldTie p err eM (rankLib p.S.fold) (heldAlong p err eM e (claimsLedgerOnAt D₀ N pp req) R)
      (matN D₀ N) := by
  subst e
  subst hN
  exact heldTie_range p err eM (rankLib p.S.fold) p.S.fold.index.plain
    VerifiableInference.OnPublicFiles.Flat.InRange hcut (Nat.le_trans hcut (Nat.sub_le _ _))

/-- **"held" at the release's configuration's own held.** -/
theorem heldTie_full (p : Par) (err sb : Nat)
    (h : p.S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩) (N : MatrixNums)
    (hN : N = ⟨p.S.matrixRows, p.S.kLo⟩) (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp))
    (hcut : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.plain) :
    HeldTie p err 2852142980 (rankLib p.S.fold) (heldFull p err sb h N pp E)
      (matN (frS.toDecR frZ 402653181) N) :=
  heldTie_along p err 2852142980 (full_of_index p.S.fold sb h) N hN pp Subtype.val (relationsAndEncodingOfClaims _ E) hcut

end Desc.K14.Law

#print axioms Desc.K14.Law.cells_one
#print axioms Desc.K14.Law.held_one
#print axioms Desc.K14.Law.heldTie_along
#print axioms Desc.K14.Law.heldTie_full
