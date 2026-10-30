-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsOfAt.lean: the lookup on the digits of a segment's approximate range
proof: WHAT THE ITEM constr m lookDigits GIVES ITS SPENDER, WHEREVER THE PUBLIC PARAMETERS ARE
publicOf's: the sentence DigitsOf (Johnson/Desc/First/K8/DigitsOf.lean: the approximate range
proof's files' own) at the parameters tl that tlAt returns. Two theorems: joinings. NO SOUNDNESS
IS CLAIMED.

Main names.
  digitsOf_at: ShapeZAll X → ColsAll X → digAt X i = some (x, tl) → DgP.DigIn tl en ν → tlAt X i =
    some tl ∧ DigitsOf tl (fun t u c => ν (en (t, u, c))).
  digitsOf_of_part: so from the lookups' sentence digitsPartK3 X D L i a y w itself, at publicOf's
    X.
HOW. digAt_is (DigitsShapeAt.lean: digAt hands on what tlAt returns) · cols_at (ColsAt.lean: what
tlAt returns passes colsTest) · digIn_digitsOf (K3DigInCols.lean) · digitsPart_at
(K3FillDigits.lean).
OBJECT. No sub-protocol's text: sentences on a reading of entries, at the public parameters.
USER. Johnson/Desc/Sound/MgAt/K3DigitsAt.lean calls digitsOf_of_part.
LETTERS. X, i, x, tl, en, ν; D, L, a, y, w.
IS IT EMPTY? ShapeZAll and ColsAll hold at whatever publicOf returns (shapeZAll_of_public,
colsAll_of_public).
Compiled with the whole library.


Limits. That the spender's table of cells is fun t u c => ν (en (t, u, c)) at the array ZZ is its
files' one equation to show: not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigInCols
import Johnson.Desc.First.Look.K3FillDigits
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.Desc.First.Look.ColsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Strs)

/-- **DigIn at digAt's parameters is DigitsOf at tlAt's.** -/
theorem digitsOf_at {J : Type} {X : Verify.Public} (Z : ShapeZAll X) (C : ColsAll X) {i : ℕ}
    {x : Desc.First.Look.Place} {tl : HTailF2} (hx : digAt X i = some (x, tl))
    (en : DgP.Ent3 → J) (ν : J → Cb.Gl.E) (h : DgP.DigIn tl en ν) :
    tlAt X i = some tl ∧ Desc.First.K8.DigitsOf tl (fun t u c => ν (en (t, u, c))) :=
  ⟨digAt_is Z hx, digIn_digitsOf tl en ν (cols_at C (digAt_is Z hx)) h⟩

/-- **From the lookups' own sentence, at publicOf's public parameters.** -/
theorem digitsOf_of_part {P Cells Tok : Type} {pol KL : ByteArray} {layout : Option ByteArray}
    {X : Verify.Public} (hX : Verify.publicOf pol KL layout = .ok X)
    (D : Desc.First.Look.Sent) (L : K3Letters Cells Tok) {i : ℕ} {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X i = some (x, tl)) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) (h : digitsPartK3 X D L i a y w) :
    tlAt X i = some tl ∧ Desc.First.K8.DigitsOf tl (fun t u c =>
      digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w (enOf x.arrays (t, u, c))) :=
  digitsOf_at (shapeZAll_of_public hX) (colsAll_of_public hX) hx (enOf x.arrays) _
    (digitsPart_at X D L i hx a y w h)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digitsOf_at
#print axioms VerifiableInference.OnPublicFiles.digitsOf_of_part
