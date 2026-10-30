-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Sentences.lean: toward a member: K5Fill's held | decodes and K5FillRel's ctxW at fillK5 d Mg1, Mg1 taken by the equations that mgAll pays by rfl (Johnson/Desc/Sound/MgAll.lean: mgAll_held · mgAll_pinW · mgAll_decodes; by reading, not machine-checked): cut out of FillK5Keeps.lean (a file that is not in this library). decodes | ctxW: under one fact on the letter decT (hT: at a record with an open attention segment it reads nothing that the kind's lay turns): paid by nobody. Mathlib beneath.
import Johnson.Desc.First.Att.Door.Law.LayKeeps
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (behind hear Heard)
open VerifiableInference.Desc (smpHeld)

section
variable {Pp W : Type} (d : K5Data) (Mg1 : Meaning Pp W) (π : Pp)

/-- **K5Fill.held**: the oracles' layer's test reads the statement and the book alone, which the lay leaves. -/
theorem at_held (hheld : Mg1.held = fun j t (a : Pp × S) => smpHeld a.2.st a.2.book j t) (j t : Nat) (s : S)
    (a : AttOwn) (h : Heard) (G : Fork) :
    (fillK5 d Mg1).held j t (π, s) = true → (fillK5 d Mg1).held j t (π, behind s a h G) = true := by
  show Mg1.held j t (π, s) = true → Mg1.held j t (π, behind s a h G) = true
  rw [hheld]
  exact fun x => x
/-- What holds the same below a base has the same stored table. -/
theorem cell_same {Fr : VerifiableInference.Desc.Sound.Frame} {bs : Nat} {y y' : Fr.E.Str}
    (h : Att.P.SameBelow Fr bs y y') :
    (VerifiableInference.Desc.Sound.strsOf Fr y').cell = (VerifiableInference.Desc.Sound.strsOf Fr y).cell := by
  show VerifiableInference.Desc.Sound.cellAt Fr y' = VerifiableInference.Desc.Sound.cellAt Fr y
  unfold VerifiableInference.Desc.Sound.cellAt
  rw [h.1]
end

section
variable {Pp Cells Tok : Type} (d : K5Data)
  (Mg1 : Meaning Pp (VerifiableInference.Desc.Wit Cells Tok VerifiableInference.Desc.Sound.MsgT)) (π : Pp)
  (decT : (Nat → Option (Nat × List UInt64)) → Pp × S → Option Cells)
  (hT : ∀ c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s))
include hT

/-- **K5Fill.decodes** at the oracles' layer's term, UNDER ONE FACT ON ITS LETTER decT: it reads nothing that the kind's lay turns. -/
theorem at_decodes (hdec : Mg1.decodes = VerifiableInference.Desc.Sound.decodesOf decT)
    {Fr : VerifiableInference.Desc.Sound.Frame} {bs : Nat} (s : S) (a : AttOwn) (h : Heard) (G : Fork) (y y' : Fr.E.Str)
    (e : s.here = .att a) (hy : Att.P.SameBelow Fr bs y y') :
    (fillK5 d Mg1).decodes (π, s) (VerifiableInference.Desc.Sound.strsOf Fr y) →
      (fillK5 d Mg1).decodes (π, behind s a h G) (VerifiableInference.Desc.Sound.strsOf Fr y') := by
  show Mg1.decodes _ _ → Mg1.decodes _ _
  rw [hdec]
  unfold VerifiableInference.Desc.Sound.decodesOf
  rw [cell_same hy, hT _ _ _ _ _ e]
  exact fun x => x

/-- **K5FillRel.ctxW** (Johnson/Desc/First/Att/K05Riders.lean): the stored table's pin rides back, under the same fact. -/
theorem at_ctxW (hW : Mg1.pinW = VerifiableInference.Desc.Sound.pinWOf decT)
    {Fr : VerifiableInference.Desc.Sound.Frame} {bs : Nat} (s : S) (a : AttOwn) (h : Heard) (G : Fork) (y y' : Fr.E.Str)
    (w : VerifiableInference.Desc.Wit Cells Tok VerifiableInference.Desc.Sound.MsgT) (e : s.here = .att a)
    (hy : Att.P.SameBelow Fr bs y y') :
    (fillK5 d Mg1).pinW (π, behind s a h G) (VerifiableInference.Desc.Sound.strsOf Fr y') w →
      (fillK5 d Mg1).pinW (π, s) (VerifiableInference.Desc.Sound.strsOf Fr y) w := by
  show Mg1.pinW _ _ _ → Mg1.pinW _ _ _
  rw [hW]
  unfold VerifiableInference.Desc.Sound.pinWOf
  rw [cell_same hy, hT _ _ _ _ _ e]
  exact fun x => x

end
#print axioms at_held
#print axioms cell_same
#print axioms at_decodes
#print axioms at_ctxW

end H2K5.Door
