-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/K5RelAt.lean: kind K5: K5FillRel, all eight fields (Johnson/Desc/First/Att/K05Riders.lean: what stays open of the relation rides back over the kind's lay), at any meaning Mg that meets the equations which the composed meaning mgAll (Johnson/Desc/Sound/MgAll.lean) pays by rfl (mgAll_pile · mgAll_pin · mgAll_row with fillRowFirst's own · mgAll_pinW). The eighth of the nine fields of K5AtMg. Mathlib beneath.
-- Five fall by lemmas that lie: pile (at_pile) · pinI | ctxPin (at_pin_back) · row (at_row) · ctxW (at_ctxW): under facts on four letters of the composed meaning's ("it reads nothing that the kind's lay turns"): hrw (rw13) · hsmp (smp) · hT (decT); and "below the base": hlowI (the index masks' tenant) · hlow0 (the first sending's tenants): seated_fenced (Johnson/Desc/Sound/PieceSeated.lean).
-- Three stay as named premises, left to the composed meaning's files: hconstr (constr n p, n ≠ m) · hsmall (constr m .small): the text of constrQAt (Johnson/P5J/MeansQ.lean) lies outside this file's imports · hobjects (formsT m 2 "objects": one reader's answer at two states of the verifier).
import Johnson.Desc.First.Att.Door.Law.FillK5Pile
import Johnson.Desc.First.Att.Door.Law.FillK5Pins
import Johnson.Desc.First.Att.Door.Law.FillK5Row
import Johnson.Desc.First.Att.Door.Law.FillK5Sentences
import Johnson.Desc.First.Att.K05Riders

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind hear Heard SameBelow K5FillRel)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)

theorem k5Rel_at {Pp Xi Cells Tok : Type} {nR : Nat} (d : K5Data) (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp)
    (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR) (hpile : Mg.pile = (fillK13 D13 Mg0).pile)
    (cs : OnBytes.Codes) (G0 : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (hpin : Mg.pin = pinJT cs G0 arr smp ms) (N : Numbers) (hrow : Mg.row = rowSays N (wordsAtFirst arr))
    (decT : (Nat → Option (Nat × List UInt64)) → Pp × S → Option Cells) (hW : Mg.pinW = pinWOf decT)
    (hrw : ∀ s a h G, s.here = .att a → D13.rw (π, behind s a h G) = D13.rw (π, s))
    (hsmp : ∀ s a h Gk, s.here = .att a → smp (π, behind s a h Gk) = smp (π, s))
    (hT : ∀ c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s))
    (links : List ModelPart) (Fr : Frame) (bs m : Nat) (pl : Place) (O : List Item) (Q : List Pub) (own : Params.AttentionRounds)
    (hlowI : N.index.1 < bs) (hlow0 : ∀ t ∈ N.sent m 0, t.1 < bs)
    (hconstr : ∀ n p, n ≠ m → ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w)
    (hsmall : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.constr m .small (π, behind s att hd G) (strsOf Fr y') w → Mg.constr m .small (π, s) (strsOf Fr y) w)
    (hobjects : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      Mg.formsT m 2 "objects" (π, behind s att hd G) (strsOf Fr y') w → Mg.formsT m 2 "objects" (π, s) (strsOf Fr y) w) :
    K5FillRel Mg N links π Fr bs m pl O Q own where
  pile := fun s att hd G _ y y' w _ _ e _ _ => at_pile d Mg Mg0 π D13 hpile hrw s att hd G (strsOf Fr y) (strsOf Fr y') w e
  constr := hconstr
  pinI := fun s att hd G _ y y' w _ _ e _ hy => at_pin_back d Mg π cs G0 arr smp ms hsmp hpin hlowI s att hd G y y' w e hy
  row := fun c s att hd G _ y y' w _ _ _ _ _ => at_row d Mg π arr N hrow m c s att hd G (strsOf Fr y) (strsOf Fr y') w
  objects := hobjects
  ctxPin := fun t ht s att hd G _ y y' w _ _ e _ hy =>
    at_pin_back d Mg π cs G0 arr smp ms hsmp hpin (hlow0 t ht) s att hd G y y' w e hy
  ctxW := fun s att hd G _ y y' w _ _ e _ hy => at_ctxW d Mg π decT hT hW s att hd G y y' w e hy
  ctxSmall := hsmall

#print axioms k5Rel_at

end H2K5.Door
