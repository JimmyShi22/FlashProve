-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5GainsPlus.lean: kind K5: FOUR MORE EQUATIONS ON THE FILLING,
BESIDE MgIs (Johnson/Desc/First/Att/Door/Law/K5AtEqsPlus.lean), AND WHAT THEY PAY: the premises hfT
(the road "behind") and hW (the clauses "keys", "rider", "planes" of K5FillIns).

IS IT EMPTY HERE? Equations at letters, and implications from them. NO MEMBER IS SHOWN.

Main names:
  `MgGains`: formsT: the right side of mgAll_formsT (MgAll.lean) · planes, keys, rider: the right
    sides of mgAll_worth_att_planes | _keys | _rider (Johnson/Desc/Sound/MgAllAt.lean), at piece 2
    (attWorth…, Johnson/Desc/First/Look/K3CallsTies.lean). The wider filling turns none of the four
    fields (widen turns more, pub, inOrder alone).
  `hfT_plus`: the item formsT at the filling gives THE SENTENCE, written out: its first conjunct.
  `hW_keys`, `hW_rider`, `hW_planes`: the lookup argument's files' three sentences give the
    filling's item worth: the equations read from right to left; fork and heard are the seat's by
    unfolding.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5AtEqsPlus
import Johnson.Desc.First.Look.K3CallsTies
import Johnson.Desc.First.Look.K3FillWorth
import Johnson.Desc.Sound.FormsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent sigListCalls attLay attRider)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.OnPublicFiles (attWorthPlanes attWorthKeys attWorthRider forkR heardC K3WorthPlanes K3WorthKeys K3WorthRider attNu attMu attMs)

section
variable {Pp Cells Tok : Type} (Mg : Meaning Pp (Wit Cells Tok MsgT)) (cs : Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated) (N : Numbers)
  (wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (m : ℕ)
  (x : Look.Place) (A : Attention.Shape) (tl : HTailF2) (Dn : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ) (arrL : ℕ → ℕ → ℕ)

/-- **Four more equations on the filling.** Beside each: mgAll's own lemma. -/
structure MgGains : Prop where
  /-- mgAll_formsT -/
  formsT : Mg.formsT = fun m k r (a : Pp × S) y w =>
    (∀ p ∈ runs m k r, formsTQ (Rd m) St (N.sent m 0) p.1 p.2 a.2 (seatTab cs arr ms w)) ∧ (r = "weights" → wt m a y w)
  /-- mgAll_worth_att_planes -/
  planes : ∀ (a : Pp × S) y w, Mg.worth m 2 "planes" a y w = attWorthPlanes x A tl Dn rad seatT arrL forkR heardC a.2 w
  /-- mgAll_worth_att_keys -/
  keys : ∀ (a : Pp × S) y w, Mg.worth m 2 "keys" a y w = attWorthKeys x A tl Dn rad seatT arrL forkR heardC a.2 w
  /-- mgAll_worth_att_rider -/
  rider : ∀ (a : Pp × S) y w, Mg.worth m 2 "rider" a y w = attWorthRider x A tl Dn rad seatT arrL forkR heardC a.2 w

variable {Mg cs arr ms Rd runs St N wt m x A tl Dn rad seatT arrL}
variable (G : MgGains Mg cs arr ms Rd runs St N wt m x A tl Dn rad seatT arrL)
include G

/-- **hfT**: the item gives the sentence. -/
theorem hfT_plus (n j : ℕ) (name : String) (a : Pp × S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : Mg.formsT n j name a y w) :
    ∀ p ∈ runs n j name, formsTQ (Rd n) St (N.sent n 0) p.1 p.2 a.2 (seatTab cs arr ms w) := by
  rw [G.formsT] at h
  exact h.1

theorem hW_keys {Cl : Type} (claim : Aff → Cl) (π : Pp) (s : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthKeys (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next (attNu x A tl Dn rad seatT arrL)
      (fun w => forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) () (zext (attMu x tl Dn rad seatT arrL w))) s w) :
    Mg.worth m 2 "keys" (π, s) y w := by
  rw [G.keys]
  exact h

theorem hW_rider {Cl : Type} (claim : Aff → Cl) (π : Pp) (s : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthRider (K3.seatCalls claim).fork (K3.seatCalls claim).heard (attRider x A tl Dn rad Iop.extNone Unit) x.lm x.F.next
      (fun _ => ()) (attMs x Dn rad seatT arrL) s w) :
    Mg.worth m 2 "rider" (π, s) y w := by
  rw [G.rider]
  exact h

theorem hW_planes {Cl : Type} (claim : Aff → Cl) (π : Pp) (s : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : K3WorthPlanes (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next (attNu x A tl Dn rad seatT arrL) s w) :
    Mg.worth m 2 "planes" (π, s) y w := by
  rw [G.planes]
  exact h

end

end H2K5.Door

#print axioms H2K5.Door.hfT_plus
#print axioms H2K5.Door.hW_keys
#print axioms H2K5.Door.hW_rider
#print axioms H2K5.Door.hW_planes
