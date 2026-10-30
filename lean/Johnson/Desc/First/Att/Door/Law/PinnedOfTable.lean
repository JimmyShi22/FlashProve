-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/PinnedOfTable.lean: kind K5: K5Behind's field item AT THE FILLED PIN
("pinned": behind the kind's rounds every member of the caller's list is pinned at the statement's
oracle messages and the book) FROM THE TABLE OF JOINTS' ITEM pin m 0 at another file's part of the
filling (pinJT, Johnson/Desc/Sound/MeaningSig.lean).

As reported: THE
CALLER's LIST (the kept messages, then the segment's own of moment 0) IS NO SENDING OF THE COMPOSED
MEANING's LIST OF MEMBERS ms, which holds the real sendings alone: the premise
"each member of the caller's list lies in ms" cannot be met. IN ITS PLACE, in the
form of someB (Rad3Seat3At.lean): hsome: for each member of the caller's list SOME member of ms is
alike (one entry: shape and radius; one seat) · hSB: the OOD samples hang on the entry and the seat,
not on the list (SmpBySeat). The pin is carried from the real member to the caller's by pin_move_mp
(Johnson/Desc/Sound/PinMove.lean). UNDER, BESIDE: hsent: each member's seat is a tenant of N.sent m
0 · hsm: the pin's letter smpR, which reads the statement's oracles and the book, is smp at the
caller's list · hpin: Mg.pin = pinJT … · hopen: pin m 0 stands among what the kind's row opens or
reads: k5_pin_open: by the table's text. NAMED PAYERS, NOT JOINED: hsome: someB | listSits_some
(P5J/Rad3Seat3At.lean; as reported, no test has run) · hSB: smpNamed_bySeat
(Sound/SmpNamed.lean). Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05AtMgPin
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.PinMove

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent sigListCalls)
open VerifiableInference.Desc.First.Att.P (k5Pin)

/-- **From the table's pins at the members' seats to the pin at each member of the caller's list.**
A: what the part of the filling reads; R: what the filled pin reads. -/
theorem pinAt_of_pinJT (cs : OnBytes.Codes) {Xi A R Cells Tok : Type} (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (l : List (OnBytes.OracleShape × Nat)) (seat : Fin l.length → Nat × Nat)
    (smpR : R → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp) (a : A) (r : R) (y : Strs) (w : Wit Cells Tok MsgT)
    (hsome : ∀ i : Fin l.length, ∃ x ∈ ms, Alike x (⟨⟨l, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat cs smp)
    (hsm : ∀ i, smpR r i = smp a ⟨l, seat⟩ i)
    (h : ∀ i : Fin l.length, pinJT cs G arr smp ms (seat i).1 (seat i).2 a y w) (i : Fin l.length) :
    PinAt G cs l seat smpR arr i r y w := by
  obtain ⟨x, hx, hal⟩ := hsome i
  obtain ⟨z, hz, hs, hd⟩ := pin_move_mp cs G arr smp x ⟨⟨l, seat⟩, i⟩ hal a (hSB a x _ hal) y w ((h i).2 x hx hal.2)
  exact ⟨z, (hsm i).trans hz, hs, hd⟩

/-- **K5Behind.item at the filled pin**, at R' := what the kind's row opens and reads. -/
theorem pinned_of_table {Xi Pp Cells Tok : Type} (Gd : FileDescription Xi) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (seat : Fin (sigListCalls D rad x.link).length → Nat × Nat)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (arr : Nat → Nat → Nat) (Fr : Frame) (base : Nat) (hlow : ∀ i, (seat i).1 < base) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k m : Nat) (π : Pp)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp) (ms : List Mem)
    (hpin : Mg.pin = pinJT D.codes Gd arr smp ms) (hopen : outsQ links ps k (.pin m 0))
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ N.sent m 0)
    (hsm : ∀ (s : S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i)
    (b : S × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hR : relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w) :
    (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arr Fr base hlow).holds
      ((k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arr Fr base hlow).rc b.1) b.2 w := by
  have h0 : ∀ t ∈ N.sent m 0, Mg.pin t.1 t.2 (π, b.1) (strsOf Fr b.2) w := hR (.pin m 0) hopen
  rw [hpin] at h0
  exact fun i => pinAt_of_pinJT D.codes Gd arr smp ms _ seat smpR (π, b.1) (b.1.st.oracles, b.1.book) (strsOf Fr b.2) w hsome hSB
    (hsm b.1) (fun j => h0 (seat j) (hsent j)) i

/-- pin m 0 stands in the kind's row's context: by the table's text. -/
theorem k5_pin_open {links : List ModelPart} {ps : List Place} {k m : Nat} {pl pl' : Place}
    (Ix : VerifiableInference.Desc.First.Att.P.K5Place links m pl pl') (hk : ps[k]? = some pl) : outsQ links ps k (.pin m 0) := by
  unfold outsQ rowQ
  rw [hk]
  show Item.pin m 0 ∈ (rowOf links pl).outs ++ (rowOf links pl).ctx ++ [.unmarked]
  rw [VerifiableInference.Desc.First.Att.P.k5_row Ix]
  show Item.pin m 0 ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join"] ++ (segRow .attention m 3).ctx ++ [.unmarked]
  have hc : (segRow .attention m 3).ctx = [.pin m 0, .pinW, .constr m .small] := rfl
  rw [hc]
  simp

#print axioms k5_pin_open
#print axioms pinAt_of_pinJT
#print axioms pinned_of_table

end H2K5.Door
