-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/DoorYesPlus.lean: kind K5: THE LEAN STRUCTURE DoorYes
(Johnson/Desc/First/Att/K05DoorYes.lean: "the door's Bools say yes at the verifier's state s, and
five equations") FROM THE TABLE OF JOINTS' PROMISE IN FRONT OF THE KIND's SUB-PROTOCOL, AT THE WIDER
FILLING (Johnson/Desc/First/Att/Door/Plus.lean) OVER THE COMPOSED FILLING.
ALL NINE FIELDS.
After DoorYesOfOn.lean (a file that is not in this library, written at another form of the
composed filling): what stays is taken over line for line,
by program. FIELD BY FIELD: live: K5's item K5.liveReq · reads: K5's item K5.readsThere · look:
the item look m · sized: ledger m · ns: freeAbove m · heard: the item left m's sentence · link: the
promise's clause on the open link; frame.liveIs (AT THE WIDER FILLING); linkFresh m; the wider "in
order"'s last clause · seats, shapes: NEW HERE: from frame.sentIs m (open at that form's own
list), K12.seatsCarried | K12.msgShapes (AT THE WIDER FILLING), the promise's own clause bookAt and
one test each on public data: seatsOn_of_items, shapesOn_of_items
(Johnson/Desc/First/Att/K05OwnersSent.lean). LEFT AS PREMISES: that eleven items are open at the
border (q1 … q11: tests on the table; evaluated, not typed) · the ties between the law's Sent and
the composed data (hsh · hly · har · hcs · hborn) · the two tests on public data (hPs · hPq: STATED
HERE AT THE COMPOSED DATA's D.dS: RUN NOWHERE AT THAT TERM: the like was evaluated true at 14 of 14
attention links at sentDataOf with a base counted off the planner's labels and at a
reading of two more parameters) · hleft. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.K05DoorYes
import Johnson.Desc.First.Att.K05T2
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.First.Att.Door.Law.DoorTie
import Johnson.Desc.First.Att.Door.Law.FillK5Keeper
import Johnson.Desc.First.Att.Door.Law.PlusAt
import Johnson.Desc.First.Att.K05OwnersSent

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent liveIsC linkFreshC)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Att.P (DoorYes K5Place K3LeftOutIs onAt_pub onAt_pubP onAt_shape k5_link link_front seatsOnB shapesOnB
  seatsPlanB shapesPlanB seatsOn_of_items shapesOn_of_items)
open VerifiableInference.Desc.K12.Door (Laid)

theorem doorYes_plus {Pp W St₀ J₀ : Type} [DecidableEq J₀] (D : PubData) (L : Laid) (M : List OracleShape) (base : Pub → Pp × S → Bool)
    (Mg : Meaning Pp W) (hpub : Mg.pub = pubAll D (pubPlus L M D.d3 base)) (cs : Codes)
    (rest : Pp × S → Bool) (hin : ∀ a : Pp × S, Mg.inOrder a = (rest a && decide (a.2.st.codes = cs)))
    (N : Numbers) (links : List ModelPart) {pl pl' : VerifiableInference.Desc.Place} {m : ℕ} (Ix : K5Place links m pl pl')
    (O : List Item) (Q : List Pub) (hatt : D.d5.isAtt m = true) (hlay : isLay D.links m = false) (hmH : (m == D.mH) = false)
    {nsPlan : ℕ} (hn : D.nsOf m = some nsPlan)
    (q1 : Pub.more (some m) "K5.liveReq" ∈ Q) (q2 : Pub.more (some m) "K5.readsThere" ∈ Q) (q3 : Pub.look m ∈ Q)
    (q4 : Pub.ledger m ∈ Q) (q5 : Pub.freeAbove m ∈ Q) (q6 : Pub.left m ∈ Q) (q7 : Pub.more (some m) "frame.liveIs" ∈ Q)
    (q8 : Pub.linkFresh m ∈ Q) (q9 : Pub.more none "K12.seatsCarried" ∈ Q) (q10 : Pub.more none "K12.msgShapes" ∈ Q)
    (q11 : Pub.more (some m) "frame.sentIs" ∈ Q)
    (x : Look.Place) (hxl : x.link = m) (Dn : Sent) (hsh : D.d3.shape = Dn.shape) (hly : D.d3.layout = Dn.layout)
    (har : D.d3.arrayOf.getD m #[] = Dn.arrayOf.getD m #[]) (hcs : cs = Dn.codes)
    (born : Array (ℕ × ℕ)) (hborn : bornOf D.d5.shape m = born) (kept : ℕ) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    (π : Pp) (s : S) (y : Strs) (hon : onAt N Mg links (some pl) O Q (π, s) y) (hu : s.failed = none)
    (att : AttOwn) (e : s.here = .att att)
    (fork : S → Option Fork) (hS : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀) (Qf : Fork → Prop)
    (x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gL : Forest.Heard)
    (hleft : Mg.pubP (.left m) (π, s) → K3LeftOutIs fork (fun s : S => s.lookHeard?) hS lm first ι Qf x0 gL s)
    (hPs : seatsPlanB D.dS m kept L ps (D.d5.ownOf m) (N.msgsAt (some pl)) = true)
    (hPq : shapesPlanB D.dS m kept M qs (N.msgsAt (some pl)) = true) :
    DoorYes D.d5.W x Dn born kept (D.d5.ownOf m) ps qs nsPlan gL s := by
  have P := fun q hq => by have := onAt_pub hon hu q hq; rwa [hpub] at this
  have hl : att.L.link = m := k5_link Ix e (onAt_shape hon hu)
  have hB : Mg.inOrder (π, s) = true ∧ bookAt N (some pl) s = true := by
    obtain ⟨_, hm | ⟨h1, _, _, _⟩⟩ := hon
    · exact absurd hu hm
    simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1.1.2, h1.2⟩
  have hio := hB.1
  rw [hin] at hio
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hio
  have heq := hio.2
  have p7 := P _ q7
  rw [pubAll_plus_live] at p7
  unfold liveIsC S.live at p7
  rw [link_front e] at p7
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p7
  have p8 := P _ q8
  rw [pubAll_linkFresh] at p8
  unfold linkFreshC at p8
  rw [link_front e] at p8
  simp only [Bool.and_eq_true, Option.any_some, beq_iff_eq] at p8
  have p5 := P _ q5
  rw [pubAll_freeAbove, hn] at p5
  obtain ⟨_, _, _, _, _, _, hh, _, _⟩ := hleft (onAt_pubP hon hu _ q6)
  exact
    { live := by have := P _ q1; rwa [pubAll_more_liveReq D _ m hatt, hborn] at this
      seats := seatsOn_of_items (by have := P _ q11; rwa [pubAll_more_sentIs] at this) (P _ q9) hB.2 (link_front e) hPs
      shapes := shapesOn_of_items (by have := P _ q11; rwa [pubAll_more_sentIs] at this) (P _ q10) hB.2 (link_front e) hPq
      reads := by have := P _ q2; rwa [pubAll_more_readsThere D _ m hatt] at this
      look := by have := P _ q3; rwa [pubAll_look_att D _ m hmH hlay hatt] at this
      sized := P _ q4
      ns := fun F hF => by
        simp only [Option.any_some] at p5
        unfold First.freeAboveB at p5
        rw [hF] at p5
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at p5
        omega
      heard := hh
      link := ⟨att.L, link_front e, hl.trans hxl.symm, p7.1.trans hsh, p7.2.trans hly, by rw [p8.2, hxl, har], heq.trans hcs⟩ }

#print axioms doorYes_plus

end H2K5.Door
