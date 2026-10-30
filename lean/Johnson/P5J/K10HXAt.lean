-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K10HXAt.lean (kind K10): THE FIELD hX OF WHAT IS LEFT OF K10's ASSEMBLED LAW
(`K10Heavy`, Johnson/Desc/First/Close/Law/K10Heavy.lean: "at every statement that has X: RowAsks"),
AT THE CLOSED CONSTANT's LETTERS, AT ALL 25 LINKS IN ONE STATEMENT. ONE PREMISE ON THE
STATE IS LEFT (seats). Statements and proofs: a join; two kernel lines, each with a negative one.

The letters. cs := At.cs Zp · lo := loAt l (the l-th written list) · gs := gsAt l · kb := kbW l
(the written request's flags) · no := noK10 (At.seats Zp) lo (At.pseats Zp) l (the plan's public
numbering) · Nm := namesOf .. no · Nu := At.N Zp cF · X := XK h l (the table's promise, "reached"
and "no mark" at K10's border of link l) · O := oAt (ixK10 l) · p: the place at that number of the
constant's list.

What is joined. rowAsks_whole (RowAsksWhole.lean: RowAsks' ten fields in one call) with: shapes :=
the hinge at all 25 links (`AtMg.hinge_all`: HingeAtMg.lean at 1 .. 23;
HingeAtMgHead.lean, HingeAtMgZero.lean at 24 and 0) · hinj := AtMg.hinge_inj · hc := the third
conjunct of five_of_facts (FiveOfFacts.lean) · hA := linksFull_layout · hk, hh:
BY THE KERNEL (`kh_full`) · hl, hst and the piece's bound: BY THE KERNEL (`k10_place_full`) · hgr,
hcs: by definition at At.foldD · the codes and the shape: AtMg.codes_full, AtMg.shapeAt_full.

What is said.
  `ixK10_is`: K10's number is the batching's + 3. `AtMg.hinge_all`: the hinge at every l < 25, at
    the number ixK10 l.
  `k10_place_full`, `k10_place`: at every l < 25 the place at ixK10 l is of link l, a segment of
    the sort subAt l stands open there, and its piece is at most 11 + 2 · the head's shift.
    `k10_place_off`: THE NEGATIVE LINE: at the next link's number none is of link l.
  `kh_full`, `kh_at`: kLay lo kb = s.h + s.g and s.h = 0 at s := stageOf (gsAt l) 219. `kh_off`:
    THE NEGATIVE LINE: at the next link's group's sizes the first fails somewhere.
  `AtMgA.hX_at`: **the field.**

PREMISES. h : AtMgA OnBytes.secondHashFunction .. · Fo : FoldFacts at h.rch and At.foldD (FoldAt.lean's form) ·
hp · hM, hZ (the typed group's own two) · **seats: under X the book places message no i at seat i**
(on the state).

Limits. AT LINK 0 IT STANDS AT THE SIX-LIST. AtMgA and FoldFacts are premises. secondHashFunction alone.
Nothing on soundness.

-/
import Johnson.P5J.HingeAtMgHead
import Johnson.P5J.HingeAtMgZero
import Johnson.P5J.K10PieceOfAsks
import Johnson.P5J.K10Open
import Johnson.P5J.CodesFullAtMg
import Johnson.P5J.FoldAt
import Johnson.Desc.First.Close.Law.RowAsksWhole
import Johnson.Desc.First.Close.Law.LayoutDrawn
import Johnson.Desc.First.Link.Law.FiveOfFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData standAt shiftAt
  Stand)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks rowAsks_whole rdK ShapesAre
  kbAt noK10 kLay linksFull_layout link_of_stand)
open VerifiableInference.Desc.LinkJoin (batchAt loAt kbW gsAt five_of_facts)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H
open LPFK10 (ixK10)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- K10's number is the batching's + 3. -/
theorem ixK10_is (l : ℕ) (hl : l < 25) : ixK10 l = batchAt fullLinks At.ps l + 3 := by
  rw [LPFK9.batchAt_full l hl]
  rfl

/-- The test on the place at K10's number of link l, read as of link m. -/
def k10PlaceB (l m : ℕ) : Bool :=
  (At.ps[ixK10 l]?).any fun p => decide (p.link = some m) &&
    decide (standAt fullLinks p = Stand.link (subAt m)) &&
    decide (p.piece ≤ 11 + 2 * shiftAt fullLinks m)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL.** -/
theorem k10_place_full : (List.range 25).all (fun l => k10PlaceB l l) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: the next link's place is of no link l. -/
theorem k10_place_off : (List.range 24).any (fun l => k10PlaceB (l + 1) l) = false := by
  decide +kernel

/-- The fact at a place. -/
theorem k10_place (l : ℕ) (hl : l < 25) (p : Place) (hp : At.ps[ixK10 l]? = some p) :
    p.link = some l ∧ standAt fullLinks p = Stand.link (subAt l) ∧
      p.piece ≤ 11 + 2 * shiftAt fullLinks l := by
  have h := List.all_eq_true.1 k10_place_full l (List.mem_range.2 hl)
  unfold k10PlaceB at h
  rw [hp] at h
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The test on the two numbers of the stage at the sizes g, against link l's list. -/
def khB (g : GroupSize) (l : ℕ) : Bool :=
  decide (kLay (loAt l) (kbW l) = (stageOf g 219).h + (stageOf g 219).g) &&
    decide ((stageOf g 219).h = 0)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL.** -/
theorem kh_full : (List.range 25).all (fun l => khB (gsAt l) l) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: not at every link do the next link's sizes fit. -/
theorem kh_off : (List.range 24).all (fun l => khB (gsAt (l + 1)) l) = false := by decide +kernel

/-- The fact at a link. -/
theorem kh_at (l : ℕ) (hl : l < 25) :
    kLay (loAt l) (kbW l) = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (stageOf (gsAt l) 219).h = 0 := by
  have h := List.all_eq_true.1 kh_full l (List.mem_range.2 hl)
  unfold khB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- The l-th written list is one of the written lists. -/
theorem loAt_mem (l : ℕ) (hl : l < 25) : loAt l ∈ linksFullLit := by
  have hn : l < linksFullLit.length := by
    have e : linksFullLit.length = 26 := by decide
    omega
  unfold loAt
  rw [List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

/-- **THE HINGE AT EVERY LINK**, at K10's own number. -/
theorem AtMg.hinge_all (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1) {l : ℕ} (hl : l < 25)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (ixK10 l) a) (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (loAt l) (kbW l)
        (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) := by
  rw [ixK10_is l hl] at hr
  by_cases h0 : l = 0
  · subst h0
    exact h.hinge_zero_at_border FF hM a hr hu
  · by_cases h24 : l = 24
    · subst h24
      exact h.hinge_head_at_border FF hM a hr hu
    · exact h.hinge_at_border FF hM (by omega) (by omega) a hr hu

/-- **K10Heavy's FIELD hX, AT THE CONSTANT's LETTERS, AT EVERY LINK.** -/
theorem AtMgA.hX_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (hl : l < 25) (p : Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (seat : Fin (loAt l).length → ℕ × ℕ)
    (seats : ∀ s, XK h l s → ∀ i, memMain (loAt l) i →
      seatBy noFirst s.1.2.book (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l i) =
        some (seat i)) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      RowAsks (At.cs Zp) (loAt l) seat (kbW l)
        (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
        (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
          (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 l))
        (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) a.1 := by
  intro z a hX
  obtain ⟨hon, hr, hu'⟩ := hX
  have hu : a.1.failed = none := not_not.1 hu'
  obtain ⟨e1, e2, e3⟩ := k10_place l hl p hp
  have H := h.toAtMg.hinge_all Fo rfl hl ((z, a.1), a.2) hr hu
  have hsh := VerifiableInference.Desc.First.K8.shapeAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks
    At.ps (fun a => a) (ixK10 l) ((z, a.1), a.2) hon hu
  rw [hp] at hsh
  unfold VerifiableInference.Desc.First.shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨Lk, hLk⟩ := link_of_stand a.1 (subAt l) (hsh.1.1.trans e2)
  have h5 := five_of_facts Fo ((z, a.1), a.2) hr hu hl p hp e1 e3 Lk hLk h.toAtMg.codes_full rfl
    h.toAtMg.shapeAt_full hM hZ [] H
  rw [e1]
  exact rowAsks_whole (At.cs Zp) (loAt l) seat (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) l Fo _ ((z, a.1), a.2) hon hr
    hu p hp e1 (subAt l) e2 rfl rfl (linksFull_layout _ (loAt_mem l hl) _)
    (h.toAtMg.hinge_inj l (by omega)) (kh_at l hl).1 (kh_at l hl).2 h5.2.2.1
    (seats _ ⟨hon, hr, hu'⟩) H

end P5J

#print axioms P5J.ixK10_is
#print axioms P5J.k10_place_full
#print axioms P5J.k10_place_off
#print axioms P5J.k10_place
#print axioms P5J.kh_full
#print axioms P5J.kh_off
#print axioms P5J.kh_at
#print axioms P5J.loAt_mem
#print axioms P5J.AtMg.hinge_all
#print axioms P5J.AtMgA.hX_at
