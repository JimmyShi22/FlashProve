-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5DoorAtPlus.lean: kind K5: THE PREMISE hdoor OF THE ROAD "behind"
(k5AtMg_behind_door, Johnson/Desc/First/Att/K05AtMgBehind.lean: "wherever the table's promise in
front of the kind's sub-protocol holds at a state without a mark, DoorYes holds there") AT ANY
FILLING THAT MEETS THE EQUATIONS MgIs (Johnson/Desc/First/Att/Door/Law/K5AtEqsPlus.lean): meant: the
wider filling over the composed filling.

IS IT EMPTY HERE? Fenced by the promise: at a filling whose promise never holds it is idle. NO
MEMBER IS SHOWN.

Main names:
  `k5_here`: at a place of the kind the promise's own clause on where the chain stands gives an open
    attention segment.
  `DataSent`: the law's Sent is the composed data's: three equations (by the make at the
    composed meaning's 𝔇.pubD (MgData.pubD, Johnson/Desc/Sound/MgAll.lean) with Dn := 𝔇.sent).
  `OpenQ`: fourteen public items are open at the border (among them K5.rowsBare,
    K5.lookLeft, and callerIn m, which the clause "planes" spends).
  `hdoor_plus`: **hdoor**, general in the two lists ps, qs.
  `hbare_plus`: **wherever the promise holds at a state without a mark, the kept rows of what the
    verifier has received from the lookup argument name no entry**: the fourth name's test; the item
    left's sentence pins what was received.
  `hleft_plus`: **the like for the test leftAtB (Johnson/Desc/First/FillBare.lean)
    at what was received and the open segment's ledger**: the fifth name's test.
PREMISES LEFT: MgIs · DataIs · DataSent (equations at mgAll's term) · K5Place · x.link = 2 g
+ 1 · the segment is not the output head's · D.nsOf's value · OpenQ (tests on the table; evaluated
at two written lists of segments, not typed) · LeftIsP (found by leftIs_at) · two tests on public
data (hPs · hPq: stated at D.dS; run nowhere at that term). Nothing is claimed on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5AtEqsPlus
import Johnson.Desc.First.Att.Door.Law.DoorYesPlus
import Johnson.Desc.First.Att.K05BehindOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask K3Data bornAt keptAt)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)

/-- **At a place of the kind an attention segment stands open.** -/
theorem k5_here {links : List ModelPart} {m : ℕ} {p p' : VerifiableInference.Desc.Place} (Ix : K5Place links m p p') {s : S}
    (h : shapeAt links (some p) s = true) : ∃ att, s.here = .att att := by
  unfold shapeAt at h
  simp only [Bool.and_eq_true] at h
  have h1 : standOf s = standAt links p := by simpa using h.1.1
  have h2 : standAt links p = .link .attention := by
    simp [standAt, Ix.link, Ix.sub, Ix.piece]
  rw [h2] at h1
  unfold standOf at h1
  cases e : s.here with
  | att a => exact ⟨a, rfl⟩
  | between => rw [e] at h1; cases h1
  | lay _ => rw [e] at h1; cases h1
  | head _ =>
    rw [e] at h1
    dsimp only at h1
    split at h1 <;> cases h1
  | fin _ => rw [e] at h1; cases h1
  | mem _ => rw [e] at h1; cases h1

/-- **The law's Sent is the composed data's.** -/
structure DataSent (D : PubData) (cs : Codes) (Dn : Sent) : Prop where
  d3 : D.d3 = K3Data.of D.d3.X Dn
  d5shape : D.d5.shape = Dn.shape
  codes : cs = Dn.codes

/-- Fourteen public items are open at the border. -/
structure OpenQ (m : ℕ) (Q : List Pub) : Prop where
  q1 : Pub.more (some m) "K5.liveReq" ∈ Q
  q2 : Pub.more (some m) "K5.readsThere" ∈ Q
  q3 : Pub.look m ∈ Q
  q4 : Pub.ledger m ∈ Q
  q5 : Pub.freeAbove m ∈ Q
  q6 : Pub.left m ∈ Q
  q7 : Pub.more (some m) "frame.liveIs" ∈ Q
  q8 : Pub.linkFresh m ∈ Q
  q9 : Pub.more none "K12.seatsCarried" ∈ Q
  q10 : Pub.more none "K12.msgShapes" ∈ Q
  q11 : Pub.more (some m) "frame.sentIs" ∈ Q
  q12 : Pub.more (some m) "K5.rowsBare" ∈ Q
  q13 : Pub.more (some m) "K5.lookLeft" ∈ Q
  q14 : Pub.callerIn m ∈ Q

section
variable {Pp Xi Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}

/-- **hdoor.** -/
theorem hdoor_plus (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (cs : OnBytes.Codes) (G0 : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
    (E : MgIs Mg Mg0 D cs G0 arr smp ms decT in0 c5 Ld Ms D13)
    (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
    (links : List ModelPart) (T : DataIs D Wv links (2 * g + 1)) (Dn : Sent) (Sn : DataSent D cs Dn)
    {pl pl' : VerifiableInference.Desc.Place} (Ix : K5Place links (2 * g + 1) pl pl') (hxl : x.link = 2 * g + 1)
    (hmH : (2 * g + 1 == D.mH) = false) {hi : ℕ} (hn : D.nsOf (2 * g + 1) = some hi)
    (O : List Item) (Q : List Pub) (Oq : OpenQ (2 * g + 1) Q) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → S × Fr.E.Str → Forest.Heard) (hL : LeftIsP Mg claim Wv g before a x plJ x0 gOf)
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    (hPs : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld ps (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true)
    (hPq : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms qs (D.N.msgsAt (some pl)) = true) :
    ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length (D.N.sent x.link 0) ps qs hi (gOf π a') a'.1 := by
  intro π a' hon
  obtain ⟨att, e⟩ := k5_here Ix (onAt_shape hon.1 hon.2)
  have hsub : links[2 * g + 1]? = some .attention := Ix.sub
  have hatt : D.d5.isAtt (2 * g + 1) = true := isAtt_of D.d5 (by rw [T.d5links]; exact hsub)
  have hlay : FillK4.isLay D.links (2 * g + 1) = false := att_not_lay (by rw [T.links]; exact hsub)
  have hsh : D.d3.shape = Dn.shape := by rw [Sn.d3]; rfl
  have hly : D.d3.layout = Dn.layout := by rw [Sn.d3]; rfl
  have har : D.d3.arrayOf.getD (2 * g + 1) #[] = Dn.arrayOf.getD (2 * g + 1) #[] := by rw [Sn.d3]; rfl
  have hborn : bornOf D.d5.shape (2 * g + 1) = bornAt Dn x.link := by rw [Sn.d5shape, hxl]; rfl
  have hown : D.d5.ownOf (2 * g + 1) = D.N.sent x.link 0 := by rw [T.own, hxl]
  have R := doorYes_plus D Ld Ms Mg0.pub Mg E.pub cs (fun z => in0 z && c5 z.1) E.inOrder D.N links Ix O Q hatt hlay hmH hn
    Oq.q1 Oq.q2 Oq.q3 Oq.q4 Oq.q5 Oq.q6 Oq.q7 Oq.q8 Oq.q9 Oq.q10 Oq.q11 x hxl Dn hsh hly har Sn.codes (bornAt Dn x.link) hborn
    (keptAt Dn x.link).length ps qs π a'.1 (strsOf Fr a'.2) hon.1 hon.2 att e _ _ _ _ _ _ _ (gOf π a') (hL π a')
    (by rw [hown]; exact hPs) hPq
  rw [T.d5W, hown] at R
  exact R

/-- **The kept rows are bare, under the promise.** -/
theorem hbare_plus (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (cs : OnBytes.Codes) (G0 : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
    (E : MgIs Mg Mg0 D cs G0 arr smp ms decT in0 c5 Ld Ms D13)
    (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
    (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (Oq : OpenQ (2 * g + 1) Q)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → S × Fr.E.Str → Forest.Heard) (hL : LeftIsP Mg claim Wv g before a x plJ x0 gOf) :
    ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ f ∈ ((gOf π) a').rows.toList, f.ents = #[] := by
  intro π a' hon f hf
  have hb : bareAttB a'.1 = true := by
    have := onAt_pub hon.1 hon.2 _ Oq.q12
    rwa [E.pub, pubAll_plus_bare] at this
  obtain ⟨_, _, _, _, hd', _⟩ := left_parts (hL π a' (onAt_pubP hon.1 hon.2 _ Oq.q6))
  unfold bareAttB at hb
  cases e : a'.1.here with
  | att att =>
    rw [e] at hb
    have hl : att.lookHeard = some ((gOf π) a') := by
      have := hd'
      unfold K3.seatCalls S.lookHeard? at this
      simp only [e] at this
      exact this
    simp only [hl, Option.any_some, List.all_eq_true] at hb
    simpa [Array.isEmpty_iff] using hb f hf
  | between => rw [e] at hb; cases hb
  | lay _ => rw [e] at hb; cases hb
  | head _ => rw [e] at hb; cases hb
  | fin _ => rw [e] at hb; cases hb
  | mem _ => rw [e] at hb; cases hb

/-- **What the lookup argument has left passes the test FillBare.leftAtB, under the promise.** -/
theorem hleft_plus (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (cs : OnBytes.Codes) (G0 : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
    (E : MgIs Mg Mg0 D cs G0 arr smp ms decT in0 c5 Ld Ms D13)
    (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
    (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (Oq : OpenQ (2 * g + 1) Q)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → S × Fr.E.Str → Forest.Heard) (hL : LeftIsP Mg claim Wv g before a x plJ x0 gOf) :
    ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' → ∀ att, a'.1.here = .att att →
      FillBare.leftAtB ((gOf π) a') att.F = true := by
  intro π a' hon att e
  have hb : leftAttB a'.1 = true := by
    have := onAt_pub hon.1 hon.2 _ Oq.q13
    rwa [E.pub, pubAll_plus_left] at this
  obtain ⟨_, _, _, _, hd', _⟩ := left_parts (hL π a' (onAt_pubP hon.1 hon.2 _ Oq.q6))
  have hl : att.lookHeard = some ((gOf π) a') := by
    have := hd'
    unfold K3.seatCalls S.lookHeard? at this
    simp only [e] at this
    exact this
  unfold leftAttB at hb
  rw [e] at hb
  simpa [hl] using hb

end

end H2K5.Door

#print axioms H2K5.Door.hleft_plus
#print axioms H2K5.Door.hbare_plus
#print axioms H2K5.Door.k5_here
#print axioms H2K5.Door.hdoor_plus
