-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05BehindWorth.lean: kind K5: THE UPPER JOINT: THE FIELD worth OF K5Behind
(Johnson/Desc/First/Att/K05LawOne.lean: what the kind's law asks of the relation behind the kind),
AT THE LAW's OWN LETTERS, FROM billsWorthJ_public (Johnson/Desc/First/Att/K05TiePublic.lean): the
carriage ends where the law begins, and Lean holds that the letters fit. WHAT IS ASKED BEHIND THE
LAY IS PROVED HERE, out of LaidBehind (the record behind comes of a real hearing from a record with
"on"), what stands in front, and public data.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. Of the premises one payer of TiePub, tiePublicB's yes, has
been evaluated (at the library's two written policy texts: true at every attention link); none of
the others.

EVERY LETTER UNDER ∀ THAT THE CONCLUSION READS, AND WHAT PINS IT: a: on a · b, w: LaidBehind ∧ R' ·
F: the ledger of a.1 · G, h: the lay's equation pins b.1 BY them; LaidBehind's own hearing lays the
same b.1: so they are that hearing's (lay_same) · Ls: Said · l, i, l₁, l₂, jn, kf, xj: Returns'
fields, i.iU3 by its field u3 · pt, L: segAt? and link?.

Main names:
  `SecL L t`: the open link's list of arrays names an array at t, the link's own, of its second
    sending: a fact on the link alone. `secL_gives`: so it is of the second sending at every state
    at which that link is open.
  `u3PublicB D x A`: a Bool on public data: link x.link's list of arrays names an array at A.iU3;
    the layout has it; it is that link's own; its message is of moment 1 (the second sending).
  `sec_of_public`: so, at a state whose open link bears D's letters, the list names it and it is of
    the second sending: a second payer; no top asks it.
  `lay_same`: two lays with one return have one ledger and one heard record.
  `LedgerOk A hi F`: what is asked of the ledger in front: sized; at most hi slots; the array A.iU3
    is there, as wide as the plan's, at least A.nW wide, of one row.
  `FrontAll … a`: ALL THAT IS ASKED IN FRONT, under "on" alone: FrontFacts · LedgerOk at the
    record's ledger · the open segment's field g holds a record with SeatReadsSame to gOf a · gOf
    a's closing form names no entry · SecL at the open link and A.iU3.
  `behind_of_laid`: **BehindFacts and "G has the array", PROVED.**
  `k5Behind_worth`: **K5Behind's field worth, to the letter**: N := numsPlan p.own (x.F.next +
    Forest.elems x.fs) · A0 := { A with NC := A.S.calls.size } · tl := A.seam.tl · Kc := plannedK A
    · nW := A.nW · xr := p.own · part := I.part · the relation behind := LaidBehind ∧ R'.
  `k5Behind_worth_table`: **the same AT THE LETTERS AT WHICH THE KIND's ROW OF THE TABLE OF JOINTS
    CALLS THE LAW**: R' := relAt (meansQ Nn Mg' fun s => (π, s)) (outsQ links ps k).
ALL PREMISES OF THE TOPS: hpart (the pin's item's part is msgsOf …) · hitems | hfT, o1, o2 (the two
filled items) · hpub (TiePub: four facts on public data) · r1 r2 r3 (three memberships in the
filling's letter runs) · hRd (the reader's three lists hold the returned forms; asked under all that
BillsWorthJ hands) · hm (MemAt at the read members) · hSt (the one St at the states of this
attention segment) · hfront (FrontAll under "on"). Limits. A rule over letters. It stands over
Returns WITH the field u3. Nothing
is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05TiePublic
import Johnson.Desc.First.Att.K05EntsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT seatTab formsTQ Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt)

/-- The array of the reads is the link's own, of its second sending: on public data. -/
def u3PublicB (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan) : Bool :=
  match (D.arrayOf.getD x.link #[])[A.iU3]? with
  | none => false
  | some bq =>
    match OnBytes.reqArray D.layout bq.1 bq.2 with
    | none => false
    | some Ar =>
      bq.1 == x.link &&
        match (D.shape.link[bq.1]?).bind fun l => l.messages[Ar.message]? with
        | some m => m.moment == 1
        | none => false

/-- The open link's list of arrays names an array at t, the link's own, of its second sending: a
fact on the link alone. -/
def SecL (L : LinkCtx) (t : ℕ) : Prop :=
  ∃ b Ar, L.arrayOf[t]? = some b ∧ OnBytes.reqArray L.check.rows.layout b.1 b.2 = some Ar ∧
    (b.1 == L.check.frame.link &&
      match (L.check.frame.shape.link[b.1]?).bind fun l => l.messages[Ar.message]? with
      | some m => m.moment == 1
      | none => false) = true

/-- At every state of the verifier at which that link is open the array is of the second sending. -/
theorem secL_gives {L : LinkCtx} {t : ℕ} (h : SecL L t) {s : First.S}
    {pt : VerifiableInference.Desc.K9.Part} (hpt : segAt? s = some pt) (hL : s.link? = some L) :
    (L.arrayOf[t]?).isSome = true ∧ ∀ b, L.arrayOf[t]? = some b → second s b = true := by
  obtain ⟨b, Ar, hb, ha, hm⟩ := h
  obtain ⟨e1, _, _⟩ := seg_parts hpt hL
  refine ⟨by rw [hb]; rfl, fun b' hb' => ?_⟩
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  unfold second
  rw [hpt]
  show (match OnBytes.reqArray pt.L.check.rows.layout b.1 b.2 with
    | some A' => atMoment1 pt b A'
    | none => false) = true
  rw [e1, ha]
  show atMoment1 pt b Ar = true
  unfold atMoment1
  rw [e1]
  exact hm

/-- At a state whose open link bears D's letters: the list names the array; it is of the second
sending: a second payer, off public data. -/
theorem sec_of_public {D : Sent} {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan}
    (h : u3PublicB D x A = true) {s : First.S} {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx}
    (hpt : segAt? s = some pt) (hL : s.link? = some L) (hfl : L.check.frame.link = x.link)
    (hshape : L.check.frame.shape = D.shape) (hlay : L.check.rows.layout = D.layout)
    (harr : L.arrayOf = D.arrayOf.getD x.link #[]) :
    (L.arrayOf[A.iU3]?).isSome = true ∧ ∀ b, L.arrayOf[A.iU3]? = some b → second s b = true := by
  obtain ⟨e1, _, _⟩ := seg_parts hpt hL
  unfold u3PublicB at h
  rw [harr]
  cases hb : (D.arrayOf.getD x.link #[])[A.iU3]? with
  | none =>
    rw [hb] at h
    cases h
  | some bq =>
    rw [hb] at h
    simp only at h
    refine ⟨rfl, fun b hbb => ?_⟩
    obtain rfl := Option.some.inj hbb
    cases ha : OnBytes.reqArray D.layout bq.1 bq.2 with
    | none =>
      rw [ha] at h
      cases h
    | some Ar =>
      rw [ha] at h
      simp only at h
      unfold second
      rw [hpt]
      show (match OnBytes.reqArray pt.L.check.rows.layout bq.1 bq.2 with
        | some A' => atMoment1 pt bq A'
        | none => false) = true
      rw [e1, hlay, ha]
      show atMoment1 pt bq Ar = true
      unfold atMoment1
      rw [e1, hfl, hshape]
      exact h

/-- Two lays with one return have one ledger and one heard record. -/
theorem lay_same {a a' b : First.S} {h h' : Heard} {F F' G G' : Fork}
    (l1 : seatSO.ledger a = some F) (e1 : seatSO.lay a h G = some b)
    (l2 : seatSO.ledger a' = some F') (e2 : seatSO.lay a' h' G' = some b) : G' = G ∧ h' = h := by
  obtain ⟨t1, _, _, r1⟩ := lay_is l1 e1
  obtain ⟨t2, _, _, r2⟩ := lay_is l2 e2
  have e : (behind a t1 h G).here = (behind a' t2 h' G').here := by rw [← r1, ← r2]
  have e' : (First.Here.att { t1 with F := G, heard5 := some h }) =
      First.Here.att { t2 with F := G', heard5 := some h' } := e
  have e3 := First.Here.att.inj e'
  exact ⟨(congrArg (·.F) e3).symm, (Option.some.inj (congrArg (·.heard5) e3)).symm⟩

/-- What is asked of the ledger in front. -/
def LedgerOk (A : Attention.Plan) (hi : ℕ) (F : Fork) : Prop :=
  Sized F ∧ F.ns ≤ hi ∧ U3At A (plannedK A) F

/-- **All that is asked in front, under "on" alone.** -/
structure FrontAll (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan) (D : Sent)
    (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (hi : ℕ)
    (gL : Forest.Heard) (s : First.S) : Prop where
  facts : ∃ L, FrontFacts x A D own ps qs s L
  ledger : ∀ F, seatSO.ledger s = some F → LedgerOk A hi F
  reads : ∀ a₀, s.here = .att a₀ → ∃ g, a₀.g = some g ∧ SeatReadsSame g gL
  plain : gL.cEnd.ents = #[]
  sec : ∀ L, s.link? = some L → SecL L A.iU3

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **What is asked behind the lay, proved**: out of LaidBehind, the front's facts and public data.
-/
theorem behind_of_laid {Fr : Frame} (p : Par) (base : ℕ) (k3 : Runs.PadIn) (tj : OnBytes.K.Kc.Tape)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (on : First.S × Fr.E.Str → Prop)
    (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (hi : ℕ)
    (hfront : ∀ a : First.S × Fr.E.Str, on a → FrontAll x A D own ps qs hi (gOf a) a.1)
    (a b : First.S × Fr.E.Str) (ha : on a) (hLB : LaidBehind Fr seatSO p base on b) (F G : Fork)
    (h : Heard) (Ls : Lists) (h1 : seatSO.ledger a.1 = some F) (h2 : seatSO.lay a.1 h G = some b.1)
    (s1 : Said p.own h G Ls) (s3 : G.ns = F.ns) (l : Left) (i : Runs.In) (l₁ l₂ : List Aff)
    (jn : Runs.JoinsP) (kf : Array Aff) (xj : Aff × Fork × OnBytes.K.Kc.Tape)
    (Rt : Returns A.S (gOf a).zx (gOf a).zk G h l { A with NC := A.S.calls.size } (gOf a) i (plannedK A)
      l₁ l₂ jn k3 kf G tj xj A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)))
    (pt : VerifiableInference.Desc.K9.Part) (L : LinkCtx) (hpt : segAt? b.1 = some pt)
    (hLa : a.1.link? = some L) :
    BehindFacts A hi b.1 L pt (l₁ ++ l₂ ++ [xj.1]) ∧ (G.trees[A.iU3]?).isSome = true := by
  obtain ⟨a', F0, G', h', rs, ha', _, hl', _, _, hh, hlay', _⟩ := hLB
  obtain ⟨rfl, rfl⟩ := lay_same h1 h2 hl' hlay'
  -- the ledger behind has the arrays of the ledger from which it was heard
  obtain ⟨hz0, _, T, hT, hK, hW, hR1⟩ := (hfront a' ha').ledger F0 hl'
  obtain ⟨_, bl⟩ := hear_below hh hz0
  have hU : U3At A (plannedK A) G' := ⟨T, by rw [bl.trees]; exact hT, hK, hW, hR1⟩
  -- the open link
  obtain ⟨L', T'⟩ := (hfront a ha).facts
  obtain rfl : L' = L := Option.some.inj (T'.hL.symm.trans hLa)
  have hLb : b.1.link? = some L' := (lay_keeps h1 h2).1.trans hLa
  obtain ⟨_, hsec⟩ := secL_gives ((hfront a ha).sec L' T'.hL) hpt hLb
  -- the part's ledger is G
  obtain ⟨att, _, _, eb⟩ := lay_is h1 h2
  have hF : pt.F = G' := by
    have hp : segAt? b.1 = segAt? (behind a.1 att h' G') := by rw [eb]
    rw [hp] at hpt
    have : (segAt? (behind a.1 att h' G')).map (·.F) = some G' := rfl
    rw [hpt] at this
    exact Option.some.inj this
  refine ⟨⟨?_, hsec, ents_of_returns Rt rfl s1 hU (hfront a ha).plain⟩, ?_⟩
  · rw [hF, s3]
    exact ((hfront a ha).ledger F h1).2.1
  · obtain ⟨T2, hT2, _⟩ := hU
    rw [hT2]
    rfl

/-- **K5Behind's field worth, to the letter.** -/
theorem k5Behind_worth {Fr : Frame} (p : Par) (ns base : ℕ) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base (Wit Cells Tok MsgT) (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (Nn : Numbers)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ)
    (hpart : I.part = fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w)
    (hitems : ∀ b w, LaidBehind Fr seatSO p base on b → R' b w →
      (∀ p ∈ runs x.link 3 "own", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w)) ∧
      ∀ p ∈ runs x.link 2 "join", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (hpub : TiePub D x A.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    (hRd : ∀ (a b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT), on a →
      (LaidBehind Fr seatSO p base on b ∧ R' b w) →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said p.own h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l { A with NC := A.S.calls.size } (gOf a) i (plannedK A)
          l₁ l₂ jn k3 kf G tj xj A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          (Rds x.link).forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          (Rds x.link).forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          (Rds x.link).forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Fr.E.Str, on a →
      FrontAll x A D (Nn.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi (gOf a) a.1) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns
      (numsPlan p.own (x.F.next + Forest.elems x.fs)) { A with NC := A.S.calls.size } (plannedK A) k3
      A.nW tj gOf (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO p.own
      (fun a : First.S × Fr.E.Str => a.1) (fun a : First.S × Fr.E.Str => a.1) on I.part
      (fun b w => LaidBehind Fr seatSO p base on b ∧ R' b w) := by
  rw [hpart]
  exact billsWorthJ_public x A D rad Ex Wp α ns _ { A with NC := A.S.calls.size } k3 tj gOf p.own on
    (fun b w => LaidBehind Fr seatSO p base on b ∧ R' b w) Rds runs St Nn arr seat ms hi
    hpub r1 r2 r3 (fun b w h => hitems b w h.1 h.2) hRd hm hSt
    (fun a ha => ⟨(hfront a ha).facts, (hfront a ha).reads⟩)
    (fun a b _ ha hR F G h Ls h1 h2 s1 _ s3 l i l₁ l₂ jn kf xj Rt pt L hpt hLa =>
      behind_of_laid x A D p base k3 tj gOf on _ _ _ hi hfront a b ha hR.1 F G h Ls h1 h2 s1 s3 l i
        l₁ l₂ jn kf xj Rt pt L hpt hLa)

/-- **The same at the letters at which the kind's row of the table calls the law.** -/
theorem k5Behind_worth_table {Pp : Type} {Fr : Frame} (p : Par) (ns base : ℕ) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base (Wit Cells Tok MsgT) (attSg x D rad).Msg) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (Nn : Numbers)
    (Mg' : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp) (links : List ModelPart) (pls : List Place) (k : ℕ)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ)
    (hpart : I.part = fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w)
    (hfT : ∀ (pc : ℕ) (r : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg'.formsT x.link pc r (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link pc r, formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (o1 : outsQ links pls k (.formsT x.link 3 "own"))
    (o2 : outsQ links pls k (.formsT x.link 2 "join"))
    (hpub : TiePub D x A.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    (hRd : ∀ (a b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT), on a →
      (LaidBehind Fr seatSO p base on b ∧
        relAt (meansQ (Fr := Fr) Nn Mg' fun s => (π, s)) (outsQ links pls k) b w) →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said p.own h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l { A with NC := A.S.calls.size } (gOf a) i (plannedK A)
          l₁ l₂ jn k3 kf G tj xj A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          (Rds x.link).forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          (Rds x.link).forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          (Rds x.link).forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Fr.E.Str, on a →
      FrontAll x A D (Nn.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi (gOf a) a.1) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns
      (numsPlan p.own (x.F.next + Forest.elems x.fs)) { A with NC := A.S.calls.size } (plannedK A) k3
      A.nW tj gOf (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO p.own
      (fun a : First.S × Fr.E.Str => a.1) (fun a : First.S × Fr.E.Str => a.1) on I.part
      (fun b w => LaidBehind Fr seatSO p base on b ∧
        relAt (meansQ (Fr := Fr) Nn Mg' fun s => (π, s)) (outsQ links pls k) b w) := by
  refine k5Behind_worth x A D rad Ex Wp α p ns base k3 tj gOf on I _ Rds runs St Nn
    arr seat ms hi hpart (fun b w _ h => ?_) hpub r1 r2 r3 hRd hm hSt hfront
  exact ⟨hfT 3 "own" b w (h _ o1), hfT 2 "join" b w (h _ o2)⟩

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.sec_of_public
#print axioms VerifiableInference.Desc.First.Att.P.lay_same
#print axioms VerifiableInference.Desc.First.Att.P.behind_of_laid
#print axioms VerifiableInference.Desc.First.Att.P.k5Behind_worth
#print axioms VerifiableInference.Desc.First.Att.P.k5Behind_worth_table
