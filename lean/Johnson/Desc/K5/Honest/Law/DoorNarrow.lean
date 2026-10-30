-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/DoorNarrow.lean: CONDITIONAL: the library's list of tests and equations
on the verifier's state in front of the block of an attention segment's own rounds (`DoorYes`,
Johnson/Desc/First/Att/K05DoorYes.lean) holds at ONE state that meets the promise which the table
of the verifier's blocks carries in front of that block, AT THE TABLE'S OWN FILLING, and at which
five named facts hold. From it: what the library's laws on the state behind the block's lay ask in
front, and that the segment's four runs of claims return.

Why. The library has `DoorYes` from the promise at a wider filling of the table
(`doorYes_plus`, Johnson/Desc/First/Att/Door/Law/DoorYesPlus.lean), in which three further public
items are open and the clause "in order" holds the statement's codes. What these four hand to that
proof are five facts on the state. Here the five are premises at the one state, and the promise
stays at the caller's own filling and the caller's own list Q of open items: of the filling it is
asked only that its tests with code are `pubAll D base`, at any base. So no widening of the promise
is needed for `DoorYes`. The proof follows that of `doorYes_plus` field by field.

Main names:
  `FiveAt L M sent s`: the five facts at a state: the book carries the listed seats; the
    statement's messages have the listed shapes; the live request's shape, its rows' layout and
    the statement's codes are those of `sent`. They are five of the seven fields of the library's
    `K5Along` (Johnson/Desc/First/Att/Door/Law/K5Along.lean), at one state.
  `fiveAt_of_along`: from `K5Along Rch L M sent` at a state that Rch admits and that bears no mark.
  `doorYes_narrow`: **`DoorYes`**.
  `front_of_door`: from `DoorYes`: `FrontAll`, `U3There`, "every slot that the lookup's last claim
    names is filled", and "the ledger is sized".
  `runsReturn_of_door`: from `DoorYes`, what the lookup leaves (`K3LeftOutIs`), tests on the plan
    and the hearing's return: `RunsReturn`.

Limits. All are conditional. The five facts are a trade for what the wider filling hands over, not
a gift. `doorYes_narrow` keeps these premises of `doorYes_plus`: eight public items are open
in the caller's list (that they are open at the table's own list at the border is not decided
here); equations between the law's letters and the composed data; two tests on public data; what
the item on the lookup's leavings says. The premises hsh, hly, hcs of `doorYes_plus` fall away;
three of the five facts take their place. That the five facts hold at
a state of an honest run is not shown here. The two further fields of `K5Along` are not spent.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.DoorYesPlus
import Johnson.Desc.First.Att.Door.Law.K5Along
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsB
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsF
import Johnson.Desc.First.Att.K05FrontOfDoor
import Johnson.Desc.First.Att.K05RunsReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent linkFreshC)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Att.P (DoorYes K5Place K3LeftOutIs onAt_pub onAt_pubP onAt_shape
  k5_link link_front seatsPlanB shapesPlanB seatsOn_of_items shapesOn_of_items)
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes)

/-- Five facts at a state of the verifier. Whoever follows the run up to the state pays them. -/
structure FiveAt (L : Laid) (M : List OracleShape) (sent : Sent) (s : S) : Prop where
  /-- the book carries the listed seats -/
  seats : atFirstSeats L s = true
  /-- the statement's messages have the listed shapes -/
  shapes : atFirstShapes M s = true
  /-- the live request's shape -/
  liveShape : s.live.frame.shape = sent.shape
  /-- its rows' layout -/
  liveLayout : s.live.rows.layout = sent.layout
  /-- the statement's codes -/
  codes : s.st.codes = sent.codes

/-- The five from the library's structure of facts along a condition Rch, at a state that Rch
admits and that bears no mark. Conditional: A, hr, hm. -/
theorem fiveAt_of_along {P : Type} {Fr : Frame} {Rch : ℕ → (P × S) × Fr.E.Str → Prop} {L : Laid}
    {M : List OracleShape} {sent : Sent} (A : H2K5.Door.K5Along Rch L M sent) {k : ℕ}
    {a : (P × S) × Fr.E.Str} (hr : Rch k a) (hm : a.1.2.failed = none) : FiveAt L M sent a.1.2 :=
  ⟨A.seats k a hr hm, A.shapes k a hr hm, A.liveShape k a hr hm, A.liveLayout k a hr hm,
    A.codes k a hr hm⟩

/-- **The list of tests and equations in front of the block, from the promise at the table's own
filling and the five facts.** Conditional:
  hpub: the filling's public half is the composed one;
  Ix, hatt, hlay, hmH, hn: the place is the block's, at an attention segment m that is not the
    output head's, with a planned number of slots;
  q1 .. q11: eight public items are open at the border (tests on the table's lists);
  hxl, har, hborn: equations between the law's letters and the composed data;
  hon, hu, e: the promise holds at the state, which bears no mark and has the segment open;
  hleft: what the item on the lookup's leavings says (at the library's composed filling:
    `leftIs_at`, Johnson/Desc/First/Att/Door/Law/LeftIsAt.lean);
  hPs, hPq: two tests on public data;
  F: the five facts, at the law's own `Sent`. -/
theorem doorYes_narrow {Pp W St₀ J₀ : Type} [DecidableEq J₀] (D : PubData) (L : Laid)
    (M : List OracleShape) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W)
    (hpub : Mg.pub = pubAll D base) (N : Numbers) (links : List ModelPart)
    {pl pl' : VerifiableInference.Desc.Place} {m : ℕ} (Ix : K5Place links m pl pl') (O : List Item)
    (Q : List Pub) (hatt : D.d5.isAtt m = true) (hlay : isLay D.links m = false)
    (hmH : (m == D.mH) = false) {nsPlan : ℕ} (hn : D.nsOf m = some nsPlan)
    (q1 : Pub.more (some m) "K5.liveReq" ∈ Q) (q2 : Pub.more (some m) "K5.readsThere" ∈ Q)
    (q3 : Pub.look m ∈ Q) (q4 : Pub.ledger m ∈ Q) (q5 : Pub.freeAbove m ∈ Q)
    (q6 : Pub.left m ∈ Q) (q8 : Pub.linkFresh m ∈ Q)
    (q11 : Pub.more (some m) "frame.sentIs" ∈ Q) (x : Look.Place) (hxl : x.link = m) (Dn : Sent)
    (har : D.d3.arrayOf.getD m #[] = Dn.arrayOf.getD m #[]) (born : Array (ℕ × ℕ))
    (hborn : H2K5.Door.bornOf D.d5.shape m = born) (kept : ℕ) (ps : List (ℕ × (ℕ × ℕ)))
    (qs : List (ℕ × OracleShape)) (π : Pp) (s : S) (y : Strs)
    (hon : onAt N Mg links (some pl) O Q (π, s) y) (hu : s.failed = none) (att : AttOwn)
    (e : s.here = .att att) (fork : S → Option Fork) (hS : Forest.Shape) (lm first : ℕ)
    (ι : Fo.Pl → Option J₀) (Qf : Fork → Prop) (x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
    (gL : Forest.Heard)
    (hleft : Mg.pubP (.left m) (π, s) →
      K3LeftOutIs fork (fun s : S => s.lookHeard?) hS lm first ι Qf x0 gL s)
    (hPs : seatsPlanB D.dS m kept L ps (D.d5.ownOf m) (N.msgsAt (some pl)) = true)
    (hPq : shapesPlanB D.dS m kept M qs (N.msgsAt (some pl)) = true) (F : FiveAt L M Dn s) :
    DoorYes D.d5.W x Dn born kept (D.d5.ownOf m) ps qs nsPlan gL s := by
  have P := fun q hq => by have := onAt_pub hon hu q hq; rwa [hpub] at this
  have hl : att.L.link = m := k5_link Ix e (onAt_shape hon hu)
  have hB : bookAt N (some pl) s = true := by
    obtain ⟨_, hm | ⟨h1, _, _, _⟩⟩ := hon
    · exact absurd hu hm
    simp only [Bool.and_eq_true] at h1
    exact h1.2
  have l1 : att.L.check.frame.shape = Dn.shape := by
    have := F.liveShape
    unfold S.live at this
    rw [link_front e] at this
    exact this
  have l2 : att.L.check.rows.layout = Dn.layout := by
    have := F.liveLayout
    unfold S.live at this
    rw [link_front e] at this
    exact this
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
      seats := seatsOn_of_items (by have := P _ q11; rwa [pubAll_more_sentIs] at this) F.seats hB
        (link_front e) hPs
      shapes := shapesOn_of_items (by have := P _ q11; rwa [pubAll_more_sentIs] at this) F.shapes hB
        (link_front e) hPq
      reads := by have := P _ q2; rwa [pubAll_more_readsThere D _ m hatt] at this
      look := by have := P _ q3; rwa [pubAll_look_att D _ m hmH hlay hatt] at this
      sized := P _ q4
      ns := fun F' hF => by
        simp only [Option.any_some] at p5
        unfold First.freeAboveB at p5
        rw [hF] at p5
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at p5
        omega
      heard := hh
      link := ⟨att.L, link_front e, hl.trans hxl.symm, l1, l2, by rw [p8.2, hxl, har], F.codes⟩ }

/-- **What the library's laws on the state behind the lay ask in front, from the list of tests.**
Conditional: hA, hP: the public parameters have the plan A at the place's group, and it is one that
the planner returned, but for one field; Y; e: the segment is open. -/
theorem front_of_door {W : Verify.Public} {x : Look.Place} {A : Attention.Plan} {D : Sent}
    {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ}
    {gL : Forest.Heard} {s : S} {att : AttOwn} (hA : W.A[x.link / 2]? = some A)
    (hP : K5Law.OfPlan A)
    (Y : DoorYes W x D (Look.bornAt D x.link) (Look.keptAt D x.link).length own ps qs hi gL s)
    (e : s.here = .att att) :
    Att.P.FrontAll x A D own ps qs hi gL s ∧ Att.P.U3There own s att (Att.P.parCOf A) ∧
      _root_.Fo.FilledA att.F gL.cEnd ∧ OnBytes.Model.Road.Sized att.F := by
  have Fa := Att.P.frontAll_of_door hA hP Y
  have led : Att.P.seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  refine ⟨Fa, ?_, H2K5.Door.fill_of_door W x D Y e, (Fa.ledger att.F led).1⟩
  obtain ⟨L₀, hL₀, hl₀, _⟩ := Y.link
  obtain rfl : att.L = L₀ := Option.some.inj ((link_front e).symm.trans hL₀)
  exact H2K5.Door.u3There_of_sheet W own s att e A (by rw [hl₀]; exact hA) Y.reads

/-- **The segment's four runs of claims return behind the lay.** Conditional:
  hP, h4, ha, hx: the public parameters' plans are the planner's, the proof covers attention, the
    group g has the plan a and the lookup on the calls has the place x;
  hG, hb, hc: three tests with code on the plan (the block's guard asks them);
  hl: what the lookup leaves, at the state;
  Y: the list of tests in front; e: the segment is open; hh: the hearing returns.
Dn, rad, Ex, Wp, al: letters of the library's law that is called; free. -/
theorem runsReturn_of_door {Cl : Type} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : Att.P.PlanIs Wv) (h4 : Wv.p4 = true) {g : ℕ} (before : List (ℕ × ℕ))
    {a : Attention.Plan} (ha : Wv.A[g]? = some a) {x : Look.Place}
    (hx : Look.lookAt Wv (2 * g + 1) false = some x)
    (hG : Att.P.k5GuardN Wv (2 * g + 1) g = true)
    (hb : Att.P.planOk (Att.P.parO Wv (2 * g + 1) a before) = true)
    (hc : Att.P.claimsOkAtO a = true) (Dn : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec)
    (Wp : Type) (al : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (Look.JAtt x.ns a.seam.tl)) → Cb.Gl.E)
    {ι : Fo.Pl → Option (Look.JAtt x.ns a.seam.tl)} {Qf : Fork → Prop}
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (Look.JAtt x.ns a.seam.tl))} {gL : Forest.Heard}
    {s : S}
    (hl : K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next ι Qf
      x0 gL s)
    {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))} {qs : List (ℕ × OracleShape)} {hi : ℕ}
    (Y : DoorYes Wv x Dn (Look.bornAt Dn x.link) (Look.keptAt Dn x.link).length own ps qs hi gL s)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Att.P.Heard} {G : Fork}
    (hh : Att.P.hear (Att.P.parO Wv (2 * g + 1) a before).own (att.F, rs, 0) =
      some (hd, G, [], 0)) :
    Att.P.RunsReturn a s att hd G := by
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ha hx
  have hOf : K5Law.OfPlan a := by
    obtain ⟨A0, pf, h0, e'⟩ := hP g a ha
    exact ⟨_, _, _, A0, pf, h0, e'⟩
  have hA : Wv.A[x.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ha
  obtain ⟨Fa, _, hFl, _⟩ := front_of_door hA hOf Y e
  obtain ⟨x', A0, hx', ⟨pf, e'⟩, Pb⟩ := Att.P.guard_gives_written hP h4 g before Dn rad ha hG hb hc
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  have eS : a.S = A0.S := by rw [e']
  have eF : a.fs = A0.fs := by rw [e']
  have elm : (Att.P.parCOf A0).geo.lmb = (Att.P.parCOf a).geo.lmb := by rw [e']; rfl
  exact Att.P.runsReturn_at x' Dn rad Ex Wp claim al a.ns Pb eS eF elm hl Fa hFl e hh

end H2K5.Honest

#print axioms H2K5.Honest.fiveAt_of_along
#print axioms H2K5.Honest.doorYes_narrow
#print axioms H2K5.Honest.front_of_door
#print axioms H2K5.Honest.runsReturn_of_door
