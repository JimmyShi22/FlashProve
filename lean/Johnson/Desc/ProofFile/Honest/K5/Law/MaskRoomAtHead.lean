-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskRoomAtHead.lean: CONDITIONAL: UNDER THE LIBRARY's
HYPOTHESIS ON THE PUBLIC INPUT (`P5J.AtMgA`) THE SLOTS OF AN ATTENTION SEGMENT's PLAN AND ONE PLACE
MORE HAVE ROOM IN THE MASK CODE's MESSAGE LENGTH; so `MaskRoom` (Honest/K5/Law/ScriptQRaw.lean) is
no premise there, and `ReaderReads` at the member of the kind K5 (Honest/K5/Law/ReaderReadsK5.lean)
stands without it. Statements with their proofs; no definition.

  `room_of_built`       CONDITIONAL: from a return of the planning program's `buildLinksH`: at every
                        built link X: X.ns + 1 ≤ the message length of the mask code of the message
                        that holds the link's mask row
  `room_at_head`        CONDITIONAL: a.ns + 1 ≤ that length, at the hypothesis' letters
  `maskRoom_at_head`    CONDITIONAL: `MaskRoom` … a.ns 1
  `letters_head`        CONDITIONAL: there are a plan, a place and a message's number as the others
                        take them
  `readerReads_K5_h`    CONDITIONAL: **`ReaderReads` at the letters as they are laid, WITHOUT
                        `MaskRoom`**

THE PREMISES OF `readerReads_K5_h`, ALL OF THEM. h · hg: g is below 12 · Pl, hx, hm: WHICH plan a,
place x₁ and number kM are meant: the group's plan, the place of the segment's lookup on the calls,
the number of the message that holds the mask row: `letters_head` has such letters under h and hg ·
hN: N is at most the number of challenges heard at the border in front of the member: N is a letter:
the larger it is, the less hQ asks, and hN bounds it · hQ: the hypothesis on the Script, as in
Honest/K5/Law/ReaderReadsK5.lean: under the three guards of the frame's form `OwnMsgs`. SO h AND hQ
ALONE ASK SOMETHING.

The road. The planning program tests of every link that it builds that its slots and the answers'
pads have room in the mask row (`linkLaid`, OnBytes/Model/StagesLinks.lean). The library has that
test's yes from the program's return (`links_laid`, Johnson/Desc/First/Att/K05PublicOfBuilt.lean)
and what it says (`linkLaid_ns`, Johnson/Desc/Kinds/Law/LinksFitNs.lean); its own test on the seats
of mask entries (`masksUpTo`) keeps only the weaker "the slots have room". Three ties are drawn
here. The program's return under h: `built_of_pub` (Johnson/H2K5R/BuiltOfPub.lean). The built link's
number of slots is the plan's: `nsOf_all` (Johnson/Desc/First/Att/Door/Law/K5RestPublic.lean). The
message's mask code is the request's, and there is at least one answer: two clauses of the request's
own test `reqShapeOk` (OnBytes/Iop/Req.lean), which the program asks. WHAT THIS OVERTAKES: the heads
of Honest/K5/Law/ReaderReadsK5.lean ("hroom AT NO PLAN") and of Honest/K5/Law/ScriptQRaw.lean ("no
theorem that gives it at any plan is called") say of the room that it is shown nowhere: it is shown
here, under h. Kin in the library, not called here: `room_of_linksLaid` and `free_one`
(Johnson/Desc/Sound/Clamp/InsideOfPlan.lean): the like bound from the written protocol's own public
test, and the arithmetic of `room_of_free`.

Limits. Conditional. h is a hypothesis of every statement that names it. hQ is shown of no Script.
Below the plan's number of slots alone. Where `Thr` T has no member `readerReads_K5_h` says nothing.
At the library's full size and the format's second hash function alone; `room_of_built` is general in the
program's arguments.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReaderReadsK5
import Johnson.Desc.First.Att.K05PublicOfBuilt
import Johnson.Desc.Kinds.Law.LinksFitNs
import Johnson.H2K5R.BuiltOfPub
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Desc.First.Att.Door.Law.K5RestPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E OracleShape reqShapeOk reqOk)
open OnBytes.Model (Reading)
open OnBytes.Model.Stages (LinkH LinksH buildLinksH)
open OnBytes.Maker (WholeD)
open Johnson.Pack (pMask)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls keptAt messagesAt)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo masksUpTo_yes sentOfBuilt links_laid
  buildLinks_cut shapes_own shapes_any shapesCalls messages_of_built built_of_pub)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (linkLaid_ns)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT dataQ seatTab)
open H2K5.Door (nsOf_all)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

/-! ## 1 From the planning program's return -/

/-- **THE SLOTS AND ONE PLACE MORE HAVE ROOM.** CONDITIONAL: hb: the program returns B; X is its
link number l; k is the number of the message that holds that link's mask row. -/
theorem room_of_built {links0 : Array LinkH} {NGr : Nat} {p4 : Bool}
    {wsLay : OnBytes.Model.WsLay} {p : OnBytes.Params.First} {B : LinksH}
    (hb : buildLinksH links0 NGr p4 wsLay p = .ok B) {l : Nat} {X : LinkH}
    (hX : B.links[l]? = some X) (rad : OracleShape → Nat) {k : Nat}
    (hk : k < (sigListCalls (sentOfBuilt p B) rad l).length)
    (hm : maskMsg (sentOfBuilt p B) l = some k) :
    X.ns + 1 ≤ (pMask (sentOfBuilt p B).codes
      ((sigListCalls (sentOfBuilt p B) rad l).get ⟨k, hk⟩).1).ell := by
  obtain ⟨zk, hzk, hlaid⟩ := links_laid hb
  have r := linkLaid_ns (hlaid l X hX)
  obtain ⟨_, _, _, h8, _, _⟩ := buildLinks_cut hb
  have hs : reqShapeOk p.shape = true := by
    unfold reqOk at h8
    exact (Eq.mp (Bool.and_eq_true _ _) h8).1
  unfold reqShapeOk at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hans⟩, hall⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  have ha1 : 1 ≤ p.shape.answers := of_decide_eq_true hans
  unfold maskMsg at hm
  obtain ⟨mi, hf, rfl⟩ := Option.map_eq_some_iff.1 hm
  have ho : (shapesCalls (sentOfBuilt p B) l)[(keptAt (sentOfBuilt p B) l).length + mi]? =
      some ((sigListCalls (sentOfBuilt p B) rad l).get ⟨_, hk⟩).1 := by
    rw [← shapes_any (sentOfBuilt p B) rad l, List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  obtain ⟨msg, hmsg, e⟩ := shapes_own ho
  obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
  have e' : (messagesAt (sentOfBuilt p B) l)[mi] = msg :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hmsg)
  rw [e'] at hp
  obtain ⟨L, hL, hm'⟩ := messages_of_built hmsg
  have hLl := List.all_eq_true.1 hall (L, l) (List.mem_zipIdx_iff_getElem?.2 hL)
  simp only [Bool.and_eq_true] at hLl
  obtain ⟨_, hms⟩ := hLl
  have hc := List.all_eq_true.1 hms msg (List.mem_of_getElem? hm')
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  have hcode : msg.shape.maskCode = p.shape.maskCode := by
    rcases hc.1.2 with h0 | h0
    · rw [h0] at hp
      simp at hp
    · exact h0
  have hpm : (pMask (sentOfBuilt p B).codes msg.shape).ell = zk.ell := by
    unfold Johnson.Pack.pMask
    rw [hcode, Array.getD_eq_getD_getElem?]
    show ((p.codes.mask[p.shape.maskCode]?).getD default).ell = _
    rw [hzk]
    rfl
  rw [e, hpm]
  omega

/-! ## 2 Under the hypothesis on the public input -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE INEQUALITY AT THE HYPOTHESIS' LETTERS.** CONDITIONAL: under the hypothesis h; g is below
12; the group's plan; the place of the lookup on the calls; kM is the number of the message that
holds the mask row. -/
theorem room_at_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    a.ns + 1 ≤
      (pMask h.𝔇.sent.codes ((sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).get ⟨kM, hk⟩).1).ell := by
  obtain ⟨l₀, -, hb⟩ := built_of_pub h.laid.pub
  have hl : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  have hn : (Zp.p.built.links[2 * g + 1]?).map (fun l : LinkH => l.ns) = some a.ns :=
    nsOf_all h hg ea
  obtain ⟨X, hX, e⟩ := Option.map_eq_some_iff.1 hn
  have e2 : X.ns = a.ns := e
  have r := room_of_built hb (l := x₁.link) (X := X) (by rw [hl]; exact hX) h.𝔇.l3.rad hk hm
  rw [e2] at r
  exact r

/-- **`MaskRoom` IS NO PREMISE UNDER THE HYPOTHESIS.** CONDITIONAL: as `room_at_head`. -/
theorem maskRoom_at_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk a.ns 1 :=
  maskRoom_head h hg ea hx hm (room_at_head h hg ea hx hm)

/-- **THERE ARE SUCH LETTERS.** CONDITIONAL: under the hypothesis h; g is below 12. -/
theorem letters_head {g : Nat} (hg : g < 12) :
    ∃ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : Nat)
      (_ : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      PlanAt Zp g a ∧ lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ ∧
        maskMsg h.𝔇.sent x₁.link = some kM := by
  obtain ⟨_, a, _, Pl, _⟩ := k5_member h hg
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨-, kM, hk, hm, -, -⟩ := masksUpTo_yes (masks_head h hg Pl.plan hx).1 h.𝔇.l3.rad
  exact ⟨a, x₁, kM, hk, Pl, hx, hm⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **`ReaderReads` AT THE KIND's MEMBER, AT THE LETTERS AS THEY ARE LAID, WITHOUT `MaskRoom`.**
CONDITIONAL: every premise stands, by name, in the file's head. -/
theorem readerReads_K5_h {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g)) {d : Due} (rowOf : Cs d → Nat → E)
    (ownC : Coins Bk → Cs d)
    (hQ : ∀ k v (hd : List Fmt.Drawn) ν, Vd v → N ≤ hd.length → ν < a.ns →
      Q.msg (maskNo5 h x₁ kM hk) k v (hd.take (Q.fixedMsg (maskNo5 h x₁ kM hk))) true 0 ν =
        Reading.gl.val (rowOf (ownC k) ν)) :
    ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
      (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread (borderOf g)) segAt?
      (fun pt _ _ v ν =>
        (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask ν)
      Reading.gl.val (fun k _ _ ν => rowOf (ownC k) ν) (· < a.ns) :=
  readerReads_K5 h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg Pl hx
    (maskRoom_at_head h hg Pl.plan hx hm) hN rowOf ownC hQ

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.room_of_built
#print axioms ProofFile.Honest.K5.room_at_head
#print axioms ProofFile.Honest.K5.maskRoom_at_head
#print axioms ProofFile.Honest.K5.letters_head
#print axioms ProofFile.Honest.K5.readerReads_K5_h
