-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/AttAtHead.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): in the world in which the table's sentence on the
forms of an attention segment's own runs evaluates them, at the state behind the lay
(`worldBehind`, Johnson/Desc/K5/Honest/Law/Own.lean), every table of the verifier's list is true
of the matrices read off the witness's data: the library's `AttAt`
(Johnson/Road/Rows/AttRead.lean).

It is `attAt_stated` (Johnson/Desc/K5/Honest/Law/Planes.lean) and `readsStated_behind`
(Johnson/Desc/K5/Honest/Law/FrameFacts.lean) at the head's letters: the facts on the state in front
come from `front_at_head`, the claims' reading's return from `runs_at_head`
(Johnson/Desc/K5/Honest/Law/DoorAtHead.lean); that the filling's letter St reads the array of the
tables as the stated function is the library's `hSt_of_arm`
(Johnson/Desc/First/Att/K05StatedArm.lean).

WHAT IT SAYS AND WHAT NOT. The sentence's world does not read the array of the tables off the
witness: it reads it THROUGH the letter St, as the stated function of the cells of the first
sending. So `AttAt` holds in that world whatever the witness's data are. That the array which the
honest side commits holds these entries is another matter and is not touched here: on it see
Johnson/Desc/K5/Honest/Law/U3Law.lean, U3Shape.lean and ReadsAfter.lean. What the witness's data do
decide here is WHICH matrices: the letter M of `AttAt` is read off them.

Main names:
  `matsAt_behind`: the matrices read off the data are the same at the state in front and behind.
  `stated_at_head`: the letter St reads the array as the stated function, behind the lay.
  `attAt_behind_at_head`: **`AttAt`**, at every return (i, K) of the claims' reading behind the lay;
    beside it: there is such a return, and K is the planned number of columns. (The runs' returns
    at the same reading are `runs_at_head`'s.)

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front is not shown here; nor that an attention segment is open there, nor that the
hearing of its own rounds returns with no round left over. At the function `OnBytes.secondHashFunction`, of
which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DoorAtHead
import Johnson.Desc.K5.Honest.Law.FrameFacts
import Johnson.Desc.First.Att.K05StatedArm
import Johnson.Desc.First.Att.K05PlanesWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (behind hear Heard partAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.K9L (Bound)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- The matrices read off the data are the same at the state in front of the lay and behind it. -/
theorem matsAt_behind (A : Attention.Plan) {s : S} {a : AttOwn} (e : s.here = .att a) (h : Heard)
    (G : Fork) (Dt : Bound GQ) : matsAt A (behind s a h G) Dt = matsAt A s Dt := by
  unfold matsAt
  rw [Att.P.link_front e]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The filling's letter St reads the array of the tables as the stated function, behind the
lay.** Conditional as `front_at_head`. -/
theorem stated_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) (hd : Heard) (G : Fork) :
    Att.P.StatedAtt h.𝔇.St a (K5Law.funsAt a) (behind s att hd G) := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  obtain ⟨_, _, _, Fa, _⟩ := front_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e
  obtain ⟨Lc, T⟩ := Fa.facts
  have eL : att.L = Lc := Option.some.inj ((Att.P.link_front e).symm.trans T.hL)
  have hfl : att.L.check.frame.link = x₁.link := by
    rw [eL]
    exact (Att.P.liveReqB_at T.hB1 T.hL).1.trans T.hlink
  exact Att.P.hSt_of_arm hA h.𝔇.uL h.𝔇.uH (behind s att hd G)
    { att with F := G, heard5 := some hd } rfl hfl

/-- **Every table of the verifier's list is true of the matrices read off the witness's data, in
the sentence's own world behind the lay.** Conditional as `runs_at_head`. rd: the reading of the
witness's messages; free. Handed out: the shape's return; a return (i₀, K₀) of the claims' reading
behind the lay; and, at EVERY return (i, K) of it: K is the planned number of columns, and `AttAt`
at every gL (of what the lookup returned the tables read nothing). -/
theorem attAt_behind_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
    (hh : hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) (rd : ℕ × ℕ → MsgQ) :
    ∃ (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape),
      Attention.shapeHid lid cf = .ok (a.S, fs) ∧
      (∃ i₀ K₀, Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (behind s att hd G) =
        some (i₀, K₀)) ∧
      ∀ i K, Att.P.inOf (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (behind s att hd G) =
          some (i, K) →
        K = Att.P.plannedK a ∧
        ∀ gL : Forest.Heard, AttAt Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd G rd) a.seam.tl K
          (matsAt a (behind s att hd G)
            (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (partAt s att G none) rd))
          (K5Law.oldOf a.S gL i) lid cf fs := by
  obtain ⟨_, _, _, Fa, _⟩ := front_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e
  obtain ⟨i₀, K₀, _, _, _, _, _, _, hin₀, _⟩ :=
    runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  obtain ⟨lid, cf, hs⟩ := K5Law.ofPlan_shape (ofPlan_all h ea)
  have hSt := stated_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hd G
  obtain ⟨hUG, _, _⟩ := frame_of_front Fa e hh
  refine ⟨lid, cf, _, hs, ⟨i₀, K₀, hin₀⟩, fun i K hin => ?_⟩
  obtain rfl : K = Att.P.plannedK a :=
    Att.P.width_of_inOf a (a₀ := { att with F := G, heard5 := some hd }) rfl hUG hin
  refine ⟨rfl, fun gL => ?_⟩
  obtain ⟨b, hW⟩ := readsStated_behind Fa e hh hSt []
    (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (partAt s att G none) rd)
  exact attAt_stated a hin hs (K5Law.ofPlan_matsFit (ofPlan_all h ea)) gL hW

end

end H2K5.Honest

#print axioms H2K5.Honest.matsAt_behind
#print axioms H2K5.Honest.stated_at_head
#print axioms H2K5.Honest.attAt_behind_at_head
