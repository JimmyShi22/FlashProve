-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinAtHead.lean: CONDITIONAL: the sentence "the form that the run "join"
gathers is worth 0" (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean) at the verifier's state just behind
the lay of an attention segment's own rounds, in the closed filling's own letters, under the
hypothesis `P5J.AtMgA` that ties the library's letters to the proof file's description, the other
premises of `runs_at_head`, and h0, which is the sentence's own clause on values. A joining:
`join_of_runs` (Johnson/Desc/K5/Honest/Law/Join.lean) called with what
Johnson/Desc/K5/Honest/Law/DoorAtHead.lean shows at these letters. No algebra is in this file.

Main name:
  `join_at_head`: under the premises of `runs_at_head`, and h0: whatever form the lookup's text
    returns on the segment's key forms at the state behind the lay is worth 0 in the sentence's
    world: the sentence holds at every run that the table's item "join" names.

Limits. The hypothesis is not shown here; nor that a state is reached, bears no mark and meets the
promise; `Open8` is asked at the caller's own list Q, and that the eight are open at the table's own
list is not decided here. h0 holds the sentence's clause on values under another name: the four
other clauses (the open segment's part is there; the reader returns; the late slots pass; each form
passes the public test) are what this file adds. That h0 can be met is not shown here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.DoorAtHead
import Johnson.Desc.K5.Honest.Law.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The sentence on the form that the run "join" gathers, in the closed filling's own letters.**
CONDITIONAL as `runs_at_head`, and h0: whatever form the lookup's text returns on the key forms at
the state behind the lay is worth 0 in the sentence's world. St, rd: letters. -/
theorem join_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {rs : List Fmt.RoundView} {hd : Att.P.Heard} {G : Fork}
    (hh : Att.P.hear a.own (att.F, rs, 0) = some (hd, G, [], 0)) (St : Stated)
    (rd : ℕ × ℕ → MsgQ)
    (h0 : ∀ (gL : Forest.Heard) (kf : Array Aff) (z : Aff × Fork × OnBytes.K.Kc.Tape),
      att.lookHeard = some gL →
      Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf a)) (Att.P.parCOf a) (Att.P.behind s att hd G) =
        some kf →
      Look.joinF gL kf G [] = some z →
      z.1.value Reading.gl (worldBehind St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd G rd) = 0) :
    ∀ p ∈ h.𝔇.pubD.runs (2 * g + 1) 2 "join",
      formsTQ (h.𝔇.pubD.Rd (2 * g + 1)) St (h.𝔇.pubD.N.sent (2 * g + 1) 0) p.1 p.2
        (Att.P.behind s att hd G) rd := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hb⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hb
  have pOk := planOk_plus (beforeAll Zp g) hb hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hb hok ea
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  have hRd := rds_plus h.𝔇.pubD g a _ Lk (hRd_plus (rdIs_all h) hLk) ProofFile.sameReply
    (statesAt_all h hg ea hLk) sameOut_all
  have gf := Att.P.geoFits_at_seat (planIs_all h) ea
    (okAll_plus (P5J.At.X Zp) g (beforeAll Zp g) a h.𝔇.sent h.𝔇.l3.rad (planIs_all h) h4 ea hG pOk
      cOk)
  obtain ⟨_, _, _, _, U, _, hz⟩ := front_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e
  have U' : Att.P.U3There (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att (Att.P.parCOf a) := by
    have := U
    unfold ownAt at this
    rwa [hxl] at this
  have Rt := runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh
  have H := join_of_runs (h.𝔇.pubD.Rd (2 * g + 1)) St a (h.𝔇.pubD.N.sent (2 * g + 1) 0)
    (fun name R hn hR => hRd name _ R hn hR) hh hz Rt gf U' rd h0
  intro p hp
  rw [runsJ_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg)] at hp
  obtain rfl : p = (2, "join") := List.mem_singleton.1 hp
  exact H

end

end H2K5.Honest

#print axioms H2K5.Honest.join_at_head
