-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksFit.lean: CONDITIONAL: WHAT THE SILENCE OF THE TWO MARKS
AT THE OWN ROUNDS OF AN ATTENTION SEGMENT GIVES (`mkReads`, MarkReads.lean; `mkLive`, MarkLive.lean
beside this file), WITH ONE PREMISE ON THE LIST OF CHALLENGES IN THE STEAD OF THREE: `drawsFit` at
the member's declared rounds (Johnson/Desc/ProofFile/Honest/Frame.lean): the test that stands under
every sentence "at every list of challenges" over the frame.

Why. Two laws take: the list has all the listed rounds (hlen, once for each mark); and, for
the second mark, what the rounds of the further variables drew is not 0 (`BetaNz`). All three follow
from `drawsFit`: the two lists have one length, each listed number has a declared round, and at a
round whose entry counts its element as never 0 the test refuses 0.

Main names:
  `live_len_of_fit`, `reads_len_of_fit`: hlen for the two lists.
  `mkLive_held_fit`, `mkReads_liveV_fit`: **the two laws, so.**

Limits. As those two laws'. p: any parameters of the kind whose structure of rounds is the plan's
(ep): that the member's own declared rounds are `rounds` p at p := `parAt` is `rounds_at_head`
(MarksOwn.lean beside this file), not drawn here. Nothing on how often `drawsFit` holds. No sentence
on a measure stands here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkLive
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkReadsVal
import Johnson.Desc.ProofFile.Honest.K5.Law.BetaFit
import Johnson.Desc.K5.Honest.Law.LiveEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (liveRounds readRounds live_entry read_round_plan Chal Reads HeldLive Live2V
  public_at_head)
open P5J (AtMgA TS)

/-- Each round of the second mark's list is below the list's length. Conditional: hf. -/
theorem live_len_of_fit (p : Att.P.Par) {own : List Fmt.Drawn}
    (hf : drawsFit (Att.P.rounds p) own = true) : ∀ n ∈ liveRounds p.own, n < own.length := by
  intro n hn
  obtain ⟨e, he, _, _⟩ := live_entry p.own n hn
  refine len_of_fit p hf (n := n) (d := { entry := if e.drawE == 0 then e else
    { e with work := p.work } }) ?_
  unfold Att.P.rounds
  rw [List.getElem?_map, he]
  rfl

/-- Each round of the first mark's list is below the list's length. S: the segment's shape.
Conditional: H, Pl: two structures of facts on public numbers; hf. -/
theorem reads_len_of_fit (p : Att.P.Par) (S' : OnBytes.Attention.Shape)
    (H : H2K5.Honest.Sized ⟨S', p.own⟩) (Pl : H2K5.Honest.Planned ⟨S', p.own⟩)
    {own : List Fmt.Drawn} (hf : drawsFit (Att.P.rounds p) own = true) :
    ∀ n ∈ readRounds p.own (H2K5.Honest.Pub5.g ⟨S', p.own⟩), n < own.length :=
  fun n hn => len_of_fit p hf (read_round_plan p S' H Pl n hn)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **WHAT THE SECOND MARK's SILENCE GIVES, UNDER THE TEST ON THE LIST OF CHALLENGES.** Conditional:
as `mkLive_held`, with p, ep (its structure of rounds is the plan's) and hf (the list is one that
the declared rounds can draw) in the stead of hlen and hb. -/
theorem mkLive_held_fit {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) {att : AttOwn} (e4 : s4.here = .att att)
    (hz : OnBytes.Model.Road.Sized att.F) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4) (p : Att.P.Par) (ep : p.own = a.own)
    (hf : drawsFit (Att.P.rounds p) own = true)
    (hs : (mkLive (2 * g + 1) a.own).test fr own = none) : HeldLive a.own att.F.next s9 :=
  mkLive_held h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 e4 hz zk hc
    (ep ▸ live_len_of_fit p hf) hs (ep ▸ betaNz_of_fit p zk hf)

/-- **WHAT THE FIRST MARK's SILENCE GIVES, AT VALUES, UNDER THE TEST ON THE LIST OF CHALLENGES.**
Conditional: as `mkReads_liveV`, with p, ep and hf in the stead of hlen. -/
theorem mkReads_liveV_fit {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4) (p : Att.P.Par) (ep : p.own = a.own)
    (hf : drawsFit (Att.P.rounds p) own = true)
    (hs : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test fr own = none) :
    Live2V (Att.P.parCOf a).geo a.mats s9 := by
  have Pu := public_at_head h hg ea
  refine mkReads_liveV h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 zk hc ?_ hs
  have H : H2K5.Honest.Sized ⟨a.S, p.own⟩ := by rw [ep]; exact Pu.sized
  have Pl : H2K5.Honest.Planned ⟨a.S, p.own⟩ := by rw [ep]; exact Pu.planned
  have k := reads_len_of_fit p a.S H Pl hf
  rw [ep] at k
  exact k

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.live_len_of_fit
#print axioms ProofFile.Honest.K5.reads_len_of_fit
#print axioms ProofFile.Honest.K5.mkLive_held_fit
#print axioms ProofFile.Honest.K5.mkReads_liveV_fit
