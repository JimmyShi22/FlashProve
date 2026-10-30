-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K2AtHead.lean: what an accepting step of the code switch (K2)
gives, under the library's hypothesis `AtMgA`, at 24 of the kind's 25 numbers in the first chain:
the first places of segments 1 to 23, and number 353 after the last segment. The clause is `K2Keeps`
(Johnson/Desc/K2/Honest/KeepsAt.lean) of the authors of K2's lemmas. It reads of its parameter only
the field `stands`, so the lemmas here give it at some parameter with the right `stands`. Which
sub-protocol stands at these numbers, and with which `stands`, is the library's `P1K2.k02_sits_pAt`
(Johnson/Top/H0/K2Caller/SitsAtP.lean). Its two conditions on the public part are theorems under
`AtMgA`: `H2K12.spots_atAll` with `cut_of_head`, and `P1K2.links25_atAll`. No definition.

  1  `k2_link_head`   at number `14 * l + 0 + 2` for `l` from 1 to 23: there is a state between;
     `K2Keeps` holds up to it at a parameter that stands at a segment's first place; from it the
     segment's own "opened" returns the state after the step, which bears no mark
  2  `k2_finish_head`   at number 353: `K2Keeps` at a parameter that stands after the last segment

Limits.
  * Number 339, the code switch in the output head's segment, is not treated.
  * That a `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.K2.Honest.KeepsAt
import Johnson.Top.H0.K2Caller.SitsAtP
import Johnson.P1K2R.SitsDoor
import Johnson.P1K2R.SitsNoMark
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.Top.H0.Opts.Links25AtHead
import Johnson.Road.K4.K4HeadWritten
import Johnson.IMR.BackSeat
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.K2.Honest (K2Keeps k2Keeps_link k2Keeps_finish)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)
open Johnson.Desc.First.Walk.Seat (framesOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At the first place of segment `l`, for `l` from 1 to 23. -/
theorem k2_link_head {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∀ blk, cF.blocksInOrder[14 * l + 0 + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      ∃ (m : TS) (q : P2) (fs : _) (f : _), q.stands = .link ∧ K2Keeps q s m ∧
        framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs ∧ fs[l]? = some f ∧
        f.opened m = .ok s' ∧ s'.failed = none := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', Bs', base', c', A', B', O', H⟩ :=
    P1K2.k02_sits_pAt h.scope h.reads h.laid.value
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  obtain ⟨a1, -, -⟩ := H (H2K12.spots_atAll h (OnBytes.Road.K4.cut_of_head h.toAtMg))
    (P1K2.links25_atAll h)
  obtain ⟨b, hb', hX⟩ := a1 l h1 h24
  obtain rfl : b = blk := Option.some.inj (hb'.symm.trans hb)
  obtain ⟨hst, fs, f, hfs, hf, hS⟩ :=
    hX (P1K2.flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
  obtain ⟨R, c, hlen, e⟩ := hy
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step 0 s s' R c c.length e
  obtain rfl : s = t := Except.ok.inj e1
  exact ⟨t', _, fs, f, hst, k2Keeps_link hst ⟨R, c, by rw [← hS.rounds]; exact hlen, e2⟩, hfs, hf,
    P1K2.leaveOpened_is e3, P1K2.leaveOpened_unmarked e3⟩

/-- At number 353, after the last segment. -/
theorem k2_finish_head :
    ∀ blk, cF.blocksInOrder[353]? = some blk → ∀ s s', StepYes 0 blk s s' →
      ∃ q : P2, q.stands = .finish ∧ K2Keeps q s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, q, e0, hq, hU⟩ := IM.k2_finish_under O
  obtain ⟨b₂, y, e0', -, -, hla, -⟩ := IM.k2_finish_of O
  obtain rfl : b₂ = b := Option.some.inj (e0'.symm.trans e0)
  obtain ⟨hfr, h352⟩ := IM.links_flat_352 h.scope h.reads O
  have hf := IM.back_at_flat e0
  rw [hfr, h352] at hf
  have hf' : cF.blocksInOrder[353]? = some { b₂ with planOk := b₂.planOk && b₂.hasNoClaimsAndNothingAfter } := hf
  obtain rfl := Option.some.inj (hf'.symm.trans hb)
  exact ⟨q, hq, k2Keeps_finish hq
    (fun s rs gs t d => ⟨hU s rs gs t d, (IM.alone_noMark hla d).2⟩) hy⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k2_link_head
#print axioms ProofFile.Honest.FirstThread.k2_finish_head
