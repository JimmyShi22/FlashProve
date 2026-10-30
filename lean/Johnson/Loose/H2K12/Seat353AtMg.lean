-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Seat353AtMg.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST
CHAIN: ALL SIX FACTS that the first half of the fourth tie takes from "reached" (FactsK12,
H2K12/Promise354.lean) AT THE IOP AS WRITTEN IN LEAN, OPENED (IM.Open,
Johnson/IMR/SeatOpen.lean), and at the one head (P5J.AtMg, Johnson/P5J/AtMg.lean): of the
last code switch nothing is left as a premise. Statements and proofs: a joining.

Why a count. factsK12_of_reach (H2K12/SeedAt354.lean) takes the equation "the
group that the switch's numbers name is the table's number of the last group" as a closed premise.
The code switch's files have it under a test on the planner's sizes alone
(Johnson/Top/H0/Tw/K2C/GroupAtNums.lean, GroupAtScope.lean [not in this library]),
which the head does not hold. At an
accept it follows from a count: the quiet step in front of the switch pushes a group and names it by
the number of groups in front (finishFrontQ_fr, Johnson/Top/H0/Tw/K2C/FinFront.lean), the switch's
own decision tests that number against its own (FinIs.hGrp, Johnson/Top/H0/Tw/K2C/Closed.lean), and
in scope the statement in front of sub-protocol number 353 has just 25 groups (count_fin,
Johnson/IMR/FinCount.lean: from the fold's return alone).
Main names:
  grp_of_yes      at an accept at the place of the last code switch: the switch's group's number is
                  the number of groups in front.
  factsK12_of_count   factsK12_of_reach with a count along "reached" in the equation's place.
  seat353_open    in scope, where the IOP as written passes its tests on the list of rounds:
                  sub-protocol number 353 is there and sits at the place of the last code switch
                  (SeatF1, H2K12/GroupAt354.lean), by seatF1_open
                  (H2K12/SeatF1AtOpen.lean).
  count353_open   in scope: 25 groups at every state that is reached by 353 sub-protocols.
  factsK12_open   FactsK12 at the opened IOP. factsK12_at_head: at the head.
Limits. (1) A JOINING OVER LETTERS: FoldFacts (Johnson/Desc/First/FoldFacts.lean) at a condition Rch
that gives "reached", d.sent.codes = cs, and the two premises on the lists hM and hTie (see
H2K12/SeedAt354.lean's head) stay premises. (2) The full size alone: the numbers 353 and 25 are
written. (3) WHETHER ALL PREMISES CAN BE MET TOGETHER IS SHOWN NOWHERE HERE. No soundness statement.
Nothing on hiding.

-/
import Johnson.IMR.FinCount
import Johnson.IMR.MsgsBehind
import Johnson.Desc.Sound.PieceLaid
import Johnson.P5J.AtMg
import Johnson.Loose.H2K12.SeedAt354
import Johnson.Loose.H2K12.SeatF1AtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-- **At an accept at the place of the last code switch, the group that the switch's numbers name is
the number of groups of the statement in front**: the quiet step in front pushes a group and lays
its number into the finish's own frame; the switch's own decision tests that number against its own.
-/
theorem grp_of_yes (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') : p.grp = s.st.groups.size := by
  obtain ⟨t, t', rs', gs', h1, h2, -, -⟩ := finishPlace_cut p h
  obtain ⟨r₁, r₂, a, G, w, roots, -, F⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h2
  obtain ⟨a₁, G₁, ha₁, -, -, -, -, -, -, -, -, hg₁⟩ :=
    VerifiableInference.Desc.First.K2.finishFrontQ_fr h1
  obtain rfl : a₁ = a := by
    rw [F.hHere] at ha₁
    injection ha₁ with e
    exact e.symm
  exact F.hGrp.symm.trans hg₁

/-- **ALL SIX FACTS, WITH A COUNT ALONG "REACHED" IN THE PLACE OF THE EQUATION ON THE SWITCH's
NUMBERS.** -/
theorem factsK12_of_count {Cl P Str : Type} (bs : List (Block S Cl)) (start : P → S) (k : ℕ)
    (B : Block S Cl) (hB : bs[k]? = some B) (p : P2) (hK : SeatF1 B p)
    (N : VerifiableInference.Desc.First.Numbers) (n : ℕ)
    (hcount : ∀ z s, Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start k (z, s) →
      s.st.groups.size = N.groupAt n)
    (cs : OnBytes.Codes) (ms : List VerifiableInference.Desc.Sound.Mem)
    (d : VerifiableInference.Desc.First.FoldData) (hcs : d.sent.codes = cs)
    {reqW : P → Array UInt32} {links : List VerifiableInference.Desc.First.ModelPart}
    {ps : List VerifiableInference.Desc.Place}
    (Rch : ℕ → (P × S) × Str → Prop)
    (hR : ∀ j a, Rch j a → Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start j a.1)
    (hf : VerifiableInference.Desc.First.FoldFacts Rch (fun a => a.1) d reqW links ps)
    (hM : ∀ o x, ListedAt ms d.L.places o x → d.M[o]? = some (x.1.l.get x.2).1)
    (hTie : ∀ x ∈ ms, VerifiableInference.Desc.K1.Tie cs (x.1.l.get x.2).1)
    (a : (P × S) × Str) (hr : Rch (k + 1) a) (hm : a.1.2.failed = none) :
    FactsK12 d N n cs ms a.1.2 := by
  have h1 : Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start (k + 1) (a.1.1, a.1.2) :=
    hR _ a hr
  obtain ⟨s, b, h0, hb, hy⟩ := reach_last h1
  rw [List.getElem?_map, hB] at hb
  obtain rfl : VerifiableInference.Desc.Sound.below B = b := Option.some.inj hb
  obtain ⟨rs, gs, -, hd⟩ := seat_yes hK hy
  exact factsK12_of_reach bs start k B hB p hK N n
    ((grp_of_yes p hK.1 hd).trans (hcount _ _ h0)) cs ms d hcs Rch hR hf hM hTie a hr hm

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **SUB-PROTOCOL NUMBER 353 IS THERE AND SITS AT THE PLACE OF THE LAST CODE SWITCH.** -/
theorem seat353_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∃ b p, c.blocksInOrder[353]? = some b ∧ SeatF1 b p := by
  obtain ⟨k0, x, name, e0, -, -, -⟩ := Meaning.Carry.back_zero_at O
  have hb : c.blocksInOrder[353]? = some { k0 with planOk := k0.planOk && k0.hasNoClaimsAndNothingAfter } :=
    (IM.back_numbers hS hR O).1 0 k0 e0
  have hbl := (VerifiableInference.Desc.Sound.planOk_parts F hp).1
  have eF := O.desc
  subst eF
  have hbl' : VerifiableInference.Desc.blocksOk c.blocksInOrder = true := hbl
  have h1 := List.all_eq_true.1 hbl' _ (List.mem_of_getElem? hb)
  rw [Bool.and_eq_true] at h1
  obtain ⟨Pp, n, nm, a, -, -, hK, -⟩ := seatF1_open hS hR O hb h1.1
  exact ⟨_, _, hb, hK⟩

/-- **25 GROUPS AT EVERY STATE THAT IS REACHED BY 353 SUB-PROTOCOLS.** -/
theorem count353_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (z : ProofFile.InstPub) (s : S)
    (h : Reach 0 (c.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Z) 353 (z, s)) :
    s.st.groups.size = 25 := by
  obtain ⟨-, rs, cols, f⟩ := Reach.fold (Johnson.Desc.First.Walk.Tied.reach_raw h)
  exact Meaning.K2.count_fin hS hR O f

/-- **ALL SIX FACTS AT THE IOP AS WRITTEN IN LEAN, OPENED.** -/
theorem factsK12_open {Str : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    (N : VerifiableInference.Desc.First.Numbers) (hN : N.groupAt 25 = 25) (cs : OnBytes.Codes)
    (ms : List VerifiableInference.Desc.Sound.Mem) (d : VerifiableInference.Desc.First.FoldData)
    (hcs : d.sent.codes = cs) {reqW : ProofFile.InstPub → Array UInt32}
    {links : List VerifiableInference.Desc.First.ModelPart} {ps : List VerifiableInference.Desc.Place}
    (Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop)
    (hR' : ∀ j a, Rch j a →
      Reach 0 (c.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Z) j a.1)
    (hf : VerifiableInference.Desc.First.FoldFacts Rch (fun a => a.1) d reqW links ps)
    (hM : ∀ o x, ListedAt ms d.L.places o x → d.M[o]? = some (x.1.l.get x.2).1)
    (hTie : ∀ x ∈ ms, VerifiableInference.Desc.K1.Tie cs (x.1.l.get x.2).1)
    (a : (ProofFile.InstPub × S) × Str) (hr : Rch 354 a) (hm : a.1.2.failed = none) :
    FactsK12 d N 25 cs ms a.1.2 := by
  obtain ⟨b, p, hb, hK⟩ := seat353_open hS hR O hp
  exact factsK12_of_count c.blocksInOrder (ProofFile.startS Z) 353 b hb p hK N 25
    (fun z s h => (count353_open hS hR O z s h).trans hN.symm) cs ms d hcs Rch hR' hf hM hTie a hr
    hm

end

/-- **ALL SIX FACTS AT THE ONE HEAD.** -/
theorem factsK12_at_head {Str : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (cs : OnBytes.Codes)
    (ms : List VerifiableInference.Desc.Sound.Mem) (d : VerifiableInference.Desc.First.FoldData)
    (hcs : d.sent.codes = cs) {reqW : ProofFile.InstPub → Array UInt32}
    {links : List VerifiableInference.Desc.First.ModelPart} {ps : List VerifiableInference.Desc.Place}
    (Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop)
    (hR' : ∀ j a, Rch j a →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) j a.1)
    (hf : VerifiableInference.Desc.First.FoldFacts Rch (fun a => a.1) d reqW links ps)
    (hM : ∀ o x, ListedAt ms d.L.places o x → d.M[o]? = some (x.1.l.get x.2).1)
    (hTie : ∀ x ∈ ms, VerifiableInference.Desc.K1.Tie cs (x.1.l.get x.2).1)
    (a : (ProofFile.InstPub × S) × Str) (hr : Rch 354 a) (hm : a.1.2.failed = none) :
    FactsK12 d (P5J.At.N Zp cF) 25 cs ms a.1.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact factsK12_open h.scope h.reads O h.laid.planOk (P5J.At.N Zp cF) rfl cs ms d hcs Rch hR' hf
    hM hTie a hr hm

end H2K12

#print axioms H2K12.grp_of_yes
#print axioms H2K12.factsK12_of_count
#print axioms H2K12.seat353_open
#print axioms H2K12.count353_open
#print axioms H2K12.factsK12_open
#print axioms H2K12.factsK12_at_head
