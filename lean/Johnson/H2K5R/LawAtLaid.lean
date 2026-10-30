-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/LawAtLaid.lean: THE JOINT BETWEEN THE VALUE THAT
verify() LAYS (LPFD.Full.proofDataAndDecisionOfPublicFiles, Johnson/Desc/Laid/ProofFull.lean) AND KIND K5's LAWS AT THE KIND's
OWN BLOCK: every fact on public data that these laws take as a premise, at every attention segment,
from that value's return and nothing else.

Why. The rule of composition takes, at an entry of the description's flat list, (1) the entry, (2)
that it is the kind's block as the seat lays it, alone (IM.LaidAlone), and (3) the kind's laws at
that block. The kind's laws at k5AtN's block take eight facts on public data as premises. Here these
eight, with (1) and (2), are handed out by name; nothing is swallowed in a proof.

W below: the public parameters, that is the plan derived from the three public files, as the seat
holds it: what publicOfO o returns.

OVER WHAT IT STANDS: all that Johnson/H2K5R/LawAtEntry.lean's head names, and
Johnson/Desc/Laid/: the door ProofAsks.lean with K5's seven rows;
ProofAsksLaw.lean; ProofFullLaw.lean.

Main names:
  `guard_of_asks`: where every test of the door says yes and publicOfO o returns W, the guard says
    yes at every attention segment of W. From asks_guard (ProofAsksLaw.lean: the seven rows by
    name), rowsO_at (Johnson/Desc/First/Att/GuardAtSeat.lean) and the walk's membership.
  `laid_opens`: **one opening on top**: where proofDataAndDecisionOfPublicFiles o pol lay KL returns (D, r): the description F
    that onlineDescription o returns, its test on the plan, its data D, its run r, the door's yes, and an
    opening of F (IM.Open: its field desc is the equation for F). A caller opens once, here, and
    spends every theorem "…_of_open" of K5's files at the same letters.
  `K05_facts_of_open`: **from an opening, F.planOk and the door's yes**: publicOfO o returns W;
    PlanIs W; and at every entry E of the first chain's flat list that bears the kind K5 there are
    g, blk, a, x with: the proof covers attention; g is below the number of groups; E stands at the
    number IM.flatIx c (2 g + 1) 2; the tie LaidAlone between E and the lot's block; k5AtN … = some
    blk; "before" can be made (so the default in "getD []" does not fire); blk.planOk; the guard's
    yes; the group's plan a; the place x of the segment's lookup, which bears the link's number. The
    profile and the group are handed out (k5_only), not asked.
  `K05_facts_at_entry`: the same from proofDataAndDecisionOfPublicFiles's return (two lines). `K05_facts_at_laid`: the elder
    form, group by group, under "the proof covers attention".
The lot's block is blk with one more conjunct in its test on the plan (IM.k5Dress). A law that reads
of a block its rounds and its decision alone holds of the one where it holds of the other. EMPTY
wherever proofDataAndDecisionOfPublicFiles refuses; where no entry bears K5 nothing is said. That proofDataAndDecisionOfPublicFiles returns at the
goals' full-size files with twelve attention links is evaluated, not proved.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.LawAtEntry
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.First.Att.GuardAtSeat
import Johnson.Desc.First.Att.LookLinkAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.PlanWritten (publicOfO)

/-- **The door's yes is the guard's yes**, at every attention segment of the public parameters that
publicOfO o returns. -/
theorem guard_of_asks {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {D : OnBytes.Maker.WholeD} {W : Verify.Public}
    (h : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true)
    (hW : publicOfO o pol KL (some lay) = .ok W) (h4 : W.p4 = true) {g : ℕ} (hg : g < W.NGr) :
    k5GuardN W (2 * g + 1) g = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := LPFD.asks_guard h
  refine rowsO_at a1 a2 a3 a4 a5 a6 a7 hW (2 * g + 1, g) ?_
  unfold attLinksN
  rw [if_pos h4]
  exact List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩

/-- **THE JOINT: WHAT THE VALUE's RETURN GIVES OF PUBLIC DATA AT EVERY ATTENTION SEGMENT**, each
fact under
its own clause, so that a law at the kind's own block can be called at these letters. -/
theorem K05_facts_at_laid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B, ProofFile.onlineDescription o pol lay KL = .ok F ∧ F.planOk = true ∧
      F.data "proof file" = .ok D ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      IM.Open o pol lay KL F Z Bs base₀ c A B ∧
      publicOfO o pol KL (some lay) = .ok Bs.G₀.W ∧ PlanIs Bs.G₀.W ∧
      (Bs.G₀.W.p4 = true → ∀ g < Bs.G₀.W.NGr,
        ∃ (b blk : Block First.S Claim) (a : Attention.Plan)
          (x : VerifiableInference.Desc.First.Look.Place),
        c.blocksInOrder[IM.flatIx c (2 * g + 1) 2]? = some b ∧
        IM.LaidAlone ProofFile.sameReply b (IM.k5Dress Z ("A" ++ toString g) blk) b.name
          ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk ∧
        (H2K5.k5Before? Z ("A" ++ toString g)).isSome = true ∧
        blk.planOk = true ∧ k5GuardN Bs.G₀.W (2 * g + 1) g = true ∧ Bs.G₀.W.A[g]? = some a ∧
        lookAt Bs.G₀.W (2 * g + 1) false = some x ∧ x.link = 2 * g + 1) := by
  obtain ⟨F, hF, hpl, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok h
  obtain ⟨Z, Bs, base₀, c, A, B, O, -, hX, H, -⟩ := K05_sits hF
  have hP := planIs_publicO hX
  refine ⟨F, Z, Bs, base₀, c, A, B, hF, hpl, hD, hr, O, hX, hP, fun h4 g hg => ?_⟩
  obtain ⟨Lk, b, blk, e1, e2, hat, hla⟩ := H h4 g hg
  obtain ⟨a, ea, -⟩ := k5AtN_is _ _ _ _ _ hat
  have hfl := IM.hear_at_flat e1 e2
  have hokb : b.planOk = true := by
    have hd := O.desc
    subst hd
    exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hpl).1 b (List.mem_of_getElem? hfl)
  have e : (blk.planOk && (H2K5.k5Before? Z ("A" ++ toString g)).isSome) = true :=
    (IM.alone_planOk hla).symm.trans hokb
  obtain ⟨hok, hbf⟩ := Bool.and_eq_true_iff.1 e
  have hG := guard_of_asks hs hX h4 hg
  obtain ⟨x, -, hx, -, -⟩ := guard_binds hP ea hG
  exact ⟨b, blk, a, x, hfl, hla, hat, hbf, hok, hG, ea, hx, lookAt_att_link h4 ea hx⟩

/-- **ONE OPENING ON TOP**: what the value's return gives, with an opening of the description. -/
theorem laid_opens {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B, ProofFile.onlineDescription o pol lay KL = .ok F ∧ F.planOk = true ∧
      F.data "proof file" = .ok D ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      (∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true) ∧
      IM.Open o pol lay KL F Z Bs base₀ c A B := by
  obtain ⟨F, hF, hpl, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok h
  obtain ⟨Z, Bs, base₀, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨F, Z, Bs, base₀, c, A, B, hF, hpl, hD, hr, hs, O⟩

/-- **THE JOINT, FROM AN OPENING**: at every entry of the first chain that bears the kind K5. -/
theorem K05_facts_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : OnBytes.Maker.WholeD} (hs : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    publicOfO o pol KL (some lay) = .ok Bs.G₀.W ∧ PlanIs Bs.G₀.W ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K5 →
        ∃ (g : ℕ) (blk : Block First.S Claim) (a : Attention.Plan)
          (x : VerifiableInference.Desc.First.Look.Place),
        Bs.G₀.W.p4 = true ∧ g < Bs.G₀.W.NGr ∧ c.blocksInOrder[IM.flatIx c (2 * g + 1) 2]? = some E ∧
        IM.LaidAlone ProofFile.sameReply E (IM.k5Dress Z ("A" ++ toString g) blk) E.name
          ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk ∧
        (H2K5.k5Before? Z ("A" ++ toString g)).isSome = true ∧
        blk.planOk = true ∧ k5GuardN Bs.G₀.W (2 * g + 1) g = true ∧ Bs.G₀.W.A[g]? = some a ∧
        lookAt Bs.G₀.W (2 * g + 1) false = some x ∧ x.link = 2 * g + 1 := by
  have hX := (IM.ground_public O.pub O.blank).1
  have hP := planIs_publicO hX
  refine ⟨hX, hP, fun E hE hK => ?_⟩
  obtain ⟨h4, g, hg, Lk, l1, l2⟩ := k5_only O hE hK
  obtain ⟨Lk', b, blk, e1, e2, hat, hla⟩ := k5_alone O h4 hg
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans l1)
  obtain rfl : b = E := Option.some.inj (e2.symm.trans l2)
  obtain ⟨a, ea, -⟩ := k5AtN_is _ _ _ _ _ hat
  have hokb : b.planOk = true := by
    have hd := O.desc
    subst hd
    exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hpl).1 b hE
  have e : (blk.planOk && (H2K5.k5Before? Z ("A" ++ toString g)).isSome) = true :=
    (IM.alone_planOk hla).symm.trans hokb
  obtain ⟨hok, hbf⟩ := Bool.and_eq_true_iff.1 e
  have hG := guard_of_asks hs hX h4 hg
  obtain ⟨x, -, hx, -, -⟩ := guard_binds hP ea hG
  exact ⟨g, blk, a, x, h4, hg, IM.hear_at_flat e1 e2, hla, hat, hbf, hok, hG, ea, hx,
    lookAt_att_link h4 ea hx⟩

/-- **THE JOINT AT THE ENTRY**: at every entry of the first chain that bears the kind K5, whatever
the
profile and the number of groups: that the proof covers attention is handed out, not asked. -/
theorem K05_facts_at_entry {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B, ProofFile.onlineDescription o pol lay KL = .ok F ∧ F.planOk = true ∧
      F.data "proof file" = .ok D ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      IM.Open o pol lay KL F Z Bs base₀ c A B ∧
      publicOfO o pol KL (some lay) = .ok Bs.G₀.W ∧ PlanIs Bs.G₀.W ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K5 →
        ∃ (g : ℕ) (blk : Block First.S Claim) (a : Attention.Plan)
          (x : VerifiableInference.Desc.First.Look.Place),
        Bs.G₀.W.p4 = true ∧ g < Bs.G₀.W.NGr ∧ c.blocksInOrder[IM.flatIx c (2 * g + 1) 2]? = some E ∧
        IM.LaidAlone ProofFile.sameReply E (IM.k5Dress Z ("A" ++ toString g) blk) E.name
          ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
        k5AtN Bs.G₀.W (2 * g + 1) g ((H2K5.k5Before? Z ("A" ++ toString g)).getD []) = some blk ∧
        (H2K5.k5Before? Z ("A" ++ toString g)).isSome = true ∧
        blk.planOk = true ∧ k5GuardN Bs.G₀.W (2 * g + 1) g = true ∧ Bs.G₀.W.A[g]? = some a ∧
        lookAt Bs.G₀.W (2 * g + 1) false = some x ∧ x.link = 2 * g + 1 := by
  obtain ⟨F, Z, Bs, base₀, c, A, B, hF, hpl, hD, hr, hs, O⟩ := laid_opens h
  obtain ⟨hX, hP, H⟩ := K05_facts_of_open O hpl hs
  exact ⟨F, Z, Bs, base₀, c, A, B, hF, hpl, hD, hr, O, hX, hP, H⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.guard_of_asks
#print axioms VerifiableInference.Desc.First.Att.P.K05_facts_at_laid
#print axioms VerifiableInference.Desc.First.Att.P.laid_opens
#print axioms VerifiableInference.Desc.First.Att.P.K05_facts_of_open
#print axioms VerifiableInference.Desc.First.Att.P.K05_facts_at_entry
