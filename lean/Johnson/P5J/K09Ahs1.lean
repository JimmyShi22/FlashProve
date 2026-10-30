-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09Ahs1.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE FIELD Ahs1 OF WHAT
IS LEFT OF A LINK (Johnson/Desc/First/Link/Law/LinkRest.lean): BEHIND THE BATCHING's SUB-PROTOCOL
KIND K9's LENS FINDS A PART: to the field's letter, at all 25 links. Two closed facts by Lean's
kernel and one theorem. A law file; no running text imports it.
  `standsNextB`, `stands_next`   BY THE KERNEL: the place behind the batching's stands in link m,
                    and that link's sort is the head's just at m = 24.
  `batch_head_full`   BY THE KERNEL: the head's batching has the number 347.
  `ahs1_at`           (h : AtMgA secondHashFunction …) (hm : m < 25) (St : h.Sits m L p Q b₃ b₅) (share :
LinkShare L p) (z) : ∀ b, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s => (z, s)) (RchAt
h.toAtMg.rch z) (batchAt fullLinks At.ps m + 1) b → (atS.get? b.1).isSome = true. HOW. At the 24
links that are not the head's: from the promise's book-keeping alone (part_of_onTR). At the head's:
the lens wants the number of slots taken, which the merge lays (number 346): it is there at every
state reached at 347 (used_at_347, Johnson/LPFE1R/PartAtBatch.lean), and a yes of the batching's
sub-protocol keeps it there (used_behind_batch, Johnson/Desc/First/Link/Law/UsedStays.lean);
"reached at 348" is such a yes behind a state reached at 347.

Limits. St and share are premises (St: sits_at gives such letters at every link; share: the sorts'
laws). At OnBytes.secondHashFunction. No member. Nothing on soundness or on hiding.

-/
import Johnson.P5J.K09List
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.UsedStays
import Johnson.LPFE1R.PartAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart standAt Stand)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS usedOf Where)
open VerifiableInference.Desc.LinkJoin (batchAt onTR LinkShare part_of_onTR part_of_onTR_head
  used_behind_batch used_at_347 usedSome)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- A closed test on the written lists: the place behind the batching's. -/
def standsNextB (m : ℕ) : Bool :=
  (At.ps[batchAt fullLinks At.ps m + 1]?).any fun p =>
    (fullLinks[m]?).any fun sub => decide (standAt fullLinks p = .link sub) &&
      (decide (sub = .head) == decide (m = 24))

set_option maxRecDepth 1000000 in
theorem stands_next : (List.range 25).all standsNextB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem batch_head_full : batchAt fullLinks At.ps 24 = 347 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **The field Ahs1, at all 25 links.** -/
theorem ahs1_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25)
    {L : Link S ProofFile.Cl} {p : Where} {Q : VerifiableInference.Desc.First.Close.Par}
    {b₃ b₅ : Block S ProofFile.Cl} (St : h.Sits m L p Q b₃ b₅) (share : LinkShare L p)
    (z : ProofFile.InstPub) :
    ∀ b, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m + 1) b → (atS.get? b.1).isSome = true := by
  intro b hb
  have hB := List.all_eq_true.1 stands_next m (List.mem_range.2 hm)
  unfold standsNextB at hB
  cases hp : At.ps[batchAt fullLinks At.ps m + 1]? with
  | none =>
    rw [hp] at hB
    cases hB
  | some pl =>
    rw [hp] at hB
    cases hs : fullLinks[m]? with
    | none =>
      rw [hs] at hB
      cases hB
    | some sub =>
      rw [hs] at hB
      simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        decide_eq_decide] at hB
      by_cases h24 : m = 24
      · obtain rfl : sub = .head := hB.2.2 h24
        subst h24
        refine part_of_onTR_head hp hB.1 hb ?_
        obtain ⟨Bs, base, O⟩ := h.laid.opened
        have hr := list_rchIs h z _ _ hb.2
        obtain ⟨s1, y⟩ := b
        cases hr with
        | @succ _ z' s s' b0 hr0 hbk hy =>
          obtain ⟨R, cs, _, e⟩ := hy
          obtain rfl : L.batchB = b0 := Option.some.inj (St.atK.symm.trans hbk)
          have hu := used_behind_batch L p St.drawB share.stand 0 s R cs _ cs.length e
          have h347 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (_, s) := batch_head_full ▸ hr0
          exact hu.trans (used_at_347 h.scope h.reads O h347)
      · exact part_of_onTR hp hB.1 (fun e => h24 (hB.2.1 e)) hb

end P5J

#print axioms P5J.stands_next
#print axioms P5J.batch_head_full
#print axioms P5J.ahs1_at
