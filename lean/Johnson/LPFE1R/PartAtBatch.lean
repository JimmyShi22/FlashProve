-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/PartAtBatch.lean: "K9's PART IS THERE" AT EVERY STATE OF THE
TABLE's OWN CONDITION IN FRONT OF A LINK's BATCHING, AT ALL 25 LINKS OF THE WRITTEN LIST, IN THE
LETTERS OF AN OPENED SEAT (`IM.Open`). Theorems. A law file; no running text
imports it.
  `merge_lays_slot`   a yes of the merge's decision (headMergeDecide,
                    Johnson/Desc/First/Fork/MergeKind.lean) leaves a state at which usedOf answers:
                    the head's part is open and its slot is laid, in that one write.
  `used_at_347`     in scope, at secondHashFunction: at every state that is reached at number 347 of the first
                    chain's flat list (the head's batching's) usedOf answers: THE MERGE's
                    SUB-PROTOCOL STANDS AT NUMBER 346, RIGHT IN FRONT: no walk. CALLED:
                    IM.k11_of · IM.k11_yes (Johnson/IMR/K11Seat.lean) ·
                    IM.hear_at_flat · IM.flatIx_scope (FlatIx.lean, FlatScope.lean).
  `standsB`, `stands_W`   a closed test on the written lists, by the kernel: at each m < 25 the
                    place at batchAt is there, and the table asks there an open segment of link m's
                    sort; the head's batching's number is 347.
  `part_at_batch_all`   m < 25 · onTR N Mg IM.linksW IM.placesW (fun s => (z, s)) Rz (batchAt
                    IM.linksW IM.placesW m) a · "Rz gives Reach over c.blocksInOrder" ⊢ (atS.get? a.1).isSome
                    = true. AT THE 24 LINKS THAT ARE NOT THE HEAD's: FROM THE PROMISE's BOOK-KEEPING
                    ALONE (PartOfPromise.lean); "reached" is spent at the head's alone.

Limits. In scope, at secondHashFunction. No member: that a state is reached there is shown of no proof. Of the
batching's book-keeping k9OnA this is the first of eight sentences; the seven others are not
treated. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.PartOfPromise
import Johnson.Desc.First.Link.Law.K9KindTiedR
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.WrittenList
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K9 (atS usedOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning standAt Stand)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- A yes of the merge's decision lays the slot. -/
theorem merge_lays_slot {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') : (usedOf s').isSome = true := by
  unfold headMergeDecide at h
  split at h
  · rename_i a ha
    obtain ⟨_, ho, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨t, _, h⟩ := K9L.ok_bind h
    obtain ⟨claim, _, h⟩ := K9L.ok_bind h
    obtain ⟨x, _, h⟩ := K9L.ok_bind h
    obtain ⟨⟨wo, F, t'⟩, _, h⟩ := K9L.ok_bind h
    dsimp only at h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    obtain ⟨_, _, h⟩ := K9L.ok_bind h
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain rfl := Except.ok.inj h
    simp [usedOf, hop]
  · exact nomatch h

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At every state reached at the head's batching's number the merge's slot is laid.** -/
theorem used_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {a : ProofFile.InstPub × S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 a) : (usedOf a.2).isSome = true := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (346 + 1) a := h
  cases h' with
  | @succ _ z s s' b0 hr hb hy =>
    obtain ⟨R, cs, _, e⟩ := hy
    have hd := ((step_ok_iff 0 b0 s s' R cs cs.length).1 e).2.2.2
    obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
    have h3 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
    obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hb)
    exact merge_lays_slot ((IM.k11_yes hla _ _ _ _).1 hd).1

/-- A closed test on the written lists. -/
def standsB (m : ℕ) : Bool :=
  (IM.placesW[batchAt IM.linksW IM.placesW m]?).any fun p =>
    (IM.linksW[m]?).any fun sub => decide (standAt IM.linksW p = .link sub) &&
      (decide (sub = .head) == decide (m = 24))

theorem stands_W : (List.range 25).all standsB = true := by decide +kernel

theorem batch_head_W : batchAt IM.linksW IM.placesW 24 = 347 := by decide +kernel

/-- **A part is there in front of every link's batching.** -/
theorem part_at_batch_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    {N : Numbers} {Mg : Meaning ProofFile.InstPub W} {z : ProofFile.InstPub}
    {Rz : ℕ → S × Fr.E.Str → Prop}
    (hRz : ∀ j a, Rz j a → Reach 0 c.blocksInOrder (ProofFile.startS Z) j (z, a.1)) {m : ℕ} (hm : m < 25)
    {a : S × Fr.E.Str}
    (h : onTR N Mg IM.linksW IM.placesW (fun s : S => (z, s)) Rz
      (batchAt IM.linksW IM.placesW m) a) : (atS.get? a.1).isSome = true := by
  have hB := List.all_eq_true.1 stands_W m (List.mem_range.2 hm)
  unfold standsB at hB
  cases hp : IM.placesW[batchAt IM.linksW IM.placesW m]? with
  | none =>
    rw [hp] at hB
    cases hB
  | some p =>
    rw [hp] at hB
    cases hs : IM.linksW[m]? with
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
        refine part_of_onTR_head hp hB.1 h ?_
        have hr := hRz _ _ h.2
        rw [batch_head_W] at hr
        exact used_at_347 hS hR O hr
      · exact part_of_onTR hp hB.1 (fun e => h24 (hB.2.1 e)) h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.merge_lays_slot
#print axioms VerifiableInference.Desc.LinkJoin.used_at_347
#print axioms VerifiableInference.Desc.LinkJoin.stands_W
#print axioms VerifiableInference.Desc.LinkJoin.part_at_batch_all
