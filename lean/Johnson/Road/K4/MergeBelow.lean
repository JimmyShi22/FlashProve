-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MergeBelow.lean: THE SLOT OF THE MERGE's END VALUE LIES BELOW THE OPEN LEDGER's NEXT
SLOT: MADE BY K4's SUB-PROTOCOL, at every state that the first chain's run reaches just behind it. A
definition; statements with their proofs: calls.

  `MergeBelow s`: where the state's reader `K9.mergeOf` (Johnson/Desc/First/Batch/AtS.lean) finds a
    slot j: a ledger F is open (`S.fork?`) and j < F.next.
  `mergeOf_own`: where the state bears what K4's hearing returned (`S.own?` = some o), the reader
    finds o.wo.sFv.
  `merge_last`: at a hearing's return from a ledger with arrays of the right sizes: o.wo.sFv + 1 =
    G.next: THE MERGE's SLOT IS THE LAST THAT THE HEARING TAKES (`hear_end_first` |
    `hear_end_later`, Johnson/Road/K4/HearSlotsEnd.lean).
  `mergeBelow_kept`: at two states with an accept of K4's sub-protocol between them, the ledger in
  front with its sizes: s'.own? = some o · s'.fork? = some G · o.wo.sFv + 1 = G.next.
  **`mergeBelow_made`**: hS · hR · an opening · F.planOk = true · g < 12 · Reach 0 c.blocksInOrder start (28
  * g + 5) (z, s') ⟹ ∃ o G, s'.own? = some o ∧ s'.fork? = some G ∧ o.wo.sFv + 1 = G.next.
  `mergeBelow_behind`: so MergeBelow s'. THE SIZES OF THE LEDGER IN FRONT OF K4 ARE ANOTHER FILE's:
  `sized_upTo` (Johnson/Desc/First/Look/K03RowsBare.lean).

Limits. AT THE BORDER JUST BEHIND K4 ALONE (28 g + 5): that own? stays and the ledger only grows up
to the front of the lookup on the digits is not said here. That there is an opening is shown by no
theorem here. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.FunsThirdReached
import Johnson.Road.K4.HearSlotsEnd
import Johnson.Desc.First.Look.K03RowsBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.K4 (Par hear engFl hear_end_first hear_end_later)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (mergeOf)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)

/-- **Where the merge has a slot, a ledger is open and the slot lies below its next.** -/
def MergeBelow (s : S) : Prop := ∀ j, mergeOf s = some j → ∃ F, s.fork? = some F ∧ j < F.next

theorem mergeOf_own {s : S} {o : Own} (h : s.own? = some o) : mergeOf s = some o.wo.sFv := by
  unfold S.own? at h
  unfold mergeOf
  cases hh : s.here with
  | lay a =>
    rw [hh] at h
    have h' : a.own = some o := h
    show a.own.map (·.wo.sFv) = some o.wo.sFv
    rw [h']
    rfl
  | between => rw [hh] at h; exact nomatch h
  | att a => rw [hh] at h; exact nomatch h
  | head a => rw [hh] at h; exact nomatch h
  | fin a => rw [hh] at h; exact nomatch h
  | mem a => rw [hh] at h; exact nomatch h

/-- The merge's slot is the last that the hearing takes. -/
theorem merge_last {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (hF : PscRun.Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.wo.sFv + 1 = G.next := by
  cases hg : (g == 0) with
  | true =>
    obtain ⟨_, _, e1, _, e2⟩ := hear_end_first Reading.gl hF h hg
    rw [e1, e2]
  | false =>
    obtain ⟨_, _, e1, _, e2⟩ := hear_end_later Reading.gl hF h hg
    rw [e1, e2]

theorem mergeBelow_kept {p : Par} {s s' : S} (K : KeptAtS p s s')
    (hS : ∀ F, s.fork? = some F → PscRun.Sized F) :
    ∃ o G, s'.own? = some o ∧ s'.fork? = some G ∧ o.wo.sFv + 1 = G.next := by
  obtain ⟨a, fo, o, G, ha, _, hG, _, ho, _, _, _, _, _, _, t, u, hh⟩ := K
  have hf : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
  exact ⟨o, G, ho, hG, merge_last (hS _ hf) hh⟩

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **Behind K4's sub-protocol, at every reached state: the merge's slot is the ledger's last.** -/
theorem mergeBelow_made (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {Q : Type} {start : Q → S} {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')) :
    ∃ o G, s'.own? = some o ∧ s'.fork? = some G ∧ o.wo.sFv + 1 = G.next := by
  obtain ⟨z', s, s'', b, e, hr, hb, hy⟩ := reach_pred (k := 28 * g + 4) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b₀, x, e1, e2, _, e4, _⟩ := IM.k4_of hS hR O g hg
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b₀ := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have K : KeptAtS { x.2 with k3Runs := true } s s' :=
    kept_atS ((IM.k4_yes e4 s s' rs gs).1 hd).1
  obtain ⟨_, R, C, hfold⟩ := hr.fold
  have hk : 28 * g + 4 = 14 * (2 * g) + 1 + 2 + 1 := by omega
  rw [hk] at hfold
  obtain ⟨F₀, hF₀, hZ₀⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 1
    (by omega) hfold
  exact mergeBelow_kept K fun F' hF' => by
    obtain rfl : F₀ = F' := Option.some.inj (hF₀.symm.trans hF')
    exact hZ₀

theorem mergeBelow_behind (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {Q : Type} {start : Q → S} {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')) : MergeBelow s' := by
  obtain ⟨o, G, ho, hG, e⟩ := mergeBelow_made hS hR O hOk hg h
  intro j hj
  rw [mergeOf_own ho] at hj
  obtain rfl := Option.some.inj hj
  exact ⟨G, hG, by omega⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mergeOf_own
#print axioms OnBytes.Road.K4.merge_last
#print axioms OnBytes.Road.K4.mergeBelow_kept
#print axioms OnBytes.Road.K4.mergeBelow_made
#print axioms OnBytes.Road.K4.mergeBelow_behind
