-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqAdd.lean: what the adding of a list of claims (`addList`,
Johnson/Desc/First/Batch/Add.lean) leaves of the ledger, and what it does to the marks "this claim's weight has been
handed out": for the tests on numbers and marks that the sub-protocol "the one equation" asks of the ledger later.
General lemmas on plain data; from a yes of the adding.

  `AddLeaves F G`      G has F's number of slots, next slot, shown values, factors, marks "filled", list of owed claims;
                       as many coefficients on slots, as many marks on claims, and as many arrays
  `Marked F`           every claim's number below the count bears its mark
  `addForm_size`, `addOne_leaves`, **`addList_leaves`**   a yes of the adding gives `AddLeaves`, and hands `Marked` on
  **`marks_full`**     where the count is the plan's number and there are as many marks: all marks are set

Limits. Nothing on the sums. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.K9.Honest.AddYes
import Johnson.Desc.First.Batch.Shape.DoorMade
import Johnson.Desc.First.Batch.Law.AddAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.K9 (addList addOne addForm addRuns weightNext)
open VerifiableInference.Desc.K9.Shape (foldlM_keeps ans_bind)
open VerifiableInference.Desc.K9H (addForm_iff addRuns_iff addOne_only)

/-- What the adding leaves of the ledger. -/
structure AddLeaves (F G : Fork) : Prop where
  ns : G.ns = F.ns
  next : G.next = F.next
  vp : G.vp = F.vp
  mf : G.mf = F.mf
  got : G.gotF = F.gotF
  owed : G.owed = F.owed
  coefs : G.LS.size = F.LS.size
  marks : G.kapMapF.size = F.kapMapF.size

theorem AddLeaves.refl (F : Fork) : AddLeaves F F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem AddLeaves.trans {F G H : Fork} (a : AddLeaves F G) (b : AddLeaves G H) : AddLeaves F H :=
  ⟨b.ns.trans a.ns, b.next.trans a.next, b.vp.trans a.vp, b.mf.trans a.mf, b.got.trans a.got,
    b.owed.trans a.owed, b.coefs.trans a.coefs, b.marks.trans a.marks⟩

/-- Every claim's number below the count bears its mark. -/
def Marked (F : Fork) : Prop := ∀ i, i < F.nClaim → F.kapMapF[i]? = some true

/-- The adding of a form leaves the number of coefficients on slots. -/
theorem addForm_size (F H : Fork) (w : E) (a : Aff) (h : addForm F w a = .ok H) : H.LS.size = F.LS.size := by
  unfold addForm at h
  simp only [] at h
  obtain ⟨T, -, h⟩ := (ans_bind _ _ _).1 h
  obtain ⟨Y, hY, h⟩ := (ans_bind _ _ _).1 h
  obtain rfl := Except.ok.inj h
  show Y.size = F.LS.size
  rw [← Array.foldlM_toList] at hY
  refine foldlM_keeps (K9.addSlot w F.ns) (fun A => A.size = F.LS.size) _ _ _ rfl (fun x _ c c' hc hx => ?_) hY
  unfold K9.addSlot at hx
  obtain ⟨_, -, hx⟩ := (ans_bind _ _ _).1 hx
  obtain rfl := Except.ok.inj hx
  simpa using hc

/-- One claim. -/
theorem addOne_leaves (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    AddLeaves F G ∧ (Marked F → Marked G) := by
  obtain ⟨-, -, hA⟩ := addOne_only F G cl h
  unfold addOne at h
  simp only [] at h
  cases hx : weightNext F with
  | error m => rw [hx] at h; exact nomatch h
  | ok x =>
    rw [hx] at h
    obtain ⟨-, -, hlt, hsz, -, ex⟩ := K9L.weightNext_ok F x hx
    have ex2 : x.2 = { F with kapMapF := F.kapMapF.set! F.nClaim true, nClaim := F.nClaim + 1 } :=
      congrArg (·.2) ex
    cases hf : addForm x.2 ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.form with
    | error m => simp only [bind, Except.bind, hf] at h; exact nomatch h
    | ok H =>
      simp only [bind, Except.bind, hf] at h
      have a1 := (addForm_iff x.2 _ cl.form).1 ⟨H, hf⟩
      obtain ⟨H', hH', -, eH⟩ := (addForm_iff x.2 ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.form).2 a1
      obtain rfl : H' = H := Except.ok.inj (hH'.symm.trans hf)
      have a2 := (addRuns_iff H' _ cl.runs).1 ⟨G, h⟩
      obtain ⟨G', hG', -, eG⟩ := (addRuns_iff H' ((cl.eqFirst.map fun first =>
        powE F.theta (F.planClaimsF + first)).getD x.1) cl.runs).2 a2
      obtain rfl : G' = G := Except.ok.inj (hG'.symm.trans h)
      have sz := addForm_size _ _ _ _ hf
      refine ⟨⟨by rw [eG, eH, ex2], by rw [eG, eH, ex2], by rw [eG, eH, ex2], by rw [eG, eH, ex2],
        by rw [eG, eH, ex2], by rw [eG, eH, ex2], ?_, by rw [hA.marks]; simp⟩, fun hM i hi => ?_⟩
      · have e1 : G'.LS = H'.LS := by rw [eG]
        rw [e1, sz, ex2]
      · rw [hA.count] at hi
        rw [hA.marks]
        by_cases hc : i = F.nClaim
        · subst hc
          simp [Array.getElem?_setIfInBounds, hsz, hlt]
        · have := hM i (by omega)
          simp [Array.getElem?_setIfInBounds, Ne.symm hc, this]

/-- **A list of claims.** -/
theorem addList_leaves : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    AddLeaves F G ∧ (Marked F → Marked G)
  | [], F, G, h => by
    obtain rfl : F = G := Except.ok.inj h
    exact ⟨AddLeaves.refl F, id⟩
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, h⟩ := (ans_bind _ _ _).1 h
    obtain ⟨a1, m1⟩ := addOne_leaves F H cl hH
    obtain ⟨a2, m2⟩ := addList_leaves l H G h
    exact ⟨a1.trans a2, fun hM => m2 (m1 hM)⟩

/-- **All marks are set.** -/
theorem marks_full (G : Fork) (hM : Marked G) (hc : G.nClaim = G.planClaimsF)
    (hs : G.kapMapF.size = G.planClaimsF) : G.kapMapF.all id = true := by
  rw [Array.all_eq_true]
  intro i hi
  have := hM i (by omega)
  rw [Array.getElem?_eq_getElem hi] at this
  exact Option.some.inj this

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.addForm_size
#print axioms ProofFile.Honest.K9.addOne_leaves
#print axioms ProofFile.Honest.K9.addList_leaves
#print axioms ProofFile.Honest.K9.marks_full
