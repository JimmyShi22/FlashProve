-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SitsAtt.lean: THE ONE NAMED PREMISE OF k01_law_reads IS PAID: LeavesAtt G, at every G: an attention link's quiet step behind the
reads (Johnson/Desc/First/Att/ReadsO.lean: readsAtO) leaves the statement: by readsAtSO_st (Johnson/Goal/Meaning/RecReadsAtt.lean).
  leavesAtt              at every ground
  k01_law_reads_whole    so at all 25 links' reads' places the description's own entry pays the law's two premises, outright
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.SitsLaw
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.ReqLit (shapeFull)
open ProofFile (Cl)
open IM (Open k1Ix)

theorem leavesAtt (G : ProofFile.Ground) : LeavesAtt G := by
  intro l g q h
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s s' rs gs hy
  have e : s'.st = s.st := Meaning.K2.readsAtSO_st hy
  show SameMsgs s.st s'.st
  rw [e]
  exact ⟨rfl, fun _ => rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At every link's reads' place the description's own entry pays the law's two premises.** -/
theorem k01_law_reads_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l false]? = some b ∧
      LawAt b (3 * l + 1) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) :=
  k01_law_reads hS hR O hc hs (leavesAtt _)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.leavesAtt
#print axioms VerifiableInference.Desc.K1.k01_law_reads_whole
