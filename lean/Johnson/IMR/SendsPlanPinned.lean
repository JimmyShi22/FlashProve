-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SendsPlanPinned.lean: THE ONE TEST ON THE PUBLIC PART FOR THE TWO
SENDINGS OF THE OWN GROUP, ToldDesc.sendsPlanB Z (Johnson/ToldDescR/PlanAtSendB.lean), ACCEPTS WHERE
madeRow
ACCEPTS. With that file's hP_of_sendsPlanB: the premises hP₁ and hP₂ of
ToldDesc.sampleTwoB_h4_paid, as theorems under madeRow. Statements and proofs.

  planAtSendB_congr   the test planAtSendB reads of a sending's parameters the codes and the named
                      parts alone: not the place, not gp (the answers to a sample; the first tree),
                      not the work, not the groups
  partsOf · firstParts_eq   the first sending's named parts are a function of the request's shape
  planW y co sh li    sendsPlanB's text at four letters: the sized proof, the codes, the request's
                      shape, the shape of the test on the table
  sendsPlanB_eq       sendsPlanB Z is planW at Z's own four (by unfolding: so gp is idle in it)
  planW_written       at the written four: true (by the kernel)
  planW_can_fail      the closed fact can fail: with nothing sent at the start it is false
  **sendsPlanB_pinned**   madeRow Z = true → sendsPlanB Z = true

What is not claimed. That madeRow accepts at any files. The full size alone. No member. No soundness.

-/
import Johnson.ToldDescR.PlanAtSendB
import Johnson.IMR.SendsPinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (madeRow)
open ToldDesc (planAtSendB sendsPlanB p14At)

/-- **The test reads the codes and the named parts alone.** -/
theorem planAtSendB_congr {P P' : K1.Par} (hc : P.codes = P'.codes) (hp : P.parts = P'.parts)
    (cs : Codes) (sh : OracleShape) (k : ℕ) (rad : ℕ → ℕ) :
    planAtSendB P cs sh k rad = planAtSendB P' cs sh k rad := by
  obtain ⟨pl, co, gp, wk, pa, gr⟩ := P
  obtain ⟨pl', co', gp', wk', pa', gr'⟩ := P'
  obtain rfl : co = co' := hc
  obtain rfl : pa = pa' := hp
  rfl

/-- The first sending's named parts, out of the request's shape. -/
def partsOf (sh : ReqShape) : List (String × Array OracleNotice) :=
  let f : ReqFrame := { shape := sh, groups := reqGroups sh }
  [("own", ReqFrame.notices (f.atMoment 0)), ("the fold's mask", #[foldMaskNotice (f.foldShape 0 {})]),
    ("at the start", sh.atStart.toArray)]

theorem firstParts_eq (q : Params.First) : K1.firstParts q = partsOf q.shape := rfl

/-- sendsPlanB's text, at four letters. -/
def planW (y : ProofSized) (co : Codes) (sh : ReqShape) (li : LinShape) : Bool :=
  planAtSendB { place := ⟨1, some 0, 1, .K1⟩, codes := co, gp := ⟨0, 0⟩, work := 0, parts := partsOf sh }
      (Third.p₁₄Z y.set y.codes y.batch).codes
      ((y.request.atStart.head?.map (·.shape)).getD default) 4 (fun _ => 0) &&
    match linMessageW li with
    | some msg => planAtSendB { place := ⟨1, none, 4, .K1⟩, codes := co, gp := ⟨0, 0⟩, work := 0,
                                parts := [("W and the messages sent with it", msg)] }
        (Third.p₁₄Z y.set y.codes y.batch).codes (Third.p₁₄Z y.set y.codes y.batch).S.w 0 (fun _ => 0)
    | none => true

theorem sendsPlanB_eq (Z : ProofFile.Pub) :
    sendsPlanB Z = planW Z.p.chains.made.sized.proof Z.first.codes Z.first.shape Z.first.lin := by
  unfold sendsPlanB planW
  congr 1

set_option maxRecDepth 1000000 in
/-- **At the written four: true.** -/
theorem planW_written : planW zW zW.codes zW.request zW.batch.shape = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed fact can fail: at the written request's shape with nothing sent at the start. -/
theorem planW_can_fail :
    planW zW zW.codes { zW.request with atStart := [] } zW.batch.shape = false := by decide +kernel

/-- **sendsPlanB, WHERE madeRow ACCEPTS.** -/
theorem sendsPlanB_pinned {Z : ProofFile.Pub} (hy : madeRow Z = true) : sendsPlanB Z = true := by
  obtain ⟨hz, hsh, hli, hco, -⟩ := pins hy
  rw [sendsPlanB_eq, hz, hco, hsh, hli]
  exact planW_written

end IM

#print axioms IM.planAtSendB_congr
#print axioms IM.sendsPlanB_eq
#print axioms IM.planW_written
#print axioms IM.planW_can_fail
#print axioms IM.sendsPlanB_pinned
