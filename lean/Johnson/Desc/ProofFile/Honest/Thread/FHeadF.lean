-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadF.lean: one clause more for the condition `keeps` of the
first chain's invariant at the full size, the same at every kind of sub-protocol. An item on linear
forms that passes over a sub-protocol needs, of the state after the step, a public test that is tied
to the item. The invariant after the step contains that test, but the hypothesis in which an item
passes over a sub-protocol (`RidesPastS`, PaysS.lean) has of the state after the step only `keeps`.
So the test is laid into `keeps`. FHead.lean is not changed.

  1  `formsBehind`, `fHeadF`   the two definitions
  2  `pubForms_other`   at a public item that is none of the claims on linear forms, the clause says
     "true = true"
  3  `form_pubI`   every public item that is tied to an item open at a border holds of the state,
     from the part `Form` of the invariant alone. `thr_pubI` (FormLawI.lean) has the same conclusion
     from the whole invariant
  4  `formsBehind_of_form`   the clause, from `Form` at the border after the sub-protocol
  5  `head_hK_forms`   the column `hK` of `owesS_head_form` (GatherHeadForm.lean) at a family `f`
     with the clause beside it, from the column `hK` at `f` and the column `hF`

Limits.
  * The clause is proved from the column `hF`. It is proved no further than `hF` is. So far `hF` is
    proved at 51 of K1's 52 numbers (K1FormBehind.lean, K1FormBehindEnds.lean) and where the authors
    of a kind's lemmas prove it.
  * Full size only, and parts 4 and 5 only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.FormLawI
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.IMR.BorderW
import Johnson.IMR.HandsDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S onAt openSets pubSets pubHeld pubOfItems start borderOf
  pubAll)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The definitions -/

/-- The public tests of the claims on linear forms hold of the state `s'`, at every public item that
is tied to an item open at the border after the place `p`. `pubForms`
(Johnson/Desc/First/Batch/FormsPub.lean) is the library's text of these tests. It reads the state
alone. At every other public item it answers with its argument `base`, which is "true" here, so
the clause says nothing of those. It is a definition: a part of a clause of `keeps`. -/
def formsBehind (D : VerifiableInference.Desc.First.PubData) (p : Place) (s' : TS) : Prop :=
  ∀ q ∈ pubOfItems (IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p) + 1)),
    VerifiableInference.Desc.K9.pubForms D.Rd D.runs D.ah D.N (fun _ (_ : Unit × TS) => true) q
      ((), s') = true

/-- `fHead` with that clause beside it, the same at every kind. It is a definition: it fills an
argument of the invariant. -/
def fHeadF (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (D : VerifiableInference.Desc.First.PubData) :
    KindName → Place → TS → TS → Prop :=
  fun κ p s s' => fHead Zp cF G take P11 p12 P13 κ p s s' ∧ formsBehind D p s'

/-- At a public item that is none of the claims on linear forms the test is "true". -/
theorem pubForms_other (D : VerifiableInference.Desc.First.PubData) (s' : TS) :
    VerifiableInference.Desc.K9.pubForms D.Rd D.runs D.ah D.N (fun _ (_ : Unit × TS) => true)
      VerifiableInference.Desc.First.Pub.unheard ((), s') = true := rfl

/-! ## 2 From the part `Form` of the invariant -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- Every public item that is tied to an item open at the border holds of the state, from `Form`
alone. -/
theorem form_pubI (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m)
    {q : VerifiableInference.Desc.First.Pub}
    (hq : q ∈ pubOfItems (((openSets L.links L.ps (start L.links))[b]?).getD [])) :
    L.mgP.pub q (L.pubOf m.st.input.x, s) = true := by
  obtain ⟨hf, hP⟩ := hF
  have hf' : s.failed.isNone = true := hf
  have hP' : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hP
  obtain ⟨-, hP2⟩ := hP'
  rcases hP2 with hm | ⟨hB, -⟩
  · exfalso
    have hm' : s.failed ≠ none := hm
    cases hs : s.failed with
    | none => exact hm' hs
    | some e =>
      rw [hs] at hf'
      cases hf'
  · simp only [Bool.and_eq_true] at hB
    obtain ⟨⟨-, hpub⟩, -⟩ := hB
    unfold pubHeld at hpub
    exact List.all_eq_true.1 hpub q (List.mem_append_right _ hq)

end

/-! ## 3 At the first chain at the full size -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The clause, from `Form` at the border after the sub-protocol.** -/
theorem formsBehind_of_form {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) {k : Coins Bk}
    {s' : TS} {m' : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' m') :
    formsBehind h.𝔇.pubD p s' := by
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hb : b < 358 := by
    have hlt := (List.getElem?_eq_some_iff.1 hp).1
    rw [← e', IM.places_len] at hlt
    exact hlt
  have hbo : borderOf P5J.At.ps (some p) = b := by
    have e := IM.border_W b (by omega)
    rw [e', hp] at e
    exact e
  intro q hq
  rw [hbo] at hq
  have t := form_pubI (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF (q := q) hq
  rw [head_pub_all] at t
  cases q <;> first | rfl | exact t

/-- **The column `hK` with the clause beside it**, from the column `hK` and the column `hF`. -/
theorem head_hK_forms (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (f : KindName → Place → TS → TS → Prop)
    (hF : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' y.2)
    (hK : ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s') :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      f blk.place.kind blk.place s s' ∧ formsBehind h.𝔇.pubD blk.place s' :=
  fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
    ⟨hK b hb blk hblk k s m E ds y cols s' hA hd hS,
      formsBehind_of_form h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
        (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk)
        (hF b hb blk hblk k s m E ds y cols s' hA hd hS)⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.pubForms_other
#print axioms ProofFile.Honest.FirstThread.form_pubI
#print axioms ProofFile.Honest.FirstThread.formsBehind_of_form
#print axioms ProofFile.Honest.FirstThread.head_hK_forms
