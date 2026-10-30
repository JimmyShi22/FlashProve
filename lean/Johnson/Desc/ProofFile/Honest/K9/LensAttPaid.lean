-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/LensAttPaid.lean: FOR THE ITEM "totalB": AT AN ATTENTION SEGMENT THE ONE NUMBER THAT
Honest/K9/LensLook.lean LEAVES OWED (hruns of `lensAt_att_look`: at every stand the attention kind's two runs together
make attOwnB A.S claims): PAID, UNDER THE HEAD; AND SO THERE `LensAt` FROM THE YES OF OUR PUBLIC TEST (`LensEqAsked`)
ALONE, BESIDE THE HEAD, AN OPENING O, THE SEAT AND THE READINGS, WHICH THE ASSEMBLY ALREADY BINDS. Statements and
proofs: calls; no goal is stated.
  **`attRuns_paid`**   under the head, an opening O, g < 12, K9's seat, the readings hA, e3, hd, hC, hD ⊢ the premise
      hruns of `lensAt_att_look`, to the letter. THE COUNT IS THAT KIND's HOUSE's: `H2K5.Honest.Count.lenBoth_eq`
      (Johnson/Desc/K5/Honest/Law/RunsCount.lean: over the sealed library alone): where both lists of forms are there at
      what is fixed, and the place is the usual call list, the two lengths together are just attOwnB S. OURS IS THAT ITS
      PREMISES ARE MET AT A STAND: both lists are there because both runs have returned (`runs_at_fixed`,
      Honest/K9/LensRuns.lean; the library's `still_first`, `still_second`: the field forms; the ties of `take_att`);
      the place: `law_at_head` (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean), off hA
  **`lensAt_att_runs`**   `LensAt` at an attention segment, in the very form of the premise hlens of `givesTotalB_att`,
      from hLE, O, g < 12, Sd, hA, e3, hd, hC, hD
SO, WITH Honest/K9/LensRuns.lean: AT ALL 25 SEGMENTS hlens FOLLOWS FROM hLE, beside what the assemblies bind. hLE: a
test with code that no verifier asks; evaluated true at the stored full-size example alone, proved at no public part
(Johnson/Desc/K9/Honest/LensEq.lean): OURS.
GROUND: beside the sealed library, what lies beneath Honest/K9/LensRuns.lean, and two files of that kind's house's:
RunsCount.lean (live, not sealed) and PublicAtHead.lean with what lies beneath it, as they lie with us. At the full size
and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. hLE at any public part; the readings, O or Sd at any public part. That a stand is there: where
there is none both say nothing. No member; `lensAt_att_runs` is called by Honest/K9/TotalLens.lean, `attRuns_paid`
outside this file by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.LensRuns
import Johnson.Desc.K5.Honest.Law.RunsCount
import Johnson.Desc.K5.Honest.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun (lenStill)
open VerifiableInference.Desc.First.Att (P.parCOf)
open K5Law (fsFirst fsSecond still_first still_second)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The attention kind's two runs together: their number at every stand.** -/
theorem attRuns_paid {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww)
    {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) :
    NumAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1))
      (fun q => lenStill (fsFirst rdAll (P.parCOf A)) q + lenStill (fsSecond rdAll (P.parCOf A)) q)
      (K9Asks.attOwnB A.S) := by
  intro κ s m En ds y cols s' x' z G St hOk
  have hm : 2 * g + 1 < 25 := by omega
  have hs := sub_odd g hg
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  have seg' : SegAt (2 * g + 1) .attention Lk := hs ▸ seg
  have hA' : Bs.G₀.W.A[g]? = some A := by
    rw [O.W]
    exact hA
  obtain ⟨A₁, X₁, a1, a2, SL⟩ := seal_att h O hg hs Lk p hlk seg drawB kp pC pD hC hD xx tlD hd
  obtain rfl : A₁ = A := Option.some.inj (a1.symm.trans hA')
  obtain rfl : X₁ = Xl := Option.some.inj (a2.symm.trans e3)
  obtain ⟨A₂, X₂, b1, b2, TK⟩ := take_att h O hg hs Lk p hlk seg drawB kp pC pD hC tlD
  obtain rfl : A₂ = A₁ := Option.some.inj (b1.symm.trans hA')
  obtain rfl : X₂ = X₁ := Option.some.inj (b2.symm.trans e3)
  have hord : ∀ o, o ∈ First.orderOf .attention → o ∈ Lk.order := fun o ho => by
    rw [(order_at seg').1]
    exact ho
  obtain ⟨r1, n1, t1, c1, u1, hAt1, hFx1, hy1⟩ :=
    runs_at_fixed SL _ s s' _ cols _ St.step.2 hOk (2, "first") (hord _ (by decide))
  obtain ⟨lf, hlf, -⟩ := (still_first (phiAll tlD psiAll) _ rdAll (P.parCOf A₂) TK.hrd TK.okK5).forms _ n1 t1 c1 u1
    hFx1 (TK.ties.tFirst r1 hAt1 n1 t1 c1 u1 hy1)
  obtain ⟨r2, n2, t2, c2, u2, hAt2, hFx2, hy2⟩ :=
    runs_at_fixed SL _ s s' _ cols _ St.step.2 hOk (2, "second") (hord _ (by decide))
  obtain ⟨ls, hls, -⟩ := (still_second (phiAll tlD psiAll) _ rdAll (P.parCOf A₂) TK.hrd TK.okK5).forms _ n2 t2 c2 u2
    hFx2 (TK.ties.tSecond r2 hAt2 n2 t2 c2 u2 hy2)
  have Pl := (H2K5.Honest.law_at_head h hg hA).2.place
  exact H2K5.Honest.Count.lenBoth_eq Pl rfl rdAll _ hlf hls

/-- **`LensAt` at an attention segment, from our public test's yes alone**, beside the head, an opening, the seat and
the readings. -/
theorem lensAt_att_runs (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww)
    {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) :
    LensAt Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillAtt A pC pD)
      (lenFillAtt A pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) ww :=
  lensAt_att_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd hA e3 hd hC hD
    (attRuns_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg Sd hA e3 hd hC hD)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.attRuns_paid
#print axioms ProofFile.Honest.K9.lensAt_att_runs
