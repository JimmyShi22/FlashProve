-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BackLookHead.lean: FOR THE ITEM "totalB": `ItemBack` AT THE LOOKUPS' THREE ENTRIES OF
THE HEAD's SEGMENT, AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT OUR FILLING, AT Front := "forms" AT WHATEVER
SECOND HOLE. Statements and proofs: calls; no goal is stated.
  `formsQ_congr`   the table's sentence "forms" reads of the readers their answer at its own entry and state alone
  **`itemBack_look_head`**   under the head, an opening O, the head's own link at 24 (hlk) and the calls' place (hC): at
      (2, "objects"), (2, "planes"), (7, "objects"): `ItemBack` at `okFillHead`, `tmFillHead`, at T := the thread of
      `lettersHead …`, b := the number of the head's batching, at every holes Hc
THE KNOT AT THIS SEGMENT, AS THE LOOKUPS' HEADS TELL IT: at the library's own holes the second hole is filled, so their
hypothesis hsil cannot be had there; their laws are meant at the empty hole (`K9.withSmall K9.LinkHoles.none`: hsil by
rfl). THE CARRY, MADE HERE: at a stand the run's own reader answers at the state in front, at every entry of the head's
order but "K8.equations" (the frame's `head_hrun`, Honest/Law/Rule/HeadHrun.lean); where it answers, the readers' answer
does not hang on the second hole (the library's `forms_of_run`); so "forms" at Hc is "forms" at the empty hole
(`formsQ_congr`). Then `objects_back`, `planes_back_head` (Honest/K3/Law/Total/). The road is that of the library's own
`k3i_planes_head_at` and of `LPFK9.k3i_planes_head_24`, walked the other way.
THE OTHER HYPOTHESES: as Honest/K9/BackLook.lean's head says; the head's readers: `readersAt_head`,
`LPFK9.ties_head_mg`, `head_24`; the promise: `kxHead_k3`.
THE TENTH ENTRY, the head's (3, "join"), is none of these three: `ItemBack` there stands in Honest/K9/BackAt.lean
(`itemBack_head`, under `RunAnswers`, at Front := "forms"), with K6's; Honest/K9/TotalHead.lean calls it under hforms.
GROUND: beside the sealed library: what lies beneath Honest/K9/BackLook.lean and RunAnswersAt.lean (the frame's threads
and rule among it). At the full size and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. "forms" at any state. Ok at what is fixed at any state. That a stand is there: where there is none
it says nothing. No member; `itemBack_look_head` is called by Honest/K9/TotalBack.lean alone. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.BackLook
import Johnson.Desc.ProofFile.Honest.K9.RunAnswersAt
import Johnson.LPFK9R.ItemPlanesAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Strs Place Link Claim Block FileDescription)
open VerifiableInference.Desc
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open VerifiableInference.OnPublicFiles (atS2_seatOf hdAt t3Obj heard_at k3Ok_at bvHead pvHead readersAt_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3.Law.Total (objects_back planes_back_head)

/-- The table's sentence "forms" reads of the readers their answer at its own entry and state alone. -/
theorem formsQ_congr {Rd Rd' : Desc.K9.Readers} {own : List (ℕ × ℕ)} {k : ℕ} {nm : String} {s : S}
    {rd : ℕ × ℕ → MsgQ} (e : Rd'.forms k nm s = Rd.forms k nm s) (hq : formsQ Rd own k nm s rd) :
    formsQ Rd' own k nm s rd := by
  obtain ⟨a, R, h1, h2, h3, h4⟩ := hq
  exact ⟨a, R, h1, e.trans h2, h3, h4⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)


/-- **`ItemBack` at the lookups' three entries of the head's segment, at the frame's own thread, at our filling, at
Front := "forms" AT WHATEVER SECOND HOLE.** -/
theorem itemBack_look_head {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {L : Link TS Claim}
    (hlk : h.𝔇.lk 24 = some L) (pw : Desc.K9.Where) (own : List (ℕ × ℕ))
    (rdW : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → ℕ × ℕ → MsgQ) (nU : Array ℕ)
    (tlD : HTailF2) {pC : First.Look.P} (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (pD : First.Look.P)
    (Hc : Desc.K9.LinkHoles) :
    ∀ o ∈ [((2 : ℕ), "objects"), (2, "planes"), (7, "objects")],
      ItemBack L pw (phiFill tlD) (okFillHead Bs.G₀.W nU tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (batchAt P5J.fullLinks P5J.At.ps 24) own rdW o
        fun s v => formsQ (Desc.K9.readersOfLink Hc L) own o.1 o.2 s (rdW v) := by
  have hm : 24 < 25 := by omega
  have hs : IM.subAt 24 = .head := by decide
  have hK : ∀ q, okFillHead Bs.G₀.W nU tlD pC pD q → kxAll pC.lm pC.first 0 pD.first q :=
    fun q hq => kxHead_k3 q hq.2
  intro o ho κ s m En ds y cols s' x' z G St a v ha hOk hF
  have hr : (o.2 == "K8.equations") = false → o ∈ sortItems .head →
      (Desc.K9.readerOf (Desc.K9.statesOfLink L) o.1 o.2 s).isSome = true := fun h8 hi =>
    head_hrun h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w St.thr.1 hlk o hi h8
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · have hF0 := formsQ_congr (forms_of_run (Desc.K9.withSmall Desc.K9.LinkHoles.none) Hc L 2 "objects" s rfl
      (hr rfl (by decide))) hF
    exact objects_back (Desc.K9.withSmall Desc.K9.LinkHoles.none) L (phiAll tlD psiAll) (hdAt false) _ _
      (OnPublicFiles.seatOf K3Lot.ofForm false) (atS2_seatOf false) (heard_at tlD false) (tmFillHead Bs.G₀.W pC pD) own
      (rdW v) (2, "objects") rfl (at_objects h hm false hlk)
      (by simp [tmFillHead, tmH, t3All, v3All, hdAt]) s a ha (k3Ok_at hK false _ hOk) rfl hF0
  · have hF0 := formsQ_congr (forms_of_run (Desc.K9.withSmall Desc.K9.LinkHoles.none) Hc L 2 "planes" s rfl
      (hr rfl (by decide))) hF
    obtain ⟨iU3, _, hi, _, _⟩ := LPFK9.ties_head_mg h O 24 hm hs L hlk
    have e : Kinds.Head.Law.readsOf Bs.G₀.W = iU3 := by
      unfold Kinds.Head.Law.readsOf
      rw [hi]
      rfl
    subst e
    obtain ⟨h4, hN⟩ := head_24 h.toAtMg.scope O.public
    have hH : Desc.K3.isHead Bs.G₀.W 24 = true := by
      unfold Desc.K3.isHead
      rw [h4, hN]
      rfl
    have eW : Bs.G₀.W = P5J.At.X Zp := O.W
    have hrd := readersAt_head hH hi
    rw [show K3Lot.readersAt Bs.G₀.W 24 = K3Lot.readersAt (P5J.At.X Zp) 24 by rw [← eW]] at hrd
    obtain ⟨p', hp', hAt⟩ := at_planes h hm hlk hrd
    obtain rfl : p' = pC := Option.some.inj (hp'.symm.trans hC)
    exact planes_back_head (u := tlD) (jC := p'.first) (Desc.K9.withSmall Desc.K9.LinkHoles.none)
      (Kinds.Head.Law.readsOf Bs.G₀.W) (tmFillHead Bs.G₀.W p' pD) own (rdW v) (2, "planes") rfl hAt
      (by simp [tmFillHead, tmH, t3All, v3All]) s a ha hOk (fun q hq => (hK q hq).1) rfl hF0
  · have hF0 := formsQ_congr (forms_of_run (Desc.K9.withSmall Desc.K9.LinkHoles.none) Hc L 7 "objects" s rfl
      (hr rfl (by decide))) hF
    exact objects_back (Desc.K9.withSmall Desc.K9.LinkHoles.none) L (phiAll tlD psiAll) (hdAt true) _ _
      (OnPublicFiles.seatOf K3Lot.ofForm true) (atS2_seatOf true) (heard_at tlD true) (tmFillHead Bs.G₀.W pC pD) own
      (rdW v) (7, "objects") rfl (at_objects h hm true hlk)
      (by simp [tmFillHead, tmH, t3All, v3All, hdAt]) s a ha (k3Ok_at hK true _ hOk) rfl hF0

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.formsQ_congr
#print axioms ProofFile.Honest.K9.itemBack_look_head
