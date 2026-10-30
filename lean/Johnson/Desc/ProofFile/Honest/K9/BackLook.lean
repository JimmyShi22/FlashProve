-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BackLook.lean: FOR THE ITEM "totalB": THE NAMED SENTENCE `ItemBack`
(Honest/K9/TotalFront.lean) AT THE LOOKUPS' ENTRIES OF AN ATTENTION AND OF A FEED-FORWARD SEGMENT (SIX OF THEIR NINE),
AT OUR OWN FILLING, AT Front := THE TABLE's SENTENCE "forms" AT THE TABLE's OWN HOLES. THE LAWS ARE THE LOOKUPS'
HOUSE's; OURS IS THAT THEIR HYPOTHESES ARE MET UNDER THE LIBRARY's HEAD. Statements and proofs: calls; no goal is
stated.
  `itemBack_objects_at`   at a segment m < 25 that is not number mH, at either lookup (d): `ItemBack` at (IM.k3Ix m d,
      "objects"), general in the thread T, the border b, Ok (which gives `kxAll`) and the table of terms (which is
      `t3Obj` there): one call of `objects_back` (Honest/K3/Law/Total/ObjectsBack.lean)
  **`itemBack_look_lay`**   at 2 g, g < 12: at (1, "objects"), (6, "objects"), at `okFillLay`, `tmFillLay`
  **`itemBack_look_att`**   at 2 g + 1, g < 12, under an opening O, the plan A (hA) and the calls' place (hC): at (1,
      "objects"), (2, "join"), (1, "planes"), (6, "objects"), at `okFillAtt`, `tmFillAtt`: by `objects_back`, 
      and `join_back_att`, `planes_back_att` (Honest/K3/Law/Total/CallersPaid.lean)
HOW THEIR HYPOTHESES ARE MET, EACH BY A SEALED LEMMA, BY UNFOLDING, OR BY `ItemBack`'s OWN PREMISES: the kind's own run
stands at the entry: `at_objects`, `at_planes` (Johnson/P1K9R/ItemObjectsAt.lean, ItemPlanesAt.lean; the readers by
`H2K5.Door.readersAt_att`), `LPFK9.at_join` (Johnson/LPFK9R/ItemJoinAtLetters.lean) · the accessors and what was heard:
`atS2_seatOf`, `heard_at` · the entry's name is not "K8.equations": rfl · the table of terms is `plainTm` of the run's
values: by unfolding our filling · the lookups' promise at what is fixed: our Ok's second half (`kxAll3_k3`, `kxAtt_k3`,
`k3Ok_at`) · the attention's promise on what it heard: our Ok's field k5 · the second hole says nothing:
`H2K5.Door.silent_none` · a part is there, Ok at what is fixed, and "forms": `ItemBack`'s own three premises at a stand.
T, b, pw and the stand are not spent: these are sentences on the verifier's state and the library's algebra.
GROUND: beside the sealed library: what lies beneath Honest/K9/BackAt.lean, TotalFill.lean and SeatTied.lean, and three
files of the lookups' house's (ObjectsBack.lean, PlanesJoinBack.lean, CallersPaid.lean), which, besides each other,
import sealed modules alone. At the full size and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. "forms" at any state: Front is a letter of whoever calls. Ok at what is fixed at any state. That a
stand is there. The head's three entries (Honest/K9/BackLookHead.lean). No member; the two marked are called by
Honest/K9/TotalBack.lean alone, `itemBack_objects_at` by these two alone. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.BackAt
import Johnson.Desc.ProofFile.Honest.K9.TotalFill
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.ObjectsBack
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.CallersPaid
import Johnson.P1K9R.ItemObjectsAt
import Johnson.P1K9R.ItemPlanesAt
import Johnson.LPFK9R.ItemJoinAtLetters
import Johnson.Desc.First.Att.Door.Law.K5RestOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Link Claim Chain Block FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc
open VerifiableInference.OnPublicFiles (atS2_seatOf hdAt t3Obj heard_at k3Ok_at plVals jnVals bvAtt pvAtt kvAtt)
open VerifiableInference.Desc.First.Look (placeAt)
open ProofFile.Honest.K3.Law.Total (objects_back planes_back_att join_back_att)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ) (pw : Desc.K9.Where)
  (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → MsgQ)
variable {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}

/-- **`ItemBack` at an entry "objects", away from the head's segment, at Front := the table's sentence "forms".** -/
theorem itemBack_objects_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (hlk : h.𝔇.lk m = some L) (d : Bool) (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (ht : tmOf (IM.k3Ix m d, "objects") = t3Obj lmC jC lmD jD d) (Xp : Verify.Public) {mH : ℕ}
    (hmH : (m == mH) = false) :
    ItemBack L pw (phiAll u psiAll) Ok tmOf T b own rdW (IM.k3Ix m d, "objects") fun s v =>
      formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH m L) L) own (IM.k3Ix m d) "objects" s (rdW v) :=
  fun _ s _ _ _ _ _ _ _ _ _ _ a v ha hOk hF =>
    objects_back (Desc.K9.holesAt Xp mH m L) L (phiAll u psiAll) (hdAt d) _ _ (OnPublicFiles.seatOf K3Lot.ofForm d)
      (atS2_seatOf d) (heard_at u d) tmOf own (rdW v) (IM.k3Ix m d, "objects") rfl (at_objects h hm d hlk) ht s a ha
      (k3Ok_at hK d _ hOk) (by rw [H2K5.Door.silent_none Xp hmH L]) hF

variable {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat}
  {B₂ : ProofFile.SecondSeat}

/-- **`ItemBack` at the lookups' two entries of a feed-forward segment, at our filling, at Front := "forms".** -/
theorem itemBack_look_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (hlk : h.𝔇.lk (2 * g) = some L) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD : HTailF2)
    (pC pD : First.Look.P) (Xp : Verify.Public) {mH : ℕ} (hmH : (2 * g == mH) = false) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")],
      ItemBack L pw (phiFill tlD) (okFillLay p4 nU tlD pC pD) (tmFillLay p4 pC pD) T b own rdW o fun s v =>
        formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g) L) L) own o.1 o.2 s (rdW v) := by
  have hm : 2 * g < 25 := by omega
  have hne : 2 * g ≠ 24 := by omega
  have hK : ∀ q, okFillLay p4 nU tlD pC pD q → kxAll pC.lm pC.first 0 pD.first q := fun q hq => kxAll3_k3 q hq.2
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · have e1 : IM.k3Ix (2 * g) false = 1 := by simp [IM.k3Ix, hne]
    have H := itemBack_objects_at (u := tlD) T b pw own rdW h hm hlk false hK (tmFillLay p4 pC pD)
      (by rw [e1]; simp [tmFillLay, tmL, t3All, v3All, t3Obj, hdAt]) Xp hmH
    rw [e1] at H
    exact H
  · have e1 : IM.k3Ix (2 * g) true = 6 := by simp [IM.k3Ix, hne]
    have H := itemBack_objects_at (u := tlD) T b pw own rdW h hm hlk true hK (tmFillLay p4 pC pD)
      (by rw [e1]; simp [tmFillLay, tmL, t3All, v3All, t3Obj, hdAt]) Xp hmH
    rw [e1] at H
    exact H

/-- **`ItemBack` at the lookups' four entries of an attention segment, at our filling, at Front := "forms".** -/
theorem itemBack_look_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) (nU : Array ℕ)
    (tlD : HTailF2) {pC : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (pD : First.Look.P)
    (Xp : Verify.Public) {mH : ℕ} (hmH : (2 * g + 1 == mH) = false) :
    ∀ o ∈ [((1 : ℕ), "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      ItemBack L pw (phiFill tlD) (okFillAtt A nU tlD pC pD) (tmFillAtt A pC pD) T b own rdW o fun s v =>
        formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH (2 * g + 1) L) L) own o.1 o.2 s (rdW v) := by
  have hm : 2 * g + 1 < 25 := by omega
  have hne : 2 * g + 1 ≠ 24 := by omega
  have hs := sub_odd g hg
  have hK : ∀ q, okFillAtt A nU tlD pC pD q → kxAll pC.lm pC.first 0 pD.first q := fun q hq => kxAtt_k3 q hq.2
  have hQ : ∀ q v g' h', okFillAtt A nU tlD pC pD q → q.2 = some v → rdAll q.1 = some (g', h') →
      K5Law.K5OkAt (P.parCOf A) g'.zk h' v.F := fun q v g₁ h₁ hq hv hr => hq.1.k5 v g₁ h₁ hv hr
  have hsil : ∀ (n : ℕ) (nm : String) (s : S), (Desc.K9.holesAt Xp mH (2 * g + 1) L).silent n nm s = none :=
    fun n nm s => by rw [H2K5.Door.silent_none Xp hmH L]
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · have e1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, hne]
    have H := itemBack_objects_at (u := tlD) T b pw own rdW h hm hlk false hK (tmFillAtt A pC pD)
      (by rw [e1]; simp [tmFillAtt, tmA, t3All, v3All, t3Obj, hdAt]) Xp hmH
    rw [e1] at H
    exact H
  · obtain ⟨h4, g', hg', e, _⟩ := LPFK9.att_facts h O (2 * g + 1) hm hs
    obtain rfl : g = g' := by omega
    have hA' : Bs.G₀.W.A[g]? = some A := by
      rw [O.W]
      exact hA
    have hAt := LPFK9.at_join O h4 hg' hA' (LPFK9.link_of_lk h O (2 * g + 1) L hlk)
    exact fun _ s _ _ _ _ _ _ _ _ _ _ a v ha hOk hF =>
      join_back_att (u := tlD) (lmC := pC.lm) (jC := pC.first) (Desc.K9.holesAt Xp mH (2 * g + 1) L) A hQ
        (tmFillAtt A pC pD) own (rdW v) (2, "join") rfl hAt (by simp [tmFillAtt, tmA, t3All, v3All]) s a ha hOk
        (fun q hq => (hK q hq).1) (hsil _ _ _) hF
  · have e1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, hne]
    obtain ⟨p', hp', hAt⟩ := at_planes h hm hlk (H2K5.Door.readersAt_att (H2K5.Door.scope_all h).1 hA)
    obtain rfl : p' = pC := Option.some.inj (hp'.symm.trans hC)
    rw [e1] at hAt
    exact fun _ s _ _ _ _ _ _ _ _ _ _ a v ha hOk hF =>
      planes_back_att (u := tlD) (jC := p'.first) (Desc.K9.holesAt Xp mH (2 * g + 1) L) A hQ
        (tmFillAtt A p' pD) own (rdW v) (1, "planes") rfl hAt (by simp [tmFillAtt, tmA, t3All, v3All]) s a ha hOk
        (fun q hq => (hK q hq).1) (hsil _ _ _) hF
  · have e1 : IM.k3Ix (2 * g + 1) true = 6 := by simp [IM.k3Ix, hne]
    have H := itemBack_objects_at (u := tlD) T b pw own rdW h hm hlk true hK (tmFillAtt A pC pD)
      (by rw [e1]; simp [tmFillAtt, tmA, t3All, v3All, t3Obj, hdAt]) Xp hmH
    rw [e1] at H
    exact H

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.itemBack_objects_at
#print axioms ProofFile.Honest.K9.itemBack_look_lay
#print axioms ProofFile.Honest.K9.itemBack_look_att
