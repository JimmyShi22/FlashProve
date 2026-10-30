-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsAtHead.lean: WHAT K9's BATCHING LEAVES OF THE STATE, UNDER THE LIBRARY's ONE
HEAD: the premise "each run of the order keeps it" of Honest/K9/KeepsPaid.lean's corollaries, paid at a link that sits
at a segment of the library's own description. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this
file, and no goal is stated.
  **`fieldRun_lay_at`**, **`fieldRun_att_at`**, **`fieldRun_head_at`**   under the head `P5J.AtMgA`, an opening of the
      description, and, with the segment's number and sort, four facts that seat L and p at the segment (hlk · seg ·
      drawB · kp: the premises of the library's `LPFK9.layersOwesC_whole`, `attOwesC_g`, `headOwesC_24`): for every
      reading f with `FieldRests f`: at every yes of every run that the order names, at whatever state, f reads the
      same behind as in front. NO PIN ON THE LOOKUPS' PLACES AND NO PROMISE IS WANTED: the library's structures are
      taken at the promise's free letter Kx := "never", at which their clauses on the promise are empty; what is spent
      bears no promise and stands as it is: the field seg, the ties, the lookups' field k3p, and of the library's
      `Still` the field hands alone (at every yes, with no `Fx9` in front)
  **`bat_leaves_lay`**   at a feed-forward segment: K9's clause at the link's own gatherer ⊢ `setLeaves s s'` ∧
      s'.own? = s.own?
  **`bat_leaves_att`**   at an attention segment: ⊢ `setLeaves s s'`
  **`bat_leaves_head`**   at the head's: ⊢ `setLeaves s s'` ∧ ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x
      = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo
`setLeaves` (Honest/K9/Leaves.lean) holds s'.out = s.out. The letter u : HTailF2 is read by nothing in the
conclusions: a caller lays any value. On a member: the head is met under four premises on the public files, at D :=
dpZ Z and r := theProofRun (asDescriptionFiles Z) alone (the library's `P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it here is shown. The first three are called by
the last three and by Honest/K9/KeepsDecide.lean, the second also by Honest/K9/GoodAtt.lean and GoodAttLook.lean, the
third by GoodHead.lean; the last three by Honest/K9/SeatTied.lean.
WHAT IS NOT CLAIMED. K9's clause at any pair of states (its payers: Honest/K9/Keeps.lean: at the member's step, or at
its decision at one drawn element and no column). The four seating facts at any link. That the four hold at the link
of `SeatedFree`, at which the payers give K9's clause: Honest/K9/SeatTied.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsPaid
import Johnson.LPFK9R.LayersOwesWhole
import Johnson.LPFK9R.OwesAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Look (placeAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {γ : Type} {f : S → γ}

/-- **Run by run, at a feed-forward segment of the description.** -/
theorem fieldRun_lay_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (IM.subAt m) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) (u : HTailF2) (R : FieldRests f) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e := by
  obtain ⟨p4, X, _, _, Wh⟩ := LPFK9.layersOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact fieldRun_layers R (Wh (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) u u
    fun _ hq => hq.elim)

/-- **Run by run, at an attention segment of the description.** -/
theorem fieldRun_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (u : HTailF2) (R : FieldRests f) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e := by
  obtain ⟨A, X, _, _, Wh⟩ := LPFK9.attOwesC_g h O hg hs L p hlk seg drawB kp
  exact fieldRun_att R (Wh (fun _ => False) (((placeAt (P5J.At.X Zp) (2 * g + 1) false).map (·.lm)).getD 0) 0 0 0 u u
    (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl)

/-- **Run by run, at the head's segment of the description.** -/
theorem fieldRun_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (hs : IM.subAt 24 = .head)
    (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk 24 = some L) (seg : SegAt 24 (IM.subAt 24) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) (u : HTailF2) (R : FieldRests f) :
    ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e := by
  obtain ⟨X, _, Wh⟩ := LPFK9.headOwesC_24 h O hs L p hlk seg drawB kp
  exact fieldRun_head R (Wh (fun _ => False) (((placeAt (P5J.At.X Zp) 24 false).map (·.lm)).getD 0) 0 0 0
    (fun _ _ _ => 0) u u (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl)

/-- **What the batching leaves at a feed-forward segment.** -/
theorem bat_leaves_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (IM.subAt m) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) (u : HTailF2) {s s' : S}
    (H : K9Keeps p (claimsInBy L.each L.hear L.order) s s') : setLeaves s s' ∧ s'.own? = s.own? :=
  ⟨H.seven_of fun o ho run hr => fieldRun_lay_at h O m hm hs L p hlk seg drawB kp u rests_seven o ho run hr,
    H.own_of fun o ho run hr => fieldRun_lay_at h O m hm hs L p hlk seg drawB kp u rests_own o ho run hr⟩

/-- **What the batching leaves at an attention segment.** -/
theorem bat_leaves_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (u : HTailF2) {s s' : S}
    (H : K9Keeps p (claimsInBy L.each L.hear L.order) s s') : setLeaves s s' :=
  H.seven_of fun o ho run hr => fieldRun_att_at h O hg hs L p hlk seg drawB kp u rests_seven o ho run hr

/-- **What the batching leaves at the head's segment.** -/
theorem bat_leaves_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (hs : IM.subAt 24 = .head)
    (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk 24 = some L) (seg : SegAt 24 (IM.subAt 24) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) (u : HTailF2) {s s' : S}
    (H : K9Keeps p (claimsInBy L.each L.hear L.order) s s') :
    setLeaves s s' ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo :=
  ⟨H.seven_of fun o ho run hr => fieldRun_head_at h O hs L p hlk seg drawB kp u rests_seven o ho run hr,
    H.head_of fun o ho run hr => fieldRun_head_at h O hs L p hlk seg drawB kp u rests_headOf o ho run hr⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.fieldRun_lay_at
#print axioms ProofFile.Honest.K9.fieldRun_att_at
#print axioms ProofFile.Honest.K9.fieldRun_head_at
#print axioms ProofFile.Honest.K9.bat_leaves_lay
#print axioms ProofFile.Honest.K9.bat_leaves_att
#print axioms ProofFile.Honest.K9.bat_leaves_head
