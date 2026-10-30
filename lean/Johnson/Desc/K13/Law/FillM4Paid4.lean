-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillM4Paid4.lean: WHAT THE TIE AT W's COMMITMENT ASKS OF THE TABLE's LETTERS
(`FillM4`, Johnson/Desc/K13/Law/AtTableW.lean), AT FillM3Paid4.lean's DOOR, WITH LEMMAS
CALLED BY NAME. Statements with their proofs.
  `atM4_oneRow`: W's commitment keeps "K13.oneRow": the chain stood, and stands, at its end, and the
  rows on the table stay.
  `rider4_oneRow`, `rider4_pileWithin`: the two new items are riders at that block; the second FROM
  `OwedWithinM4` (OwedWithin.lean).
  `fillM4_paid4`: **`FillM4` at any list Q of riders** that holds the four of `knownK13`, and beside
  them at most `frontOk`, "K13.weightsOk", "K13.pileWithin", "K13.oneRow". CALLED BY NAME:
  `fillM4_of` · `others4_at_sig` (Others4AtSig.lean) · `weightsKeeps`
  (RidersWeights.lean) · the riders of FillFromSentences.lean, RidersK12.lean,
  PileMasks.lean · `rider4_kept` (FillM4At.lean). ITS PREMISES: what the letters of Mg say
  (`FillsK13` at the place's code table; Mg at "K13.weightsOk") · tests on the plan (`PlanM3`,
  `PlanM4` at first tree 0, the joined block's own `planOk`) · which items are in Q · `OwedWithinM4`
  (OWED) · `SmpOld N p ms smp` · `DecBlind decT` · what other layers say of "in order" rides.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillM3Paid4
import Johnson.Desc.K13.Law.FillM4At
import Johnson.Desc.K13.Law.Others4AtSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame bookStepB)
open VerifiableInference.Desc.K12.Door (toTree)

/-- At the chain's end the item's test is the test on the rows. -/
theorem oneRowC_end (t : S) (b : First.MemOwn) (hb : t.here = .mem b) :
    oneRowC t = (match t.rows with
      | [r] => !r.masks.isEmpty
      | _ => false) := by
  unfold oneRowC
  rw [hb]
  rfl

section
variable {Pp W Cl : Type}

/-- W's commitment keeps "K13.oneRow". -/
theorem atM4_oneRow {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (h0 : oneRowC s = true) : oneRowC s' = true := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨a, ids, ha, _⟩ := K1.sendAtS_here P' s s₁ _ g₁ h1
  obtain ⟨⟨o, ho⟩, _, _, _, hrows⟩ := atM4_rec h
  rw [oneRowC_end s a ha] at h0
  rw [oneRowC_end s' o ho, hrows]
  exact h0

theorem rider4_oneRow {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub}
    {p : Option Place} (hm : oneRowItem ∈ Q) (hM : ∀ x, Mg.pub oneRowItem x = oneRowC x.2)
    (hP : ∀ x, Mg.pubP oneRowItem x) : Rider4 Cl P P' N Mg Q p oneRowItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hM] at h0
  exact ⟨by rw [hM]; exact atM4_oneRow hd h0, fun _ => hP x'⟩

theorem rider4_pileWithin {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {Q : List Pub} {p : Option Place} (hO : OwedWithinM4) (hm : pileWithinItem ∈ Q)
    (hM : ∀ x, Mg.pub pileWithinItem x = pileWithinC x.2) (hP : ∀ x, Mg.pubP pileWithinItem x) :
    Rider4 Cl P P' N Mg Q p pileWithinItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hM] at h0
  exact ⟨by rw [hM]; exact hO P P' x.2 x'.2 r₁ r₂ gs hd h0, fun _ => hP x'⟩

end

/-- **`FillM4` at the door with the two items more, with what was compiled called by name.** -/
theorem fillM4_paid4 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {F : Frame} (y₀ : F.E.Str) {P : Where}
    {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)}
    {sh : Params.ReqShape} {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf P'.codes s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub) (p : Option Place)
    (hF : FillsK13 P N Mg P'.codes sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hPl : PlanM3 L M ms P'.codes N) (h4 : PlanM4 0 L M N p P')
    (hplan : (atM4 (Cl := Cl) P (K1.sendAtS P')).planOk = true)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem ∨ q = pileWithinItem ∨
      q = oneRowItem)
    (hIn : ∀ q ∈ knownK13, q ∈ Q) (hO : OwedWithinM4) (hsmp : SmpOld N p ms smp)
    (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM4 Cl P P' x x' → rest x = true → rest x' = true) :
    FillM4 Cl P P' N Mg Q p := by
  have hMg := mgK13_of_fills hF
  have hB : ∀ x, Mg.pub bookItem x = bookStepB P'.gp.firstTree x.2.book x.2.roots := fun x =>
    (hMg.book x).trans (congrArg (fun ft => bookStepB ft x.2.book x.2.roots) h4.hft)
  refine fillM4_of Q p hMg.ours
    (others4_at_sig P P' arr mat N Mg Q p P'.codes G smp ms decT L hMg.sig
      (hIn _ (by simp [knownK13])) (hIn _ (by simp [knownK13])) hMg.masks hMg.seats
      (fun x h => by rw [hMg.ours.indexThere] at h; exact h) (planK13_of hPl).below hsmp hdec)
    hrest hplan fun q hq => ?_
  rcases hQ q hq with hk | rfl | rfl | rfl | rfl
  · have hP := hMg.quiet q hk
    simp only [knownK13, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact rider4_book hq hB hP
    · exact rider4_seats (L := toTree L) hq hMg.seats hP h4.hp h4.hs
    · exact rider4_shapes hq hMg.shapes hP h4.hx
    · exact rider4_pileMasks hq hMg.masks hP
  · exact rider4_frontOk y₀ hMg.ours hq
  · exact rider4_kept hq weightsKeeps hW hWP
  · exact rider4_pileWithin hO hq hF.within (hF.quiet _ (by simp [quietK13]))
  · exact rider4_oneRow hq hF.oneRow (hF.quiet _ (by simp [quietK13]))

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.atM4_oneRow
#print axioms VerifiableInference.Desc.K13.Law.fillM4_paid4
