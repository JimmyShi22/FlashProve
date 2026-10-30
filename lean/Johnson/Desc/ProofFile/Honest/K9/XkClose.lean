-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkClose.lean: FOR "THE FORM BEHIND" AT K9's TWO MEMBERS WITHOUT A ROUND: NO MARK
BEHIND, AND THE PROMISE's FIVE Bools THAT READ THE VERIFIER's STATE, HANDED ON BY EVERY YES OF THE SEATED BLOCK's
STEP, UNDER THE LIBRARY's HEAD AND K9's SEAT (`SeatedClose`, Honest/K9/CloseKeeps.lean), AT ALL 25 SEGMENTS. No
thread, no prover, no string is in this file. Statements and proofs ON THE VERIFIER's TEXT; no goal is stated.
  `mark_behind_eq`, `mark_behind_shut`   behind a yes of either block's step no mark of failure stands (the clauses'
      own)
  **`hands_shut`**, **`xk_behind_shut`**   "the segment is shut": `IM.Hands … (14 l + nAt l + 4 + 2) bS`, all six
      fields, and so XK behind from XK in front: the library's `LPFK9.HandsAt.close2_E`, carried to the seated block,
      its two counts paid by `P5J.k9_counts_at`. NOTHING STAYS
  **`handsPt_eq`**, **`xk_behind_eq`**   "the one equation": `IM.HandsPt … (14 l + nAt l + 4 + 0) bE s`, AT ONE STATE
      IN FRONT, and so XK behind from XK in front: the library's `LPFK9.HandsAt.close0_Pt`, carried to the seated
      block, its test on the plan's numbers paid by `LPFK9.rowsAtFit_at`, its two counts by `P5J.k9_counts_mid`. TWO
      NAMED PREMISES AT THE STATE IN FRONT STAY: hg: the table's number of the segment's group is the field
      check.group of the link's book-keeping in K9's part (the frame's `head_live` ends elsewhere thrice: in
      check.frame.group · at `s.link?`, not at K9's lens · at h.𝔇.N's number, not at `P5J.At.N Zp cF`'s: this third in
      the letter alone: the two are one by unfolding) · hne: no message of the link's own is the index masks' message
      (the library's `OwnNotIndex`). In `handsPt_eq` both are asked as the library's own lemma asks them: where s
      bears no mark and XK holds at s; in `xk_behind_eq`, where these two are in the caller's hand, outright. THEY ARE
      A FIFTH AND A SIXTH beside the four premises in front that the frame allows (no mark · XK ·
      samplesHeld · pubP)
E IS THE PROMISE's PUBLIC TEST (`EW`), as in Honest/K9/XkBat.lean.
WHO PAYS THE TWO: Honest/K9/XkEqReach.lean, under the head, from the library's raw "reached" at that border (at the
first tree 0), no mark and XK in front: `hg_of_reach` (the library's `LPFK9.HandsAt.grp_reached`; "the table's number
of group l is l" holds by unfolding) · `hne_of_reach` (the library's `ownNotIndex_reached` at the frame's
`foldFacts_raw`, with `AtMg.notIx`; the index masks' number off the public item "indexIs" in XK in front). "Reached"
at any state: shown there of none; at the frame's thread, from its stand: `xk_eq_thr`.
WHAT IS NOT CLAIMED. That a yes is there. XK at any state. hg or hne at any state. `samplesHeld`
(Honest/K9/XkSamples.lean). pubP. No member. `hands_shut`, `handsPt_eq`: called here alone; the two marks here and by
Honest/K9/XkAtHead.lean; the two `xk_behind_…` by that file alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.XkBat
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.LPFK9R.SharesPt
import Johnson.LPFK9R.RowsAtFitAt
import Johnson.P5J.K09CountsMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open LPFK9.HandsAt (EW close2_E close0_Pt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- No mark behind a yes of "the one equation". -/
theorem mark_behind_eq {c : Chain S Claim} {Zq : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {Q : Close.Par} {bE bS : Block S Claim} (H : SeatedClose c Zq l Lk p Q bE bS) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft bE s s') : s'.failed = none := by
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact (H.eqKeeps ft s s' rs cols n hstep).mark

/-- No mark behind a yes of "the segment is shut". -/
theorem mark_behind_shut {c : Chain S Claim} {Zq : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {Q : Close.Par} {bE bS : Block S Claim} (H : SeatedClose c Zq l Lk p Q bE bS) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft bS s s') : s'.failed = none := by
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact (H.shutKeeps ft s s' rs cols n hstep).mark

/-- **"The segment is shut" hands the promise's five Bools on.** -/
theorem hands_shut (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S ProofFile.Cl} (H : SeatedClose cF Zp l Lk p Q bE bS)
    {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) :
    IM.Hands (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) ft (14 * l + IM.nAt l + 4 + 2) bS := by
  have C := (P5J.k9_counts_at h l hl).2
  rw [batch_number l hl, P1K2.ps_written] at C
  have e : 14 * l + IM.nAt l + 2 + 4 = 14 * l + IM.nAt l + 4 + 2 := by omega
  rw [e] at C
  exact (close2_E h.𝔇.pubD base z hb hl p Q C.1 C.2 _ rfl).under (IM.alone_underR H.aloneS)

/-- **XK behind the yes of "the segment is shut", from XK in front.** -/
theorem xk_behind_shut (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S ProofFile.Cl}
    (H : SeatedClose cF Zp l Lk p Q bE bS) {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) {s s' : S} (hy : IM.Yes ft bS s s')
    (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 2) s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 2 + 1) s' = true :=
  ((hands_shut h hl H base z hb ft).fenced (Fk := fun _ _ => True)).step trivial hy h0
    (mark_behind_shut H ft hy) hx

/-- **"The one equation" hands the promise's five Bools on, at one state in front.** -/
theorem handsPt_eq (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S ProofFile.Cl} (H : SeatedClose cF Zp l Lk p Q bE bS)
    {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) (s : S)
    (hg : s.failed = none → ∀ a,
      IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0) s = true →
      Desc.K9.atS.get? s = some a → (P5J.At.N Zp cF).groupAt l = a.L.check.group)
    (hne : s.failed = none →
      IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0) s = true →
      LinkJoin.OwnNotIndex s) :
    IM.HandsPt (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) ft (14 * l + IM.nAt l + 4 + 0) bE s := by
  have C := (P5J.k9_counts_mid h l hl).2
  rw [batch_number l hl, P1K2.ps_written] at C
  have e : 14 * l + IM.nAt l + 2 + 1 + 1 = 14 * l + IM.nAt l + 4 + 0 := by omega
  rw [e] at C
  exact (close0_Pt h.𝔇.pubD base z hb hl (LPFK9.rowsAtFit_at h) p Q C.1 C.2 s hg hne _ rfl).under
    (IM.alone_underR H.aloneE)

/-- **XK behind the yes of "the one equation", from XK in front.** -/
theorem xk_behind_eq (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S ProofFile.Cl}
    (H : SeatedClose cF Zp l Lk p Q bE bS) {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft bE s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0) s = true)
    (hg : ∀ a, Desc.K9.atS.get? s = some a → (P5J.At.N Zp cF).groupAt l = a.L.check.group)
    (hne : LinkJoin.OwnNotIndex s) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0 + 1) s' = true :=
  ((IM.handsR_iff_pt (Fk := fun _ t => t = s)).2 fun t ht => by
    subst ht
    exact handsPt_eq h hl H base z hb ft _ (fun _ a _ ha => hg a ha) fun _ _ => hne).step rfl hy h0
      (mark_behind_eq H ft hy) hx

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.mark_behind_eq
#print axioms ProofFile.Honest.K9.mark_behind_shut
#print axioms ProofFile.Honest.K9.hands_shut
#print axioms ProofFile.Honest.K9.xk_behind_shut
#print axioms ProofFile.Honest.K9.handsPt_eq
#print axioms ProofFile.Honest.K9.xk_behind_eq
