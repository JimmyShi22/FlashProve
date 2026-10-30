-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.YesHolds
import Johnson.Desc.K12.Law.BatValsPay
import Johnson.Desc.K12.Law.FitsLen
import Johnson.Desc.K12.Law.PayPub
import Johnson.Desc.K12.Law.BatOneLaw
import Johnson.Desc.K12.Law.TupleValsOn
import Johnson.Desc.K12.Law.BatPriceLaw
import OnBytes.Flat.RoundsT
/-
Johnson/Desc/K12/Law/BatValsPayAt.lean: THE PAYER OF THE BATCHING's CONVERSE (BatVals | BatAtN | BatAtY of the law of the proximity test in the plain form, at N := NTuple), WITH WHAT IT ASKS CUT DOWN: the number is the PLAN's; the layout's four numbers come off the piece's yes; the public half comes off tests with code. BESIDE BatValsPay.lean (NTuple is its). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  PayRec        WHAT IS ASKED OF THE RECORD IN FRONT, at whatever it fixes: ONE THING: combineAt at the statement behind the beginning (a test with code: the group is in order, every batched row lies within it). As one test no guard of the block asks it; the front asks rowL of every open claim and three of groupOkB's four clauses: whether a yes gives combineAt (the sample rows; the twin texts; behind the beginning) is not typed: until then a table's promise
  PayNum        the layout's four numbers are the first stage's: asked by batVals_pay_pub | batAtN_pay_pub; SPARED at BatAtY
  yes_lens      where the piece says yes: PayNum: by k12_lens (FitsLen.lean: the frame's guard firstFits and the plan's sizesOk), walked as the sheet's yes_fits walks
  batVals_pay_pub   PayPub at dB.entry.rows (PayPub.lean: StageJ at the radius · lstJ (radius) * (rows − 1) ≤ v₀: A NUMBER OF PLAN AND CODES ALONE) · PayRec · PayNum · "BAT"'s round draws one element and nothing else ⇒ BatVals F π no rad rd dB v₀ (NTuple …) x
  batAtN_pay_pub    … · logN ≤ 64 ⇒ BatAtN at e₀ := v₀ * w
  batAtY_pay_yes    early · planOk · PayPub · PayRec · the draws · logN ≤ 64 ⇒ BatAtY at that e₀: by cases: where no challenge behind m has a yes the counted set is empty; else yes_lens pays PayNum
  batAtY_pay_like   early · planOk · the stretch's rounds are like the plan's written rounds (three fields that both arms' places hold) · the radius letter is r · johOk π r · batOneOk π (two tests with code on the plan) · PayRec ⇒ BatAtY at e₀ := batV0 π r * w: the number is batV0 (BatPriceOk.lean), which has code
  batAtY_pay_at | batAtY_pay_atO   the same at AtPlace | at AtPlaceOwn (the own mask's arm): one call each
  batBelow_like     the plan's first stage stands · the likeness · batPriceOk π r k = true ⇒ RoundBelow (batV0 π r) (toRD dB) (2⁻¹ ^ k): the library's comparison AT THE COIN's OWN ROUND: that round's verifier messages are (wRound (toRD dB)).Chal by the library's chal_eq (OnBytes/Flat/RoundsT.lean)
  NOn · PayOn · batVals_pay_on | batAtN_pay_on | batAtY_pay_on   THE COUSIN AT A SECOND LETTER: N := NOn: tuple_on_or_few's first arm (OnAt, TupleValsOn.lean) at the written oracles W0 F no D.book x.2 and radii e0s a member: «one tuple of candidates, one message a member, of whose words all the batched rows hold»: under PayOn more (siteL's yes at every member · at every member a message with sampleL's yes · the radius below the fence of e0s). It is the letter «eitherArm» of Johnson/Flat/Last/RowTwoPays.lean [not in this library] at dM D i := (W0 F no D.book y (D.mems.get i).t).1, which hangs on no y, and os D y i := (W0 …).2: THAT TIE IS NOT TYPED HERE
WHAT STANDS AGAINST IT: (1) PayRec IS A PREMISE; johOk's and batOneOk's yes are runs' words (true at the four proximity tests of both stored proofs; johOk false at the tiny proof at the radii that the prices need) · (2) that e₀ is small against the number of "BAT"'s verifier messages is batPriceOk's comparison: a run's (its law: batBelow_like) · (3) NTuple IS NOT NearAll · (4) which arm holds no program can choose.

(Where this and lean/THEOREM.md differ,
the page holds.)
No sorry, no axiom of ours; each theorem has its premises;
what each rests on is asked at the file's end.
-/
set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open OnBytes.Means
open Iop Prob _root_.Run Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Coin
open H2K.JointK (yOf Blk' k12_lens first_sizes bat_front)
open H2K.Pub (sgOf PayPub payPub_of_joh johOk batV0 writtenOf batPriceOk batBelow_of_ok roundBelow_like)
open OnBytes.Flat (toRD)
open scoped ENNReal
open H2K.First (gpL Plain good_of_ok batOneOk batOne_of_ok)

/-- What is asked of a record in front of the block, at whatever the record fixes. -/
def PayRec (π : P12) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true

/-- The layout's four numbers are the first stage's. -/
def PayNum (π : P12) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l

/-- Where the piece says yes, the layout's four numbers are the first stage's. -/
theorem yes_lens {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) : PayNum π x.1 := by
  intro a rest G0 Ly D hf
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨first, rest', e, r, row, L, S', e1, hbat, h1, h2, h3, h4⟩ :=
    k12_lens π he x.1 b.1 _ _ hp hdec
  obtain ⟨G1, _, g2, _⟩ := bat_front _ _ _ _ _ _ _ hbat
  obtain ⟨rfl, _⟩ := List.cons.inj (e1.symm.trans hf.1)
  obtain rfl := Option.some.inj (g2.symm.trans hf.2.2.1)
  obtain ⟨_, _, hhk⟩ := first_sizes guardedProximityTestParts π hp first rest' e1
  refine ⟨?_, h2, h3, h4⟩
  show L.k = first.h + (first.k - first.h)
  rw [h1]
  omega


theorem batVals_pay_pub (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (x : T12 × F.E.Str) (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1)
    (hN : PayNum π x.1) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) :
    BatVals F π no rad rd dB v₀ (NTuple F π no rad rd) x := by
  intro a rest G0 Ly D row₀ hok hf m
  obtain ⟨hJ, hv⟩ := hP a rest hf.1
  have ht := hR a rest G0 Ly D hf
  obtain ⟨hk, hh, hl, hz⟩ := hN a rest G0 Ly D hf
  rcases bat_vals_yOf_rows π x.1 a G0 Ly D row₀ hok hf.2.1 hf.2.2.1 (hf.2.2.2 row₀) rd
    (W0 F no D.book x.2) (rad (sgOf a)) hJ ht hk hh hl hz dB.entry dB.kind h1 with hT | hC
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro v ⟨_, _, _, _, hn⟩
      exact hn ⟨row₀, hok, hT⟩
  · refine le_trans (cnt_mono ?_)
      ((hC (PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) m.2))).trans hv)
    rintro v ⟨row, w, hb, hr, _⟩
    exact ⟨row, w, hb, hr⟩

theorem batAtN_pay_pub (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (x : T12 × F.E.Str) (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1)
    (hN : PayNum π x.1) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) :
    BatAtN F π no rad rd dB (v₀ * (bsRound .two dB.entry dB.kind).w) (NTuple F π no rad rd) x :=
  batAtN_of_vals F π no rad rd dB v₀ _ x hlog
    (batVals_pay_pub F π no rad rd dB v₀ x hP hR hN h1)


theorem batAtY_pay_yes (F : Frame) (W : Type) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (x : T12 × F.E.Str) (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    BatAtY F W π no rad rd base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt
      (NTuple F π no rad rd) x := by
  intro a rest G0 Ly D row₀ hok hf m
  by_cases hy : ∃ (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) dt))
      (b : T12 × F.E.Str),
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.out x
        (m, c, τ) = some b
  · obtain ⟨c, τ, b, hb⟩ := hy
    have hN : PayNum π x.1 := yes_lens F π he hp base dB dt _ εt x (m, c, τ) b hb
    exact batAtY_of_N F W π no rad rd base dB dt _ εt _ x
      (batAtN_pay_pub F π no rad rd dB v₀ x hP hR hN h1 hlog) a rest G0 Ly D row₀ hok hf m
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro c ⟨⟨τ, b, hb⟩, _⟩
      exact hy ⟨c, τ, b, hb⟩

/-- What both arms' places hold is enough: early masks, the plan's test, rounds like the plan's. -/
theorem batAtY_pay_like (F : Frame) (W : Type) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l))
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) (x : T12 × F.E.Str) (hR : PayRec π x.1) :
    BatAtY F W π no rad rd base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt
      (NTuple F π no rad rd) x := by
  obtain ⟨w0, l, hw, hlike⟩ := hl
  cases hlike with
  | cons hB _ =>
    obtain ⟨h1, hlog⟩ := batOne_of_ok π w0 l hw hb1
    have hP := payPub_of_joh π r rad hr hj w0 l hw
    have hen : dB.entry = w0.entry := hB.1
    have hkd : dB.kind = w0.kind := hB.2.1
    exact batAtY_pay_yes F W π he hp no rad rd base dB dt _ εt x
      (by rw [hen]; exact hP) hR (by rw [hen, hkd]; exact h1) (by rw [hen]; exact hlog)

/-- At a place of the first arm. -/
theorem batAtY_pay_at (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (εt : Err (uLT (ckP .two) dt)) (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) (x : T12 × F.E.Str) (hR : PayRec π x.1) :
    BatAtY F W π no rad rd base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt
      (NTuple F π no rad rd) x :=
  batAtY_pay_like F W π hA.early hA.planOk no rad rd base dB dt εt hA.like r hr hj hb1 x hR

/-- At a place of the own mask's arm. -/
theorem batAtY_pay_atO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (εt : Err (uLT (ckP .two) dt)) (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) (x : T12 × F.E.Str) (hR : PayRec π x.1) :
    BatAtY F W π no rad rd base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt
      (NTuple F π no rad rd) x :=
  batAtY_pay_like F W π hA.early hA.planOk no rad rd base dB dt εt hA.like r hr hj hb1 x hR

/-- The number's law at the coin's own round. -/
theorem batBelow_like (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: rest) (dB : RDT) (dt : List RDT)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l))
    (h : batPriceOk π r k = true) :
    RoundBelow (batV0 π r) (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨w0, l, hw, hlike⟩ := hl
  cases hlike with
  | cons hB _ =>
    exact roundBelow_like _ (toRD dB) w0.rd _ hB.1 hB.2.1 (batBelow_of_ok π r k a rest hs w0 l hw h)

/-- A second letter: tuple_on_or_few's first arm at the statement's own oracles. -/
def NOn (F : Frame) (no : ℕ → ℕ) (e0s : (D : Plain) → Fin D.mems.length → ℕ) : ConclK F :=
  fun x _ _ G0 _ D =>
    OnAt (begun x.1.st x.1.g G0) x.1.st G0 D (e0s D)
      (fun i => (W0 F no D.book x.2 (D.mems.get i).t).1)
      (fun i => (W0 F no D.book x.2 (D.mems.get i).t).2)

/-- What the second letter asks more, at whatever the record fixes. -/
def PayOn (π : P12) (rad : Sg → ℕ) (e0s : (D : Plain) → Fin D.mems.length → ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    (∀ j : Fin D.mems.length, ok (siteL D.st.codes a (D.mems.get j)) = true) ∧
    (∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      ok (sampleL D.st.codes (D.mems.get j) x) = true) ∧
    ∀ j : Fin D.mems.length,
      rad (sgOf a) < (e0s D j + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh)

theorem batVals_pay_on (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (e0s : (D : Plain) → Fin D.mems.length → ℕ) (x : T12 × F.E.Str)
    (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1) (hN : PayNum π x.1)
    (hO : PayOn π rad e0s x.1) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) :
    BatVals F π no rad rd dB v₀ (NOn F no e0s) x := by
  intro a rest G0 Ly D row₀ hok hf m
  obtain ⟨hJ, hv⟩ := hP a rest hf.1
  have ht := hR a rest G0 Ly D hf
  obtain ⟨hk, hh, hl, hz⟩ := hN a rest G0 Ly D hf
  obtain ⟨hS, hQ, hfit⟩ := hO a rest G0 Ly D hf
  rcases bat_vals_on π x.1 a G0 Ly D row₀ hok hf.2.1 hf.2.2.1 (hf.2.2.2 row₀) rd
    (W0 F no D.book x.2) (rad (sgOf a)) hJ ht hk hh hl hz dB.entry dB.kind h1 (e0s D) hS hQ hfit
    with hT | hC
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro v ⟨_, _, _, _, hn⟩
      exact hn hT
  · refine le_trans (cnt_mono ?_)
      ((hC (PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) m.2))).trans hv)
    rintro v ⟨row, w, hb, hr, _⟩
    exact ⟨row, w, hb, hr⟩

theorem batAtN_pay_on (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
    (v₀ : ℕ) (e0s : (D : Plain) → Fin D.mems.length → ℕ) (x : T12 × F.E.Str)
    (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1) (hN : PayNum π x.1)
    (hO : PayOn π rad e0s x.1) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) :
    BatAtN F π no rad rd dB (v₀ * (bsRound .two dB.entry dB.kind).w) (NOn F no e0s) x :=
  batAtN_of_vals F π no rad rd dB v₀ _ x hlog
    (batVals_pay_on F π no rad rd dB v₀ e0s x hP hR hN hO h1)


theorem batAtY_pay_on (F : Frame) (W : Type) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (e0s : (D : Plain) → Fin D.mems.length → ℕ) (x : T12 × F.E.Str)
    (hP : PayPub π rad dB.entry.rows v₀) (hR : PayRec π x.1) (hO : PayOn π rad e0s x.1)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    BatAtY F W π no rad rd base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt
      (NOn F no e0s) x := by
  intro a rest G0 Ly D row₀ hok hf m
  by_cases hy : ∃ (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) dt))
      (b : T12 × F.E.Str),
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.out x
        (m, c, τ) = some b
  · obtain ⟨c, τ, b, hb⟩ := hy
    have hN : PayNum π x.1 := yes_lens F π he hp base dB dt _ εt x (m, c, τ) b hb
    exact batAtY_of_N F W π no rad rd base dB dt _ εt _ x
      (batAtN_pay_on F π no rad rd dB v₀ e0s x hP hR hN hO h1 hlog) a rest G0 Ly D row₀ hok hf m
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro c ⟨⟨τ, b, hb⟩, _⟩
      exact hy ⟨c, τ, b, hb⟩

end H2K.Pin

#print axioms H2K.Pin.yes_lens
#print axioms H2K.Pin.batVals_pay_pub
#print axioms H2K.Pin.batAtN_pay_pub
#print axioms H2K.Pin.batAtY_pay_yes
#print axioms H2K.Pin.batAtY_pay_like
#print axioms H2K.Pin.batAtY_pay_at
#print axioms H2K.Pin.batAtY_pay_atO
#print axioms H2K.Pin.batBelow_like
#print axioms H2K.Pin.batVals_pay_on
#print axioms H2K.Pin.batAtN_pay_on
#print axioms H2K.Pin.batAtY_pay_on
