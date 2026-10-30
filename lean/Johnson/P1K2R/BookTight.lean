-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/BookTight.lean: code switching (K2): THE BOOK's SIDE: THE BINDERS hBook AND
hOld OF K2AllOwes (Johnson/Top/H0/K2Ties/Assembly.lean; the same binders of K2Caller/TieOneR.lean |
TieFourR.lean) AT EACH OF THE 25 PLACES, IN THE TIGHT FORM AND ON NAMED TESTS ALONE.
  keeps_id · keeps_fin  the two ways in of HT1Tight.lean leave the book and the count of roots
  noMark_switch  a state reached at one of the 25 switches' numbers bears no mark
  hBook_tight  hBook at a switch's number k, from THREE FIELDS OF FoldFacts (bookInOrder ·
               seatsCarried · bookFits) at an Rch that holds reached states alone
  hBook_plain  hBook with no field of FoldFacts: bookInOrder and bookFits by atFirstBook_all |
               atFirstFits_all (Johnson/IMR/AtReach.lean; from the tests on the plan alone);
               seatsCarried by seatsCarried_field (Johnson/IMR/SeatsField.lean; hB · hLd)
  keptAt_row   the written entry's kept members fit the written front's frame (a closed fact)
  hOld_of_hT1  hOld from hT1's end at the same letters
  hOld_link · hOld_head · hOld_fin  hOld in the tight form: over hT1_link | hT1_head | hT1_fin
  hOld_link_plain · hOld_head_plain · hOld_fin_plain  the same over hT1_…_plain
WHICH NUMBERS. IsSwitchNo k: k = 14 (m + 1) + 2 with m < 23, or 339, or 353.
WHAT STANDS IN FRONT, BY NAME.
  hBook_tight: hS · hR · O · hRch (what Rch holds is reached) · the three fields, in their own
      letters at at_ := (·.1), d.ft := ft, d.L := L · hE: the way in leaves the book and the count
      of roots · hFt: the place's first tree is ft.
  hBook_plain: hS · hR · O · hpl · hRch · hB: sendsAreB accepts · hLd: laidAtCodes names L · hE ·
      hFt at ft := 0 (ft_at_switch pays it at q := ProofFile.pAtK2 Z m; not called here).
  hOld_…: what hT1_… has in front, and THE PROMISE IN FRONT (onQ …): hOld SPENDS IT: «the book has
      as many places as the statement has oracle messages» comes from it
      (old_of_front over places_of_promise).
NOT SPENT OF THE BINDERS' OWN PREMISES, AND LEFT OUT: «the state bears no mark», in all; the promise
in front, in hBook.
SO TO THE ROW's QUESTION: bookInOrder AND bookFits HAVE A THEOREM: Meaning.K2.bookInOrder_field |
bookFits_field (Johnson/IMR/AtReach.lean): from the opening and the
sub-protocols' tests on the plan, at d.ft := 0.
LIMITS. Joins: every step is a call. No premise is shown met at a real value: no example. hOld's end
says nothing at a state of which the switch's text makes no front. The full size alone. No
probability; no soundness is claimed.
-/
import Johnson.P1K2R.HT1Plain
import Johnson.Top.H0.K2Caller.KeptMembersInBookAtFront
import Johnson.Top.H0.K2Caller.TieOneR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below onQ Frame)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit DoorKeepsBook tests_same
  old_of_front keptK2 plainHd keptAt_renumber)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB laidAtCodes Laid atFirstBook atFirstSeats
  atFirstFits)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt storedB hx_of front_tests_full)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

/-- The numbers of the 25 code switches in the first chain's flat list. -/
def IsSwitchNo (k : ℕ) : Prop := (∃ m, m < 23 ∧ k = 14 * (m + 1) + 2) ∨ k = 339 ∨ k = 353

/-- The way in that lets a state in as it is leaves the book and the count of roots. -/
theorem keeps_id {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) :
    DoorKeepsBook enter := fun s t h => by
  obtain rfl := hent s t h
  exact ⟨rfl, rfl⟩

/-- So does the finish's. -/
theorem keeps_fin {enter : S → Except String S}
    (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t) : DoorKeepsBook enter :=
  fun s t h => ⟨(K2.finishFrontQ_rest (hent s t h)).1, (K2.finishFrontQ_rest (hent s t h)).2.1⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Str : Type}
  {Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop}

/-- A state reached at a switch's number bears no mark. -/
theorem noMark_switch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : IsSwitchNo k)
    {z : ProofFile.InstPub} {t : S} (ht : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, t)) :
    t.failed = none := by
  refine IM.noMark_reach_below hS hR O ht ?_ fun l _ => ?_
  · rcases hk with ⟨m, -, rfl⟩ | rfl | rfl <;> omega
  · unfold IM.nAt
    rcases hk with ⟨m, -, rfl⟩ | rfl | rfl <;> split <;> omega

/-- **hBook IN THE TIGHT FORM**, at a switch's number. -/
theorem hBook_tight (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1) {ft : ℕ} {L : Laid}
    (bookInOrder : ∀ k x, Rch k x → x.1.2.failed = none → atFirstBook ft x.1.2 = true)
    (seatsCarried : ∀ k x, Rch k x → x.1.2.failed = none → atFirstSeats L x.1.2 = true)
    (bookFits : ∀ k x, Rch k x → x.1.2.failed = none → atFirstFits x.1.2 = true)
    {k : ℕ} (hk : IsSwitchNo k) {enter : S → Except String S} (hE : DoorKeepsBook enter) {q : K2.P2}
    (hFt : (K2.par9 q).firstTree = ft) :
    ∀ z, ∀ a : S × Str, Rch k ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      atFirstBook (K2.par9 q).firstTree t = true ∧ atFirstSeats L t = true ∧
        atFirstFits t = true := by
  intro z a ha t he
  have hu := noMark_switch hS hR O hk (hRch _ _ ha)
  obtain ⟨eb, er⟩ := hE _ _ he
  obtain ⟨e1, e2, e3⟩ := tests_same ft L eb er
  rw [hFt]
  exact ⟨e1.trans (bookInOrder _ _ ha hu), e2.trans (seatsCarried _ _ ha hu),
    e3.trans (bookFits _ _ ha hu)⟩

/-- **hBook WITH NO FIELD OF FoldFacts.** -/
theorem hBook_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) {L : Laid}
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some L)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {k : ℕ} (hk : IsSwitchNo k) {enter : S → Except String S} (hE : DoorKeepsBook enter) {q : K2.P2}
    (hFt : (K2.par9 q).firstTree = 0) :
    ∀ z, ∀ a : S × Str, Rch k ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      atFirstBook (K2.par9 q).firstTree t = true ∧ atFirstSeats L t = true ∧
        atFirstFits t = true :=
  hBook_tight hS hR O hRch
    (Meaning.K2.bookInOrder_field O (plan_of O hpl) Rch (fun x => x.1)
      fun k x h => reach_raw (hRch k x h))
    (IM.seatsCarried_field hS hR O Rch (fun x => x.1)
      (fun k x h => by
        obtain ⟨-, rs, cols, f⟩ := (reach_raw (hRch k x h)).fold
        exact ⟨rs, cols, [], [], f⟩) hpl hB hLd)
    (Meaning.K2.bookFits_field O (plan_of O hpl) Rch (fun x => x.1)
      fun k x h => reach_raw (hRch k x h))
    hk hE hFt

end

/-- The written entry's kept members fit the written front's frame. -/
theorem keptAt_row {i : ℕ} {r : SwRow} {W : SwitchFrame} (h : tableFullLit[i]? = some r)
    (hW : K2.frameAt (fxAt r) = some W) : r.keptAt W = true := by
  obtain ⟨W', hW', -, -, -, hk, -, -⟩ := front_tests_full (List.mem_of_getElem? h)
  obtain rfl : W' = W := Option.some.inj (hW'.symm.trans hW)
  exact hk

section
variable {Fr : Frame} {Wt : Type} (N : Numbers) (Mg : Meaning ProofFile.InstPub Wt) (links : List ModelPart)
  (ps : List Place)
  {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}

/-- **hOld FROM hT1's END, at the same letters.** hu: «no mark» at what Rch holds at k. -/
theorem hOld_of_hT1 {k : ℕ} {enter : S → Except String S} (hE : DoorKeepsBook enter) {q : K2.P2}
    {r : SwRow} (h : r.ok = true) {W : SwitchFrame} (hkA : r.keptAt W = true)
    {f₀ : _root_.Tw.K2.Front} {grp rows n0 : ℕ} {olds : List ℕ}
    (hu : ∀ z, ∀ a : S × Fr.E.Str, Rch k ((z, a.1), a.2) → a.1.failed = none)
    (hT1 : ∀ z, ∀ a : S × Fr.E.Str, Rch k ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
        K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true ∧
        a.1.st.oracles = fx.st.oracles) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old < t.book.place.size := by
  intro z a ha hr t he fx hfx κ
  obtain ⟨-, -, -, hSt, hor⟩ := hT1 z a hr t he fx hfx
  have hk' : r.keptAt (placeFrame W n0 olds) = true := (keptAt_renumber r W _ _ _).trans hkA
  obtain ⟨xo, hmsg, -⟩ := hx_of hk' hSt ⟨⟨κ.1.1, κ.2.fst⟩, κ.2.snd⟩
  exact old_of_front N Mg links ps k z enter hE a ha (not_not.2 (hu z a hr)) he hor hmsg

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {Fr : Frame} {Wt : Type} (N : Numbers) (Mg : Meaning ProofFile.InstPub Wt) (links : List ModelPart)
  (ps : List Place)
  {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}

/-! ## hOld in the tight form: over hT1_link | hT1_head | hT1_fin -/

theorem hOld_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {m : ℕ} (h23 : m < 23)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .link) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[m]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (14 * (m + 1) + 2) a →
      Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_id hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inl ⟨m, h23, rfl⟩) ((hRch _ _).1 ha))
    (hT1_link hS hR O hF hpl hy hcut hRch msgShapes h23 hent hq hrw h0f)

theorem hOld_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .head) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[23]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (339) a →
      Rch (339) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At 24) (K2.oldsAt 24)) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_id hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inr (Or.inl rfl)) ((hRch _ _).1 ha))
    (hT1_head hS hR O hF hpl hy hcut hRch msgShapes hent hq hrw h0f)

theorem hOld_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hRch : ∀ k x, Rch k x ↔ Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (msgShapes : ∀ k x, Rch k x → x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)
    {q : K2.P2}
    (hq : q.stands = .finish) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[24]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (353) a →
      Rch (353) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At 25) (K2.oldsAt 25)) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_fin hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inr (Or.inr rfl)) ((hRch _ _).1 ha))
    (hT1_fin hS hR O hF hpl hy hcut hRch msgShapes hent hq hrw h0f)

/-! ## hOld with no field of FoldFacts: over hT1_link_plain | hT1_head_plain | hT1_fin_plain -/

theorem hOld_link_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {m : ℕ} (h23 : m < 23)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .link) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[m]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (14 * (m + 1) + 2) a →
      Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_id hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inl ⟨m, h23, rfl⟩) (hRch _ _ ha))
    (hT1_link_plain hS hR O hF hpl hy hcut hB hRch h23 hent hq hrw h0f)

theorem hOld_head_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .head) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[23]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (339) a →
      Rch (339) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At 24) (K2.oldsAt 24)) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_id hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inr (Or.inl rfl)) (hRch _ _ ha))
    (hT1_head_plain hS hR O hF hpl hy hcut hB hRch hent hq hrw h0f)

theorem hOld_fin_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)
    {q : K2.P2}
    (hq : q.stands = .finish) {r : SwRow} (h : r.ok = true) (hrw : tableFullLit[24]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Fr.E.Str, onQ N Mg links ps (fun s => (z, s)) (353) a →
      Rch (353) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt q t = some fx →
      ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        (keptK2 r (r.ok_says h) (placeFrame W (K2.n0At 25) (K2.oldsAt 25)) κ).old <
          t.book.place.size :=
  hOld_of_hT1 N Mg links ps (keeps_fin hent) h (keptAt_row hrw h0f)
    (fun _ _ ha => noMark_switch hS hR O (Or.inr (Or.inr rfl)) (hRch _ _ ha))
    (hT1_fin_plain hS hR O hF hpl hy hcut hB hRch hent hq hrw h0f)

end

end P1K2

#print axioms P1K2.keeps_id
#print axioms P1K2.keeps_fin
#print axioms P1K2.noMark_switch
#print axioms P1K2.hBook_tight
#print axioms P1K2.hBook_plain
#print axioms P1K2.keptAt_row
#print axioms P1K2.hOld_of_hT1
#print axioms P1K2.hOld_link
#print axioms P1K2.hOld_head
#print axioms P1K2.hOld_fin
#print axioms P1K2.hOld_link_plain
#print axioms P1K2.hOld_head_plain
#print axioms P1K2.hOld_fin_plain
