-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameSits.lean: THE KIND "frame" AT THE PROOF FILE's DESCRIPTION's OWN PIECES, TIED
AT THE TABLE OF JOINTS, AT THE WRITTEN LIST OF PLACES, AT THE FULL SIZE, IN THE GOALS' SCOPE. BY THE
STRAIGHT ROAD: from OfDesc.pieceAt (Johnson/Desc/Sound/AtDriver.lean) and the places
(Johnson/IMR/FrameSeat.lean: frame_of; Johnson/IMR/FrontSeat.lean: front_of) to the frame's own rule
tied_of_rides (Johnson/Top/H0/Walk/FrameTiedStep.lean), at the piece with the table's extractor laid
in.

  sits_lift, laysNothing_withMap   Sits and LaysNothing at the description's OWN piece q.withMap E
  plan_of_joined, plans_hold   in scope, where every block of the flat list passes its test on the
                   plan, every row of the frame's value passes its own ("opened" bears it, joined
                   behind each link's first block: Johnson/IMR/FirstSeats.lean)
  clear_with_flag  what a row's clear is, WITH THE FLAG AND THE LINK's OWN PLANNED ENTRY: an
                   attention link's leaves no row; every other's leaves one, by a reader that
                   leftOf gathers
  kind_not_att     in scope the planned entry's kind is not attention's where the link's sort is not
  fvs_bearing      so the links' flags are true just at the segments that are not attention's
  placesAtB_full, places_full, front_places_full, frameAllB_full, frame_places_full   what the
                   written list has at the frame's places, and where the kind stands in it (77
                   numbers): closed facts, by Lean's kernel (decide +kernel; no native code)
  laysNoneB_full, ext_lays_nothing   PAID: FrameOwes' three fields on the extractor, at the table's
                   own extractor extQAt, whatever its letters
  places_nodup_full, none_between_paid   CUT DOWN, NOT PAID: FrameOwes' three fields NoneBetween, at
                   the numbers that are filled off what the blocks tell (Numbers.withTold at the
                   written list): to one sentence: "our 51 blocks tell nothing"
  laid_tied_full   "link l: laid": TiedAt, under NoneBetween and LettersRide AT THE STEP's OWN YES
  ClearOwes, cleared_tied_full   "link l: cleared", whichever the sort: TiedAt, under NoneBetween
                   and ClearOwes: LettersRide AT THE ROW's OWN clear's YES; and, where the link's
                   planned entry says that a row is left: "wo l" from Hold of the row that rowAt
                   gives; Hold goes back over the step
  front_tied_full  the front: TiedAt at number 0
  frame_kindTied   THE JOIN: KindTied at the kind "frame" from five shares in one form
  FrameOwes, frame_kindTied_ours   the join with 51 places laid in (the front, "laid", "cleared"):
                   what these still owe, all on N, Mg and the table's extractor; and two shares of
                   others: "behind the batching" (25), the seal (1)

Limits. A form with its debts counted: no field of FrameOwes is shown at a filling. "onlineDescription
returns in scope" and OfDesc are premises. "opened" has no tie of its own: it is a share of the
first place's block's. No soundness statement.

-/
import Johnson.IMR.FirstSeats
import Johnson.IMR.FrontSeat
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.PieceYes
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.Sound.BordersFill
import Johnson.Top.H0.Walk.FrameTiedLaid
import Johnson.Top.H0.Walk.FrameTiedCleared
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Top.H0.Walk.FrameWo
import Johnson.Top.H0.Walk.FrameNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start openSets pubSets Stand standAt
  mayWait shift flatPlacesOf rowOf)
open Johnson.Desc.First.Walk (layFront clearWith LinkPub)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ W}

/-! ### The straight road from the description's own piece -/

/-- **Sits, at the description's own piece**, with the table's extractor laid in: where the piece
holds "below B", lifted over the public part, and B says yes only where f does. No word on a mark is
wanted. By piece_lift_yes, cellStays, colStays. -/
theorem sits_lift {Pp : Type} {Fr : Frame} (q : Piece C Fr (Pp × S) Cl W) (B₀ : Block S Cl)
    (hq : q.b = (below B₀).lift Prod.snd fun t s => (t.1, s))
    (E : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W) (f : S → Except String S)
    (hY : ∀ s rs gs t, B₀.decide s rs gs = .ok t → f s = .ok t) :
    Sits (fun a => a) (q.withMap E) f := by
  intro a τ b hb
  have hb' : q.ior.red.out a τ = some b := hb
  obtain ⟨s', h1, h2, _, _, h5⟩ :=
    piece_lift_yes q Prod.snd (fun t s => (t.1, s)) B₀ hq a b τ hb'
  refine ⟨by rw [h2], by rw [h2]; exact hY _ _ _ _ h1, fun x => ?_, fun j x hj => ?_⟩
  · rw [h5]
    exact cellStays C Fr q.base q.ds a.2 τ x
  · rw [h5]
    exact colStays C Fr q.base q.ds a.2 τ j x hj

theorem laysNothing_withMap {Pp : Type} {Fr : Frame} (q : Piece C Fr (Pp × S) Cl W)
    (E : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w) :
    LaysNothing (q.withMap E) := by
  intro a τ w
  simp only [Piece.withMap]
  split
  · exact hE _ _ _
  · rfl

set_option maxRecDepth 100000 in
theorem front_places_full :
    (flatPlacesOf linksFull true)[0]? = some ⟨1, none, 0, KindName.frame⟩ ∧
      (flatPlacesOf linksFull true)[1]? = some ⟨1, some 0, 0, KindName.frame⟩ := by
  decide +kernel

/-! ### The flag "a row is left", from the description's own tests on the plan -/

/-- The row's own test on the plan stands in the test of the block behind which "opened" is joined.
-/
theorem plan_of_joined {l : ℕ} {b b' : Block S Cl} {a : Place} (h : IM.Joined Z l b b' a)
    (hp : b.planOk = true) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ f.plan = true := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  refine ⟨fs, f, hfs, hf, ?_⟩
  rw [IM.with_planOk _ e, Bool.and_eq_true] at hp
  exact (IM.retype_planOk (IM.openedOf f) hp.2).1

/-- **In scope, where every block of the first chain's flat list passes its test on the plan, every
row of the frame's value passes its own.** -/
theorem plans_hold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs) {l : ℕ}
    (hl : l < 25) {f : Johnson.Desc.First.Walk.Seat.LinkFrame} (hf : fs[l]? = some f) :
    f.plan = true := by
  have key : ∀ (Lk : Link S Cl) (b b' : Block S Cl) (a : Place), c.links[l]? = some Lk →
      Lk.hear[0]? = some b → IM.Joined Z l b b' a → f.plan = true := by
    intro Lk b b' a e1 e2 hj
    obtain ⟨fs', f', h1, h2, h3⟩ :=
      plan_of_joined hj (hp b (List.mem_of_getElem? (IM.hear_at_flat e1 e2)))
    rw [hfs] at h1
    obtain rfl : fs = fs' := Except.ok.inj h1
    rw [hf] at h2
    obtain rfl : f = f' := Option.some.inj h2
    exact h3
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨Lk, b, e1, e2, hj⟩ := IM.k1_first_sits hS hR O
    exact key Lk b _ _ e1 e2 hj
  · by_cases h24 : l = 24
    · subst h24
      obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits hS hR O
      exact key Lk b _ _ e1 e2 hj
    · obtain ⟨Lk, b, x, e1, e2, -, hj, -⟩ := IM.k2_link_sits hS hR O l (by omega) (by omega)
      exact key Lk b _ _ e1 e2 hj

/-- What a row's clear is, with the flag, where the row's test on the plan says yes: an attention
link's leaves no row; every other link's leaves one, and its reader is one that leftOf gathers. -/
theorem clear_with_flag {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs) {l : ℕ}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} (hf : fs[l]? = some f) (hp : f.plan = true) :
    ∃ (X : LinkPub) (counts : S → Except String Unit)
      (left : S → Option OnBytes.Model.WsForkOut) (X' : OnBytes.Model.Stages.LinkH),
      f.clear = clearWith X counts left (Johnson.Desc.First.Walk.Seat.rowOf Z.p.X Z.first) ∧
        Z.p.built.links[l]? = some X' ∧ X.kind = X'.kind ∧ X.NCL = X'.NCL ∧ X.fv = X'.fv ∧
        ((X.kind = 1 ∧ X.fv = false) ∨
          (X.kind ≠ 1 ∧ X.fv = true ∧
            ∀ s w, left s = some w → Johnson.Desc.First.Walk.Law.leftOf s = some w)) := by
  rcases Johnson.Desc.First.Walk.Seat.framesOf_arms hfs hf with ⟨X, hX, -, e⟩ |
    ⟨h0, X, _, Q, hX, _, _, eQ, e1, _, e2⟩ | ⟨_, X, _, Q, hX, _, _, eQ, e1, _, e2⟩ |
    ⟨_, X, _, Q, hX, _, _, eQ, e1, _, e2⟩
  · subst e
    have h2 := (Johnson.Desc.First.Walk.Props.planFlag_iff _ 2).1 hp
    exact ⟨_, _, _, X, rfl, hX, rfl, rfl, rfl, Or.inr ⟨by rw [h2.1]; decide,
      Johnson.Desc.First.Walk.Seat.headFrame_fv hp,
      fun s w h => Johnson.Desc.First.Walk.Law.leftOf_of_head h⟩⟩
  · subst h0
    subst eQ
    rw [e1] at hp
    have h2 := ((Johnson.Desc.First.Walk.Props.planLayZero_iff _ _).1 hp).2.2.2.2.2
    exact ⟨_, _, _, X, e2, hX, rfl, rfl, rfl, Or.inr ⟨by rw [h2.1]; decide,
      Johnson.Desc.First.Walk.Props.planLayZero_fv hp,
      fun s w h => Johnson.Desc.First.Walk.Law.leftOf_of_lay h⟩⟩
  · subst eQ
    rw [e1] at hp
    have h2 := ((Johnson.Desc.First.Walk.Props.planAtt_iff _ _).1 hp).2.2
    exact ⟨_, _, _, X, e2, hX, rfl, rfl, rfl,
      Or.inl ⟨h2.1, Johnson.Desc.First.Walk.Props.planAtt_fv hp⟩⟩
  · subst eQ
    rw [e1] at hp
    have h2 := ((Johnson.Desc.First.Walk.Props.planLay_iff _ _).1 hp).2.2.2.2.2
    exact ⟨_, _, _, X, e2, hX, rfl, rfl, rfl, Or.inr ⟨by rw [h2.1]; decide,
      Johnson.Desc.First.Walk.Props.planLay_fv hp,
      fun s w h => Johnson.Desc.First.Walk.Law.leftOf_of_lay h⟩⟩

/-- The kind in the link's planned entry is the sort that the driver is handed. -/
theorem kind_not_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hne : IM.subAt l ≠ ModelPart.attention) {X : OnBytes.Model.Stages.LinkH}
    (hX : Z.p.built.links[l]? = some X) : X.kind ≠ 1 := by
  intro h1
  have h := IM.subs_scope hS hR O l hl
  unfold ProofFile.subsOf at h
  rw [List.getElem?_map, Array.getElem?_toList, hX] at h
  have e : ProofFile.subOf X.kind = IM.subAt l := Option.some.inj h
  rw [h1] at e
  exact hne e.symm

/-- **THE LINKS' FLAGS ARE TRUE JUST AT THE SEGMENTS THAT THE TABLE's ROWS CALL BEARING**: in scope,
where every block of the flat list passes its test on the plan: entry l of the list of flags that
"link 0: opened" is handed says "a row is left" just where the link's sort is not attention's. Its
payer is the frame's own test on the flag (planFlag). -/
theorem fvs_bearing (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) :
    (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)[l]? =
      some (decide (IM.subAt l ≠ ModelPart.attention)) := by
  obtain ⟨-, fs, hfs, h⟩ := IM.frame_of hS hR O
  obtain ⟨-, f, -, -, -, -, -, hf, -⟩ := h l hl
  obtain ⟨X, _, _, X', _, hX', hkk, _, hfv, hflag⟩ :=
    clear_with_flag hfs hf (plans_hold hS hR O hp hfs hl hf)
  have hsub : ProofFile.subOf X'.kind = IM.subAt l := by
    have h2 := IM.subs_scope hS hR O l hl
    unfold ProofFile.subsOf at h2
    rw [List.getElem?_map, Array.getElem?_toList, hX'] at h2
    exact Option.some.inj h2
  unfold Johnson.Desc.First.Walk.Seat.fvsOf
  rw [List.getElem?_map, Array.getElem?_toList, hX']
  rcases hflag with ⟨h1, h2⟩ | ⟨h1, h2, _⟩
  · rw [hkk] at h1
    rw [hfv] at h2
    rw [← hsub, h1]
    simp [h2, ProofFile.subOf]
  · rw [hkk] at h1
    rw [hfv] at h2
    have : IM.subAt l ≠ ModelPart.attention := by
      rw [← hsub]
      unfold ProofFile.subOf
      by_cases h0 : X'.kind = 0
      · simp [h0]
      · simp [h0, h1]
    simp [h2, this]

/-! ### At the written list of places, at the full size -/

/-- The number of «link l: cleared» in the flat list. -/
abbrev clearIx (l : ℕ) : ℕ := 14 * l + (if l = 24 then 9 else 7) + 7

/-- The place of «link l: cleared». -/
abbrev clearPlace (l : ℕ) : Place := ⟨1, some l, 13 + 2 * shift (IM.subAt l), KindName.frame⟩

/-- A test with code on the written list: all that the frame's ties ask of the list of places and of
the segments' sorts, at link l. -/
def placesAtB (l : ℕ) : Bool :=
  decide ((flatPlacesOf linksFull true)[14 * l + 1]? = some ⟨1, some l, 0, KindName.frame⟩) &&
  (match (flatPlacesOf linksFull true)[14 * l + 1 + 1]? with
    | some p' => decide (p'.link = some l) && decide (p'.piece = 1)
    | none => false) &&
  decide (linksFull[l]? = some (IM.subAt l)) &&
  decide ((flatPlacesOf linksFull true)[clearIx l]? = some (clearPlace l)) &&
  (mayWait linksFull (clearPlace l) == false) &&
  (match (flatPlacesOf linksFull true)[clearIx l + 1]? with
    | some p' => decide (standAt linksFull p' = Stand.between)
    | none => false)

set_option maxRecDepth 1000000 in
theorem placesAtB_full : (List.range 25).all placesAtB = true := by decide +kernel

/-- **What the written list has at the frame's fifty places.** -/
theorem places_full {l : ℕ} (hl : l < 25) :
    (flatPlacesOf linksFull true)[14 * l + 1]? = some ⟨1, some l, 0, KindName.frame⟩ ∧
      (∃ p', (flatPlacesOf linksFull true)[14 * l + 1 + 1]? = some p' ∧ p'.link = some l ∧
        p'.piece = 1) ∧
      linksFull[l]? = some (IM.subAt l) ∧
      (flatPlacesOf linksFull true)[clearIx l]? = some (clearPlace l) ∧
      mayWait linksFull (clearPlace l) = false ∧
      ∃ p', (flatPlacesOf linksFull true)[clearIx l + 1]? = some p' ∧
        standAt linksFull p' = Stand.between := by
  have h := List.all_eq_true.1 placesAtB_full l (List.mem_range.2 hl)
  unfold placesAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, ?_⟩
  · cases hp : (flatPlacesOf linksFull true)[14 * l + 1 + 1]? with
    | none => rw [hp] at h2; cases h2
    | some p' =>
      rw [hp] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨p', rfl, h2.1, h2.2⟩
  · cases hp : (flatPlacesOf linksFull true)[clearIx l + 1]? with
    | none => rw [hp] at h6; cases h6
    | some p' =>
      rw [hp] at h6
      exact ⟨p', rfl, of_decide_eq_true h6⟩

/-! ### Paid: the table's own extractor lays nothing at the 51 rows -/

/-- A test with code on the written list: the table's row at the front's, at «laid»'s and at
«cleared»'s place lays nothing. -/
def laysNoneB : Bool :=
  !(rowOf linksFull ⟨1, none, 0, KindName.frame⟩).lays &&
    (List.range 25).all fun l =>
      !(rowOf linksFull ⟨1, some l, 0, KindName.frame⟩).lays &&
        !(rowOf linksFull (clearPlace l)).lays

set_option maxRecDepth 1000000 in
theorem laysNoneB_full : laysNoneB = true := by decide +kernel

open Cb Johnson.Pack OnBytes.Slice in
/-- **eFront · eLaid · eClear, PAID AT THE TABLE's OWN EXTRACTOR** extQAt
(Johnson/Desc/Sound/BordersFill.lean), whatever its letters. -/
theorem ext_lays_nothing {Xi Pp Cells Tok A : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
    (tokOf : Pp × S → Tok) (N : Numbers) (get : A → Pp × S) :
    (∀ (a b : A × Fr.E.Str) w, extQAt cs G arr smp ms decT c₀ tokOf N linksFull
        (flatPlacesOf linksFull true) get 0 a b w = w) ∧
      (∀ l, l < 25 → ∀ (a b : A × Fr.E.Str) w, extQAt cs G arr smp ms decT c₀ tokOf N linksFull
        (flatPlacesOf linksFull true) get (14 * l + 1) a b w = w) ∧
      ∀ l, l < 25 → ∀ (a b : A × Fr.E.Str) w, extQAt cs G arr smp ms decT c₀ tokOf N linksFull
        (flatPlacesOf linksFull true) get (clearIx l) a b w = w := by
  have h := laysNoneB_full
  unfold laysNoneB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, hl⟩ := h
  refine ⟨fun a b w => ?_, fun l hl' a b w => ?_, fun l hl' a b w => ?_⟩
  · unfold extQAt
    rw [front_places_full.1]
    exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ h0 _ _ _ w
  · unfold extQAt
    rw [(places_full hl').1]
    exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ (hl l hl').1 _ _ _ w
  · unfold extQAt
    rw [(places_full hl').2.2.2.1]
    exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ (hl l hl').2 _ _ _ w

/-! ### Cut down: the plan's numbers do not move across the 51 rows -/

set_option maxRecDepth 1000000 in
theorem places_nodup_full : (flatPlacesOf linksFull true).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
theorem places_length_full : (flatPlacesOf linksFull true).length = 358 := by decide +kernel

/-- **nFront · nLaid · nClear, AT THE NUMBERS THAT ARE FILLED OFF WHAT THE BLOCKS TELL**
(Numbers.withTold at the written list): cut down to "our 51 blocks tell nothing", which stays a
premise here. -/
theorem none_between_paid (N : Numbers) {told : List (List VerifiableInference.Desc.Oracle)}
    (h0 : told[0]? = some []) (hL : ∀ l, l < 25 → told[14 * l + 1]? = some [])
    (hC : ∀ l, l < 25 → told[clearIx l]? = some []) :
    NoneBetween (N.withTold (flatPlacesOf linksFull true) told) (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween (N.withTold (flatPlacesOf linksFull true) told)
        (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween (N.withTold (flatPlacesOf linksFull true) told)
        (flatPlacesOf linksFull true) (clearIx l) := by
  refine ⟨noneBetween_withTold N places_nodup_full (by rw [places_length_full]; omega) h0,
    fun l hl => noneBetween_withTold N places_nodup_full (by rw [places_length_full]; omega)
      (hL l hl),
    fun l hl => noneBetween_withTold N places_nodup_full ?_ (hC l hl)⟩
  rw [places_length_full]
  unfold clearIx
  split <;> omega

/-! ### The ties at the written list -/

/-- **«link l: laid».** Of the list of places alone nothing is asked; NoneBetween holds the plan's
numbers N against it. -/
theorem laid_tied_full (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T) (l : ℕ)
    (hl : l < 25) {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + 1]? = some q) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (hn : NoneBetween N (flatPlacesOf linksFull true) (14 * l + 1))
    (hL : LettersRide N Mg (Yes (layFront l)) q.base
      (FrontAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + 1))
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[14 * l + 1 + 1]?.getD
        [])
      ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[14 * l + 1 + 1]?.getD [])
      (openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) (14 * l + 1 + 1))) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + 1)
      (q.withMap E) := by
  obtain ⟨h1, ⟨p', h2, h3, h4⟩, -⟩ := places_full hl
  obtain ⟨-, fs, -, h⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, -, -, -, -, -, -, hlay, yL, -, iL, -, dL, -⟩ := h l hl
  rw [hlay] at yL
  exact tied_of_rides (step_laid h1 h2 h3 h4 hn
    (sits_lift q bL (OfDesc.pieceAt hT hq iL) E (layFront l) fun s rs gs t e => by
      rw [dL] at e
      exact ((yL s t).1 e).1)
    (laysNothing_withMap q E hE) hL)

/-- **What «link l: cleared» still owes**, at the row f of the frame's value: LettersRide AT THE
ROW's OWN clear's YES; and, at the link's own planned entry X', where it says that a row is left:
"wo l" follows from Hold of the row that rowAt gives, and Hold goes back over the step. Hold: in
what sense a pending row holds of a witness, at a statement. -/
def ClearOwes (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (Z : ProofFile.Pub)
    (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (l base : ℕ)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop) : Prop :=
  LettersRide N Mg (Yes f.clear) base
      (FrontAt N Mg linksFull (flatPlacesOf linksFull true) (clearIx l))
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[clearIx l + 1]?.getD [])
      ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[clearIx l + 1]?.getD [])
      (openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) (clearIx l + 1)) ∧
  ∀ X', Z.p.built.links[l]? = some X' → X'.fv = true →
    (∀ a y w, (∀ r, Johnson.Desc.First.Walk.Law.rowAt Z.p.X.layers.wsLay X'.NCL Z.first.lin
      a.2 = some r → Hold a w r) → Mg.wo l a y w) ∧
    ∀ p s t y w r, f.clear s = .ok t →
      FrontAt N Mg linksFull (flatPlacesOf linksFull true) (clearIx l) (p, s) y →
      Hold (p, t) w r → Hold (p, s) w r

/-- **«link l: cleared»**, whichever the segment's sort. THE ROAD FROM THE FRAME's TEST ON THE FLAG
TO THE TIE runs in it: the flat list's tests on the plan give the row's; that gives the flag; the
flag gives "the pile gives wo". -/
theorem cleared_tied_full (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : ℕ) (hl : l < 25) (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (hpile : ∀ a y w, a.2.atBetween = true → Mg.pile a y w →
      ∀ r ∈ a.2.out.pending, Hold a w r) :
    ∃ fs, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      ∃ f, fs[l]? = some f ∧
        ∀ (q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W),
        (T.p₁ :: T.l₁)[clearIx l]? = some q →
        NoneBetween N (flatPlacesOf linksFull true) (clearIx l) →
        ClearOwes N Mg Z f l q.base Hold →
        TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (clearIx l)
          (q.withMap E) := by
  obtain ⟨-, -, h3, h4, h5, p', h6, h7⟩ := places_full hl
  obtain ⟨-, fs, hfs, h⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, -, -, bC, -, hlen, hf, -, -, -, yC, -, -, -, -, -, -, iC, -, dC⟩ := h l hl
  rw [hlen] at iC
  refine ⟨fs, hfs, f, hf, fun q hq hn hO => ?_⟩
  have hSit : Sits (fun a => a) (q.withMap E) f.clear :=
    sits_lift q bC (OfDesc.pieceAt hT hq iC) E f.clear fun s rs gs t e => by
      rw [dC] at e
      exact ((yC s t).1 e).1
  obtain ⟨X, counts, left, X', e, hX', hkk, hNCL, hfv, hflag⟩ :=
    clear_with_flag hfs hf (plans_hold hS hR O hp hfs hl hf)
  have hrec : ∀ s t, f.clear s = .ok t →
      ClearedRec X left Z.p.X.layers.wsLay Z.first.lin s t := fun s t h => by
    rw [e] at h
    exact clearedGives X counts left _ _ s t h
  by_cases ha : IM.subAt l = ModelPart.attention
  · have e4 : clearPlace l = ⟨1, some l, 13, KindName.frame⟩ := by
      unfold clearPlace
      rw [ha]
      rfl
    rw [e4] at h4 h5
    rw [ha] at h3
    exact tied_of_rides (step_clearedAtt h3 h4 h5 h6 h7 hn hSit hrec
      (laysNothing_withMap q E hE) hO.1)
  · rcases hflag with ⟨h1, -⟩ | ⟨-, hv, hleft⟩
    · exact absurd (hkk ▸ h1) (kind_not_att hS hR O hl ha hX')
    · obtain ⟨hwo, hback⟩ := hO.2 X' hX' (hfv ▸ hv)
      exact tied_of_rides (step_clearedRow h3 ha h4 h5 h6 h7 hn hSit hrec
        (laysNothing_withMap q E hE) hO.1
        (pileGivesWo_of Mg l f.clear X left _ _ q.base _ Hold hrec hv hleft (hNCL ▸ hwo) hpile
          hback))

/-- **The front.** Its place by front_of (Johnson/IMR/FrontSeat.lean). -/
theorem front_tied_full (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hT : OfDesc _ T) {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[0]? = some q) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (hn : NoneBetween N (flatPlacesOf linksFull true) 0)
    (hL : LettersRide N Mg (Yes .ok) q.base
      (FrontAt N Mg linksFull (flatPlacesOf linksFull true) 0)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[1]?.getD [])
      ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[1]?.getD [])
      (openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 1)) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 0 (q.withMap E) := by
  obtain ⟨b, h0, -, -, -, -, hy⟩ := IM.front_of O
  exact tied_of_rides (step_front front_places_full.1 front_places_full.2 hn
    (sits_lift q b (OfDesc.pieceAt hT hq h0) E .ok fun s rs gs t h => by
      rw [(hy s rs gs t).1 h])
    (laysNothing_withMap q E hE) hL)

/-! ### The join: the kind "frame" at all its 77 places of the written list -/

/-- The number of «behind the batching» of link l in the flat list. -/
abbrev behindIx (l : ℕ) : ℕ := 14 * l + (if l = 24 then 9 else 7) + 3

/-- The test: number i is the front's, the seal's, or one of a link's three. -/
def frameIxB (i : ℕ) : Bool :=
  i == 0 || i == 357 ||
    (List.range 25).any fun l => i == 14 * l + 1 || i == behindIx l || i == clearIx l

/-- The test over a list of places: every entry of the kind "frame" passes frameIxB. -/
def frameAllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.frame || frameIxB i
    | none => true

set_option maxRecDepth 1000000 in
theorem frameAllB_full : frameAllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem frame_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.frame) :
    i = 0 ∨ i = 357 ∨ ∃ l, l < 25 ∧ (i = 14 * l + 1 ∨ i = behindIx l ∨ i = clearIx l) := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 frameAllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h2 : frameIxB i = true := by
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · rw [hk] at h1
      exact absurd h1 (by decide)
    · exact h1
  unfold frameIxB at h2
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at h2
  rcases h2 with (h0 | h0) | ⟨l, hl, h3⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr ⟨l, hl, by
      rcases h3 with (h4 | h4) | h4
      · exact Or.inl h4
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr h4)⟩)

/-- **THE JOIN**: the kind's share of the chain of promises, from the five shares, each in one form:
TiedAt at the written list, at the description's own piece with the table's extractor. -/
theorem frame_kindTied (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hFront : ∀ q, (T.p₁ :: T.l₁)[0]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 0 (q.withMap (E 0)))
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 357 (q.withMap (E 357)))
    (hLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + 1)
        (q.withMap (E (14 * l + 1))))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (behindIx l)
        (q.withMap (E (behindIx l))))
    (hCleared : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (clearIx l)
        (q.withMap (E (clearIx l)))) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.frame := by
  intro i q a hq ha hk
  rcases frame_places_full i a ha hk with rfl | rfl | ⟨l, hl, rfl | rfl | rfl⟩
  · exact hFront q hq
  · exact hSeal q hq
  · exact hLaid l hl q hq
  · exact hBehind l hl q hq
  · exact hCleared l hl q hq

/-- **What the 51 places still owe**, all of it on N, Mg and the table's extractor: counted,
field by field. Hold: in what sense a pending row holds of a witness, at a statement. -/
structure FrameOwes (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (Z : ProofFile.Pub)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop) : Prop where
  /-- the table's extractor lays nothing at the 51 rows -/
  eFront : ∀ a b w, E 0 a b w = w
  eLaid : ∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w
  eClear : ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w
  /-- the plan's numbers of trees and messages do not move across them (from bookFit) -/
  nFront : NoneBetween N (flatPlacesOf linksFull true) 0
  nLaid : ∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (14 * l + 1)
  nClear : ∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (clearIx l)
  /-- the letters ride past the front -/
  rFront : ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[0]? = some q →
    LettersRide N Mg (Yes .ok) q.base (FrontAt N Mg linksFull (flatPlacesOf linksFull true) 0)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[1]?.getD [])
      ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[1]?.getD [])
      (openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 1)
  /-- the letters ride past «laid» -/
  rLaid : ∀ l, l < 25 → ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[14 * l + 1]? = some q →
    LettersRide N Mg (Yes (layFront l)) q.base
      (FrontAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + 1))
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[14 * l + 1 + 1]?.getD
        [])
      ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[14 * l + 1 + 1]?.getD [])
      (openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) (14 * l + 1 + 1))
  /-- «cleared» -/
  rClear : ∀ l, l < 25 → ∀ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first
      Z.p.X = .ok fs → fs[l]? = some f →
    ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[clearIx l]? = some q → ClearOwes N Mg Z f l q.base Hold
  /-- "pile" gives Hold of every pending row, where the chain stands between two links -/
  pile : ∀ a y w, a.2.atBetween = true → Mg.pile a y w → ∀ r ∈ a.2.out.pending, Hold a w r

/-- **THE JOIN WITH THE 51 LAID IN**: in the goals' scope, where the flat list's blocks pass
their tests on the plan: KindTied at the kind "frame", from FrameOwes and the two shares of "behind
the batching" (25) and the seal (1). -/
theorem frame_kindTied_ours (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (H : FrameOwes (T := T) N Mg Z E Hold)
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 357 (q.withMap (E 357)))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (behindIx l)
        (q.withMap (E (behindIx l)))) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.frame := by
  refine frame_kindTied N Mg E (fun q hq => ?_) hSeal (fun l hl q hq => ?_) hBehind
    fun l hl q hq => ?_
  · exact front_tied_full O hT hq N Mg (E 0) H.eFront H.nFront (H.rFront q hq)
  · exact laid_tied_full hS hR O hT l hl hq N Mg (E _) (H.eLaid l hl) (H.nLaid l hl)
      (H.rLaid l hl q hq)
  · obtain ⟨fs, hfs, f, hf, h⟩ :=
      cleared_tied_full hS hR O hT hp l hl N Mg (E _) (H.eClear l hl) Hold H.pile
    exact h q hq (H.nClear l hl) (H.rClear l hl fs f hfs hf q hq)

end

end P1L20

#print axioms P1L20.sits_lift
#print axioms P1L20.plans_hold
#print axioms P1L20.clear_with_flag
#print axioms P1L20.kind_not_att
#print axioms P1L20.fvs_bearing
#print axioms P1L20.placesAtB_full
#print axioms P1L20.places_full
#print axioms P1L20.front_places_full
#print axioms P1L20.frameAllB_full
#print axioms P1L20.frame_places_full
#print axioms P1L20.laysNoneB_full
#print axioms P1L20.ext_lays_nothing
#print axioms P1L20.places_nodup_full
#print axioms P1L20.none_between_paid
#print axioms P1L20.laid_tied_full
#print axioms P1L20.cleared_tied_full
#print axioms P1L20.front_tied_full
#print axioms P1L20.frame_kindTied
#print axioms P1L20.frame_kindTied_ours
