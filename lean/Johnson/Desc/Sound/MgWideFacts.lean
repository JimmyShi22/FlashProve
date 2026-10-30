-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgWideFacts.lean: THE BRIDGE's PREMISE hF AT THE WIDER MEANING, ONCE, FOR ALL
AUTHORS: the facts on reached states (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean) give what
the bridge asks beside the table (`FactsAt`, Johnson/Desc/Sound/PlusDoorA.lean) at `mgWide`
(Johnson/Desc/Sound/MgWide.lean). Definitions and five theorems.
Why. `tiedAtR_of_classA` carries a tie that is typed at the wider meaning to the composed meaning
`mgAll` under the reached states. Its premise hF asks, at every reached state: the wide test "in
order" holds where the narrow one does; and every public item that has left the table and is open
in the wider list has a true test and a true sentence. It is meant for every author who takes the
bridge: so it stands here once.
  `FoldTies 𝔇 E d reqW`: the public numbers of `FoldFacts` are those of the composed meaning's
    parameters and of the struck parts' data: nine equations.
  `RoomOpen`, `K8Open`: at every reached state at a border at which the name is open in the wider
    list, the test at "pile.room"; at "K8.lay7", "K8.onThird", "K8.funsThird".
  `WideFacts 𝔇 E x`: what the premise spends at ONE state x: fifteen facts. `factsAt_at`: THE
    TIGHT FORM: `FactsAt` at one border j and one state, from `WideFacts` there, the four
    names' tests where they are open at j, and Mg's public sentence at every item that has left
    (hP): no structure over all borders, no reached states.
    `wideFacts_of_fold`: `FoldFacts` and `FoldTies` give `WideFacts` at every reached state
    without a mark.
  `factsAt_of_fold`: `FoldFacts` · `FoldTies` · `RoomOpen` · `K8Open` · "Mg's public sentence
    holds at every item that has left" ⟹ ∀ j a, Rch j a → `FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg)
    (pubWide …) (ioWide 𝔇 E Mg) classA links ps get j a`.
  `roomFitB M fvs links ps`: a test WITH CODE on the table alone. `roomOpen_of_fold`: where it
    accepts, `FoldFacts`' fields room and roomEarly give `RoomOpen`. `factsAt_of_fold_room`: so
    `RoomOpen` is no premise any more.
Limits: `FoldFacts`' fields are owed, most of them. `K8Open` IS STILL A NAMED PREMISE, OWED BY
THESE THREE NAMES' OWN AUTHORS (`FoldFacts` has no field for them: their one asker is their own
sub-protocol). `roomFitB` is for an evaluation or the kernel at the written lists: not shown here.
The last premise holds at the closed base (`mgBase`) by the written table (`saysNone_of_leaves`,
Johnson/Desc/First/AllSaid.lean). No soundness is claimed.

-/
import Johnson.Desc.Sound.MgWide
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.First (ModelPart Pub More Meaning pubSets classA pubWide leavesName FoldData
  FoldFacts)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The public numbers of the facts on reached states are the composed meaning's and the struck
parts'. -/
structure FoldTies (d : FoldData) (reqW : P → Array UInt32) : Prop where
  ft : d.ft = E.d12.ft
  L : d.L = E.d12.L
  M : d.M = E.d12.M
  codes : d.sent.codes = 𝔇.cs
  shape : d.sent.shape = 𝔇.shape
  layout : d.sent.layout = 𝔇.layout
  reqW : reqW = E.reqW
  free0 : d.free0 = E.dP.free0
  fvs : d.fvs = E.dP.fvs

variable {A : Type} {Fr : Frame} (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
  (Rch : ℕ → A × Fr.E.Str → Prop)

/-- Owed by the name's authors: where "pile.room" is open in the wider list, its test holds. -/
def RoomOpen : Prop :=
  ∀ j (a : A × Fr.E.Str) m, Rch j a → (get a.1).2.failed = none →
    Pub.more (some m) "pile.room" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
    Johnson.Desc.First.Walk.Tied.roomIsB E.dP.free0 E.dP.fvs m (get a.1).2 = true

/-- **A test on the table alone**: wherever (some m, "pile.room") is open in the list M, the border
stands in front of a sub-protocol of a segment m' that is not segment 0's first two, and no segment
from m' up to m leaves a row on the committed table. -/
def roomFitB (M : More) (fvs : List Bool) (links : List ModelPart) (ps : List Place) : Bool :=
  (pubSets M links ps).zipIdx.all fun x => x.1.all fun q =>
    match q with
    | .more (some m) name =>
      if name == "pile.room" then
        (ps[x.2]?).any fun p => p.link.any fun m' =>
          (decide (2 ≤ p.piece) || decide (0 < m')) &&
            Johnson.Desc.First.Walk.Tied.rowsBefore fvs m' ==
              Johnson.Desc.First.Walk.Tied.rowsBefore fvs m
      else true
    | _ => true

/-- **Where that test accepts, the facts on reached states give `RoomOpen`.** -/
theorem roomOpen_of_fold (d : FoldData) (reqW : P → Array UInt32)
    (F : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (T : FoldTies 𝔇 E d reqW) (h : roomFitB (moreW 𝔇 Mg) E.dP.fvs links ps = true) :
    RoomOpen 𝔇 E Mg links ps get Rch := by
  intro j a m hr hm hq
  cases hQ : (pubSets (moreW 𝔇 Mg) links ps)[j]? with
  | none =>
    rw [hQ] at hq
    exact absurd hq (List.not_mem_nil)
  | some Q =>
    rw [hQ] at hq
    have h1 := List.all_eq_true.1 h (Q, j) (List.mem_zipIdx_iff_getElem?.2 hQ)
    have h2 := List.all_eq_true.1 h1 _ hq
    have h3 : ((ps[j]?).any fun p => p.link.any fun m' =>
        (decide (2 ≤ p.piece) || decide (0 < m')) &&
          Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m' ==
            Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m) = true := h2
    cases hp : ps[j]? with
    | none =>
      rw [hp] at h3
      cases h3
    | some p =>
      rw [hp] at h3
      cases hl : p.link with
      | none =>
        have h4 : (p.link.any fun m' =>
          (decide (2 ≤ p.piece) || decide (0 < m')) &&
            Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m' ==
              Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m) = true := h3
        rw [hl] at h4
        cases h4
      | some m' =>
        have h4 : (p.link.any fun m' =>
          (decide (2 ≤ p.piece) || decide (0 < m')) &&
            Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m' ==
              Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m) = true := h3
        rw [hl] at h4
        have h5 : ((decide (2 ≤ p.piece) || decide (0 < m')) &&
            Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m' ==
              Johnson.Desc.First.Walk.Tied.rowsBefore E.dP.fvs m) = true := h4
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h5
        have hroom : Johnson.Desc.First.Walk.Tied.roomIsB d.free0 d.fvs m' (get a.1).2 = true := by
          by_cases h2p : 2 ≤ p.piece
          · exact F.room j a p m' hr hm hp hl h2p
          · exact F.roomEarly j a p m' hr hm hp hl (Nat.lt_of_not_le h2p)
              (h5.1.resolve_left h2p)
        rw [T.free0, T.fvs] at hroom
        unfold Johnson.Desc.First.Walk.Tied.roomIsB at hroom ⊢
        rw [← h5.2]
        exact hroom

/-- Owed by the names' authors: where one of the approximate range proof's three names is open in
the wider list, its test holds. -/
def K8Open : Prop :=
  ∀ j (a : A × Fr.E.Str) m, Rch j a → (get a.1).2.failed = none →
    (Pub.more (some m) "K8.lay7" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
      ((E.dP.tl m).any fun tlP => First.K8.Ready.lay7B tlP (get a.1).2) = true) ∧
    (Pub.more (some m) "K8.onThird" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
      First.K8.Ready.onThirdB (get a.1).2 = true) ∧
    (Pub.more (some m) "K8.funsThird" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
      First.K8.Ready.funsThirdB (get a.1).2 = true)

/-- **What the bridge's premise spends at ONE state**: fifteen facts, at the composed meaning's own
parameters and the struck parts' data. -/
structure WideFacts (x : P × First.S) : Prop where
  bookInOrder : K12.Door.atFirstBook E.d12.ft x.2 = true
  seatsCarried : K12.Door.atFirstSeats E.d12.L x.2 = true
  bookFits : K12.Door.atFirstFits x.2 = true
  msgShapes : K12.Door.atFirstShapes E.d12.M x.2 = true
  weightsOk : First.weightsB x.2 = true
  pileMasks : K13.pileMasksC x.2 = true
  pileWithin : K13.pileWithinC x.2 = true
  oneRow : K13.oneRowC x.2 = true
  tidy : OnBytes.Means.tidy4B x.2.st = true
  codes : x.2.st.codes = 𝔇.cs
  shape : x.2.check.frame.shape = 𝔇.shape
  layout : x.2.check.rows.layout = 𝔇.layout
  liveShape : x.2.live.frame.shape = 𝔇.shape
  liveLayout : x.2.live.rows.layout = 𝔇.layout
  reqIs : x.2.req = E.reqW x.1

/-- **THE TIGHT FORM: the bridge's premise hF at ONE border and ONE state**, from what it spends
there: no structure over all borders, no reached states. -/
theorem factsAt_at (j : ℕ) (a : A × Fr.E.Str)
    (hW : (get a.1).2.failed = none → WideFacts 𝔇 E (get a.1))
    (hR : ∀ m, (get a.1).2.failed = none →
      Pub.more (some m) "pile.room" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
      Johnson.Desc.First.Walk.Tied.roomIsB E.dP.free0 E.dP.fvs m (get a.1).2 = true)
    (hK : ∀ m, (get a.1).2.failed = none →
      (Pub.more (some m) "K8.lay7" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
        ((E.dP.tl m).any fun tlP => First.K8.Ready.lay7B tlP (get a.1).2) = true) ∧
      (Pub.more (some m) "K8.onThird" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
        First.K8.Ready.onThirdB (get a.1).2 = true) ∧
      (Pub.more (some m) "K8.funsThird" ∈ (pubSets (moreW 𝔇 Mg) links ps)[j]?.getD [] →
        First.K8.Ready.funsThirdB (get a.1).2 = true))
    (hP : ∀ q, classA q = true → Mg.pubP q (get a.1)) :
    FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg) classA
      links ps get j a := by
  intro hm
  have W := hW hm
  refine ⟨fun hio => ?_, fun q hq hc => ⟨?_, ?_⟩⟩
  · rw [mgAll_inOrder_at] at hio
    simp only [Bool.and_eq_true] at hio
    unfold ioWide First.eqsB First.reqIsB K13.Law.inOrderK13
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hio.1, ⟨W.codes, W.shape⟩, W.layout⟩, W.reqIs⟩,
      ⟨⟨W.tidy, W.codes⟩, W.shape⟩, W.layout⟩, hio.2⟩
  · cases q with
    | more sg name =>
      have hl : leavesName (sg, name) = true := hc
      cases sg with
      | none =>
        have hl' : (["K12.bookInOrder", "K12.seatsCarried", "K12.bookFits", "K12.msgShapes",
          "K13.weightsOk", "K13.pileMasks", "K13.pileWithin", "K13.oneRow"].contains name) =
            true := hl
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
          beq_iff_eq] at hl'
        rcases hl' with e | e | e | e | e | e | e | e <;> subst e
        · rw [First.pubWide_bookInOrder]
          exact W.bookInOrder
        · rw [First.pubWide_seatsCarried]
          exact W.seatsCarried
        · rw [First.pubWide_bookFits]
          exact W.bookFits
        · rw [First.pubWide_msgShapes]
          exact W.msgShapes
        · rw [First.pubWide_weightsOk]
          exact W.weightsOk
        · rw [First.pubWide_pileMasks]
          exact W.pileMasks
        · rw [First.pubWide_pileWithin]
          exact W.pileWithin
        · rw [First.pubWide_oneRow]
          exact W.oneRow
      | some m =>
        have hl' : (["pile.room", "frame.liveIs", "K8.lay7", "K8.onThird",
          "K8.funsThird"].contains name) = true := hl
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
          beq_iff_eq] at hl'
        rcases hl' with e | e | e | e | e <;> subst e
        · rw [First.pubWide_room]
          exact hR m hm hq
        · rw [First.pubWide_liveIs]
          show (decide ((get a.1).2.live.frame.shape = 𝔇.shape) &&
            decide ((get a.1).2.live.rows.layout = 𝔇.layout)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨W.liveShape, W.liveLayout⟩
        · rw [First.pubWide_lay7]
          exact (hK m hm).1 hq
        · rw [First.pubWide_onThird]
          exact (hK m hm).2.1 hq
        · rw [First.pubWide_funsThird]
          exact (hK m hm).2.2 hq
    | _ => exact absurd hc (by simp [classA])
  · have h0 := hP q hc
    rw [mgAll_pubP]
    cases q with
    | more sg name => exact h0
    | _ => exact absurd hc (by simp [classA])

/-- The facts on reached states give the fifteen at every reached state without a mark. -/
theorem wideFacts_of_fold (d : FoldData) (reqW : P → Array UInt32)
    (F : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (T : FoldTies 𝔇 E d reqW) (j : ℕ) (a : A × Fr.E.Str) (hr : Rch j a)
    (hm : (get a.1).2.failed = none) : WideFacts 𝔇 E (get a.1) where
  bookInOrder := by
    rw [← T.ft]
    exact F.bookInOrder j a hr hm
  seatsCarried := by
    rw [← T.L]
    exact F.seatsCarried j a hr hm
  bookFits := F.bookFits j a hr hm
  msgShapes := by
    rw [← T.M]
    exact F.msgShapes j a hr hm
  weightsOk := F.weightsOk j a hr hm
  pileMasks := F.pileMasks j a hr hm
  pileWithin := F.pileWithin j a hr hm
  oneRow := F.oneRow j a hr hm
  tidy := F.tidy j a hr hm
  codes := (F.codes j a hr hm).trans T.codes
  shape := (F.shape j a hr hm).trans T.shape
  layout := (F.layout j a hr hm).trans T.layout
  liveShape := (F.liveShape j a hr hm).trans T.shape
  liveLayout := (F.liveLayout j a hr hm).trans T.layout
  reqIs := by
    rw [← T.reqW]
    exact F.reqIs j a hr hm

/-- **The bridge's premise hF at the wider meaning.** -/
theorem factsAt_of_fold (d : FoldData) (reqW : P → Array UInt32)
    (F : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (T : FoldTies 𝔇 E d reqW) (hR : RoomOpen 𝔇 E Mg links ps get Rch)
    (hK : K8Open 𝔇 E Mg links ps get Rch)
    (hP : ∀ q, classA q = true → ∀ x, Mg.pubP q x) (j : ℕ) (a : A × Fr.E.Str) (hr : Rch j a) :
    FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg) classA
      links ps get j a :=
  factsAt_at 𝔇 E Mg links ps get j a
    (fun hm => wideFacts_of_fold 𝔇 E links ps get Rch d reqW F T j a hr hm)
    (fun m hm hq => hR j a m hr hm hq) (fun m hm => hK j a m hr hm) fun q hc => hP q hc _

/-- The same, with `RoomOpen` paid by the facts on reached states and the test on the table. -/
theorem factsAt_of_fold_room (d : FoldData) (reqW : P → Array UInt32)
    (F : FoldFacts Rch (fun a : A × Fr.E.Str => get a.1) d reqW links ps)
    (T : FoldTies 𝔇 E d reqW) (hB : roomFitB (moreW 𝔇 Mg) E.dP.fvs links ps = true)
    (hK : K8Open 𝔇 E Mg links ps get Rch)
    (hP : ∀ q, classA q = true → ∀ x, Mg.pubP q x) (j : ℕ) (a : A × Fr.E.Str) (hr : Rch j a) :
    FactsAt (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg) classA
      links ps get j a :=
  factsAt_of_fold 𝔇 E Mg links ps get Rch d reqW F T
    (roomOpen_of_fold 𝔇 E Mg links ps get Rch d reqW F T hB) hK hP j a hr

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.factsAt_at
#print axioms VerifiableInference.Desc.Sound.wideFacts_of_fold
#print axioms VerifiableInference.Desc.Sound.roomOpen_of_fold
#print axioms VerifiableInference.Desc.Sound.factsAt_of_fold_room
#print axioms VerifiableInference.Desc.Sound.factsAt_of_fold
