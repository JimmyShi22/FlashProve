-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableFirst.lean: THE FIRST SEGMENT's OPENING (kind K1's sending with "link 0:
opened" joined behind it: `K1.openingZero`, Johnson/Desc/K1/Law/OpeningZero.lean) AT THE TABLE OF
JOINTS: the five ties (`TiedAt`), by the general rule for a sending (`K1.send_tied`,
Johnson/Desc/K1/Law/AtTable.lean). Definitions, and a statement with its proof.
Where. The first block of the first chain that sends. Its row closes nothing; it opens the first
moment's pin, the index masks' pin and the class of the first moment's sample rows. Of the public
items it drops "nothing is sent yet"; four come at it (the ledger is open; the look-ups' window; the
link is fresh; the slots above are free); two are tied to the index masks' pin.
Main names:
  `StepG`: a step of the joined block, at one public part. `StepG.decide`: it holds a yes of the
    decision on two rounds.
  `RowG N M links ps k nT nM`: what is asked of the table there.
  `FillG`: what is asked of the table's letters: WHAT THE BLOCK MAKES (the four items that come; the
    two that are tied), what rides, what goes back.
  `first_tied`: **THE FIVE TIES**, of any sending whose yes is a step of the joined block.
  `first_tied_seat`: at a block as a chain holds it (it says yes only where the joined block does).
  `rowGB`, `rowG_of_test`: `RowG` as a test with code (its members by the kernel stand in
    Johnson/Desc/K13/Law/AtTableFirstRow.lean [not in this library]).
PAID HERE, OUT OF THE CHAIN STATE's OWN LAWS: where the chain stands behind; the promise's two
clauses on groups (`rowsHeld`, `membersHeld`: Johnson/Desc/K1/Law/HeldAtOpening.lean); where the
book stands. What is not claimed. `FillG` at any filling. hnew: "held", "no collision" and "shown"
at the tenants that are new at this block are premises, as at W's commitment. hgroups: that
"nothing is sent yet" gives the number of groups in front (at our layer it does: `noneSentC`).
hown: a test on the plan that has run at no plan. Nothing on soundness. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.K1.Law.HeldAtOpening

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter insL outsL openL openIsList)

/-- **A step of the joined block**, at one public part: its rounds fit what it declares. -/
def StepG {Pp : Type} (Cl : Type) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (x x' : Pp × S) : Prop :=
  x'.1 = x.1 ∧ ∃ ft rs cols n,
    (K1.openingZero q gp nm X fvs kCol : Block S Cl).step ft x.2 rs cols = .ok (x'.2, n)

/-- A step holds a yes of the decision on two rounds. -/
theorem StepG.decide {Pp Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {x x' : Pp × S} (h : StepG Cl q gp nm X fvs kCol x x') :
    ∃ r₁ r₂ gs,
      (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide x.2 [r₁, r₂] gs = .ok x'.2 := by
  obtain ⟨ft, rs, cols, n, hst⟩ := h.2
  obtain ⟨hfit, gs, hd⟩ := K1.step_ok ft _ _ _ rs cols n hst
  have hl : (rs.map noDigest).length = 2 := by
    rw [List.length_map]
    exact roundsFit_length _ _ hfit
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, rs.map noDigest = [r₁, r₂] := by
    match rs.map noDigest, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [e] at hd
  exact ⟨r₁, r₂, gs, hd⟩

/-- The four public items that come at the block by the table's own rows. A filling of the door may
add names of its own: so the list of what comes is a letter (mk) below. -/
def madeG : List Pub := [.ledger 0, .lookIn 0 2, .linkFresh 0, .freeAbove 0]

/-- What may ride past the block. -/
def riderG : Item → Bool
  | .pinW => true
  | .pile => true
  | .constr _ _ => true
  | _ => false

/-- **What is asked of the table at (M, links, ps, k).** nT, nM: the trees and the messages that the
block sends. -/
structure RowG (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place) (k nT nM : ℕ)
    (mk : List Pub) : Prop where
  /-- the row closes nothing, and reads "no mark" alone -/
  ins : ∀ i, insQ links ps k i → i = .unmarked
  /-- what rides past the block: the stored table's pin, the pile, the constraints -/
  rider : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
    ¬ insQ links ps k i → riderG i = true
  /-- behind the block the chain stands in segment 0, a segment of layers -/
  next : ∃ p', ps[k + 1]? = some p' ∧ First.standAt links p' = .link .layers ∧ p'.link = some 0
  /-- no pin with a sample is open in front -/
  noneIn : First.sampledIn N (openAt links ps k) = []
  /-- behind, rows of segment 0 alone are open, and none of them lies in the group's list yet -/
  segs : First.rowSegs (openAt links ps (k + 1)) = [0]
  noList : ∀ c, Item.row 0 c ∈ openAt links ps (k + 1) → c.inList = false
  /-- "nothing is sent yet" is open in front -/
  noneSent : Pub.noneSent ∈ (First.pubSets M links ps)[k]?.getD []
  /-- what is open behind: those that come (mk); whatever else was open in front, but "nothing is
  sent yet", which the row drops -/
  pubs : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [],
    q ∈ mk ∨ (q ∈ (First.pubSets M links ps)[k]?.getD [] ∧ q ≠ .noneSent)
  tied : ∀ q ∈ First.pubOfItems (openAt links ps (k + 1)), q = .indexIs ∨ q = .indexThere
  trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT
  msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM

/-- **What is asked of the table's letters.** Q: the public items that are open in front; p: the
block's own place. -/
structure FillG {Pp W : Type} (Cl : Type) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (N : Numbers) (Mg : Meaning Pp W) (Q : List Pub)
    (p : Option Place) (mk : List Pub) : Prop where
  /-- the items that come at the block (mk), and the two that are tied to the index masks' pin, hold
  behind a step that begins inside the promise -/
  made : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → Mg.inOrder x = true →
    (i ∈ mk ∨ i = .indexIs ∨ i = .indexThere) →
    Mg.pub i x' = true
  madeP : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → Mg.inOrder x = true → i ∈ mk → Mg.pubP i x'
  /-- every public item that is open in front and behind holds behind: inside the promise -/
  pubRide : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → i ∈ Q → i ≠ .noneSent → Mg.pub i x' = true
  pubPRide : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → i ∈ Q → i ≠ .noneSent → Mg.pubP i x → Mg.pubP i x'
  inOrder : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → Mg.inOrder x = true → Mg.inOrder x' = true
  decodes : ∀ x x' y y', StepG Cl q gp nm X fvs kCol x x' → y'.cell = y.cell → Mg.decodes x y →
    Mg.decodes x' y'
  /-- what rides past the block goes back over a step that begins inside the promise -/
  back : ∀ x x' y y' w i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → y'.cell = y.cell → riderG i = true →
    Item.holds N Mg i x' y' w → Item.holds N Mg i x y w

section
variable {A Pp Cl W : Type} {F : Frame}

/-- A piece leaves the stored table. General in the piece. -/
theorem cell_out {T : Type} {C : PQ.CK} (p : Piece C F T Cl W) {a b : T × F.E.Str}
    {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    (strsOf F b.2).cell = (strsOf F a.2).cell := by
  rw [out_imp p h]
  rfl

/-- What the table's promise in front gives at a state of the chain without a mark. -/
theorem promise_plain (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (a : A × F.E.Str) (ha : onQ N Mg links ps get k a)
    (hm : (get a.1).2.failed = none) :
    Mg.decodes (get a.1) (strsOf F a.2) ∧ Mg.inOrder (get a.1) = true ∧
      First.bookAt N ps[k]? (get a.1).2 = true ∧
      ∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [],
        Mg.pub q (get a.1) = true ∧ Mg.pubP q (get a.1) := by
  obtain ⟨hd, hr⟩ := ha
  obtain ⟨hB, _, _, hPP⟩ := hr.resolve_left (fun h => h hm)
  simp only [Bool.and_eq_true] at hB
  have hall := List.all_eq_true.1 hB.1.2
  exact ⟨hd, hB.1.1.2, hB.2, fun q hq => ⟨hall _ (List.mem_append_left _ hq), hPP q hq⟩⟩

/-- **THE FIVE TIES AT THE FIRST SEGMENT's OPENING**, of any sending whose yes is a step of the
joined block. -/
theorem first_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (mk : List Pub) (rad : Nat → Nat)
    (hC : K1.condPort (K1.firstPar q gp) rad = true) (b : Block A Cl)
    (hS : K1.IsSend (K1.firstPar q gp) (fun a => (get a).2.st) b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = K1.seedEntry (K1.firstPar q gp)) (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : K1.errPort (K1.firstPar q gp) rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ (K1.firstPar q gp).codes (K1.shapeAt (K1.firstPar q gp) j)
      (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ (K1.firstPar q gp).codes
      (K1.shapeAt (K1.firstPar q gp) j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((K1.sendPiece (W := W) (F := F) b base d₁ d₂
      (K1.firstPar q gp).coordinates e).ior.imp y τ) = fIn y τ.1)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hF : FillG Cl q gp nm X fvs kCol N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?
      mk)
    (hyes : ∀ a τ x, (K1.sendPiece (W := W) (F := F) b base d₁ d₂
      (K1.firstPar q gp).coordinates e).ior.red.out a τ = some x →
      StepG Cl q gp nm X fvs kCol (get a.1) (get x.1))
    (hgroups : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown : ∀ x, Mg.inOrder x = true → First.bookAt N ps[k]? x.2 = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true)
    (hnew : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (K1.sendPiece (W := W) (F := F) b base d₁ d₂
        (K1.firstPar q gp).coordinates e).ior.red.out a τ = some x →
      (∀ j, K1.sampledAt (K1.firstPar q gp) j →
        K1.Sealed (K1.firstPar q gp).codes (K1.shapeAt (K1.firstPar q gp) j) (rad j.val)
          (fOf x.2 j) (get x.1).2.st
          ((get x.1).2.st.oracles.size - (K1.shapesOf (K1.firstPar q gp)).length + j.val)) →
      ∀ t ∈ First.sampledIn N (openAt links ps (k + 1)),
        Mg.held t.1 t.2 (get x.1) = true ∧ Mg.shown t.1 t.2 (strsOf F x.2) ∧
          Mg.noColl t.1 t.2 (get x.1) (strsOf F x.2)) :
    TiedAt N Mg links ps get k (K1.sendPiece (W := W) (F := F) b base d₁ d₂
      (K1.firstPar q gp).coordinates e) := by
  refine K1.send_tied N Mg links ps get k (K1.firstPar q gp) rad hC b hS base d₁ d₂ he₁ hk₁ e he
    fOf fIn hf
    (fun x => ∀ t ∈ First.sampledIn N (openAt links ps (k + 1)),
      Mg.held t.1 t.2 (get x.1) = true ∧ Mg.shown t.1 t.2 (strsOf F x.2) ∧
        Mg.noColl t.1 t.2 (get x.1) (strsOf F x.2))
    hnew ?_ ?_ ?_ ?_ ?_
  · -- the promise behind
    intro a τ x ha hm hx hn
    obtain ⟨hd, hin, hbk, hQ⟩ := promise_plain N Mg links ps get k a ha hm
    have hst := hyes a τ x hx
    obtain ⟨r₁, r₂, gs, hdec⟩ := hst.decide
    obtain ⟨hstand, ⟨L, hL, hL0⟩, _, hw, hb, _, _⟩ := K1.openingZero_rec hdec
    have hQ1 : ∀ q' ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q' (get a.1) = true :=
      fun q' h' => (hQ q' h').1
    have hg := hgroups _ (hQ1 _ hT.noneSent)
    have hbk' := hbk
    unfold First.bookAt at hbk'
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
    obtain ⟨⟨b1, b2⟩, b3⟩ := hbk'
    refine ⟨hF.decodes _ _ _ _ hst (cell_out _ hx) hd, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hF.inOrder _ _ hst hin⟩, ?_⟩, ?_⟩
      · obtain ⟨p', hp, hs', hl'⟩ := hT.next
        rw [hp]
        simp [First.shapeAt, S.noneWaits, hstand, hs', hw, hL, hL0, hl']
      · exact K1.openingZero_rowsHeld hdec N _ hT.segs hT.noList hg
      · exact K1.openingZero_membersHeld hdec N _ hT.segs hg b2 (hown _ hin hbk)
      · refine List.all_eq_true.2 fun i hi => ?_
        rcases List.mem_append.1 hi with hi | hi
        · rcases hT.pubs i hi with hi' | ⟨hi', hne⟩
          · exact hF.made _ _ i hst hQ1 hbk hin (Or.inl hi')
          · exact hF.pubRide _ _ i hst hQ1 hbk hi' hne
        · rcases hT.tied i hi with rfl | rfl
          · exact hF.made _ _ _ hst hQ1 hbk hin (Or.inr (Or.inl rfl))
          · exact hF.made _ _ _ hst hQ1 hbk hin (Or.inr (Or.inr rfl))
      · unfold First.bookAt
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨by rw [hb.trees, b1, hT.trees], hb.full b2⟩, by rw [hb.msgs, b3, hT.msgs]⟩
    · exact List.all_eq_true.2 fun t ht => (hn t ht).1
    · exact fun t ht => ⟨(hn t ht).2.1, (hn t ht).2.2⟩
    · intro i hi
      rcases hT.pubs i hi with hi' | ⟨hi', hne⟩
      · exact hF.madeP _ _ i hst hQ1 hbk hin hi'
      · exact hF.pubPRide _ _ i hst hQ1 hbk hi' hne (hQ i hi').2
  · -- what the row opens goes back to what it closes
    intro a τ x w _ hm _ _ i hi
    obtain rfl := hT.ins i hi
    exact hm
  · -- the riders
    intro a τ x w i ha hm hx _ hall hi hin
    obtain ⟨_, _, hbk, hQ⟩ := promise_plain N Mg links ps get k a ha hm
    exact hF.back _ _ _ _ w i (hyes a τ x hx) (fun q' h' => (hQ q' h').1) hbk (cell_out _ hx)
      (hT.rider i hi hin) (hall i (Or.inl ⟨hi, hin⟩))
  · -- a mark stays
    intro a τ x hx hm
    obtain ⟨r₁, r₂, gs, hdec⟩ := (hyes a τ x hx).decide
    rw [(K1.openingZero_rec hdec).2.2.1]
    exact hm
  · -- "decodes" rides
    intro a τ x hx hd
    exact hF.decodes _ _ _ _ (hyes a τ x hx) (cell_out _ hx) hd

/-- **THE FIVE TIES AT A BLOCK AS A CHAIN HOLDS IT**, where the chain's state is the carried state
itself and the public part is one value z. -/
theorem first_tied_seat (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar) (fvs : List Bool)
    (kCol : ℕ) (mk : List Pub) (rad : Nat → Nat)
    (hC : K1.condPort (K1.firstPar q gp) rad = true) (c : Block S Cl)
    (hc : c.UnderR (K1.openingZero q gp nm X fvs kCol)) (base : Nat)
    (d₁ d₂ : RDT) (he₁ : d₁.entry = K1.seedEntry (K1.firstPar q gp)) (hk₁ : d₁.kind = .seeds)
    (e : Nat) (he : K1.errPort (K1.firstPar q gp) rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ (K1.firstPar q gp).codes (K1.shapeAt (K1.firstPar q gp) j)
      (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ (K1.firstPar q gp).codes
      (K1.shapeAt (K1.firstPar q gp) j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((K1.sendPiece (W := W) (F := F) c base d₁ d₂
      (K1.firstPar q gp).coordinates e).ior.imp y τ) = fIn y τ.1)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hF : FillG Cl q gp nm X fvs kCol N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?
      mk)
    (hgroups : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown : ∀ x, Mg.inOrder x = true → First.bookAt N ps[k]? x.2 = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true)
    (hnew : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (K1.sendPiece (W := W) (F := F) c base d₁ d₂
        (K1.firstPar q gp).coordinates e).ior.red.out a τ = some x →
      (∀ j, K1.sampledAt (K1.firstPar q gp) j →
        K1.Sealed (K1.firstPar q gp).codes (K1.shapeAt (K1.firstPar q gp) j) (rad j.val)
          (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (K1.shapesOf (K1.firstPar q gp)).length + j.val)) →
      ∀ t ∈ First.sampledIn N (openAt links ps (k + 1)),
        Mg.held t.1 t.2 (z, x.1) = true ∧ Mg.shown t.1 t.2 (strsOf F x.2) ∧
          Mg.noColl t.1 t.2 (z, x.1) (strsOf F x.2)) :
    TiedAt N Mg links ps (fun s : S => (z, s)) k (K1.sendPiece (W := W) (F := F) c base d₁ d₂
      (K1.firstPar q gp).coordinates e) :=
  first_tied N Mg links ps _ k q gp nm X fvs kCol mk rad hC c
    (K1.isSend_under _ _ hc.2 (K1.isSend_openingZero q gp nm X fvs kCol)) base d₁ d₂ he₁ hk₁ e he
    fOf fIn hf hT hF
    (fun a τ x hx => by
      obtain ⟨rs, cols, n, hst⟩ := piece_step _ hx
      exact ⟨rfl, _, rs, cols, n, step_under hc hst⟩)
    hgroups hown hnew

end

/-! ## `RowG` as a test with code -/

/-- No pin with a sample. -/
def noPins : Item → Bool
  | .pin _ _ => false
  | .pinKept _ => false
  | .pinI => false
  | .pinV => false
  | _ => true

/-- No class of segment 0 that lies in the group's list. -/
def notInList : Item → Bool
  | .row m c => !(m == 0 && c.inList)
  | _ => true

/-- **`RowG` as a test with code.** -/
def rowGB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (mk : List Pub) : Bool :=
  ((insL links ps k).all fun i => i == .unmarked) &&
    ((openL (insL links ps) (outsL links ps) (First.start links) k).all fun i =>
      (insL links ps k).contains i || riderG i) &&
    (ps[k + 1]?.any fun p' => First.standAt links p' == .link .layers && p'.link == some 0) &&
    (openAt links ps k).all noPins &&
    (First.rowSegs (openAt links ps (k + 1)) == [0]) &&
    (openAt links ps (k + 1)).all notInList &&
    ((First.pubSets M links ps)[k]?.getD []).contains .noneSent &&
    (((First.pubSets M links ps)[k + 1]?.getD []).all fun q =>
      mk.contains q ||
        (((First.pubSets M links ps)[k]?.getD []).contains q && q != .noneSent)) &&
    ((First.pubOfItems (openAt links ps (k + 1))).all fun q => q == .indexIs || q == .indexThere)

/-- **A yes of the test gives what is asked of the table**, at every N whose numbers of trees and
messages grow at the block by nT and nM. -/
theorem rowG_of_test (M : More) (links : List ModelPart) (ps : List Place) (k nT nM : ℕ)
    (mk : List Pub) (h : rowGB M links ps k mk = true) (N : Numbers)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT)
    (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM) : RowG N M links ps k nT nM mk := by
  unfold rowGB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, eq_of_beq h5, ?_, List.contains_iff_mem.1 h7, ?_, ?_, hT, hM⟩
  · intro i hi
    exact eq_of_beq (List.all_eq_true.1 h1 i hi)
  · intro i hi hin
    have hm := (openIsList Item (insL links ps) (outsL links ps) (First.start links) k i).1 hi
    rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.1 h2 i hm with h | h
    · exact absurd (List.contains_iff_mem.1 h) hin
    · exact h
  · cases hp : ps[k + 1]? with
    | none =>
      rw [hp] at h3
      cases h3
    | some p' =>
      rw [hp, Option.any_some, Bool.and_eq_true] at h3
      exact ⟨p', rfl, eq_of_beq h3.1, eq_of_beq h3.2⟩
  · refine List.flatMap_eq_nil_iff.2 fun i hi => ?_
    have hb := List.all_eq_true.1 h4 i hi
    cases i <;> first | rfl | exact absurd (show false = true from hb) Bool.false_ne_true
  · intro c hc
    have hb : (!((0 : ℕ) == 0 && c.inList)) = true := List.all_eq_true.1 h6 _ hc
    simpa using hb
  · intro q hq
    have := List.all_eq_true.1 h8 q hq
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at this
    rcases this with e | ⟨e, hne⟩
    · exact Or.inl (List.contains_iff_mem.1 e)
    · exact Or.inr ⟨List.contains_iff_mem.1 e, hne⟩
  · intro q hq
    rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.1 h9 q hq with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (eq_of_beq e)

end VerifiableInference.Desc.K13.Law
