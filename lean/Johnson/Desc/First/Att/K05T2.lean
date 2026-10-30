-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05T2.lean: KIND K5 AT THE TABLE OF JOINTS: THE PROMISE BEHIND THE KIND's
BLOCK FROM THE PROMISE IN FRONT OF IT ("t2"), AT THE TABLE's OWN TERM onAt
(Johnson/Desc/First/Borders.lean; imported, not turned), at the record that
the hearing's seat lays; over that table's own rule "the promise rides past a block"
(onAt_step_held, Johnson/Desc/First/PromiseRides.lean).

THE STATEMENT (`k5_t2`). At an attention segment's block number 3: from onAt at (p, O, Q), at a
record s without a mark in which the attention segment a is open, the hearing's return from a.F, and
oracles that are the same below the base: onAt at (p', stepOpen O (rowOf links p), pubStep Q
(pubRowM Mg.more links p)) at the record behind the lay. pubRowM Mg.more: the table's row with what
the meaning's filling of the table's door adds at that place; at the empty filling it is the table's
own.

THE KIND's ROW, BY THE TABLE's TEXT: asks ledger, look, left, linkFresh, freeAbove, callerIn · drops
look, left, callerIn · makes lookIn m 7, leftOn m.
WHAT IS PAID HERE: the row touches no row and no pin · the book-keeping behind (shapeAt) · rowsHeld,
membersHeld (the lay turns neither st nor book) · where the book stands (bookAt), under K5Book ·
KEPT: ledger m · lookOut m 2 · linkFresh m · freeAbove m · MADE: lookIn m 7.
WHAT STAYS A PREMISE, EACH BY NAME:
  `K5Place`: five facts on the index (decidable at the table's own list).
  `K5Book`: two equations on the table's numbers: as many trees and as many oracle messages are due
    behind the kind's block as in front of it (the block tells no oracle).
  `K5Plan`: seven facts on the plan (the two lookups' places; one equation on slots; THE ROOM FITS:
    first + kr is at most the plan's number of slots nsPlan).
  `K5Fill`: SEVENTEEN FACTS ON THE FILLINGS of the table's letters: EIGHT "it rides", each an
    implication, each asked AT A RETURN OF THE KIND's HEARING ALONE (decodes · inOrder · held · shown
    and noColl · the two items tied to the index masks' pin, indexIs and indexThere · every other
    open public item's Bool, WITH "THE OPEN LEDGER IS SIZED" IN HAND (the promise has it: without it an item of K5's files that the row
    drops, "K5.readsThere", could not be shown to ride: the field asks it of every open item but seven) · what it says beside) · six "the letter is this Bool" (ledger · lookOut
    · callerIn · lookIn · linkFresh · freeAbove) · leftOn's Bool is true · what lookIn m 7 says beside
    its Bool holds · **leftOn: what left m says in front gives what leftOn m says behind the lay**
    (paid at the lookups' two promises by Johnson/Desc/First/Att/K05LeftOn.lean; where the kind's
    law fills K5Fill the field is laid by at7_leftOn,
    Johnson/Desc/First/Att/Door/Law/K5FillPlus.lean).
  hQ: what the kind's row asks is open (the table's test pubFit says so at its own lists).
  keptForms: the public items tied to items that stay, but the index masks' pin's. madeForms: the
    three that the row opens. OWED.
  madeMore: what the filling of the door makes at the kind's place.
THE ROOM. freeAbove m is filled by freeAboveB nsPlan (Johnson/Desc/First/Att/K05BehindLay3.lean):
the open ledger has the plan's number of slots, and every slot from its next free number on is free.
"Free from next on" alone does not say how many slots there are (above_no_room): with the number,
the room that the lookup on the digits wants is K5Plan.fits, a fact on the plan.
Limits. A RULE OVER LETTERS: NONE OF THE PREMISES IS SHOWN AT ANY FILLING. Not joined to a piece
(Johnson/Desc/First/Att/K05T2Piece.lean). Nothing at a marked record. EMPTY AT: a promise in front
that holds of nothing; a filling of callerIn that is false.
No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.PubHeldStep
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.First.Att.K05FormsKept
import Johnson.Desc.First.Att.K05BehindLay3
import Johnson.Desc.First.Att.K05SeamOut
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (Item Pub BlockRow PubRow Meaning Numbers ModelPart onAt stepOpen pubStep
  rowOf pubRowOf pubRowM moreItem shapeAt rowsHeld membersHeld sampledIn tiesOf onAt_step_held
  pubHeld_step pubP_step segRow standOf standAt pubHeld bookAt)
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-! ## What the promise in front hands over -/

section
variable {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {p : Place}
  {O : List Item} {Q : List Pub} {a : Pp × First.S} {y : Strs}

theorem onAt_shape (h : onAt N Mg links (some p) O Q a y) (hu : a.2.failed = none) :
    shapeAt links (some p) a.2 = true := by
  obtain ⟨_, hm | ⟨h1, _, _, _⟩⟩ := h
  · exact absurd hu hm
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1.1.1.1

theorem onAt_pub (h : onAt N Mg links (some p) O Q a y) (hu : a.2.failed = none) :
    ∀ q ∈ Q, Mg.pub q a = true := by
  obtain ⟨_, hm | ⟨h1, _, _, _⟩⟩ := h
  · exact absurd hu hm
  simp only [Bool.and_eq_true] at h1
  have c5 := h1.1.2
  unfold pubHeld at c5
  exact fun q hq => List.all_eq_true.1 c5 q (List.mem_append_left _ hq)

theorem onAt_pubP (h : onAt N Mg links (some p) O Q a y) (hu : a.2.failed = none) :
    ∀ q ∈ Q, Mg.pubP q a := by
  obtain ⟨_, hm | ⟨_, _, _, h4⟩⟩ := h
  · exact absurd hu hm
  exact h4

end

/-! ## The records of premises -/

/-- Facts on the index. -/
structure K5Place (links : List ModelPart) (m : ℕ) (p p' : Place) : Prop where
  link : p.link = some m
  piece : p.piece = 3
  sub : links[m]? = some .attention
  link' : p'.link = some m
  piece' : p'.piece = 4

/-- Facts on the table's numbers: the kind's block tells no oracle. -/
structure K5Book (N : Numbers) (p p' : Place) : Prop where
  trees : N.treesAt (some p') = N.treesAt (some p)
  msgs : N.msgsAt (some p') = N.msgsAt (some p)

/-- Facts on the plan. -/
structure K5Plan (own : Params.AttentionRounds) (m : ℕ) (pC pD : Look.P) (hS : Forest.Shape)
    (first kr nsPlan : ℕ) : Prop where
  calls : pC.digits = false
  digits : pD.digits = true
  shape : pD.shape = some hS
  link : pD.link = m
  room : kr = slotsOf (script own) + Forest.elems hS
  fits : first + kr ≤ nsPlan
  first : pD.first = first + slotsOf (script own)

/-- Facts on the fillings of the table's letters. -/
structure K5Fill {Pp W : Type} (Mg : Meaning Pp W) (N : Numbers) (π : Pp) (Fr : Frame) (base m : ℕ)
    (O : List Item) (Q : List Pub) (own : Params.AttentionRounds) (pC pD : Look.P)
    (arr : Array (ℕ × String)) (first nsPlan : ℕ) : Prop where
  decodes : ∀ s a h G rs y y', s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
    SameBelow Fr base y y' →
    Mg.decodes (π, s) (strsOf Fr y) → Mg.decodes (π, behind s a h G) (strsOf Fr y')
  inOrder : ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
    Mg.inOrder (π, s) = true →
    Mg.inOrder (π, behind s a h G) = true
  held : ∀ x ∈ sampledIn N O, ∀ s a h G rs, s.here = .att a →
    hear own (a.F, rs, 0) = some (h, G, [], 0) → Mg.held x.1 x.2 (π, s) = true →
    Mg.held x.1 x.2 (π, behind s a h G) = true
  strs : ∀ x ∈ sampledIn N O, ∀ s a h G rs y y', s.here = .att a →
    hear own (a.F, rs, 0) = some (h, G, [], 0) → SameBelow Fr base y y' →
    Mg.shown x.1 x.2 (strsOf Fr y) ∧ Mg.noColl x.1 x.2 (π, s) (strsOf Fr y) →
    Mg.shown x.1 x.2 (strsOf Fr y') ∧ Mg.noColl x.1 x.2 (π, behind s a h G) (strsOf Fr y')
  ledger : ∀ s, Mg.pub (.ledger m) (π, s) = s.fork?.any sizedB
  lookOut : ∀ s, Mg.pub (.lookOut m 2) (π, s) = k3OnOut pC s
  callerIn : ∀ s, Mg.pub (.callerIn m) (π, s) = k5CallerIn3 first s
  lookIn : ∀ s, Mg.pub (.lookIn m 7) (π, s) =
    (k3OnIn pD s && s.link?.any fun L => L.link == pD.link && L.arrayOf == arr)
  linkFresh : ∀ s, Mg.pub (.linkFresh m) (π, s) = linkFreshB arr s
  freeAbove : ∀ s, Mg.pub (.freeAbove m) (π, s) = freeAboveB nsPlan s
  leftOnB : ∀ s, Mg.pub (.leftOn m) (π, s) = true
  lookInP : ∀ s, Mg.pubP (.lookIn m 7) (π, s)
  leftOn : ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
    s.fork?.any sizedB = true → Mg.pubP (.left m) (π, s) → Mg.pubP (.leftOn m) (π, behind s a h G)
  rides : ∀ q ∈ Q, q ≠ .ledger m → q ≠ .lookOut m 2 → q ≠ .linkFresh m → q ≠ .freeAbove m →
    q ≠ .look m → q ≠ .left m → q ≠ .callerIn m →
    ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
      s.fork?.any sizedB = true →
      Mg.pub q (π, s) = true → Mg.pub q (π, behind s a h G) = true
  indexIs : ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
    Mg.pub .indexIs (π, s) = true →
    Mg.pub .indexIs (π, behind s a h G) = true
  indexThere : ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
    Mg.pub .indexThere (π, s) = true →
    Mg.pub .indexThere (π, behind s a h G) = true
  ridesP : ∀ q ∈ Q, q ≠ .look m → q ≠ .left m → q ≠ .callerIn m →
    ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
      Mg.pubP q (π, s) → Mg.pubP q (π, behind s a h G)

/-! ## The kind's two rows, by the table's text -/

theorem k5_row {links : List ModelPart} {m : ℕ} {p p' : Place} (Ix : K5Place links m p p') :
    rowOf links p = segRow .attention m 3 := by
  unfold rowOf
  rw [Ix.link]
  simp only [Ix.sub, Ix.piece]

theorem k5_ins (m : ℕ) : (segRow .attention m 3).ins =
    [.constr m .idn, .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider"] := rfl

theorem k5_outs (m : ℕ) : (segRow .attention m 3).outs =
    [.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join"] := rfl

theorem k5_quiet {links : List ModelPart} {m : ℕ} {p p' : Place} (Ix : K5Place links m p p') :
    First.quietRow (rowOf links p) = true := by
  rw [k5_row Ix]
  rfl

theorem k5_pubRow {links : List ModelPart} {m : ℕ} {p p' : Place} (Ix : K5Place links m p p') :
    (pubRowOf links p).asks =
        [.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .callerIn m] ∧
      (pubRowOf links p).drops = [.look m, .left m, .callerIn m] ∧
      (pubRowOf links p).makes = [.lookIn m 7, .leftOn m] := by
  unfold pubRowOf
  rw [Ix.link]
  simp only [Ix.sub, Ix.piece]
  exact ⟨rfl, rfl, rfl⟩

theorem k5_pubRowM (M : First.More) {links : List ModelPart} {m : ℕ} {p p' : Place}
    (Ix : K5Place links m p p') :
    (pubRowM M links p).drops =
        [.look m, .left m, .callerIn m] ++ (M.rows links p).drops.map moreItem ∧
      (pubRowM M links p).makes =
        [.lookIn m 7, .leftOn m] ++ (M.rows links p).makes.map moreItem := by
  obtain ⟨_, h2, h3⟩ := k5_pubRow Ix
  unfold pubRowM First.PubRow.plus
  exact ⟨by rw [h2], by rw [h3]⟩

/-! ## The book-keeping behind -/

theorem k5_link {links : List ModelPart} {m : ℕ} {p p' : Place} (Ix : K5Place links m p p')
    {s : First.S} {a : First.AttOwn} (e : s.here = .att a)
    (h : shapeAt links (some p) s = true) : a.L.link = m := by
  unfold shapeAt at h
  simp only [Bool.and_eq_true] at h
  have h3 := h.2
  rw [link_front e, Ix.link] at h3
  have h4 : m = a.L.link := by simpa using h3
  exact h4.symm

theorem k5_shape {links : List ModelPart} {m : ℕ} {p p' : Place} (Ix : K5Place links m p p')
    {s : First.S} {a : First.AttOwn} (h : Heard) (G : Fork) (hl : a.L.link = m) :
    shapeAt links (some p') (behind s a h G) = true := by
  have h1 : standOf (behind s a h G) = .link .attention := rfl
  have h2 : standAt links p' = .link .attention := by
    unfold standAt
    rw [Ix.link']
    simp [Ix.sub, Ix.piece']
  have h3 : (behind s a h G).noneWaits = true := rfl
  have h4 : (behind s a h G).link? = some a.L := rfl
  show (standOf (behind s a h G) == standAt links p' &&
    ((behind s a h G).noneWaits || First.mayWait links p') &&
      (behind s a h G).link?.all fun L => p'.link == some L.link) = true
  rw [h1, h2, h3, h4, Ix.link']
  simp [hl]

theorem k5_book {N : Numbers} {p p' : Place} (Bk : K5Book N p p') {s : First.S} {a : First.AttOwn}
    (h : Heard) (G : Fork) (hb : bookAt N (some p) s = true) :
    bookAt N (some p') (behind s a h G) = true := by
  unfold bookAt at hb ⊢
  rw [Bk.trees, Bk.msgs]
  exact hb

/-! ## t2 -/

/-- **THE PROMISE BEHIND THE KIND's BLOCK FROM THE PROMISE IN FRONT OF IT.** -/
theorem k5_t2 {Pp W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (π : Pp)
    (m base : ℕ) (p p' : Place) (O : List Item) (Q : List Pub) (own : Params.AttentionRounds)
    (pC pD : Look.P) (hS : Forest.Shape) (arr : Array (ℕ × String)) (first kr nsPlan : ℕ)
    (Ix : K5Place links m p p') (Bk : K5Book N p p') (Pl : K5Plan own m pC pD hS first kr nsPlan)
    (Fi : K5Fill Mg N π Fr base m O Q own pC pD arr first nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links p).asks, q ∈ Q)
    {s : First.S} {a : First.AttOwn} {h : Heard} {G : Fork} {rs : List Fmt.RoundView} {y y' : Fr.E.Str}
    (e : s.here = .att a) (hh : hear own (a.F, rs, 0) = some (h, G, [], 0))
    (hy : SameBelow Fr base y y') (hu : s.failed = none)
    (hon : onAt N Mg links (some p) O Q (π, s) (strsOf Fr y))
    (keptForms : ∀ i ∈ O, (rowOf links p).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
      Mg.pub q (π, s) = true → Mg.pub q (π, behind s a h G) = true)
    (madeForms : ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
      Mg.pub q (π, behind s a h G) = true)
    (madeMore : ∀ x ∈ (Mg.more.rows links p).makes, Mg.pub (moreItem x) (π, behind s a h G) = true ∧
      Mg.pubP (moreItem x) (π, behind s a h G)) :
    onAt N Mg links (some p') (stepOpen O (rowOf links p)) (pubStep Q (pubRowM Mg.more links p))
      (π, behind s a h G) (strsOf Fr y') := by
  have hl := k5_link Ix e (onAt_shape hon hu)
  have hpub := onAt_pub hon hu
  have hpp := onAt_pubP hon hu
  obtain ⟨hasks, _, _⟩ := k5_pubRow Ix
  obtain ⟨hdrops, hmakes⟩ := k5_pubRowM Mg.more Ix
  rw [hasks] at hQ
  have qL : s.fork?.any sizedB = true := by
    rw [← Fi.ledger]; exact hpub _ (hQ _ (by simp))
  have qF : linkFreshB arr s = true := by
    rw [← Fi.linkFresh]; exact hpub _ (hQ _ (by simp))
  have qA : freeAboveB nsPlan s = true := by
    rw [← Fi.freeAbove]; exact hpub _ (hQ _ (by simp))
  have qC : k5CallerIn3 first s = true := by
    rw [← Fi.callerIn]; exact hpub _ (hQ _ (by simp))
  have notDropped : ∀ q, (pubRowM Mg.more links p).drops.contains q = false →
      q ≠ .look m ∧ q ≠ .left m ∧ q ≠ .callerIn m := by
    intro q hd
    rw [hdrops] at hd
    refine ⟨fun e3 => ?_, fun e3 => ?_, fun e3 => ?_⟩ <;> · rw [e3] at hd; simp at hd
  refine onAt_step_held N Mg links (some p) (some p') O Q _ _ (π, s) (π, behind s a h G) _ _
    (k5_quiet Ix) hon (fun hm => hm) (Fi.decodes s a h G rs y y' e hh hy)
    (fun _ _ => k5_shape Ix h G hl) (fun _ _ hr => hr) (fun _ _ hr => hr)
    (fun _ _ => Fi.inOrder s a h G rs e hh) (fun _ _ hP => ?_) (fun _ _ => k5_book Bk h G)
    (fun _ _ hP => ?_) (fun _ _ x hx => Fi.held x hx s a h G rs e hh)
    (fun _ _ x hx => Fi.strs x hx s a h G rs y y' e hh hy)
  · refine pubHeld_step Mg O Q _ _ (π, s) (π, behind s a h G) hP ?_ ?_ ?_ ?_
    · intro q hq hd hqa
      obtain ⟨h3, h4, h5⟩ := notDropped q hd
      by_cases h1 : q = .ledger m
      · subst h1
        rw [Fi.ledger] at hqa ⊢
        exact ledger_behind e hh hqa
      by_cases h2 : q = .lookOut m 2
      · subst h2
        rw [Fi.lookOut] at hqa ⊢
        exact lookOut_behind pC Pl.calls e hh hqa
      by_cases h6 : q = .linkFresh m
      · subst h6
        rw [Fi.linkFresh, linkFresh_behind arr e]
        exact qF
      by_cases h7 : q = .freeAbove m
      · subst h7
        rw [Fi.freeAbove]
        obtain ⟨_, _, c3⟩ := callerIn3_at e qC
        refine freeAbove_behind e hh qL qA ?_
        have c4 := Pl.fits
        rw [Pl.room] at c4
        omega
      exact Fi.rides q hq h1 h2 h6 h7 h3 h4 h5 s a h G rs e hh qL hqa
    · intro i hi hn q ht hqa
      by_cases hp : i = .pinI
      · subst hp
        have ht' : q = .indexIs ∨ q = .indexThere := by simpa [tiesOf] using ht
        rcases ht' with rfl | rfl
        · exact Fi.indexIs s a h G rs e hh hqa
        · exact Fi.indexThere s a h G rs e hh hqa
      · exact keptForms i hi hn hp q ht hqa
    · intro q hq
      rw [hmakes] at hq
      rcases List.mem_append.1 hq with hq | hq
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl
        · have hc := callerIn_of3 e qL qA qC Pl.fits
          rw [Pl.room] at hc
          have h2 : s.link?.any (fun L => L.link == pD.link) = true := by
            rw [link_front e, Pl.link, ← hl]
            simp
          obtain ⟨g1, g2⟩ := lookIn_behind pD Pl.digits Pl.shape e hh hc qF Pl.first h2
          rw [Fi.lookIn, g1, g2]
          rfl
        · exact Fi.leftOnB _
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
        exact (madeMore x hx).1
    · intro i hi q ht
      rw [k5_row Ix, k5_outs] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · obtain rfl : q = Pub.formsInT m 3 "own" := List.mem_singleton.1 ht
        exact madeForms _ (by simp)
      · obtain rfl : q = Pub.formsInT m 2 "planes" := List.mem_singleton.1 ht
        exact madeForms _ (by simp)
      · obtain rfl : q = Pub.formsInT m 2 "join" := List.mem_singleton.1 ht
        exact madeForms _ (by simp)
  · refine pubP_step Mg Q _ (π, s) (π, behind s a h G) hP ?_ ?_
    · intro q hq hd hqa
      obtain ⟨h3, h4, h5⟩ := notDropped q hd
      exact Fi.ridesP q hq h3 h4 h5 s a h G rs e hh hqa
    · intro q hq
      rw [hmakes] at hq
      rcases List.mem_append.1 hq with hq | hq
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl
        · exact Fi.lookInP _
        · exact Fi.leftOn s a h G rs e hh qL (hpp _ (hQ _ (by simp)))
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
        exact (madeMore x hx).2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5_shape
#print axioms VerifiableInference.Desc.First.Att.P.k5_pubRow
#print axioms VerifiableInference.Desc.First.Att.P.k5_pubRowM
#print axioms VerifiableInference.Desc.First.Att.P.k5_book
#print axioms VerifiableInference.Desc.First.Att.P.k5_t2
