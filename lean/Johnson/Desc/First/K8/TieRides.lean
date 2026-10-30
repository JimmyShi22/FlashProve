-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TieRides.lean: THE SMALLNESS TEST: THREE OF THE SIX TIES OF
Johnson/Desc/First/K8/TieLaws.lean's `k08_seatLaws` TO THE TABLE OF JOINTS: the promise behind (t2),
what rides (t5), "decodes" rides (hD): each brought down to what the draw writes, and to ONE
STRUCTURE OF PREMISES ON THE FILLING.

What the draw does, for certain. A yes of `approximateRangeProofDrawKind atS p` turns the verifier's state in one way: the
open link's structure of the smallness test gets the drawn matrix and its first columns (`Drawn`).
The oracles' strings behind its piece have the stored table, and every tree below the piece's base,
as they were (`SameBelow`).
  `Drawn s t`, `drawn_of_yes`; `SameBelow base y y'`, `sameBelow_behind`.
  `drawn_stand`, `drawn_shape`: PAID: where the chain stands, that no count of rows waits, and the
    open link's number are as they were: so the table's book-keeping `shapeAt` passes from a place
    to the next place of the same link, where both stand from piece 3 on and no count may wait in
    front.
  `DrawBlind Nn Mg links ps k base o'`: **WHAT THE FILLING OWES FOR THE DRAW**, one structure, each
    field at every pair of states with `Drawn` and every pair of strings with `SameBelow`: decodes ·
    inOrder · held · shown · noColl ride forward; the public items behind hold (with the kind's own
    condition behind, o', in hand); what they say beside their Bools; every item that is open
    across the draw and that the draw's row does not name rides BACKWARD, with "no mark", the
    promise in front and ALL that is open behind in hand; what the draw's row READS (its field ctx:
    the pins of the link's first two sendings) rides backward too; and two equations on the table's
    numbers: the plan counts no tree and no oracle message at the draw.
  `k08_hD`, `k08_t5`, `k08_t2`: **the three ties**, from `DrawBlind` and three facts on the list of
    places (the place at k; the place at k + 1 is the next of the same link; the row is quiet).
  `k08_ins_of_closed`: THE FOURTH TIE SHRINKS: what the row closes and reads, with "no mark", holds
    in front as soon as what it CLOSES holds there: what it reads comes back from behind.
  `k08_seatLaws_blind`: `SeatLaws` from the kind's law hG, the ties t1, t3, t4, and `DrawBlind`.
THE FENCE IS HIDDEN IN TWO FIELDS: `shown` and `noColl` are asked at ALL strings that agree below
base: they can hold only where the tree of every sampled tenant whose pin is open at the draw lies
below base. No field says that by itself; base is a letter here, the piece's own in the ties.
Limits. `DrawBlind` IS SHOWN AT NO FILLING. The three facts on the list of places are premises here.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.TieLaws
import Johnson.Desc.Sound.PromiseRidesQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8
open Iop
open OnBytes.Model (HTailF2)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place Claim Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start rowOf openSets pubSets pubRowM
  pubStep stepOpen quietRow shapeAt pubHeld sampledIn bookAt standOf standAt mayWait)

/-- **The draw's one writing.** -/
def Drawn (s t : S) : Prop :=
  ∃ (tl : HTailF2) (mm : Array Int) (f : Array Nat),
    s.tl? = some tl ∧ t = s.putTl { tl with cfF := mm, cfFirst := f }

theorem drawn_of_yes {Cl : Type} (p : Par) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok t) :
    Drawn s t := by
  obtain ⟨r, _, _, _, _, _, _, _, _, _, hl⟩ := decide_ok atS p s t rs gs h
  obtain ⟨tl, ht, e⟩ := atS_lay s t _ _ hl
  exact ⟨tl, _, _, ht, e⟩

/-- The stored table, and every tree below base, are as they were. -/
def SameBelow (base : ℕ) (y y' : Strs) : Prop :=
  y'.cell = y.cell ∧ ∀ j x, j < base → y'.col j x = y.col j x

theorem sameBelow_behind (C : CK) (Fr : Frame) (base : ℕ) (ds : List RDT) (y : Fr.E.Str)
    (τ : Iop.Tr (uLT C ds)) : SameBelow base (strsOf Fr y) (strsOf Fr (behind C Fr base ds y τ)) :=
  ⟨funext fun x => cellStays C Fr base ds y τ x, fun j x hj => colStays C Fr base ds y τ j x hj⟩

/-- Where the chain stands is as it was. -/
theorem putTl_stand (s : S) (tl : HTailF2) : standOf (s.putTl tl) = standOf s := by
  have hf : (s.putTl tl).inLink = s.inLink := by
    unfold S.inLink
    rw [putTl_fork]
  unfold standOf
  rw [hf]
  unfold S.putTl
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem putTl_noneWaits (s : S) (tl : HTailF2) : (s.putTl tl).noneWaits = s.noneWaits := by
  unfold S.noneWaits
  rw [(putTl_rest s tl).2.2.2.1]

/-- **The table's book-keeping passes the draw**: from a place to a place of the same link at which
the chain is to stand alike, where no count of rows may wait in front. -/
theorem drawn_shape (links : List ModelPart) (pK pN : Place) (s t : S) (h : Drawn s t)
    (hl : pN.link = pK.link) (hs : standAt links pN = standAt links pK)
    (hw : mayWait links pK = false) (hK : shapeAt links (some pK) s = true) :
    shapeAt links (some pN) t = true := by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  unfold shapeAt at hK ⊢
  dsimp only at hK ⊢
  rw [putTl_stand, putTl_noneWaits, putTl_link, hs, hl]
  rw [hw, Bool.or_false] at hK
  simp only [Bool.and_eq_true] at hK ⊢
  exact ⟨⟨hK.1.1, by rw [hK.1.2]; rfl⟩, hK.2⟩

section
variable {Pp W : Type}

/-- **WHAT THE FILLING OWES FOR THE DRAW.** o': the kind's own condition behind the draw. -/
structure DrawBlind (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (k base : ℕ) (o' : Pp → S → Strs → Prop) : Prop where
  decodes : ∀ z s t y y', Drawn s t → SameBelow base y y' →
    Mg.decodes (z, s) y → Mg.decodes (z, t) y'
  inOrder : ∀ z s t, Drawn s t → Mg.inOrder (z, s) = true → Mg.inOrder (z, t) = true
  held : ∀ z s t, Drawn s t → ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
    Mg.held x.1 x.2 (z, s) = true → Mg.held x.1 x.2 (z, t) = true
  shown : ∀ y y', SameBelow base y y' →
    ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
      Mg.shown x.1 x.2 y → Mg.shown x.1 x.2 y'
  noColl : ∀ z s t y y', Drawn s t → SameBelow base y y' →
    ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
      Mg.noColl x.1 x.2 (z, s) y → Mg.noColl x.1 x.2 (z, t) y'
  pub : ∀ z s t y' p, Drawn s t → ps[k]? = some p → s.failed = none → o' z t y' →
    pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (z, s) = true →
    pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))
      (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p)) (z, t) = true
  pubP : ∀ z s t y' p, Drawn s t → ps[k]? = some p → s.failed = none → o' z t y' →
    (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (z, s)) →
    ∀ q ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p),
      Mg.pubP q (z, t)
  rides : ∀ z s t y y' w i, Drawn s t → SameBelow base y y' → s.failed = none →
    First.onAt Nn Mg links ps[k]? ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (z, s) y →
    (∀ j, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1) j →
      j.holds Nn Mg (z, t) y' w) →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    i.holds Nn Mg (z, s) y w
  reads : ∀ z s t y y' w i, Drawn s t → SameBelow base y y' → s.failed = none →
    i ∈ (rowQ links ps k).ctx → i.holds Nn Mg (z, t) y' w → i.holds Nn Mg (z, s) y w
  trees : Nn.treesAt ps[k + 1]? = Nn.treesAt ps[k]?
  msgs : Nn.msgsAt ps[k + 1]? = Nn.msgsAt ps[k]?

variable {C : CK} {Fr : Frame} {Nn : Numbers} {Mg : Meaning Pp W} {links : List ModelPart}
  {ps : List Place} {k base : ℕ} {o' : Pp → S → Strs → Prop}

/-- **"decodes" rides past the draw's yes.** -/
theorem k08_hD (D : DrawBlind Nn Mg links ps k base o') (p : ParW) (ds : List RDT) (z : Pp)
    (a b : S × Fr.E.Str)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT C ds), b.2 = behind C Fr base ds a.2 τ)
    (hd : Mg.decodes (z, a.1) (strsOf Fr a.2)) : Mg.decodes (z, b.1) (strsOf Fr b.2) := by
  obtain ⟨rs, gs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  rw [hb]
  exact D.decodes z a.1 b.1 _ _ (drawn_of_yes p.toPar a.1 b.1 rs gs hy)
    (sameBelow_behind C Fr base ds a.2 τ) hd

/-- **What rides past the draw.** -/
theorem k08_t5 (D : DrawBlind Nn Mg links ps k base o') (p : ParW) (ds : List RDT) (z : Pp)
    (a b : S × Fr.E.Str) (w : W) (i : Item) (ha : onQ Nn Mg links ps (fun s => (z, s)) k a)
    (hm : ¬ a.1.failed ≠ none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT C ds), b.2 = behind C Fr base ds a.2 τ)
    (hr : relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hi : ¬ insQ links ps k i) : meansQ Nn Mg (fun s => (z, s)) i a w := by
  obtain ⟨rs, gs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  have h1 : ∀ j, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1) j →
      j.holds Nn Mg (z, b.1) (strsOf Fr (behind C Fr base ds a.2 τ)) w := by
    intro j hj
    have h2 : meansQ Nn Mg (fun s => (z, s)) j b w := hr j hj
    unfold meansQ at h2
    rw [hb] at h2
    exact h2
  exact D.rides z a.1 b.1 _ _ w i (drawn_of_yes p.toPar a.1 b.1 rs gs hy)
    (sameBelow_behind C Fr base ds a.2 τ) (Classical.byContradiction fun h => hm h) ha h1 ho hi

/-- **What the draw's row reads comes back from behind; "no mark" stands in front: so what the row
closes AND reads holds in front as soon as what it CLOSES does.** -/
theorem k08_ins_of_closed (D : DrawBlind Nn Mg links ps k base o') (p : ParW) (ds : List RDT)
    (z : Pp) (a b : S × Fr.E.Str) (w : W) (hm : ¬ a.1.failed ≠ none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT C ds), b.2 = behind C Fr base ds a.2 τ)
    (hw : relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w)
    (hc : ∀ i ∈ (rowQ links ps k).ins, meansQ Nn Mg (fun s => (z, s)) i a w) :
    relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w := by
  obtain ⟨rs, gs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  have hf : a.1.failed = none := Classical.byContradiction fun h => hm h
  intro i hi
  rcases List.mem_append.1 hi with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact hc i h2
    · have h3 : meansQ Nn Mg (fun s => (z, s)) i b w :=
        hw i (List.mem_append_left _ (List.mem_append_right _ h2))
      unfold meansQ at h3 ⊢
      rw [hb] at h3
      exact D.reads z a.1 b.1 _ _ w i (drawn_of_yes p.toPar a.1 b.1 rs gs hy)
        (sameBelow_behind C Fr base ds a.2 τ) hf h2 h3
  · obtain rfl := List.mem_singleton.1 h1
    exact hf

/-- **The promise behind the draw.** pK, pN: the places at k and at k + 1. -/
theorem k08_t2 (D : DrawBlind Nn Mg links ps k base o') (p : ParW) (ds : List RDT) (pK pN : Place)
    (hK : ps[k]? = some pK) (hN : ps[k + 1]? = some pN) (hq : quietRow (rowOf links pK) = true)
    (hl : pN.link = pK.link) (hs : standAt links pN = standAt links pK)
    (hw : mayWait links pK = false) (z : Pp) (a b : S × Fr.E.Str)
    (ha : onQ Nn Mg links ps (fun s => (z, s)) k a)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT C ds), b.2 = behind C Fr base ds a.2 τ)
    (ho : o' z b.1 (strsOf Fr b.2)) : onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b := by
  obtain ⟨rs, gs, hy⟩ := hy
  obtain ⟨τ, hb⟩ := hb
  have hd := drawn_of_yes p.toPar a.1 b.1 rs gs hy
  have hsb : SameBelow base (strsOf Fr a.2) (strsOf Fr b.2) := by
    rw [hb]
    exact sameBelow_behind C Fr base ds a.2 τ
  have hm : b.1.failed = a.1.failed := hear_leaves_mark p.toPar a.1 rs gs b.1 hy
  have hst : b.1.st = a.1.st := hear_leaves_statement p.toPar a.1 rs gs b.1 hy
  have hbk : b.1.book = a.1.book := hear_leaves_book p.toPar a.1 rs gs b.1 hy
  refine onQ_step_quiet Nn Mg links ps (fun s => (z, s)) k pK hK hq a b ha ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · intro h
    show b.1.failed ≠ none
    rw [hm]
    exact h
  · exact D.decodes z a.1 b.1 _ _ hd hsb
  · intro hf
    rw [hN]
    have h0 := ha
    unfold onQ First.onAt at h0
    rcases h0.2 with h1 | h1
    · exact absurd hf h1
    · have h2 := h1.1
      simp only [Bool.and_eq_true] at h2
      rw [hK] at h2
      exact drawn_shape links pK pN a.1 b.1 hd hl hs hw h2.1.1.1.1.1
  · show b.1.st.groups = a.1.st.groups
    rw [hst]
  · show b.1.book.place = a.1.book.place
    rw [hbk]
  · exact D.inOrder z a.1 b.1 hd
  · intro hf
    exact D.pub z a.1 b.1 _ pK hd hK hf ho
  · intro _ h
    unfold bookAt at h ⊢
    show (b.1.book.trees.size == _ && b.1.book.place.size == b.1.st.oracles.size &&
      b.1.st.oracles.size == _) = true
    rw [hbk, hst, D.trees, D.msgs]
    exact h
  · intro hf
    exact D.pubP z a.1 b.1 _ pK hd hK hf ho
  · exact D.held z a.1 b.1 hd
  · exact D.shown _ _ hsb
  · exact D.noColl z a.1 b.1 _ _ hd hsb

/-- **`SeatLaws` from the kind's law, three ties and what the filling owes for the draw.** -/
theorem k08_seatLaws_blind (q : Piece C Fr (Pp × S) Claim W) (p : ParW)
    (o : S × Fr.E.Str → Prop) (R R' : S × Fr.E.Str → W → Prop) (oB : S × Fr.E.Str → Prop)
    (hoB : ∀ z b, oB b → o' z b.1 (strsOf Fr b.2))
    (D : DrawBlind Nn Mg links ps k q.base o') (pK pN : Place)
    (hK : ps[k]? = some pK) (hN : ps[k + 1]? = some pN) (hq : quietRow (rowOf links pK) = true)
    (hl : pN.link = pK.link) (hs : standAt links pN = standAt links pK)
    (hw : mayWait links pK = false)
    (hG : ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        o oB R R')
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → o a)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      oB b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R' b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      oB b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w) :
    SeatLaws links ps k q Nn Mg (whole p) :=
  k08_seatLaws links ps k q Nn Mg p o oB R R' hG t1
    (fun z a b ha _ hy hb ho =>
      k08_t2 D p q.ds pK pN hK hN hq hl hs hw z a b ha hy hb (hoB z b ho))
    t3 t4
    (fun z a b w i ha hm hy hb _ hr ho hi => k08_t5 D p q.ds z a b w i ha hm hy hb hr ho hi)
    (fun z a b hy hb hd => k08_hD D p q.ds z a b hy hb hd)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.drawn_shape
#print axioms VerifiableInference.Desc.First.K8.k08_hD
#print axioms VerifiableInference.Desc.First.K8.k08_t5
#print axioms VerifiableInference.Desc.First.K8.k08_ins_of_closed
#print axioms VerifiableInference.Desc.First.K8.k08_t2
#print axioms VerifiableInference.Desc.First.K8.k08_seatLaws_blind
