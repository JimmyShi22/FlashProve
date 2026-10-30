-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Seam.lean: THE SEAM OF KIND K5's LAW. The law (K05_keepsW_all_any,
Att/K05KeepsAny.lean, and the elder forms) is stated over an abstract reduction over written rounds;
five premises tie that reduction to the kind's block (hyes, hpass, hd, he, hon'), and a sixth (pin)
ties the world's part to the statement in front. Here each of the five is a theorem AT THE KIND's
OWN PIECE of the rule of composition (k5Piece, Att/K05Piece.lean; Piece.ior.red,
Johnson/Desc/Sound/ChainRule.lean), and the pin is brought to one premise on the relation behind.

Main names:
  `wr`, `written p`: the kind's declared ROUNDS as the data of written rounds: each round's entry;
  the
    format's own kind of the entry's name (Fmt.kindOf); the entry's own cut of the message
    (Fmt.DeclaredRound.items); no tree is sent, nothing is opened, nothing stored is read.
  `EntCut`, `entries_cut`, `entriesOf_cut`, `rounds_cut`: each of the kind's entries has no answer
    and no root, a message of whole scalars, and the format knows its name as "elems", "join" or
    "nothing".
  `seam_yes`, `seam_pass`: AT ANY DATA ds: where the piece puts out b at (a, τ): decide's yes at the
    record a.1 on the view of τ without the sealed digest, with the record b.1; that view passes
    roundsFit; every drawn element is below the prime · the tests of work passed.
  `seam_plain`, `seam_entries`, `seam_kinds`: at ds := written p: every written round is Plain; the
    entries are the kind's; each round's kind is the format's kind of its entry's name.
  `LaidBehind`, `seam_on'`: what holds for certain of what the piece puts out from a statement with
    "on": nothing was owed; the hearing returned on rounds that fit and whose drawn elements are
    below
    the prime; the record behind is the seat's lay of just what was heard; the oracles below the
    base are as they were.
  `seam_pin_dec`: the pin from a decoder: the relation behind says "the world's part is dec of the
    oracles behind"; dec reads the stored table and trees below the base alone.
  `PinItem`, `mOfItem`, `seam_pin_item`: the pin from an item of the border without a named decoder:
    the item fixes the part; it reads the record through a reading that the seat's lay keeps, and
    the oracles below the base alone; the relation behind gives the item.

Premises: none for the five. For the pin: what its two forms name.
Limits. (1) The five say what "puts out" is: they bound nothing. seam_yes names the kind's own
decide: a block with the kind's ROUNDS and another decision does not meet it
(Att/K05SeamSilly.lean).
A block that says no to all meets all five for nothing. (2) That a file's written rounds at the
kind's stretch are `written p` is not shown: it is the format's (how a plan's rounds are made of
declared rounds) and the rule's (Tiled). (3) THE PIN IS NOT PAID: that a border's relation holds
such an item, that the item fixes the part, and that the trees which it reads are numbered below
the base, are premises; shown of no relation here. SILLY FILLINGS OF PinItem: holds := False meets
the three laws, and hR' then says that
the relation behind is empty: the law is idle; holds := True forces the part to be constant. So the
record is worth what its filler is. The filling that is meant (the table of joints' item "the
witness's messages of the sampled tenants that the segment sends at its first moment are what their
committed words decode to with their samples") IS NOT TYPED HERE. (4) `EntCut` is kin of `EntOne`
(Att/K05Member.lean), which says "the format knows the name" without saying as what. (5) seam_yes,
seam_pass and seam_on' hold at any ds; the law also wants he and hd: at a ds whose entries are not
the kind's the three are true and the law cannot be called. (6) In `LaidBehind` the rounds rs stand
under "there are" and are tied to no transcript: what the next piece's condition spends of it is not
known to us; whatever else holds for certain of what the piece puts out can be added at no cost
(Leads.conseq, Johnson/Desc/Plain/Leads.lean).
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeamOut
import Johnson.Desc.First.Att.K05Piece
import Johnson.Desc.First.Att.K05Plain
import Johnson.Desc.StepKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run (ckP)

/-! ## The kind's rounds as written rounds -/

/-- A declared round that sends no root, opens nothing and reads nothing stored, as the data of a
written round. -/
def wr (r : Fmt.DeclaredRound) : RDT :=
  { entry := r.entry, kind := (Fmt.kindOf r.entry.name).getD .nothing, items := r.items,
    trees := [], opens := [], stored := [] }

/-- The kind's declared rounds as the data of written rounds. -/
def written (p : Par) : List RDT := (rounds p).map wr

/-- No answer, no root; a message of whole scalars; a name that the format knows as "elems", "join"
or "nothing". -/
structure EntCut (e : Fmt.Entry) : Prop where
  answers : e.answers = 0
  roots : e.roots = 0
  msg : 24 ∣ e.msg
  kind : Fmt.kindOf e.name = some .elems ∨ Fmt.kindOf e.name = some .join ∨
    Fmt.kindOf e.name = some .nothing

theorem entries_cut (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, EntCut e := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      exact ⟨rfl, rfl, ⟨_, rfl⟩,
        Or.inr (Or.inl (show Fmt.kindOf "PSC epsilon" = some .join by decide))⟩
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 he
      exact ⟨rfl, rfl, ⟨_, rfl⟩, Or.inl (show Fmt.kindOf "PSC round" = some .elems by decide)⟩
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨rfl, rfl, ⟨_, rfl⟩, Or.inl (show Fmt.kindOf "PSC Y" = some .elems by decide)⟩
      · obtain rfl := List.mem_singleton.1 he
        exact ⟨rfl, rfl, ⟨_, rfl⟩,
          Or.inr (Or.inr (show Fmt.kindOf "PSC values" = some .nothing by decide))⟩

theorem entriesOf_cut : ∀ (l : List Stage) (lead : ℕ), ∀ e ∈ entriesOf lead l, EntCut e
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, e, h => entriesOf_cut l (lead + n) e h
  | .sum vs x :: l, lead, e, h => by
    rcases List.mem_append.1
      (show e ∈ MaskedSum.entries ⟨lead, vs, some x⟩ ++ entriesOf 0 l from h) with h | h
    · exact entries_cut _ e h
    · exact entriesOf_cut l 0 e h
  | .batch rows :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, ⟨_, rfl⟩, Or.inl (show Fmt.kindOf "BAT-sigma" = some .elems by decide)⟩
    · exact entriesOf_cut l 0 e h
  | .point n :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, rfl, ⟨_, rfl⟩, Or.inl (show Fmt.kindOf "ZERO" = some .elems by decide)⟩
    · exact entriesOf_cut l 0 e h

theorem rounds_cut (p : Par) : ∀ r ∈ rounds p, EntCut r.entry := by
  intro r hr
  unfold rounds at hr
  obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 hr
  have := entriesOf_cut _ _ e0 h0
  show EntCut (if e0.drawE == 0 then e0 else { e0 with work := p.work })
  split
  · exact this
  · exact ⟨this.answers, this.roots, this.msg, this.kind⟩

/-- **he.** -/
theorem seam_entries (p : Par) : (written p).map (·.entry) = (rounds p).map (·.entry) := by
  unfold written
  rw [List.map_map]
  rfl

/-- Each written round's kind is the format's kind of its entry's name. -/
theorem seam_kinds (p : Par) : ∀ d ∈ written p, Fmt.kindOf d.entry.name = some d.kind := by
  intro d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  show Fmt.kindOf r.entry.name = some ((Fmt.kindOf r.entry.name).getD .nothing)
  rcases (rounds_cut p r hr).kind with h | h | h <;> rw [h] <;> rfl

/-- **hd.** -/
theorem seam_plain (p : Par) : ∀ d ∈ written p, Plain (toRD d) := by
  intro d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  obtain ⟨a1, a2, a3, a4⟩ := rounds_ok p r.entry (List.mem_map_of_mem hr)
  have c := rounds_cut p r hr
  have hcut : r.items = List.replicate (r.entry.msg / 24) Fmt.Item.e := by
    show r.entry.cut = _
    unfold Fmt.Entry.cut
    rw [c.answers, c.roots]
    simp
  refine ⟨fun it hi => ?_, ?_, a1, a2, a3, ?_, ?_, a4⟩
  · have hi' : it ∈ r.items := hi
    rw [hcut] at hi'
    exact List.eq_of_mem_replicate hi'
  · show r.items.length = r.entry.msg / 24
    rw [hcut, List.length_replicate]
  · show (Fmt.kindOf r.entry.name).getD .nothing ≠ .sealed
    rcases c.kind with h | h | h <;> rw [h] <;> decide
  · show (Fmt.kindOf r.entry.name).getD .nothing ≠ .seeds
    rcases c.kind with h | h | h <;> rw [h] <;> decide

/-! ## What the piece's yes holds -/

section
variable {S Cl W : Type} {F : Frame}

/-- **hyes**, at any data of written rounds, at every statement. -/
theorem seam_yes (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) ds)) (b : S × F.E.Str)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b) :
    decide seat p a.1 ((rvT (ckP .two) ds τ).map noDigest) = .ok b.1 ∧
      roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
      ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true := by
  obtain ⟨_, ⟨cols, k, hs⟩, _⟩ :=
    piece_out_step (k5Piece (W := W) (ckP .two) F seat claims p base ds err) rfl a b τ h
  obtain ⟨hf, gs, hd⟩ := VerifiableInference.Desc.Keeps.step_fit _ _ _ _ _ _ _ hs
  refine ⟨hd, (roundsFit_noDigest _ _).trans hf, fun r hr x hx => ?_⟩
  obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hr
  exact rvT_okE ds τ r0 h0 x hx

/-- **hpass.** -/
theorem seam_pass (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) ds)) (b : S × F.E.Str)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b) :
    passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true :=
  (piece_out_step (k5Piece (W := W) (ckP .two) F seat claims p base ds err) rfl a b τ h).1

/-- What holds for certain of what the piece puts out from a statement with "on". -/
def LaidBehind (F : Frame) (seat : Seat S) (p : Par) (base : ℕ) (on : S × F.E.Str → Prop)
    (b : S × F.E.Str) : Prop :=
  ∃ (a : S × F.E.Str) (F0 G : Fork) (h : Heard) (rs : List Fmt.RoundView), on a ∧ seat.owed a.1 = none ∧
    seat.ledger a.1 = some F0 ∧ roundsFit (rounds p) rs = true ∧
    (∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true) ∧
    hear p.own (F0, rs, 0) = some (h, G, [], 0) ∧ seat.lay a.1 h G = some b.1 ∧
    SameBelow F base a.2 b.2

/-- **hon'**, at that condition. -/
theorem seam_on' (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds))
    (on : S × F.E.Str → Prop) (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) ds)) (b : S × F.E.Str)
    (ha : on a)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b) :
    LaidBehind F seat p base on b := by
  obtain ⟨h1, h2, h3⟩ := seam_yes seat claims p base ds err a τ b h
  obtain ⟨ho, F0, hh, G, hl, hr, hy⟩ := (decide_lays seat p a.1 b.1 _).1 h1
  exact ⟨a, F0, G, hh, _, ha, ho, hl, h2, h3, hr, hy,
    piece_same_below (k5Piece (W := W) (ckP .two) F seat claims p base ds err) a b τ h⟩

/-! ## The pin -/

/-- **The pin, from a decoder.** hR': THE ONE PREMISE ON THE RELATION BEHIND. hdec: the decoder
reads
the stored table and trees below the base alone. -/
theorem seam_pin_dec {Mg : Type} (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (part : W → Mg) (dec : F.E.Str → Mg)
    (hdec : ∀ y y', SameBelow F base y y' → dec y' = dec y) (R' : S × F.E.Str → W → Prop)
    (hR' : ∀ b w, R' b w → part w = dec b.2) (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) ds))
    (b : S × F.E.Str) (w : W)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b)
    (hw : R' b w) : part w = dec a.2 :=
  (hR' b w hw).trans (hdec _ _
    (piece_same_below (k5Piece (W := W) (ckP .two) F seat claims p base ds err) a b τ h))

/-- **An item of the border that pins the world's part**, without a named decoder. Rc: what the item
reads of the record (the samples). -/
structure PinItem (F : Frame) (seat : Seat S) (base : ℕ) (W Mg : Type) where
  Rc : Type
  rc : S → Rc
  holds : Rc → F.E.Str → W → Prop
  part : W → Mg
  /-- the item fixes the part: two worlds with the item at one statement have one part -/
  fixes : ∀ r y w w', holds r y w → holds r y w' → part w = part w'
  /-- the seat's lay keeps what the item reads of the record -/
  lay : ∀ s h G s', seat.lay s h G = some s' → rc s' = rc s
  /-- the item reads the stored table and trees below the base alone -/
  fenced : ∀ r y y' w, SameBelow F base y y' → holds r y' w → holds r y w

open Classical in
/-- The part that the item fixes at a statement; m0 where no world has the item there. -/
noncomputable def mOfItem {Mg : Type} {seat : Seat S} {base : ℕ} (I : PinItem F seat base W Mg)
    (m0 : Mg) (a : S × F.E.Str) : Mg :=
  if h : ∃ w, I.holds (I.rc a.1) a.2 w then I.part h.choose else m0

/-- **The pin, from such an item.** hR': THE ONE PREMISE ON THE RELATION BEHIND. -/
theorem seam_pin_item {Mg : Type} (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (I : PinItem F seat base W Mg) (m0 : Mg)
    (R' : S × F.E.Str → W → Prop) (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w)
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) ds)) (b : S × F.E.Str) (w : W)
    (h : (k5Piece (W := W) (ckP .two) F seat claims p base ds err).ior.red.out a τ = some b)
    (hw : R' b w) : I.part w = mOfItem I m0 a := by
  obtain ⟨h1, _, _⟩ := seam_yes seat claims p base ds err a τ b h
  obtain ⟨_, F0, hh, G, _, _, hy⟩ := (decide_lays seat p a.1 b.1 _).1 h1
  have k : I.holds (I.rc a.1) a.2 w := by
    have := hR' b w hw
    rw [I.lay _ _ _ _ hy] at this
    exact I.fenced _ _ _ _
      (piece_same_below (k5Piece (W := W) (ckP .two) F seat claims p base ds err) a b τ h) this
  have ex : ∃ w, I.holds (I.rc a.1) a.2 w := ⟨w, k⟩
  unfold mOfItem
  rw [dif_pos ex]
  exact I.fixes _ _ _ _ k ex.choose_spec

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seam_entries
#print axioms VerifiableInference.Desc.First.Att.P.seam_kinds
#print axioms VerifiableInference.Desc.First.Att.P.seam_plain
#print axioms VerifiableInference.Desc.First.Att.P.seam_yes
#print axioms VerifiableInference.Desc.First.Att.P.seam_pass
#print axioms VerifiableInference.Desc.First.Att.P.seam_on'
#print axioms VerifiableInference.Desc.First.Att.P.seam_pin_dec
#print axioms VerifiableInference.Desc.First.Att.P.seam_pin_item
