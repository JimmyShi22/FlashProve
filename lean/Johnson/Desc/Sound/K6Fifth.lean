-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K6Fifth.lean: THE OUTPUT HEAD'S BLOCK'S FIFTH TIE TO THE TABLE OF JOINTS: WHAT
RIDES PAST IT, ITEM BY ITEM, AT THE FILLING OF THE SIX LETTERS ON THE ORACLES (`meaningSig`). A
rule: which items ride is a list's evaluation; the index masks' pin is paid; what is left is one
premise an item. NO RESULT ON THE PROTOCOL.

What is said.
  `open_iff_mem`: where the table's tests `readsOpen` and `rowsApart` say yes, the rule's open set
    at border k has just the members of the list on which the promise runs (two lemmas of
    Johnson/Desc/Sound/SpineList.lean, joined).
  `ridersK6 m`: the six items that ride past K6's block. `riders61_small`, `riders341_full`, and the
    two tests at both lists: BY THE KERNEL'S EVALUATION: every item that is open in front of the
    block is closed or read by its row, or "no mark", or one of the six.
  `K6Riders`: what is left: fenceI (ON THE PLAN) · pile, carried, sample, position, objects: each
    rides back.
  `k6_t5_of_riders`: the fifth tie in the form of `K6Left` (Johnson/Desc/Sound/K6AtSig.lean).

Limits. Each of the five has the table's promise in front and behind, no mark and the yes in hand.
That they can be met is not said: the five letters have no filling here. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6Third
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item start readsOpen flatPlacesOf)

/-- **The rule's open set at border k has just the members of the promise's list.** -/
theorem open_iff_mem (links : List ModelPart) (ps : List Place)
    (hr : readsOpen links ps (start links) = true) (ha : rowsApart links ps = true)
    (hu : Item.unmarked ∈ start links) (k : ℕ) (hk : k ≤ ps.length) (i : Item) :
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i ↔ i ∈ openQ links ps k :=
  (openIsList Item (insL links ps) (outsL links ps) (start links) k i).trans
    (openL_iff_openSets links ps (start links) hr ha hu k hk i)

/-- The six items that ride past K6's block. -/
def ridersK6 (m : ℕ) : List Item :=
  [.pile, .pinI, .row m .carried, .row m (.sample 0), .row m .position, .formsT m 3 "objects"]

set_option maxRecDepth 1000000 in
theorem reads_small :
    readsOpen linksSmall (flatPlacesOf linksSmall true) (start linksSmall) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem apart_small : rowsApart linksSmall (flatPlacesOf linksSmall true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem riders61_small : ∀ i ∈ openQ linksSmall (flatPlacesOf linksSmall true) 61,
    i ∈ insL linksSmall (flatPlacesOf linksSmall true) 61 ∨ i ∈ ridersK6 4 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem reads_full :
    readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem apart_full : rowsApart linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem riders341_full : ∀ i ∈ openQ linksFull (flatPlacesOf linksFull true) 341,
    i ∈ insL linksFull (flatPlacesOf linksFull true) 341 ∨ i ∈ ridersK6 24 := by decide +kernel

end VerifiableInference.Desc.Sound

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning start readsOpen)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT onQ meansQ relQ insQ outsQ insL
  openAfter openQ strsOf meaningSig ridersK6 open_iff_mem rowsApart)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (msT : List Mem) (fld : Fmt.Fld)
  (Fr : Frame) (N : Numbers) (Mg₀ : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List Place) (k m : ℕ)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))

/-- The table's meaning with its six letters on the oracles filled. -/
local notation "MG" => meaningSig cs G arr smp msT decT Mg₀

/-- **WHAT IS LEFT OF K6's FIFTH TIE, ONE FIELD AN ITEM.** -/
structure K6Riders : Prop where
  /-- ON THE PLAN: the index masks' tree was sent in front of the piece -/
  fenceI : N.index.1 < q.base
  pile : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b →
    Mg₀.pile b.1 (strsOf Fr b.2) w → Mg₀.pile a.1 (strsOf Fr a.2) w
  carried : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b →
    Mg₀.row m .carried b.1 (strsOf Fr b.2) w → Mg₀.row m .carried a.1 (strsOf Fr a.2) w
  sample : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b →
    Mg₀.row m (.sample 0) b.1 (strsOf Fr b.2) w → Mg₀.row m (.sample 0) a.1 (strsOf Fr a.2) w
  position : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b →
    Mg₀.row m .position b.1 (strsOf Fr b.2) w → Mg₀.row m .position a.1 (strsOf Fr a.2) w
  objects : ∀ a τ b w, onQ (Fr := Fr) N MG links ps (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b →
    Mg₀.formsT m 3 "objects" b.1 (strsOf Fr b.2) w →
    Mg₀.formsT m 3 "objects" a.1 (strsOf Fr a.2) w

variable {cs G arr smp decT msT fld Fr N Mg₀ links ps k m q}

/-- **THE FIFTH TIE.** hr ha hu hk hRid: ON THE TABLE: tests and an evaluation at the list. -/
theorem k6_t5_of_riders {Wp : OnBytes.Model.Verify.Public} {l : ℕ} {bef : List (ℕ × ℕ)}
    {B bS : Block S Claim} (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (I : K6Riders cs G arr smp decT msT fld Fr N Mg₀ links ps k m q)
    (hr : readsOpen links ps (start links) = true) (ha' : rowsApart links ps = true)
    (hu : Item.unmarked ∈ start links) (hk : k ≤ ps.length)
    (hRid : ∀ i ∈ openQ links ps k, i ∈ insL links ps k ∨ i ∈ ridersK6 m)
    (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (w : Wit Cells Tok MsgT) (i : Item)
    (ha : onQ (Fr := Fr) N MG links ps (fun a => a) k a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b)
    (hon : onQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b)
    (hall : relQ (Fr := Fr) N MG links ps (fun a => a) (k + 1) b w)
    (hi : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hin : ¬ insQ links ps k i) : meansQ (Fr := Fr) N MG (fun a => a) i a w := by
  have hbw : meansQ (Fr := Fr) N MG (fun a => a) i b w := hall i (Or.inl ⟨hi, hin⟩)
  rcases hRid i ((open_iff_mem links ps hr ha' hu k hk i).1 hi) with h | h
  · exact absurd h hin
  · unfold ridersK6 at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact I.pile a τ b w ha hm hb hon hbw
    · obtain ⟨h1, h2⟩ := hbw
      refine ⟨h1, fun x hx hsx => ?_⟩
      have e : x.1.seat x.2 = (N.index.1, N.index.2) := hsx
      refine ((Sound.rides (Cells := Cells) (Tok := Tok) cs G arr smp q [x] ?_ ?_ a b τ hb x
        (List.mem_singleton.2 rfl)).1 w).1 (h2 x hx hsx)
      · intro x' hx'
        rw [List.mem_singleton.1 hx', e]
        exact I.fenceI
      · intro a' τ' b' hb' x' _
        obtain ⟨o, F1, X, Q, _, _, _, e'⟩ := k6_behind H a' b' τ' hb'
        rw [e', hBl.smp]
    · exact I.carried a τ b w ha hm hb hon hbw
    · exact I.sample a τ b w ha hm hb hon hbw
    · exact I.position a τ b w ha hm hb hon hbw
    · exact I.objects a τ b w ha hm hb hon hbw

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Sound.open_iff_mem
#print axioms VerifiableInference.Desc.Sound.reads_full
#print axioms VerifiableInference.Desc.Sound.apart_full
#print axioms VerifiableInference.Desc.Sound.riders61_small
#print axioms VerifiableInference.Desc.Sound.riders341_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t5_of_riders
