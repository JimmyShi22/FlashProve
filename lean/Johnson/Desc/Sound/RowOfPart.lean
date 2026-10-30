-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RowOfPart.lean: FROM A KIND'S LAW AT ITS OWN BLOCK TO ONE CONJUNCT OF WHAT THE
FIRST CHAIN'S TABLE OF JOINTS ASKS, AT THE REAL ROW'S PIECE: for a row that lays nothing into the
witness. Four lemmas. No protocol's soundness is said. `Block.Narrows.below` stands not in
this file but in Johnson/Desc/Sound/MergeNarrowMakers.lean.

Why. A kind's files prove its law at a piece over the chain's carried record S that holds `below
b₀`, b₀ the kind's own block, with the identity as its extractor. The piece of a description
(`OfDesc`, DescThree.lean) holds `(below B).lift Prod.snd …` over the public part and the record,
where B is b₀ AS THE SEAT LAYS IT: under another name, with guards behind its `decide`. The plain
road asks the law at that piece with the table's extractor laid in (`Piece.withMap`, ReExt.lean), at
the table's own promises and items.
  `rowOfPart`: **the wrappers**: name and guards (`goodIn_narrow`, MergeNarrow.lean), `below`, the
    lift (`ownOfPart`, LiftOwn.lean), the table's extractor: the law at `below b₀`, FOR EVERY VALUE
    z OF THE PUBLIC PART, gives `Piece.Own` at the real piece so turned, z read off the record; what
    the guards' yes gives of the record behind (G) is added to the promise behind.
  `frames_of_rides`: at a row that lays nothing `Piece.Frames` is "every open item that is not
    closed holds in front of the block if it holds behind it, of the same witness".
  `rowAtTable`: the conjunct of `EachOwn` at block number k: `rowOfPart` THROUGH THE TABLE'S OWN
    WIDE DOOR `ownAtTableWide` (BordersQ.lean): its four implications between the kind's words and
    the table's (t1 to t4), each asked AT UNMARKED STATEMENTS INSIDE THE PROMISE; the second, third
    and fourth at a yes of the block; the third and fourth with the kind's promise behind in hand,
    the fourth also with what the row opens at (b, w); and its two facts on the block's text (hMark:
    a mark stays; hDec: "the stored table decodes with the record" rides); and `frames_of_rides`.

Why the table's own door. A door whose first tie runs over every statement inside the table's
promise will not do. A marked record is inside every promise of the table: no
kind's condition follows there: such a tie can be met at no useful filling. So the ties here are
asked at unmarked statements.

Limits. For a row whose extractor is the identity (hE). "For every z": also at public parts that no
run reaches. Rules: the premises are met by no block here. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeNarrowMakers
import Johnson.Desc.Sound.LiftOwn
import Johnson.Desc.Sound.ReExt
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {P S Cl W ι κ : Type} {C : CK} {F : Frame}

/-- **The wrappers.** q: the real row's piece; B: the kind's block b₀ as the seat lays it. -/
theorem rowOfPart (q : Piece C F (P × S) Cl W) (B b₀ : Block S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (hN : B.Narrows b₀) (G : S → Prop)
    (hG : ∀ s rs gs s', B.decide s rs gs = .ok s' → G s')
    (E : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (on on' : P → S × F.E.Str → Prop) (means : P → ι → S × F.E.Str → W → Prop) (In Out : ι → Prop)
    (law : ∀ z, (⟨below b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C F S Cl W).Own (on z) (on' z) (means z) In Out) :
    (q.withMap E).Own (fun a => on a.1.1 (a.1.2, a.2))
      (fun a => on' a.1.1 (a.1.2, a.2) ∧ G a.1.2) (fun i a w => means a.1.1 i (a.1.2, a.2) w) In
      Out :=
  ownOfPart (P × S) S P Cl W ι C F Prod.snd (fun t s => (t.1, s)) Prod.fst (q.withMap E) (below B)
    (fun _ _ _ w => w) on (fun z b => on' z b ∧ G b.1) means In Out (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => rfl) hq (withMap_id q E hE)
    (fun z => goodIn_narrow ⟨below b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ (below B)
      hN.below G (fun s rs gs s' e => hG s rs gs s' ((below_narrows B).2 s rs gs s' e)) _ _ _ _
      (law z))

/-- **A yes of the real row's piece is a yes of the seated block's `decide`**, at the record's
carried part; the public part stays. -/
theorem yes_of_part (q : Piece C F (P × S) Cl W) (B : Block S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (a b : (P × S) × F.E.Str)
    (τ : Iop.Tr (uLT C q.ds)) (h : q.ior.red.out a τ = some b) :
    (∃ rs gs, B.decide a.1.2 rs gs = .ok b.1.2) ∧ b.1.1 = a.1.1 := by
  obtain ⟨rs, gs, hd⟩ := out_yes q a b τ h
  rw [hq] at hd
  have e' : ((below B).decide a.1.2 rs gs).map (fun s => (a.1.1, s)) = .ok b.1 := hd
  cases hb : (below B).decide a.1.2 rs gs with
  | error m =>
    rw [hb] at e'
    cases e'
  | ok s' =>
    rw [hb] at e'
    have e2 : (a.1.1, s') = b.1 := Except.ok.inj e'
    rw [← e2]
    exact ⟨⟨rs, gs, (below_narrows B).2 _ _ _ _ hb⟩, rfl⟩

/-- At a row that lays nothing: what is owed for the items that ride past. -/
theorem frames_of_rides (q : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In : ι → Prop)
    (hr : ∀ a τ b w i, on a → q.ior.red.out a τ = some b → on' b → O i → ¬ In i → means i b w →
      means i a w) :
    (q.withMap E).Frames on on' means O In := fun a τ b w i ha hb hb' hO hI hm => by
  rw [withMap_id q E hE]
  exact hr a τ b w i ha hb hb' hO hI hm

/-- **THE CONJUNCT OF `EachOwn` AT A ROW THAT LAYS NOTHING, AT THE REAL ROW'S PIECE**, through the
table's own door. -/
theorem rowAtTable (q : Piece C F (P × First.S) Cl W) (B b₀ : Block First.S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (hN : B.Narrows b₀) (G : First.S → Prop) (hG : ∀ s rs gs s', B.decide s rs gs = .ok s' → G s')
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (on on' : P → First.S × F.E.Str → Prop) (means : P → ι → First.S × F.E.Str → W → Prop)
    (In Out : ι → Prop)
    (law : ∀ z, (⟨below b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C F First.S Cl W).Own (on z) (on' z) (means z) In Out)
    (N : First.Numbers) (Mg : First.Meaning P W) (links : List First.ModelPart) (ps : List Place) (k : ℕ)
    (t1 : ∀ a, onQ (Fr := F) N Mg links ps (fun a => a) k a → ¬ a.1.2.failed ≠ none →
      on a.1.1 (a.1.2, a.2))
    (t2 : ∀ a τ b, onQ (Fr := F) N Mg links ps (fun a => a) k a → ¬ a.1.2.failed ≠ none →
      q.ior.red.out a τ = some b → on' b.1.1 (b.1.2, b.2) ∧ G b.1.2 →
      onQ (Fr := F) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := F) N Mg links ps (fun a => a) k a → ¬ a.1.2.failed ≠ none →
      q.ior.red.out a τ = some b → on' b.1.1 (b.1.2, b.2) ∧ G b.1.2 →
      relAt (meansQ (Fr := F) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means b.1.1) Out (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := F) N Mg links ps (fun a => a) k a → ¬ a.1.2.failed ≠ none →
      q.ior.red.out a τ = some b → on' b.1.1 (b.1.2, b.2) ∧ G b.1.2 →
      relAt (meansQ (Fr := F) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means a.1.1) In (a.1.2, a.2) w →
      relAt (meansQ (Fr := F) N Mg fun a => a) (insQ links ps k) a w)
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → a.1.2.failed ≠ none → b.1.2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf F a.2) →
      Mg.decodes b.1 (strsOf F b.2))
    (hr : ∀ a τ b w i, onQ (Fr := F) N Mg links ps (fun a => a) k a →
      q.ior.red.out a τ = some b → onQ (Fr := F) N Mg links ps (fun a => a) (k + 1) b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := F) N Mg (fun a => a) i b w → meansQ (Fr := F) N Mg (fun a => a) i a w) :
    (q.withMap E).Own (onQ (Fr := F) N Mg links ps (fun a => a) k)
        (onQ (Fr := F) N Mg links ps (fun a => a) (k + 1)) (meansQ N Mg fun a => a)
        (insQ links ps k) (outsQ links ps k) ∧
      (q.withMap E).Frames (onQ (Fr := F) N Mg links ps (fun a => a) k)
        (onQ (Fr := F) N Mg links ps (fun a => a) (k + 1)) (meansQ N Mg fun a => a)
        (openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k) (insQ links ps k) :=
  ⟨ownAtTableWide (P × First.S) Cl P W C F N Mg links ps (fun a => a) k (q.withMap E) _ _ _ _
      (rowOfPart q B b₀ hq hN G hG E hE on on' means In Out law) t1 t2 t3
      (fun a τ b w ha hm hb h' hw hi => by
        rw [withMap_id q E hE] at hi ⊢
        exact t4 a τ b w ha hm hb h' hw hi)
      hMark hDec,
    frames_of_rides q E hE _ _ _ _ _ hr⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowOfPart
#print axioms VerifiableInference.Desc.Sound.yes_of_part
#print axioms VerifiableInference.Desc.Sound.frames_of_rides
#print axioms VerifiableInference.Desc.Sound.rowAtTable
