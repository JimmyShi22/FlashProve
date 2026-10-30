-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K6Second.lean: THE OUTPUT HEAD'S BLOCK'S SECOND TIE TO THE TABLE OF JOINTS: the
promise behind it: ONE CALL of the
table's own kind-free rule for a quiet row (`onQ_step_quiet`, PromiseRidesQ.lean).

A rule over letters. NO RESULT ON THE PROTOCOL.

What is said.
  `shape_behind`: the stand's test rides from piece 4 to piece 5 of the head's segment past a step
    that turns the head's own part alone and leaves its link.
  `BlindOrder`: ON THE FILLING: "in order" and "held" do not read the open segment's own part.
  `quiet_K6`: ON THE TABLE: K6's row opens and closes no class of rows and no pin.
  **`k6_t2_quiet`**: the promise in front, no mark, the piece's yes and K6's files' own promise
    behind give the table's promise behind. PAID: the mark · the stand · the groups and the book's
    places (the record behind parts from the one in front in the head's own part alone). ONLY
    CARRIED: "in order" and "held", UNDER THE PREMISE `BlindOrder` ON THE FILLING (so no clause of
    "in order" may read the open segment's own part: what does comes as a public item of the
    segment) · the book's numbers, under hNum. LEFT, BY NAME: hDec hSh hNc (they
    ride: paid at the filling of the six letters on the oracles in K6AtSig.lean) · **hPub, hPP:
    every public item that is open behind holds, as a Bool and as a sentence**: the row's makes,
    what is tied to the items that it opens, and what rides · hNum: ON THE PLAN's NUMBERS: the block
    sends no tree and no message.

Limits. That hPub and hPP can be met is not said. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6Tied
import Johnson.Desc.Sound.PromiseRidesQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Numbers Meaning Pub shapeAt standOf standAt
  mayWait rowsHeld membersHeld sampledIn pubOfItems kindsBeforeBatching)

/-- The book-keeping rides from the front of piece 4 to the front of piece 5 of the head's segment.
-/
theorem shape_behind (links : List ModelPart) (p p' : Place) (m : ℕ) (hl : p.link = some m)
    (hl' : p'.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (hpc' : p'.piece = 5) (s : S) (o o' : HeadOwn) (hh : s.here = .head o)
    (ho : o.opened = true) (ho' : o'.opened = true) (hL : o'.L = o.L)
    (h : shapeAt links (some p) s = true) :
    shapeAt links (some p') { s with here := .head o' } = true := by
  unfold shapeAt at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨_, h2⟩, h3⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [standOf, standAt, S.inLink, S.fork?, ho', hl', hs, hpc']
  · have hw : mayWait links p = false := by simp [mayWait, hl, hs, hpc, kindsBeforeBatching]
    rw [hw, Bool.or_false] at h2
    have e : ({ s with here := .head o' } : S).noneWaits = s.noneWaits := rfl
    rw [e, h2]
    rfl
  · have e1 : s.link? = some o.L := by simp [S.link?, hh, ho]
    have e2 : ({ s with here := .head o' } : S).link? = some o'.L := by simp [S.link?, ho']
    rw [e1, hl] at h3
    rw [e2, hL, hl']
    exact h3

/-- ON THE FILLINGS: two Bools of the promise do not read where the chain stands. -/
structure BlindOrder {P W : Type} (Mg : Meaning P W) : Prop where
  order : ∀ (z : P) (s : S) h, Mg.inOrder (z, { s with here := h }) = Mg.inOrder (z, s)
  held : ∀ j t (z : P) (s : S) h, Mg.held j t (z, { s with here := h }) = Mg.held j t (z, s)

open VerifiableInference.Desc.First (quietRow) in
/-- K6's row is quiet. -/
theorem quiet_K6 (links : List ModelPart) (p : Place) (m : ℕ) (hl : p.link = some m)
    (hs : links[m]? = some .head) (hpc : p.piece = 4) :
    quietRow (First.rowOf links p) = true := by
  simp [First.rowOf, First.segRow, First.shift, quietRow, First.Item.isRow, First.Item.isPin, hl,
    hs, hpc]

end VerifiableInference.Desc.Sound

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub sampledIn pubOfItems bookAt)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ strsOf openQ pubQ onParts_of_on
  shape_behind BlindOrder quiet_K6 onQ_step_quiet)

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **THE SECOND TIE, BY THE KIND-FREE RULE.** -/
theorem k6_t2_quiet (H : Seated Wp fld Fr q l bef B bS) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (p p' : Place) (m : ℕ) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p')
    (hl : p.link = some m) (hl' : p'.link = some m) (hs : links[m]? = some .head)
    (hpc : p.piece = 4) (hpc' : p'.piece = 5) (hO : BlindOrder Mg)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2))
    (hSh : ∀ a τ b, q.ior.red.out a τ = some b → ∀ x ∈ sampledIn N (openQ links ps k),
      Mg.shown x.1 x.2 (strsOf Fr a.2) → Mg.shown x.1 x.2 (strsOf Fr b.2))
    (hNc : ∀ a τ b, q.ior.red.out a τ = some b → ∀ x ∈ sampledIn N (openQ links ps k),
      Mg.noColl x.1 x.2 a.1 (strsOf Fr a.2) → Mg.noColl x.1 x.2 b.1 (strsOf Fr b.2))
    (hPub : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ x ∈ pubQ Mg.more links ps (k + 1) ++ pubOfItems (openQ links ps (k + 1)),
        Mg.pub x b.1 = true)
    (hPP : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ x ∈ pubQ Mg.more links ps (k + 1), Mg.pubP x b.1)
    (hNum : N.treesAt ps[k + 1]? = N.treesAt ps[k]? ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) N Mg links ps (fun a => a) k a)
    (hm : a.1.2.failed = none) (hb : q.ior.red.out a τ = some b) (hA : K6After Wp b.1.2) :
    onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b := by
  have A := onParts_of_on N Mg links ps (fun a => a) k a ha hm
  obtain ⟨o, F1, X, Q, h1, h2, _, e⟩ := k6_behind H a b τ hb
  refine onQ_step_quiet N Mg links ps (fun a => a) k p hp (quiet_K6 links p m hl hs hpc) a b ha
    (fun h => absurd hm h) (hDec a τ b hb) (fun _ => ?_) ?_ ?_ (fun h => ?_) (fun _ _ => ?_)
    (fun _ h => ?_) (fun _ _ => ?_) (fun x _ h => ?_) (hSh a τ b hb) (hNc a τ b hb)
  · have hs0 : First.shapeAt links (some p) a.1.2 = true := by
      have := A.shape
      rw [hp] at this
      exact this
    show First.shapeAt links ps[k + 1]? b.1.2 = true
    rw [hp', e]
    exact shape_behind links p p' m hl hl' hs hpc hpc' a.1.2 o _ h1 h2 h2 rfl hs0
  · show b.1.2.st.groups = a.1.2.st.groups
    rw [e]
  · show b.1.2.book.place = a.1.2.book.place
    rw [e]
  · show Mg.inOrder b.1 = true
    rw [e, hO.order]
    exact h
  · rw [← First.openSets_succ links ps (First.start links) k p hp,
      ← First.pubSets_succ Mg.more links ps k p hp]
    unfold First.pubHeld
    exact List.all_eq_true.2 (hPub a τ b ha hm hb hA)
  · show bookAt N ps[k + 1]? b.1.2 = true
    have h' : bookAt N ps[k]? a.1.2 = true := h
    unfold bookAt at h' ⊢
    rw [hNum.1, hNum.2, e]
    exact h'
  · rw [← First.pubSets_succ Mg.more links ps k p hp]
    exact hPP a τ b ha hm hb hA
  · show Mg.held x.1 x.2 b.1 = true
    rw [e, hO.held]
    exact h

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Sound.shape_behind
#print axioms VerifiableInference.Desc.Sound.quiet_K6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t2_quiet
