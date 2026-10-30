-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9Row11.lean: WHAT THE ACCEPT OF THE DIGITS' ROW (row 11 of the proof
file's entry tests: `K3Asks.digRow`, Johnson/Desc/First/Look/K3Asks.lean) GIVES AT A SEGMENT FOR
THE LAWS ON THE KIND K9: two fields of `DigStatic` (Law/RestStatic.lean), OF THE STRUCTURE AND THE
LEDGER THAT THE ROW ITSELF TESTS. With a lemma on two lists that differ in one field. Theorems. No
scope is named here.
  `zip_at`: an entry of "the built segments, each with its routine exchanged" is a built segment's
  in the three fields `tl`, `Fp`, `arrayOf`. (The one form of `OnBytes.L5.LinksOrder.zipped` and of
  `blank_built`.)
  `pieceOK_of_held`: the model's own test `HTailF2.pieceHeld`, with the array and the first
  column, gives `Fo.PieceOK`. The one step of arithmetic: a power of two is 2 to its rounded-up
  logarithm (`Slice.ceilLog2_two_pow`).
  `row11_at`: where the row accepts, at each number below the number of segments: the place and
  the structure are there, and three of the row's tests accept: `tailB`, `portB`, `digAddrB`.
  `digAt_parts`: what `digAt` returns: the place of `lookAt`; the structure of `tlAt` with the
  field f9 alone exchanged.
  `pieces_of_row`: **the field `pieces`**, at the structure that the row tests.
  `inside_of_row`: **the field `inside`**, at that structure and the place's ledger.
Limits. THAT THE STRUCTURE AND THE LEDGER WHICH THE ROW TESTS ARE THE BUILT SEGMENT's IS NOT HERE:
Law/K9DigStatic.lean. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3AsksLaw
import OnBytes.Tie.Pv.Lookup.Digits.PortSeam
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place P lookAt tlAt)
open VerifiableInference.Desc.K3Asks (digRow digAt digB shapeB tailB portB digAddrB linksOf sigList
  lastMoment Sent)

/-- An entry of the built segments with their routines exchanged. -/
theorem zip_at {bs ls : Array Stages.LinkH} {j : ℕ} {Y : Stages.LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.tl = b.tl ∧ Y.Fp = b.Fp ∧ Y.arrayOf = b.arrayOf := by
  rw [Array.getElem?_zipWith] at h
  cases hb : bs[j]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hx : ls[j]? with
    | none =>
      rw [hx] at h
      cases h
    | some y =>
      rw [hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl, rfl⟩

/-- The model's own test on a member of a call gives the law's sentence. -/
theorem pieceOK_of_held {tl : HTailF2} {q n : ℕ} {p : Piece}
    (h : HTailF2.pieceHeld n p = true) (ht : p.tree = tl.ix.ZZ) (hc : p.c0 = q * tl.mz) :
    Fo.PieceOK tl q n p := by
  simp only [HTailF2.pieceHeld, HTailF2.isPow2, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hR⟩, _⟩, hle⟩, _, hp⟩, hb⟩, hbn⟩, hd⟩, hf⟩ := h
  have hw : clog2 p.CP = Nat.log2 p.CP := by
    conv_lhs => rw [← hp]
    exact Slice.ceilLog2_two_pow _
  exact ⟨ht, hc, hle, by rw [hw]; exact hp.symm, hR.symm, hb, hbn, Nat.dvd_of_mod_eq_zero hd, hf⟩

/-- Where the digits' row accepts. -/
theorem row11_at {X : Verify.Public} {D : Sent} (h : digRow X D = true) {i : ℕ}
    (hi : i < linksOf X) :
    ∃ x tlD, digAt X i = some (x, tlD) ∧ tailB tlD = true ∧ portB tlD = true ∧
      digAddrB x tlD D (sigList D x.link (lastMoment D x.link)) = true := by
  have h0 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  cases e : digAt X i with
  | none =>
    rw [e] at h0
    cases h0
  | some xt =>
    rw [e] at h0
    have h1 : digB (Params.settingOf X.P.frame) xt.1 xt.2 D = true := h0
    simp only [digB, shapeB, Bool.and_eq_true] at h1
    obtain ⟨⟨⟨_, ⟨⟨ht, _⟩, _⟩, hp⟩, _⟩, ha⟩ := h1
    exact ⟨xt.1, xt.2, rfl, ht, hp, ha⟩

/-- What `digAt` returns. -/
theorem digAt_parts {X : Verify.Public} {i : ℕ} {x : Place} {tlD : HTailF2}
    (h : digAt X i = some (x, tlD)) :
    ∃ tl hS, lookAt X i true = some x ∧ tlAt X i = some tl ∧ tlD = { tl with f9 := hS } := by
  unfold digAt at h
  cases e1 : lookAt X i true with
  | none =>
    rw [e1] at h
    cases h
  | some x' =>
    rw [e1] at h
    have h2 : ((tlAt X i).bind fun tl =>
        (P.ofPlace (Params.settingOf X.P.frame) true x').shape.map fun hS =>
          (x', { tl with f9 := hS })) = some (x, tlD) := h
    cases e2 : tlAt X i with
    | none =>
      rw [e2] at h2
      cases h2
    | some tl =>
      rw [e2] at h2
      have h3 : ((P.ofPlace (Params.settingOf X.P.frame) true x').shape.map fun hS =>
          (x', { tl with f9 := hS })) = some (x, tlD) := h2
      cases e3 : (P.ofPlace (Params.settingOf X.P.frame) true x').shape with
      | none =>
        rw [e3] at h3
        cases h3
      | some hS =>
        rw [e3] at h3
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h3)
        exact ⟨tl, hS, rfl, rfl, rfl⟩

/-- The row's test has two calls. -/
theorem two_of_tail {tl : HTailF2} (h : tailB tl = true) : tl.f9.NC = 2 := by
  simp only [tailB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

/-- **The field `pieces`, at the structure that the row tests.** -/
theorem pieces_of_row {tl : HTailF2} (ht : tailB tl = true) (hp : portB tl = true) :
    ∀ q < 2, ∀ p ∈ OnBytes.DgP.piecesL tl q, Fo.PieceOK tl q (tl.zOf q).call.n p := by
  intro q hq p hm
  have H := (OnBytes.DgP.portOK_of_test (K3Asks.port_up hp)).held q
    (by rw [two_of_tail ht]; exact hq) p hm
  exact pieceOK_of_held H.1 H.2.1 H.2.2

/-- **The field `inside`, at that structure and the place's ledger.** -/
theorem inside_of_row {x : Place} {tl : HTailF2} {D : Sent} {l : List OracleShape}
    (ht : tailB tl = true) (hp : portB tl = true) (ha : digAddrB x tl D l = true) :
    ∀ a ∈ Fo.allPieces tl, a.2.r0 + a.2.Rp ≤ (x.base.trees.getD a.2.tree {}).R := by
  have hN := two_of_tail ht
  have hP := (OnBytes.DgP.portOK_of_test (K3Asks.port_up hp)).held
  simp only [tailB, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hT := ht.1.1.1.2
  have key : ∀ q < 2, ∀ p ∈ (tl.zOf q).pieces.toList,
      p.r0 + p.Rp ≤ (x.base.trees.getD p.tree {}).R := by
    intro q hq p hm
    have hq' : q < tl.f9.NC := by rw [hN]; exact hq
    have h1 : p.r0 + p.Rp ≤ tl.tau := (hT q hq' p hm).2.2.2.2
    have h2 : p.tree = tl.ix.ZZ := (hP q hq' p hm).2.1
    unfold digAddrB at ha
    simp only [Bool.and_eq_true] at ha
    have h3 := ha.1.1.1.1.1
    rw [h2, Array.getD_eq_getD_getElem?]
    cases e : x.base.trees[tl.ix.ZZ]? with
    | none =>
      rw [e] at h3
      cases h3
    | some T =>
      rw [e] at h3
      have h4 : tl.tau ≤ T.R := of_decide_eq_true ((Bool.and_eq_true _ _).mp h3).1
      exact Nat.le_trans h1 h4
  intro a hm
  unfold Fo.allPieces at hm
  rcases List.mem_append.1 hm with h | h
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 h
    exact key 0 (by decide) p hp'
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 h
    exact key 1 (by decide) p hp'

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.zip_at
#print axioms VerifiableInference.Desc.K9Asks.pieceOK_of_held
#print axioms VerifiableInference.Desc.K9Asks.row11_at
#print axioms VerifiableInference.Desc.K9Asks.digAt_parts
#print axioms VerifiableInference.Desc.K9Asks.two_of_tail
#print axioms VerifiableInference.Desc.K9Asks.pieces_of_row
#print axioms VerifiableInference.Desc.K9Asks.inside_of_row
