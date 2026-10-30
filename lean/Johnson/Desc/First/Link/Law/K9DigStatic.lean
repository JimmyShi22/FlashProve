--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K9DigStatic.lean: **THE FIRST LAW OF THE CANDIDATE ROW `k9Entry`,
CLOSED: IN THE GOALS' SCOPE, FROM THE ACCEPT OF THE DIGITS' ROW (row 11) AND THE ACCEPT OF
`k9Entry`'s TWO TESTS AT A BUILT SEGMENT: `DigStatic tlD X.tl X.Fp`, WHOLE** (Law/RestStatic.lean:
six fields), at the very tlD that `digAt` gives. Theorems.
Why. The row's measure is that its accept gives each premise in its spender's own type. `StaticOk`
is whole in Law/K9AsksLaw.lean. Of `DigStatic` three fields come of the row (`small`, `apart`,
`coef`), two of row 11 (`pieces`, `inside`: Law/K9Row11.lean), and `same` of both: its equation on
f9 of the row's `sameB`, the five others of what is shown here: THE STRUCTURE AND THE LEDGER THAT
ROW 11 TESTS ARE THE BUILT SEGMENT's.
THE LETTERS. W: what `publicOf` returns on the public files. Bt: what `builtOf W ch` returns. THE
PROOF FILE's PUBLIC PART HOLDS Bt WITH EVERY ROUTINE BLANKED (`ProofFile.Law.blankB`): so the built
segment X is taken there.
  `built_tails`: in scope: the segments number 2 g, 2 g + 1 and 24 of Bt have the `tl` and `Fp` of
  W's layers' group g, attention g's seam, and head. ITS PROOF IS THE LANDED `link_tails_at`'s
  (Johnson/Goal/Meaning/PlanShapes.lean), line for line, from these two letters in the place of
  all that `verify-on-bytes`'s `planned` returns; with `zip_at`.
  `blank_at`: a blanked segment is the segment in `tl`, `Fp`, `arrayOf`.
  `tlAt_built`: **`tlAt W l = some b.tl`** at the segment b number l below 25 of Bt.
  `base_built`: **the place's ledger has that segment's arrays' numbers of rows**: it is that
  ledger through `fillL`, which keeps them (`Fo.frame_fillL`).
  `digStatic_of_rows`: ★ THE CLOSING THEOREM.
Limits. In scope alone. That either row accepts at any public files is no theorem. No probability:
no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.K9AsksLaw
import Johnson.Desc.First.Link.Law.K9Row11
import Johnson.Desc.First.Link.Law.RestStatic
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Goal.Meaning.PlanShapes
import OnBytes.Tie.Pv.Lookup.Ends.FoFramePass

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf builtOf linksOf)
open OnBytes.L5.LinksOrder (ok_bind zipped zipped_layers zipped_attention zipped_head linksOf_size)
open VerifiableInference.Desc.First.Look (lookAt tlAt)
open VerifiableInference.Desc.LinkJoin (DigStatic)
open VerifiableInference.Desc.K3Asks (digRow digAt Sent)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {W : Verify.Public}
  {ch : Verify.Chains} {Bt : Stages.LinksH}

/-- In scope the built segments have the structure and the ledger of the public part's own parts. -/
theorem built_tails (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) :
    (∀ g < 12, ∃ hpl a b b', W.G[g]? = some hpl ∧ W.A[g]? = some a ∧
      Bt.links[2 * g]? = some b ∧ b.tl = hpl.tl ∧ b.Fp = hpl.Fp ∧
      Bt.links[2 * g + 1]? = some b' ∧ b'.tl = a.seam.tl ∧ b'.Fp = a.seam.Fp) ∧
      ∃ b, Bt.links[24]? = some b ∧ b.tl = W.H.tl ∧ b.Fp = W.H.Fp := by
  obtain ⟨hq, hN, -, hA⟩ := _root_.Meaning.scope_plans hZ hR hW
  have hB' := hB
  unfold builtOf at hB'
  obtain ⟨ls, hl, _⟩ := ok_bind hB'
  have hG : W.G.size = 12 := (linksOf_size hl).1.trans hN
  refine ⟨fun g hg => ?_, ?_⟩
  · have hg' : W.G[g]? = some W.G[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨a, ha, -⟩ := hA g hg
    obtain ⟨ar, e⟩ := zipped_layers hB hl g _ hg'
    obtain ⟨ar', e'⟩ := zipped_attention hB hl hq g a ha
    have el : Stages.layersLink W.p4 g = 2 * g := by
      unfold Stages.layersLink
      rw [if_pos hq]
    rw [el] at e
    unfold zipped at e e'
    obtain ⟨b, hb, u1, u2, _⟩ := zip_at e
    obtain ⟨b', hb', v1, v2, _⟩ := zip_at e'
    exact ⟨_, a, b, b', hg', ha, hb, u1.symm, u2.symm, hb', v1.symm, v2.symm⟩
  · obtain ⟨ar, e⟩ := zipped_head hB hl
    rw [if_pos hq, hN] at e
    unfold zipped at e
    obtain ⟨b, hb, u1, u2, _⟩ := zip_at e
    exact ⟨b, hb, u1.symm, u2.symm⟩

/-- A blanked segment is the segment, but for its routine. -/
theorem blank_at {l : ℕ} {X : Stages.LinkH} (h : (ProofFile.Law.blankB Bt).links[l]? = some X) :
    ∃ b, Bt.links[l]? = some b ∧ X.tl = b.tl ∧ X.Fp = b.Fp ∧ X.arrayOf = b.arrayOf := by
  have h' : (Bt.links.map ProofFile.Law.blank)[l]? = some X := h
  rw [Array.getElem?_map] at h'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨b, hb, rfl, rfl, rfl⟩

/-- A number below 25 is 24, or twice a number below 12, or one more. -/
theorem split25 {l : ℕ} (hl : l < 25) : l = 24 ∨ ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) := by
  by_cases h : l = 24
  · exact Or.inl h
  · exact Or.inr ⟨l / 2, by omega, by omega⟩

/-- **The structure that row 11 tests is the built segment's, but for f9.** -/
theorem tlAt_built (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) : tlAt W l = some X.tl := by
  obtain ⟨hq, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR hW
  obtain ⟨T1, b, hb, e1, _⟩ := built_tails hZ hR hW hB
  unfold tlAt
  simp only [hq, hN, ↓reduceIte]
  rcases split25 hl with rfl | ⟨g, hg, rfl | rfl⟩
  · rw [hX] at hb
    obtain rfl := Option.some.inj hb
    rw [if_pos (by decide), e1]
  · obtain ⟨hpl, a, c, c', hG, _, hc, t1, _, _, _, _⟩ := T1 g hg
    rw [hX] at hc
    obtain rfl := Option.some.inj hc
    rw [if_neg (by simp; omega), if_pos (by simp), show 2 * g / 2 = g by omega, hG, t1]
    rfl
  · obtain ⟨hpl, a, c, c', _, hA, _, _, _, hc, t2, _⟩ := T1 g hg
    rw [hX] at hc
    obtain rfl := Option.some.inj hc
    rw [if_neg (by simp; omega), if_neg (by simp), show (2 * g + 1) / 2 = g by omega, hA,
      t2]
    rfl

/-- `fillL` keeps an array's number of rows. -/
theorem fillL_R (F : Fork) (t : ℕ) : (F.fillL.trees.getD t {}).R = (F.trees.getD t {}).R :=
  ((Fo.frame_fillL F).2 t).1

/-- **The ledger that row 11 tests has the built segment's arrays' numbers of rows.** -/
theorem base_built (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {l : ℕ} (hl : l < 25)
    {X : Stages.LinkH} (hX : Bt.links[l]? = some X) {x : First.Look.Place}
    (hx : lookAt W l true = some x) (t : ℕ) :
    (x.base.trees.getD t {}).R = (X.Fp.trees.getD t {}).R := by
  obtain ⟨hq, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR hW
  obtain ⟨T1, b, hb, _, e2⟩ := built_tails hZ hR hW hB
  unfold lookAt at hx
  simp only [hq, hN, ↓reduceIte] at hx
  rcases split25 hl with rfl | ⟨g, hg, rfl | rfl⟩
  · rw [hX] at hb
    obtain rfl := Option.some.inj hb
    rw [if_pos (by decide)] at hx
    obtain ⟨nx, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    show ((({ trees := W.H.Fp.trees } : Fork).fillL).trees.getD t {}).R = _
    rw [fillL_R, e2]
  · obtain ⟨hpl, a, c, c', hG, _, hc, _, f1, _, _, _⟩ := T1 g hg
    rw [hX] at hc
    obtain rfl := Option.some.inj hc
    rw [if_neg (by simp; omega), if_pos (by simp), show 2 * g / 2 = g by omega, hG] at hx
    obtain ⟨nx, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    show ((hpl.Fp.fillL).trees.getD t {}).R = _
    rw [fillL_R, f1]
  · obtain ⟨hpl, a, c, c', _, hA, _, _, _, hc, _, f2⟩ := T1 g hg
    rw [hX] at hc
    obtain rfl := Option.some.inj hc
    rw [if_neg (by simp; omega), if_neg (by simp), show (2 * g + 1) / 2 = g by omega,
      hA] at hx
    obtain ⟨nx, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    show ((a.seam.Fp.fillL).trees.getD t {}).R = _
    rw [fillL_R, f2]

/-- **THE CLOSING THEOREM: `DigStatic`, WHOLE.** -/
theorem digStatic_of_rows (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hW : publicOf Z.pol Z.KL lay = .ok W) (hB : builtOf W ch = .ok Bt) {D : Sent}
    (hd : digRow W D = true) {l : ℕ} (hl : l < 25) {X : Stages.LinkH}
    (hX : (ProofFile.Law.blankB Bt).links[l]? = some X) (hs : segOk X = true)
    (hm : sameB W l X = true) :
    ∃ x tlD, digAt W l = some (x, tlD) ∧ DigStatic tlD X.tl X.Fp := by
  obtain ⟨hq, hN, -, -⟩ := _root_.Meaning.scope_plans hZ hR hW
  have hl' : l < K3Asks.linksOf W := by
    unfold K3Asks.linksOf
    rw [hq, hN]
    exact hl
  obtain ⟨b, hb, eT, eF, _⟩ := blank_at hX
  obtain ⟨x, tlD, hD, ht, hpo, ha⟩ := row11_at hd hl'
  obtain ⟨tl, hS, hx, htl, rfl⟩ := digAt_parts hD
  rw [tlAt_built hZ hR hW hB hl hb, ← eT] at htl
  obtain rfl := Option.some.inj htl
  obtain ⟨xt, hD', ef⟩ := same_gives hm
  rw [hD] at hD'
  obtain rfl := Option.some.inj hD'
  unfold segOk at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hc⟩, hsm⟩, hr⟩, _⟩, _⟩, _⟩ := hs
  refine ⟨x, _, hD, ⟨ef.symm, rfl, rfl, rfl, rfl, rfl⟩, small_gives hsm, fun q hq' p hp' => ?_,
    ranges_gives hr, coef_gives hc, fun a hA => ?_⟩
  · have k := pieces_of_row ht hpo q hq' p hp'
    exact ⟨k.tree, k.c0, k.le, k.pw, k.rp, k.b, k.bn, k.dvd, k.fit⟩
  · rw [eF, ← base_built hZ hR hW hB hl hb hx]
    exact inside_of_row ht hpo ha a hA

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.built_tails
#print axioms VerifiableInference.Desc.K9Asks.blank_at
#print axioms VerifiableInference.Desc.K9Asks.split25
#print axioms VerifiableInference.Desc.K9Asks.tlAt_built
#print axioms VerifiableInference.Desc.K9Asks.fillL_R
#print axioms VerifiableInference.Desc.K9Asks.base_built
#print axioms VerifiableInference.Desc.K9Asks.digStatic_of_rows
