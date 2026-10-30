-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Head/HeadCover.lean: the output head's runs on shapes with a cover in the
place of the reads' entries: the forms' slots at the leaves with no read, and as entries the first
and the n-th of row 0 of the reads' array. At "join" the entries of the form in which the lookup's
key side ends stay beside the cover. Where such a light run returns, the run with the
entries returns, the light claims standing under its claims (ClaimStandsUnder,
Johnson/AtFull/Shape/Lines/Layers/ClaimCovers.lean). General in the view, the sizes and n. Nothing
is evaluated.

Why. rowZeroCover as in Johnson/AtFull/Shape/Lines/Layers/BackRunCover.lean: the forms then need not
name their reads (the Why of ClaimCovers.lean says why a cover will do).

  headThreeFormsCovered, headJoinFormCovered, headThreeRunCovered, headJoinRunCovered   the runs
                          with the cover: "norm", "policy" and "logits", and "join".
  **headThreeFormsCovered_standUnder, headJoinFormCovered_standsUnder,
  headThreeRunCovered_standsUnder, headJoinRunCovered_standsUnder**   their laws.

Limits. Laws on shapes, one way. hp: the sizes at which the forms run are those at which the test on
the reads reckons. The cover's entries need be no entries of a form: where row 0 of that array is
shorter than n, or begins behind 0, the light run's claims fail at the adding and these laws say
nothing. A form without an entry gets the cover too. What any of this costs Lean's kernel is not
measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Head.HeadLeaves
import Johnson.AtFull.Shape.Lines.Layers.BackRunCover
import Johnson.Desc.K6.Shape.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open VerifiableInference.Desc.First.Shape (AffSh ClaimSh LedSh ChainSh EntSh)
open VerifiableInference.Desc.K9.Shape (EntriesCover ClaimStandsUnder ClaimsStandUnder
    claimStandsUnder_ofCover claimsStandUnder_cons)
open OnBytes.Desc.First.K4.Rt (rowZeroCover rowZeroCover_covers)

/-- **"norm", "policy" and "logits" with the cover.** -/
def headThreeFormsCovered (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 n : Nat) (name : String) (v
    : View) :
    Except String (List ClaimSh) :=
  if lettersB p h iU3 v && headCoverTest p iU3 n v then
    named "the run is there" <| ((@formsSh p.sizes (v.leaves iU3).bare).lookup name).map fun fs =>
      fs.map fun a => plainSh (AffSh.mk (rowZeroCover iU3 n) a.slots)
  else .error "the light run: the letters or the cover"

/-- **"join" with the cover.** -/
def headJoinFormCovered (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 n : Nat) (v : View) :
    Except String (List ClaimSh × LedSh) :=
  if unpaidB v.led v.look.owedJoin && lettersB p h iU3 v && headCoverTest p iU3 n v &&
      (callList.length == v.look.shape.calls.size && v.look.e == v.look.shape.calls.size) then
    .ok ([plainSh (AffSh.mk (rowZeroCover iU3 n ++ v.look.cEnd.ents)
        (joinSh (@keysSh p.sizes (v.leaves iU3).bare) v.look.cEnd).slots)],
      v.led.setOwed (VerifiableInference.Desc.First.Shape.paidB v.led.owed v.look.owedJoin))
  else .error "join, with the cover"

/-- The run "norm", "policy" or "logits" with the cover, on the chain's shape. -/
def headThreeRunCovered (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (n : Nat) (name :
    String) (_ : Nat)
    (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (named "the head's view" (viewSh a)).bind fun v => (headThreeFormsCovered p h iU3 n name v).map
      fun cs => (cs, a)

/-- The run "join" with the cover, on the chain's shape. -/
def headJoinRunCovered (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (n : Nat) (_ : Nat) (a :
    ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  (named "the head's view" (viewSh a)).bind fun v =>
    (headJoinFormCovered p h iU3 n v).map fun y => (y.1, a.setLed y.2)

/-- Forms with the cover, as claims, stand under the forms to which BareOfRowZero relates them. -/
theorem coveredForms_standUnder {iU3 n : Nat} : ∀ {l l' : List AffSh},
    List.Forall₂ (BareOfRowZero iU3 n) l l' →
    ClaimsStandUnder (l'.map fun a => plainSh (AffSh.mk (rowZeroCover iU3 n) a.slots)) (l.map
        plainSh)
  | _, _, .nil => trivial
  | a :: _, a' :: _, .cons h t => by
    obtain ⟨s, -, r⟩ := h
    refine claimsStandUnder_cons.2 ⟨?_, coveredForms_standUnder t⟩
    show ClaimStandsUnder (First.Shape.ClaimSh.mk none (AffSh.mk (rowZeroCover iU3 n) a'.slots) [])
      (First.Shape.ClaimSh.mk none a [])
    rw [s]
    have e : a = AffSh.mk a.ents a.slots := by
      obtain ⟨x, y⟩ := a
      rfl
    rw [e]
    exact claimStandsUnder_ofCover none none a.slots [] (rowZeroCover_covers r)

/-- A lookup by name in two related lists finds related members. -/
theorem listLookup_alike {Q : AffSh → AffSh → Prop} {name : String} :
    ∀ {l l' : List (String × List AffSh)},
      List.Forall₂ (fun c c' => c.1 = c'.1 ∧ List.Forall₂ Q c.2 c'.2) l l' →
      ∀ {fs' : List AffSh}, l'.lookup name = some fs' →
        ∃ fs, l.lookup name = some fs ∧ List.Forall₂ Q fs fs'
  | _, _, .nil, _, h => by cases h
  | c :: _, c' :: _, .cons ⟨e, q⟩ t, fs', h => by
    rw [List.lookup_cons] at h ⊢
    rw [e]
    cases hn : name == c'.1 with
    | true =>
      rw [hn] at h
      obtain rfl := Option.some.inj h
      exact ⟨c.2, rfl, q⟩
    | false =>
      rw [hn] at h
      exact listLookup_alike t h

variable {p : Par} {h : OnBytes.Model.Head.Shape} {iU3 n : Nat} {v : View}

/-- Where the three runs' forms with the cover return, threeG (Johnson/Desc/K6/Shape/Core.lean)
returns, the light claims under its claims. -/
theorem headThreeFormsCovered_standUnder {name : String} {cs' : List ClaimSh} (hp : p.sizes =
    sizesOf h)
    (e : headThreeFormsCovered p h iU3 n name v = .ok cs') :
    ∃ cs, threeG p h iU3 name v = .ok cs ∧ ClaimsStandUnder cs' cs := by
  unfold headThreeFormsCovered at e
  split at e
  · rename_i hb
    obtain ⟨hl, hc⟩ := Bool.and_eq_true_iff.1 hb
    have A := leaves_bareOfRowZero hp hl hc
    have F := @forms_alike _ p.sizes (bareOfRowZero_kept iU3 n) _ _ A (headCoverFacts_ofTest hc).div
    cases hf : (@formsSh p.sizes (v.leaves iU3).bare).lookup name with
    | none =>
      rw [hf] at e
      cases e
    | some fs' =>
      rw [hf] at e
      obtain rfl := Except.ok.inj e
      obtain ⟨fs, h1, h2⟩ := listLookup_alike F hf
      refine ⟨fs.map plainSh, ?_, coveredForms_standUnder h2⟩
      unfold threeG
      rw [if_pos hl, h1]
      rfl
  · cases e

/-- The relation is kept over a list of key vectors. -/
theorem catSh_bareOfRowZero {l l' : List AffSh} (hF : List.Forall₂ (BareOfRowZero iU3 n) l l') :
    BareOfRowZero iU3 n (catSh l) (catSh l') := (bareOfRowZero_kept iU3 n).cat hF

/-- The join's claim with the cover stands under the join's claim. -/
theorem coveredJoin_standsUnder {KF KF' : List AffSh} (hF : List.Forall₂ (BareOfRowZero iU3 n) KF
    KF') (cE : AffSh) :
    ClaimStandsUnder (plainSh (AffSh.mk (rowZeroCover iU3 n ++ cE.ents) (joinSh KF' cE).slots))
      (plainSh (joinSh KF cE)) := by
  obtain ⟨s, -, r⟩ := catSh_bareOfRowZero hF
  have es : (joinSh KF' cE).slots = (joinSh KF cE).slots := by
    show ((catSh KF').slots ++ cE.slots) = (catSh KF).slots ++ cE.slots
    rw [s]
  rw [es]
  have ee : joinSh KF cE = AffSh.mk ((catSh KF).ents ++ cE.ents) (joinSh KF cE).slots := rfl
  show ClaimStandsUnder (First.Shape.ClaimSh.mk none _ []) (First.Shape.ClaimSh.mk none (joinSh KF
      cE) [])
  rw [ee]
  refine claimStandsUnder_ofCover none none _ [] ?_
  intro x hx
  rcases List.mem_append.1 hx with h1 | h1
  · obtain ⟨lo, hi, m1, m2, a, b⟩ := rowZeroCover_covers r x h1
    exact ⟨lo, hi, List.mem_append_left _ m1, List.mem_append_left _ m2, a, b⟩
  · exact ⟨x.2.2, x.2.2, List.mem_append_right _ h1, List.mem_append_right _ h1, Nat.le_refl _,
      Nat.le_refl _⟩

/-- Where the join with the cover returns, joinG returns, the light claims under its claims, with
the same ledger's shape. -/
theorem headJoinFormCovered_standsUnder {y' : List ClaimSh × LedSh} (hp : p.sizes = sizesOf h)
    (e : headJoinFormCovered p h iU3 n v = .ok y') :
    ∃ y, joinG p h iU3 v = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2 := by
  unfold headJoinFormCovered at e
  split at e
  · rename_i hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hu, hl⟩, hc⟩, hs⟩ := hb
    have A := leaves_bareOfRowZero hp hl hc
    have K := @keys_alike _ p.sizes (bareOfRowZero_kept iU3 n) _ _ A (headCoverFacts_ofTest hc).div
        (headCoverFacts_ofTest hc).half
    obtain rfl := Except.ok.inj e
    refine ⟨([plainSh (joinSh (@keysSh p.sizes (v.leaves iU3)) v.look.cEnd)],
      v.led.setOwed (VerifiableInference.Desc.First.Shape.paidB v.led.owed v.look.owedJoin)), ?_,
          ?_,
      rfl⟩
    · unfold joinG
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨⟨hu, hl⟩, hs⟩)]
    · exact claimsStandUnder_cons.2 ⟨coveredJoin_standsUnder K _, trivial⟩
  · cases e

/-- The same as headThreeFormsCovered_standUnder, for the run on the chain's shape. -/
theorem headThreeRunCovered_standsUnder (hp : p.sizes = sizesOf h) {name : String} {k : Nat}
    {a : ChainSh}
    {y' : List ClaimSh × ChainSh} (e : headThreeRunCovered h iU3 p n name k a = .ok y') :
    ∃ y, threeRunG h iU3 p name k a = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2 := by
  unfold headThreeRunCovered at e
  unfold threeRunG
  cases hv : named "the head's view" (viewSh a) with
  | error s =>
    rw [hv] at e
    cases e
  | ok v =>
    rw [hv] at e
    cases ht : headThreeFormsCovered p h iU3 n name v with
    | error s =>
      simp only [Except.bind, ht] at e
      cases e
    | ok cs' =>
      simp only [Except.bind, ht, Except.map] at e
      obtain rfl := Except.ok.inj e
      obtain ⟨cs, h1, h2⟩ := headThreeFormsCovered_standUnder hp ht
      refine ⟨(cs, a), ?_, h2, rfl⟩
      simp only [Except.bind, h1, Except.map]

/-- The same as headJoinFormCovered_standsUnder, for the run on the chain's shape. -/
theorem headJoinRunCovered_standsUnder (hp : p.sizes = sizesOf h) {k : Nat} {a : ChainSh}
    {y' : List ClaimSh × ChainSh} (e : headJoinRunCovered h iU3 p n k a = .ok y') :
    ∃ y, joinRunG h iU3 p k a = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2 := by
  unfold headJoinRunCovered at e
  unfold joinRunG
  cases hv : named "the head's view" (viewSh a) with
  | error s =>
    rw [hv] at e
    cases e
  | ok v =>
    rw [hv] at e
    cases ht : headJoinFormCovered p h iU3 n v with
    | error s =>
      simp only [Except.bind, ht] at e
      cases e
    | ok z' =>
      simp only [Except.bind, ht, Except.map] at e
      obtain rfl := Except.ok.inj e
      obtain ⟨z, h1, h2, h3⟩ := headJoinFormCovered_standsUnder hp ht
      refine ⟨(z.1, a.setLed z.2), ?_, h2, ?_⟩
      · simp only [Except.bind, h1, Except.map]
      · show a.setLed z'.2 = a.setLed z.2
        rw [h3]

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headThreeFormsCovered
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headJoinFormCovered
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headThreeRunCovered
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headJoinRunCovered
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.coveredForms_standUnder
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.listLookup_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headThreeFormsCovered_standUnder
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.catSh_bareOfRowZero
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.coveredJoin_standsUnder
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headJoinFormCovered_standsUnder
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headThreeRunCovered_standsUnder
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headJoinRunCovered_standsUnder
