-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/ClaimCovers.lean: the batching on shapes (batchGS,
Johnson/AtFull/Shape/BatchAtHead.lean) returns at rows g wherever it returns at rows g' that hand
on, in the place of a claim's entries, a few entries that cover them, and it returns the same. In
these files the light claim, with the cover, stands under the library's claim. General laws, one
way; nothing is evaluated.

Why. The adding of a claim on shapes (addOneS, Johnson/Desc/First/Batch/Shape/AddShape.lean) asks,
of each entry that the claim's form names, that its array and row are there and that its index
lies in the row's stretch (entryS). It sets nothing that depends on the entries: what it returns is
nextS of the ledger's shape. The test after a run (eachS,
Johnson/Desc/First/Batch/Shape/BatchFold.lean) reads the claims' slots and their number. So a row
may hand on fewer entries, if these pass only where all would.

  entry_passesBetween     entryS is a test on an interval: between two indices of one row that
                          pass, every index passes.
  EntriesCover cov ents   each entry lies, in its own array and row, between two members of cov.
  entriesCover_allPass    where all of cov pass, all of ents pass, at every list of arrays.
  ClaimStandsUnder c' c   c' may stand for c at the adding: the same slots, the same runs, and at
                          every list of arrays, where the entries of c' all pass, those of c do.
  ClaimsStandUnder        the same for two lists of claims' shapes, member by member.
  **addClaims_standUnder**   where the adding returns at the one list, it returns the same at the
                          other.
  behindRunTest_standsUnder   the test after a run answers alike.
  RowsStandUnder I g' g   two tables of rows, at the shapes of which I holds: where g' returns, g
                          returns, the claims of g' member by member under those of g, the same
                          shape after, of which I holds again. I is whatever a row's law needs to
                          know of the shape before.
  **batchingOnShapes_standsUnder**   so through the gathering, the adding and the member's whole
                          step.

Limits. One way: where the step at g' returns an error, nothing is said of the step at g. A cover
that names an index which no entry of the claim reaches can fail where all the entries pass: then
the step at g' returns an error and these laws say nothing. No row is shown here to stand under
another. What any of this costs Lean's kernel is not measured here. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-! ## 1 An entry's test is a test on an interval -/

/-- Between two indices of one row that pass, every index passes. -/
theorem entry_passesBetween {T : List TreeSh} {t r lo hi i : Nat}
    (h1 : entryS T (t, r, lo) = true) (h2 : entryS T (t, r, hi) = true) (a : lo ≤ i)
    (b : i ≤ hi) : entryS T (t, r, i) = true := by
  unfold entryS at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  cases hT : T[t]? with
  | none =>
    rw [hT] at h1
    exact nomatch h1
  | some X =>
    rw [hT] at h1 h2
    dsimp only at h1 h2 ⊢
    cases hr : X.rows[r]? with
    | none =>
      rw [hr] at h1
      exact nomatch h1
    | some R =>
      rw [hr] at h1 h2
      dsimp only at h1 h2 ⊢
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1 h2 ⊢
      omega

/-- cov covers ents: each entry lies, in its own array and row, between two members of cov. -/
def EntriesCover (cov ents : List EntSh) : Prop :=
  ∀ x ∈ ents, ∃ lo hi, (x.1, x.2.1, lo) ∈ cov ∧ (x.1, x.2.1, hi) ∈ cov ∧ lo ≤ x.2.2 ∧ x.2.2 ≤ hi

/-- Where all of a cover pass, all that it covers pass. -/
theorem entriesCover_allPass {T : List TreeSh} {cov ents : List EntSh} (h : EntriesCover cov ents)
    (hc : cov.all (entryS T) = true) : ents.all (entryS T) = true := by
  rw [List.all_eq_true] at hc ⊢
  intro x hx
  obtain ⟨lo, hi, m1, m2, a, b⟩ := h x hx
  exact entry_passesBetween (hc _ m1) (hc _ m2) a b

/-! ## 2 One claim's shape in the place of another -/

/-- **c' may stand for c at the adding**: the same slots and runs, and where the entries of c' all
pass, those of c pass, at every list of arrays. -/
def ClaimStandsUnder (c' c : ClaimSh) : Prop :=
  c'.form.slots = c.form.slots ∧ c'.runs = c.runs ∧
    ∀ T : List TreeSh, c'.form.ents.all (entryS T) = true → c.form.ents.all (entryS T) = true

/-- A claim's shape stands under itself. -/
theorem ClaimStandsUnder.refl (c : ClaimSh) : ClaimStandsUnder c c := ⟨rfl, rfl, fun _ h => h⟩

/-- A claim's shape with a cover in the place of its entries. -/
theorem claimStandsUnder_ofCover (e' e : Option Nat) {cov ents : List EntSh} (slots : List Nat)
    (runs : List RunSh) (h : EntriesCover cov ents) :
    ClaimStandsUnder (ClaimSh.mk e' (AffSh.mk cov slots) runs) (ClaimSh.mk e (AffSh.mk ents slots)
        runs) :=
  ⟨rfl, rfl, fun _ hc => entriesCover_allPass h hc⟩

/-- Where the adding of c' returns, the adding of c returns the same. -/
theorem addClaim_standsUnder {L L' : LedSh} {c' c : ClaimSh} (h : ClaimStandsUnder c' c)
    (ha : addOneS L c' = some L') : addOneS L c = some L' := by
  unfold addOneS at ha ⊢
  split at ha
  · rename_i hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hb
    rw [if_pos]
    · exact ha
    · simp only [Bool.and_eq_true]
      exact ⟨⟨⟨b1, h.2.2 _ b2⟩, h.1 ▸ b3⟩, h.2.1 ▸ b4⟩
  · exact nomatch ha

/-- ClaimStandsUnder for two lists of claims' shapes, member by member. -/
def ClaimsStandUnder : List ClaimSh → List ClaimSh → Prop
  | [], [] => True
  | c' :: l', c :: l => ClaimStandsUnder c' c ∧ ClaimsStandUnder l' l
  | _, _ => False

/-- A list with a first member stands under another where its first member and its rest do. -/
theorem claimsStandUnder_cons {c' c : ClaimSh} {l' l : List ClaimSh} :
    ClaimsStandUnder (c' :: l') (c :: l) ↔ ClaimStandsUnder c' c ∧ ClaimsStandUnder l' l := Iff.rfl

/-- A list of claims' shapes stands under itself. -/
theorem ClaimsStandUnder.refl : ∀ l : List ClaimSh, ClaimsStandUnder l l
  | [] => trivial
  | c :: l => claimsStandUnder_cons.2 ⟨ClaimStandsUnder.refl c, ClaimsStandUnder.refl l⟩

/-- A list and the list that it stands under have one length. -/
theorem ClaimsStandUnder.length : ∀ {l' l : List ClaimSh}, ClaimsStandUnder l' l → l'.length =
    l.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (ClaimsStandUnder.length (claimsStandUnder_cons.1 h).2)
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- Appending keeps the relation. -/
theorem ClaimsStandUnder.append : ∀ {a' a b' b : List ClaimSh}, ClaimsStandUnder a' a →
    ClaimsStandUnder b' b →
    ClaimsStandUnder (a' ++ b') (a ++ b)
  | [], [], _, _, _, hb => hb
  | _ :: _, _ :: _, _, _, ha, hb =>
    claimsStandUnder_cons.2 ⟨(claimsStandUnder_cons.1 ha).1,
        ClaimsStandUnder.append (claimsStandUnder_cons.1 ha).2 hb⟩
  | [], _ :: _, _, _, ha, _ => False.elim ha
  | _ :: _, [], _, _, ha, _ => False.elim ha

/-- **Where the adding of the one list returns, the adding of the other returns the same.** -/
theorem addClaims_standUnder : ∀ {l' l : List ClaimSh} {L L' : LedSh}, ClaimsStandUnder l' l →
    addListS L l' = some L' → addListS L l = some L'
  | [], [], _, _, _, h => h
  | c' :: l', c :: l, L, L', hu, h => by
    obtain ⟨M, h1, h2⟩ := Option.bind_eq_some_iff.1
      (show (addOneS L c').bind (fun M => addListS M l') = some L' from h)
    show (addOneS L c).bind (fun M => addListS M l) = some L'
    rw [addClaim_standsUnder (claimsStandUnder_cons.1 hu).1 h1]
    exact addClaims_standUnder (claimsStandUnder_cons.1 hu).2 h2
  | [], _ :: _, _, _, hu, _ => False.elim hu
  | _ :: _, [], _, _, hu, _ => False.elim hu

/-! ## 3 The test after a run -/

/-- namesIn answers alike at a claim and at the claim under it. -/
theorem namesIn_standsUnder {a b : Nat} {c' c : ClaimSh} (h : ClaimStandsUnder c' c) :
    namesIn a b c' = namesIn a b c := by
  unfold namesIn
  rw [h.1]

/-- So does its any over a list and over the list under it. -/
theorem anyNamesIn_standsUnder (a b : Nat) : ∀ {l' l : List ClaimSh}, ClaimsStandUnder l' l →
    l'.any (namesIn a b) = l.any (namesIn a b)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    rw [List.any_cons, List.any_cons, namesIn_standsUnder (claimsStandUnder_cons.1 h).1,
      anyNamesIn_standsUnder a b (claimsStandUnder_cons.1 h).2]
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- The test after a run answers alike. -/
theorem behindRunTest_standsUnder (k : SegSort) (o : Nat × String) {l' l : List ClaimSh} (h :
    ClaimsStandUnder l' l)
    (a : ChainSh) : eachS k o l' a = eachS k o l a := by
  unfold eachS
  cases a.tl with
  | none => rfl
  | some t =>
    dsimp only
    rw [anyNamesIn_standsUnder _ _ h, ClaimsStandUnder.length h]

/-! ## 4 The gathering, the adding, the member's step -/

/-- **Two tables of rows, at the shapes of which I holds**: where g' returns, g returns: the claims
of g' member by member under those of g, the same shape after, and I holds of it. -/
def RowsStandUnder (I : ChainSh → Prop)
    (g' g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)) : Prop :=
  ∀ o n a y', I a → g' o n a = .ok y' →
    ∃ y, g o n a = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2 ∧ I y.2

variable {k : SegSort} {I : ChainSh → Prop}
  {g' g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}

/-- One member of the order in the gathering: where the step at g' returns, the step at g returns.
-/
theorem gatherStep_standsUnder (hg : RowsStandUnder I g' g) {x' x : List ClaimSh × ChainSh}
    (h1 : ClaimsStandUnder x'.1 x.1) (h2 : x'.2 = x.2) (hI : I x'.2) (o : Nat × String)
    {z' : List ClaimSh × ChainSh} (hz : stepG k g' x' o = .ok z') :
    ∃ z, stepG k g x o = .ok z ∧ ClaimsStandUnder z'.1 z.1 ∧ z'.2 = z.2 ∧ I z'.2 := by
  unfold stepG at hz ⊢
  cases hy : g' o x'.1.length x'.2 with
  | error e =>
    rw [hy] at hz
    exact nomatch hz
  | ok y' =>
    rw [hy] at hz
    obtain ⟨y, e, u1, u2, u3⟩ := hg o _ _ y' hI hy
    rw [← ClaimsStandUnder.length h1, ← h2, e]
    have hz' : (if eachS k o y'.1 y'.2 then
        (.ok (x'.1 ++ y'.1, y'.2) : Except String (List ClaimSh × ChainSh))
      else .error (o.2 ++ ": behind the run: the shape")) = .ok z' := hz
    show ∃ z, (if eachS k o y.1 y.2 then
        (.ok (x.1 ++ y.1, y.2) : Except String (List ClaimSh × ChainSh))
      else .error (o.2 ++ ": behind the run: the shape")) = .ok z ∧ ClaimsStandUnder z'.1 z.1 ∧
        z'.2 = z.2 ∧ I z'.2
    rw [← u2] at u3
    rw [← behindRunTest_standsUnder k o u1, ← u2]
    split at hz'
    · rename_i hb
      rw [if_pos hb]
      obtain rfl := Except.ok.inj hz'
      exact ⟨_, rfl, ClaimsStandUnder.append h1 u1, rfl, u3⟩
    · exact nomatch hz'

/-- The whole gathering, by induction on the order. -/
theorem gathering_standsUnder (hg : RowsStandUnder I g' g) : ∀ (os : List (Nat × String))
    {x' x z' : List ClaimSh × ChainSh}, ClaimsStandUnder x'.1 x.1 → x'.2 = x.2 → I x'.2 →
    gatherFrom k g' os x' = .ok z' →
    ∃ z, gatherFrom k g os x = .ok z ∧ ClaimsStandUnder z'.1 z.1 ∧ z'.2 = z.2
  | [], x', x, z', h1, h2, _, hz => by
    obtain rfl : x' = z' := Except.ok.inj hz
    exact ⟨x, rfl, h1, h2⟩
  | o :: os, x', x, z', h1, h2, hI, hz => by
    have hz' : (stepG k g' x' o).bind (gatherFrom k g' os) = .ok z' := hz
    cases hs : stepG k g' x' o with
    | error e =>
      rw [hs] at hz'
      exact nomatch hz'
    | ok w' =>
      rw [hs] at hz'
      obtain ⟨w, e, u1, u2, u3⟩ := gatherStep_standsUnder hg h1 h2 hI o hs
      obtain ⟨z, ez, v1, v2⟩ := gathering_standsUnder hg os u1 u2 u3 hz'
      refine ⟨z, ?_, v1, v2⟩
      show (stepG k g x o).bind (gatherFrom k g os) = .ok z
      rw [e]
      exact ez

/-- Adding the gathered claims: where it returns at the one, it returns the same at the other. -/
theorem laying_standsUnder {y' y : List ClaimSh × ChainSh} (h1 : ClaimsStandUnder y'.1 y.1) (h2 :
    y'.2 = y.2)
    {u : ChainSh} (h : laidG y' = .ok u) : laidG y = .ok u := by
  obtain ⟨hb, F, F', e1, e2, rfl⟩ := laid_ok h
  have e : (y'.2.led.bind fun F => addListS F y.1) = some F' := by
    rw [e1]
    exact addClaims_standUnder h1 e2
  unfold laidG
  rw [← h2, if_pos hb, e]

/-- The gathering and the adding together. -/
theorem addingStep_standsUnder (hg : RowsStandUnder I g' g) (order : List (Nat × String))
    {a u : ChainSh}
    (hI : I a) (h : addsG k g' order a = .ok u) : addsG k g order a = .ok u := by
  unfold addsG at h ⊢
  split at h
  · rename_i hb
    rw [if_pos hb]
    cases hy : gatherG k g' order a with
    | error e =>
      rw [hy] at h
      exact nomatch h
    | ok y' =>
      rw [hy] at h
      obtain ⟨y, e, u1, u2⟩ :=
        gathering_standsUnder hg order (x' := ([], a)) (x := ([],
            a)) (ClaimsStandUnder.refl _) rfl hI hy
      have e' : gatherG k g order a = .ok y := e
      rw [e']
      exact laying_standsUnder u1 u2 h
  · exact nomatch h

/-- The draw, the gathering and the adding. hdraw: the draw keeps I. -/
theorem batching_standsUnder (hg : RowsStandUnder I g' g) (rows : Nat) (order : List (Nat × String))
    (hdraw : ∀ a b, I a → drawG rows a = .ok b → I b) {a u : ChainSh} (hI : I a)
    (h : batchG rows k g' order a = .ok u) : batchG rows k g order a = .ok u := by
  unfold batchG at h ⊢
  cases hd : drawG rows a with
  | error e =>
    rw [hd] at h
    exact nomatch h
  | ok b =>
    rw [hd] at h
    exact addingStep_standsUnder hg order (hdraw a b hI hd) h

end VerifiableInference.Desc.K9.Shape

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (SegSort)
open VerifiableInference.Desc.K9.Shape

/-- **The member's whole step**: at a shape of which I holds: where it returns at the rows g', it
returns the same at g. hdraw: the draw keeps I. -/
theorem batchingOnShapes_standsUnder {k : SegSort} {I : ChainSh → Prop}
    {g' g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hg : RowsStandUnder I g' g) (rows : Nat) (order : List (Nat × String))
    (hdraw : ∀ a b, I a → drawG rows a = .ok b → I b) {a u : ChainSh} (hI : I a)
    (h : batchGS rows k g' order a = .ok u) : batchGS rows k g order a = .ok u := by
  unfold batchGS at h ⊢
  cases hb : batchG rows k g' order a with
  | error e =>
    rw [hb] at h
    exact nomatch h
  | ok w =>
    rw [hb] at h
    rw [batching_standsUnder hg rows order hdraw hI hb]
    exact h

end Johnson.AtFull.Shape

#print axioms VerifiableInference.Desc.K9.Shape.entry_passesBetween
#print axioms VerifiableInference.Desc.K9.Shape.EntriesCover
#print axioms VerifiableInference.Desc.K9.Shape.entriesCover_allPass
#print axioms VerifiableInference.Desc.K9.Shape.ClaimStandsUnder
#print axioms VerifiableInference.Desc.K9.Shape.ClaimStandsUnder.refl
#print axioms VerifiableInference.Desc.K9.Shape.claimStandsUnder_ofCover
#print axioms VerifiableInference.Desc.K9.Shape.addClaim_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.ClaimsStandUnder
#print axioms VerifiableInference.Desc.K9.Shape.claimsStandUnder_cons
#print axioms VerifiableInference.Desc.K9.Shape.ClaimsStandUnder.refl
#print axioms VerifiableInference.Desc.K9.Shape.ClaimsStandUnder.length
#print axioms VerifiableInference.Desc.K9.Shape.ClaimsStandUnder.append
#print axioms VerifiableInference.Desc.K9.Shape.addClaims_standUnder
#print axioms VerifiableInference.Desc.K9.Shape.namesIn_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.anyNamesIn_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.behindRunTest_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.RowsStandUnder
#print axioms VerifiableInference.Desc.K9.Shape.gatherStep_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.gathering_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.laying_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.addingStep_standsUnder
#print axioms VerifiableInference.Desc.K9.Shape.batching_standsUnder
#print axioms Johnson.AtFull.Shape.batchingOnShapes_standsUnder
