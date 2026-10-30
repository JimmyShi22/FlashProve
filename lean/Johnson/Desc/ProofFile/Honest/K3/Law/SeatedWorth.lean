-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SeatedWorth.lean: the honest side of the kind "lookup" (K3).
The three claims on the planes as they are seated (`planeClaimsOwn`,
Johnson/Desc/First/Look/LookPlanesOwn.lean, at the structure that `toHeard` gives) are worth, in
every world, what the kind's own three (`planesV`, Johnson/Desc/First/Look/Via/Rounds.lean) are
worth, conditional on the caller's readers' law. Theorems, with one structure and one definition.

Terms. Honest/K3/GLOSSARY.md ("claim", "count, bits, planes", "pin", "reader, readers", "world,
worth"). In this file: the kind's own text leaves a claim as (lead, scalar, pairs): lead + scalar
times the planes' value under the product form with these pairs is 0. The seated text is given forms
by the calling kind's readers: a0, a1: the planes' value at the leaves' point and at the bits'
point; c: the counts' sum less the number of keys that are no padding.

What is shown.
  `toHeard_fields`: what `toHeard` gives of what was heard, as far as these claims read it.
  `planeClaimsOwn_is`: the seated three claims, by name, of a0, a1, c.
  `planesV_is`: the kind's own three, by name.
  `ReadersSay`: the caller's readers' law, in one world: a named hypothesis.
  `count_faceOf`, `pub_size_of_shape`: the two forms of the number of keys that are no padding; and
    where its public hypothesis is shown.
  `worth_leaves`, `worth_bits`, `worth_count`: claim by claim.
  `seated_same_worth`: the three have the same worth.
  `seated_zero`: so, where the kind's own three hold (`Left`), the seated three are worth 0. In
    these two the letters a0, a1, c are tied to the seated text by no hypothesis but `ReadersSay`:
    `planeClaimsOwn_is` has the tie, for a caller to compose.
Others: `countFold` (the one definition: the seated fold over the pins), `same_worth`,
`foldl_add_sum`, `range_getD_nat`, `const_count`.

Hypotheses that remain.
  `ReadersSay`: it is not proved in this file: it is the calling kind's (attention; the head) to
    show. Shown in part: Honest/K3/Law/ReadersSayOf.lean, Honest/K3/Law/ReadersSayAt.lean and
    Honest/K3/Law/ReadersSayCount.lean (its three clauses), conditional on two hypotheses on the
    caller's columns (`ColsSay`, `PinsSay`), which remain the calling kind's to show, and on the
    further hypotheses that are named there.
  One public hypothesis: every tree's count of padding keys is listed (pub has NT entries);
    `pub_size_of_shape` shows it at the shape that a place's public parameters fix.
  `Left` (`L`), in `seated_zero`; there besides: `hf`: the course's face is the shape's; `hg`:
    `toHeard` returns; `hS'`, `hl`, `hr`, `hl'`: a later ledger with arrays of the right size, at
    which the part's own row returns, and a ledger later still; `hM`: `MasksAre`; `hS`: `ReadersSay`
    in that last ledger's world.
  By name elsewhere: `hS`: `ReadersSay`; `hpub`: the public hypothesis; `hpo`, `h0`, `h1`, `hc`,
    `hrow`: (in `planeClaimsOwn_is`) the packing's test and the returns of the four seated texts;
    `e`, `e2`, `e3`, `e4`: what `toHeard` gives, field by field; `hn`: (in `same_worth`) the face's
    count is the number n of `ReadersSay`; `hp`: (in `pub_size_of_shape`) the parameters fix the
    shape; `hn`: (in `const_count`) n < 2 ^ 64.
  That the number of keys that are no padding fits a word is implicit in `ReadersSay.count`, which
    speaks of the number itself: a proof of that clause calls `const_count`.

Users. This file is imported by Honest/K3/Law/DigitsBehind.lean, Honest/K3/Law/ReadersSayOf.lean,
Honest/K3/Law/Thread/Group11Worth.lean [not in this library], Honest/K3/Law/Thread/PutFo.lean and
Honest/K3/Parts/NamesOwn.lean. For a proof of `ReadersSay` the library has, named here and used by
no line of this file: the fold of `planesAtF` as a plain form and its value (`planesAff`,
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean; `planesK`, `plane_sum`,
OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean). That sum has no term at a call's number from NC on, so
the planes that are given as the letter planes must be 0 there.

Limits. At a layers' link the claims on the planes are made in another kind's runs: not reached.
Shown in part: Honest/K3/Law/Thread/Group11.lean [not in this library; so here read: not proved in
this library]. `planes_twin`: where the other kind's text of these claims returns, and its text of
the leaves' late claim returns at what the first keeps, the seated text `planeClaimsOwn` returns at
the other kind's readers, with the same three forms and the same ledger behind. `rowL_returns` and
`group11_returns`: behind the lookup's hearing, the other kind's hearing and the late claim that its
run makes first, the leaves' late claim returns, and so do the three; conditional on these returns,
on the leaves' own slots being still owed at the ledger from which the other kind hears, on the
other kind's text of these claims returning, and on the other kind holding the structure of the
leaves' sumcheck that the lookup heard. What the three are worth there: `group11_zero`
(Honest/K3/Law/Thread/Group11Worth.lean [not in this library; so here read: not proved in this
library]), conditional on `Left`, on the other kind's readers' law and on what that file's head
lists. By the head of Group11.lean [not in this library], that the other kind's readers answer is
for the files of the other kind to show. No instance of `ReadersSay` is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedPlanes
import Johnson.Desc.ProofFile.Honest.K3.Law.LookLeftOf
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE subE mulE negE ofF)
open OnBytes.Model (Fork Aff Reading World ofNat)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.PscRun (Sized Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV PlaneClaim faceOf toHeard toHeardG toPsc planesV eqPairs)
open VerifiableInference.Desc.First.Look (leavesRowOwn planeClaimsOwn planesAtF planesOk)

variable {W : Type}

/-! ## The two texts' claims, by name -/

/-- What `toHeard` gives of what was heard, as far as the claims on the planes read it. -/
theorem toHeard_fields {h : Shape} {g : HeardV} {g' : OnBytes.Model.Forest.Heard}
    (e : toHeard h (toHeardG g) = some g') :
    g'.shape = h ∧ g'.leaves = toPsc g.leaves ∧ g'.sBit = g.sBit ∧
      g'.leavesA = (faceOf h).leaf g.theta g.alpha g.zb0 := by
  unfold toHeard at e
  split at e
  · simp only at e
    split at e
    · cases e
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases e
  · cases e

/-- The count's fold, as `planeClaimsOwn` has it. -/
def countFold (g' : OnBytes.Model.Forest.Heard) (lm : Nat) (pin : Nat → Fl Aff) : Fl Aff :=
  (List.range (g'.shape.NC * 2 ^ (g'.shape.kT + 5 - lm))).foldlM
    (fun (f : Aff) col => do pure (f + (← pin col)))
    (Aff.ofConst (negE (ofF (2 ^ g'.shape.v - g'.shape.padding).toUInt64)))

/-- **The seated three claims, by name.** -/
theorem planeClaimsOwn_is (g' : OnBytes.Model.Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) {F G : Fork} {t : Tape} {a0 a1 c : Aff}
    (hpo : planesOk g'.shape lm = true)
    (h0 : planesAtF g' lm 0 bit F t = some (a0, F, t))
    (h1 : planesAtF g' lm 1 bit F t = some (a1, F, t))
    (hc : countFold g' lm pin F t = some (c, F, t))
    (hrow : leavesRowOwn g'.leaves oneE (Aff.scale a0 g'.leavesA) F t =
      some (g'.leaves.rowForm oneE (Aff.scale a0 g'.leavesA), G, t)) :
    planeClaimsOwn g' lm bit pin F t =
      some (#[g'.leaves.rowForm oneE (Aff.scale a0 g'.leavesA), Aff.slot g'.sBit - a1, c], G, t) :=
        by
  have hm : Fl.must (planesOk g'.shape lm) F t = some ((), F, t) := by
    unfold Fl.must
    rw [hpo]
    rfl
  unfold countFold at hc
  unfold planeClaimsOwn
  rw [fl_bind_some hm, fl_bind_some h0, fl_bind_some h1, fl_bind_some hc, fl_bind_some hrow]
  rfl

/-- **The kind's own three claims, by name.** -/
theorem planesV_is (f : LFace) (g : HeardV) {F G : Fork} {y : Aff}
    (hr : MaskedSum.row g.leaves oneE {} F = some (y, G)) :
    planesV f g F = some
      ([⟨MaskedSum.rowAff g.leaves oneE {}, mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0),
          eqPairs (f.mu + f.d) g.zb0⟩,
        ⟨Aff.slot g.sBit, subE zeroE oneE, eqPairs (f.mu + f.d) g.zb1⟩,
        ⟨Aff.ofConst (subE zeroE (ofNat f.count)), oneE, countPairs f⟩], G) := by
  have hy := MaskedSum.row_spec hr
  unfold planesV
  rw [hr, hy]
  rfl

/-! ## The readers' law; the count's two forms -/

/-- **The caller's readers' law, in one world**: the forms that the calling kind's readers yield are
worth the planes' value under the kind's own product forms. n: the number of keys that are no
padding, as the seated text writes it. -/
structure ReadersSay (f : LFace) (g : HeardV) (planes : List (E × E) → GE) (n : Nat)
    (a0 a1 c : Aff) (Wd : World GE) : Prop where
  at0 : a0.value Reading.gl Wd = planes (eqPairs (f.mu + f.d) g.zb0)
  at1 : a1.value Reading.gl Wd = planes (eqPairs (f.mu + f.d) g.zb1)
  /-- the count's form: the pins' sum less n -/
  count : c.value Reading.gl Wd = planes (countPairs f) - (n : GE)

theorem foldl_add_sum (l : List Nat) (k : Nat) : l.foldl (· + ·) k = k + l.sum := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.sum_cons]
    omega

theorem range_getD_nat (a : Array Nat) : (List.range a.size).map (fun y => a.getD y 0) = a.toList :=
    by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < a.size := by simpa using h2
    simp [Array.getD, hi]

/-- **The number of keys that are no padding, in the two texts' forms**, where every tree's count of
padding keys is listed. -/
theorem count_faceOf (h : Shape) (hpub : h.pub.size = h.NT) :
    (faceOf h).count = 2 ^ h.v - h.padding := by
  have e1' : (faceOf h).allKeys = 2 ^ h.v := by
    simp [VerifiableInference.Desc.K3.Face.allKeys, faceOf]
  have e2 : ((faceOf h).padding.map (·.1)).sum = h.padding := by
    unfold Shape.padding
    rw [← Array.foldl_toList, foldl_add_sum, ← range_getD_nat, hpub]
    simp [faceOf, List.map_map, Function.comp_def]
  unfold VerifiableInference.Desc.K3.Face.count
  rw [e1', e2]

/-! ## Claim by claim -/

theorem worth_leaves (hd : MaskedSum.Heard) (a0 : Aff) (A : E) (Wd : World GE) :
    ((toPsc hd).rowForm oneE (Aff.scale a0 A)).value Reading.gl Wd =
      (MaskedSum.rowAff hd oneE {}).value Reading.gl Wd +
        rd (mulE hd.eps A) * a0.value Reading.gl Wd := by
  rw [rowForm_value, MaskedSum.rowAff_value, MaskedSum.rowAff_value, Aff.value_scale,
    Aff.value_empty]
  show _ = _ + Reading.gl.val (mulE hd.eps A) * _
  rw [Reading.gl.mul]
  ring

theorem worth_bits (s : Nat) (a1 : Aff) (Wd : World GE) :
    (Aff.slot s - a1).value Reading.gl Wd =
      (Aff.slot s).value Reading.gl Wd + rd (subE zeroE oneE) * a1.value Reading.gl Wd := by
  rw [Aff.value_sub]
  show _ = _ + Reading.gl.val (subE zeroE oneE) * _
  rw [Reading.gl.sub, Reading.gl.zero, Reading.gl.one]
  ring

theorem worth_count (n : Nat) (P : GE) (Wd : World GE) :
    P - (n : GE) = (Aff.ofConst (subE zeroE (ofNat n))).value Reading.gl Wd + rd oneE * P := by
  rw [Aff.value_ofConst, Reading.gl.sub, Reading.gl.zero, Fo.ofNat_val]
  show _ = _ + Reading.gl.val oneE * _
  rw [Reading.gl.one]
  ring

/-! ## The three together -/

/-- The three equations, at a face as a letter. -/
theorem same_worth (f : LFace) (g : HeardV) (g' : OnBytes.Model.Forest.Heard)
    (e2 : g'.leaves = toPsc g.leaves) (e3 : g'.sBit = g.sBit)
    (e4 : g'.leavesA = f.leaf g.theta g.alpha g.zb0) (n : Nat) (hn : f.count = n)
    (planes : List (E × E) → GE) (a0 a1 c : Aff) (Wd : World GE)
    (hS : ReadersSay f g planes n a0 a1 c Wd) :
    (g'.leaves.rowForm oneE (Aff.scale a0 g'.leavesA)).value Reading.gl Wd =
        (MaskedSum.rowAff g.leaves oneE {}).value Reading.gl Wd +
          rd (mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0)) *
            planes (eqPairs (f.mu + f.d) g.zb0) ∧
      (Aff.slot g'.sBit - a1).value Reading.gl Wd =
        (Aff.slot g.sBit).value Reading.gl Wd +
          rd (subE zeroE oneE) * planes (eqPairs (f.mu + f.d) g.zb1) ∧
      c.value Reading.gl Wd =
        (Aff.ofConst (subE zeroE (ofNat f.count))).value Reading.gl Wd +
          rd oneE * planes (countPairs f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [e2, e4, worth_leaves, hS.at0]
  · rw [e3, worth_bits, hS.at1]
  · rw [hS.count, hn]
    exact worth_count _ _ Wd

/-- **Conditional on the caller's readers' law (`ReadersSay`): the seated three claims are worth
what the kind's own three are worth**: claim by claim, lead + scalar times the planes' value under
the claim's pairs. No instance of these hypotheses is exhibited in this file. -/
theorem seated_same_worth (h : Shape) (g : HeardV) (g' : OnBytes.Model.Forest.Heard)
    (hg : toHeard h (toHeardG g) = some g') (planes : List (E × E) → GE) (a0 a1 c : Aff)
    (Wd : World GE) (hpub : h.pub.size = h.NT)
    (hS : ReadersSay (faceOf h) g planes (2 ^ h.v - h.padding) a0 a1 c Wd) :
    (g'.leaves.rowForm oneE (Aff.scale a0 g'.leavesA)).value Reading.gl Wd =
        (MaskedSum.rowAff g.leaves oneE {}).value Reading.gl Wd +
          rd (mulE g.leaves.eps ((faceOf h).leaf g.theta g.alpha g.zb0)) *
            planes (eqPairs ((faceOf h).mu + (faceOf h).d) g.zb0) ∧
      (Aff.slot g'.sBit - a1).value Reading.gl Wd =
        (Aff.slot g.sBit).value Reading.gl Wd +
          rd (subE zeroE oneE) * planes (eqPairs ((faceOf h).mu + (faceOf h).d) g.zb1) ∧
      c.value Reading.gl Wd =
        (Aff.ofConst (subE zeroE (ofNat (faceOf h).count))).value Reading.gl Wd +
          rd oneE * planes (countPairs (faceOf h)) := by
  obtain ⟨_, e2, e3, e4⟩ := toHeard_fields hg
  exact same_worth (faceOf h) g g' e2 e3 e4 _ (count_faceOf h hpub) planes a0 a1 c Wd hS

/-- **Conditional on `Left` (what the kind's own claims are worth) and on the caller's readers' law
in the world spoken of: the seated three claims are worth 0** in the world of every ledger later
than the one behind the leaves' late row, at mask entries that are the coins spent. No instance of
these hypotheses is exhibited in this file. -/
theorem seated_zero (R : Course W) (h : Shape) (hf : R.f = faceOf h) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (g : HeardV) (G : Fork) (L : Left R planes keys g G)
    (g' : OnBytes.Model.Forest.Heard) (hg : toHeard h (toHeardG g) = some g')
    (hpub : h.pub.size = h.NT) {F' G' : Fork} {y : Aff} (hS' : Sized F') (hl : Later G F')
    (hr : MaskedSum.row g.leaves oneE {} F' = some (y, G')) (a0 a1 c : Aff) (H : Fork)
    (mask : Nat → GE) (entry : Nat → Nat → Nat → GE) (hl' : Later G' H) (hM : MasksAre R mask)
    (hS : ReadersSay R.f g planes (2 ^ h.v - h.padding) a0 a1 c
      (H.worldOf Reading.gl mask entry)) :
    (g'.leaves.rowForm oneE (Aff.scale a0 g'.leavesA)).value Reading.gl
        (H.worldOf Reading.gl mask entry) = 0 ∧
      (Aff.slot g'.sBit - a1).value Reading.gl (H.worldOf Reading.gl mask entry) = 0 ∧
      c.value Reading.gl (H.worldOf Reading.gl mask entry) = 0 := by
  obtain ⟨_, e2, e3, e4⟩ := toHeard_fields hg
  have e4' : g'.leavesA = R.f.leaf g.theta g.alpha g.zb0 := by rw [hf]; exact e4
  have hn : R.f.count = 2 ^ h.v - h.padding := by rw [hf]; exact count_faceOf h hpub
  obtain ⟨w0, w1, w2⟩ := same_worth R.f g g' e2 e3 e4' _ hn planes a0 a1 c _ hS
  have all := L.2 F' G' H _ mask entry hS' hl (planesV_is R.f g hr) hl' hM
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at all
  obtain ⟨z0, z1, z2⟩ := all
  exact ⟨w0.trans z0, w1.trans z1, w2.trans z2⟩

/-- **Where the public hypothesis is shown**: the shape that a place's public parameters fix lists
one count of padding keys for each tree (the first test of `pubOk`). -/
theorem pub_size_of_shape {p : VerifiableInference.Desc.First.Look.P} {h : Shape}
    (hp : p.shape = some h) : h.pub.size = h.NT := by
  unfold VerifiableInference.Desc.First.Look.P.shape at hp
  obtain ⟨h0, _, hp⟩ := Option.bind_eq_some_iff.1 hp
  split at hp
  · rename_i hk
    obtain rfl := Option.some.inj hp
    simp only [VerifiableInference.Desc.First.Look.pubOk, Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.1.1.1
  · exact nomatch hp

/-- The constant of the seated text's count, read: for a proof of `ReadersSay.count`. -/
theorem const_count (n : Nat) (hn : n < 2 ^ 64) : rd (negE (ofF n.toUInt64)) = -(n : GE) := by
  show Reading.gl.val (negE (ofF n.toUInt64)) = _
  rw [Cb.Fo.PlaneClaims.neg_val, Fo.ofF_val, Fo.toNat_word n hn]

#print axioms ProofFile.Honest.K3.Law.same_worth
#print axioms ProofFile.Honest.K3.Law.pub_size_of_shape
#print axioms ProofFile.Honest.K3.Law.const_count
#print axioms ProofFile.Honest.K3.Law.toHeard_fields
#print axioms ProofFile.Honest.K3.Law.planeClaimsOwn_is
#print axioms ProofFile.Honest.K3.Law.planesV_is
#print axioms ProofFile.Honest.K3.Law.foldl_add_sum
#print axioms ProofFile.Honest.K3.Law.range_getD_nat
#print axioms ProofFile.Honest.K3.Law.count_faceOf
#print axioms ProofFile.Honest.K3.Law.worth_leaves
#print axioms ProofFile.Honest.K3.Law.worth_bits
#print axioms ProofFile.Honest.K3.Law.worth_count
#print axioms ProofFile.Honest.K3.Law.seated_same_worth
#print axioms ProofFile.Honest.K3.Law.seated_zero

end ProofFile.Honest.K3.Law
