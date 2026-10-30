-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkToy.lean: the kind "lookup" (K3): an instance of the two
hypotheses of the mark's bound together (`CanAll`, `FewAll`, Honest/K3/Good/MarkShare.lean): a
synthetic kit of verifier's messages at which both hold, with a written share below 1, at every face
that passes a test with code; and the face of a small synthetic lookup (the example) passes it. So
`markK3_debt` (Honest/K3/Good/MarkDebt.lean) is called at a place where its hypotheses hold.
Definitions with code; theorems; seven tests by evaluation.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: f is a lookup's face; the example is the small
synthetic lookup of Honest/K3/Toy.lean, and its face is `Toy.f₁`.
The kit. A round that samples no element has one challenge. Every other round has 101 challenges;
challenge number n shows the word n + 1, with 0 in the two other coordinates, at every element that
the round samples; positions and matrix entries show as 0. So no element shows as 0, and just one
challenge of the 101 shows 1.

What is shown.
  `kit`, `shown`, `dataOf`, `dsbOf`: the kit; what a challenge shows; a round's data; the data of a
    lookup's rounds.
  `memberOk f`: the test with code: the format knows the rounds' names; each event's round is one of
    the lookup's, and samples more elements than the event's number.
  `fits_toy`, `canAll_toy`: the first hypothesis.
  `share_toy`, `fewAll_toy`: the second, at the share 1 of 101.
  `member`: both, at every face that passes the test.
  `debt_small`: the frame's `MarkDebt` (Honest/Law/CoverJoin.lean) at the example's face, at this
    kit, at the number of its events times 1 of 101.
  `small_ok`, `small_below`: the example's face passes the test; its events are fewer than 101.
  the tests by evaluation: the example's face passes `memberOk`, and its count of events is the
    written 37. `memberOk` itself can reject: it rejects the example's face with one plane, or none,
    by its second clause (the first clause's text, written anew, holds there), and accepts it with
    two planes. It accepts two faces that `Face.ok` rejects. The last test does not call `memberOk`:
    it is the second clause's text, written anew, over the example's rounds less the last three, and
    it rejects.
Helpers: `M`, `sizeOf`, `sizeOf_pos`, `sizeOf_le`, `wordOf`, `w_lt`, `w_ne`, `w_nz`, `w_one`,
`z_lt`, `drawFit_toy`, `bears`, `parts_ok`, `cut_at`, `elem_toy`, `zero_of_shows`.

Hypotheses that remain. `h`: the face passes `memberOk`. `debt_small` has none. In the helpers:
`hk`: the format knows the round's name (in `drawFit_toy`); the element's number lies below what the
round samples (in `elem_toy`, `zero_of_shows`, `share_toy`). `hn`: n < 101 (`M`). `h`: (in
`zero_of_shows`) challenge number n shows the event.

Limits. It shows that the two hypotheses can hold together, at a number below 1. It shows nothing of
the release's kit. That the number is below 1 is `small_below`, on natural numbers (37 events, by
the first test by evaluation, against 101); the step from there to the number in `debt_small` is
arithmetic and no theorem here.
`memberOk` is no test of the face: it accepts faces that the verifier's own test `Face.ok` rejects
(no part; a part of 0 bits). No face at which its first clause (every round's name has a kind)
rejects was found: the names are the library's own. How the altered faces were found: eleven were
tried by evaluation, in a trial that is not kept; the guesses written first were right at nine.
The kit is synthetic: the elements of one of its rounds are not sampled apart from each other, and
from 101 values alone. No instance of the second mark's hypothesis (`FewOut`,
Honest/K3/Good/MarkOut.lean) is exhibited here. The first hypothesis is shown by `fits_toy`, not by
`canAll_of_kit` (Honest/K3/Good/MarkKit.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkKit
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkDebt
import Johnson.Desc.ProofFile.Honest.K3.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.MarkToy
open Prob
open scoped ENNReal
open OnBytes (E zeroE oneE isZeroE)
open VerifiableInference.Desc (fieldPrimeWord drawsMarkedNonzeroHaveNonzeroWords Place)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-! ## 1 The kit -/

/-- How many challenges a round has that samples an element. -/
def M : Nat := 101

def sizeOf (e : Fmt.Entry) : Nat := if e.drawE = 0 then 1 else M

theorem sizeOf_pos (e : Fmt.Entry) : 0 < sizeOf e := by
  unfold sizeOf M
  split <;> decide

theorem sizeOf_le (e : Fmt.Entry) : sizeOf e ≤ M := by
  unfold sizeOf M
  split <;> decide

/-- The word that challenge number n shows. -/
def wordOf (n : Nat) : UInt64 := (n + 1).toUInt64

/-- What challenge number n shows at an entry. -/
def shown (e : Fmt.Entry) (n : Nat) : Fmt.Drawn :=
  ⟨List.replicate e.drawE (wordOf n, 0, 0), List.replicate e.poss 0, List.replicate e.trits 0, none⟩

/-- **The kit.** -/
def kit : CK where
  Ch := fun e _ => Fin (sizeOf e)
  fin := fun _ _ => inferInstance
  ne := fun e _ => ⟨⟨0, sizeOf_pos e⟩⟩
  dr := fun e _ c => shown e c.val
  front := (inferInstance : Unique (Fin 1))

theorem w_lt : ∀ n : Fin M, wordOf n.val < fieldPrimeWord := by decide +kernel

theorem w_ne : ∀ n : Fin M, (wordOf n.val, (0 : UInt64), (0 : UInt64)) ≠ (0, 0, 0) := by
  decide +kernel

theorem w_nz : ∀ n : Fin M, isZeroE (E.ofTriple (wordOf n.val, 0, 0)) = false := by decide +kernel

theorem w_one : ∀ n : Fin M, (E.ofTriple (wordOf n.val, 0, 0) == oneE) = true → n.val = 0 := by
  decide +kernel

theorem z_lt : decide ((0 : UInt64) < fieldPrimeWord) = true := by decide +kernel

/-! ## 2 The first hypothesis -/

theorem drawFit_toy (z : Fmt.DeclaredRound) (hk : (Fmt.kindOf z.entry.name).isSome = true) (n : Nat)
    (hn : n < M) : drawFit z (shown z.entry n) = true := by
  have a2 : ((shown z.entry n).elems.length == z.entry.drawE) = true := by
    show ((List.replicate z.entry.drawE (wordOf n, (0 : UInt64), (0 : UInt64))).length ==
      z.entry.drawE) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have a3 : ((shown z.entry n).poss.length == z.entry.poss) = true := by
    show ((List.replicate z.entry.poss 0).length == z.entry.poss) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have a4 : ((shown z.entry n).trits.length == z.entry.trits) = true := by
    show ((List.replicate z.entry.trits (0 : Int)).length == z.entry.trits) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have a5 : ((shown z.entry n).poss.all (· < 2 ^ z.entry.logN)) = true := by
    rw [List.all_eq_true]
    intro x hx
    have hx0 : x = 0 := List.eq_of_mem_replicate hx
    rw [hx0]
    exact decide_eq_true (Nat.two_pow_pos _)
  have a6 : ((shown z.entry n).trits.all fun t => t == -1 || t == 0 || t == 1) = true := by
    rw [List.all_eq_true]
    intro t ht
    have ht0 : t = 0 := List.eq_of_mem_replicate ht
    rw [ht0]
    rfl
  have a7 : drawsMarkedNonzeroHaveNonzeroWords z ⟨[], shown z.entry n⟩ = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.1 hk
    rw [hk', Option.any_some, List.all_eq_true]
    intro x hx
    have h2 : x.2 ∈ List.replicate z.entry.drawE (wordOf n, (0 : UInt64), (0 : UInt64)) :=
      (List.of_mem_zip (a := x.1) (b := x.2) hx).2
    have h3 : x.2 = (wordOf n, 0, 0) := List.eq_of_mem_replicate h2
    have h4 : (x.2 != (0, 0, 0)) = true := by
      rw [h3]
      exact bne_iff_ne.2 (w_ne ⟨n, hn⟩)
    rw [h4, Bool.or_true]
  have a8 : ((shown z.entry n).elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
    rw [List.all_eq_true]
    intro x hx
    have h3 : x = (wordOf n, 0, 0) := List.eq_of_mem_replicate hx
    rw [h3]
    show (decide (wordOf n < fieldPrimeWord) && decide ((0 : UInt64) < fieldPrimeWord) &&
      decide ((0 : UInt64) < fieldPrimeWord)) = true
    rw [decide_eq_true (w_lt ⟨n, hn⟩), z_lt]
    rfl
  unfold drawFit
  rw [a2, a3, a4, a5, a6, a7, a8]
  rfl

/-- What the kit's messages show passes the frame's test, at data that bear the rounds' entries. -/
theorem fits_toy : ∀ (ds : List RDT) (zs : List Fmt.DeclaredRound),
    List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound) => d.entry = z.entry) ds zs →
    (∀ z ∈ zs, (Fmt.kindOf z.entry.name).isSome = true) →
    ∀ ρ : Iop.Rho (uLT kit ds), drawsFit zs (drawnT kit ds ρ) = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | d :: ds, z :: zs, h, hz, (c, ρ) => by
    obtain ⟨e1, h2⟩ := List.forall₂_cons.1 h
    have ih := fits_toy ds zs h2 (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) ρ
    show (drawFit z (kit.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)) &&
      drawsFit zs (drawnT kit ds ρ)) = true
    rw [ih, Bool.and_true]
    have hn : (show Fin (sizeOf d.entry) from Iop.GChal.old (b := d.entry.work) c).val < M :=
      lt_of_lt_of_le (Fin.isLt _) (sizeOf_le _)
    show drawFit z (shown d.entry
      (show Fin (sizeOf d.entry) from Iop.GChal.old (b := d.entry.work) c).val) = true
    generalize (show Fin (sizeOf d.entry) from Iop.GChal.old (b := d.entry.work) c).val = n at hn ⊢
    rw [e1]
    exact drawFit_toy z (hz z List.mem_cons_self) n hn

/-- A round's data: its entry, and the kind of that entry's name. -/
def dataOf (z : Fmt.DeclaredRound) : RDT :=
  { entry := z.entry, kind := (Fmt.kindOf z.entry.name).getD .nothing, items := [], trees := []
    opens := [], stored := [] }

/-- The data of a lookup's rounds. -/
def dsbOf (f : LFace) : List RDT := (declOf f).map dataOf

theorem bears : ∀ zs : List Fmt.DeclaredRound,
    List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound) => d.entry = z.entry) (zs.map dataOf) zs
  | [] => .nil
  | _ :: zs => .cons rfl (bears zs)

/-- **The test with code.** -/
def memberOk (f : LFace) : Bool :=
  ((declOf f).all fun z => (Fmt.kindOf z.entry.name).isSome) &&
    (eventsOf f).all fun e =>
      ((declOf f)[e.round f]?).any fun z => decide (e.spot.draw < z.entry.drawE)

theorem parts_ok (f : LFace) (h : memberOk f = true) :
    ((declOf f).all fun z => (Fmt.kindOf z.entry.name).isSome) = true ∧
      ((eventsOf f).all fun e =>
        ((declOf f)[e.round f]?).any fun z => decide (e.spot.draw < z.entry.drawE)) = true := by
  unfold memberOk at h
  rw [Bool.and_eq_true] at h
  exact h

theorem canAll_toy (f : LFace) (h : memberOk f = true) : CanAll kit f (dsbOf f) := fun ρ =>
  fits_toy (dsbOf f) (declOf f) (bears _)
    (fun z hz => List.all_eq_true.1 (parts_ok f h).1 z hz) ρ

/-! ## 3 The second hypothesis -/

theorem cut_at {α : Type} : ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x →
    ∃ a b, l = a ++ x :: b ∧ a.length = i
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by
    have h' : y = x := by simpa using h
    exact ⟨[], l, by rw [h']; rfl, rfl⟩
  | y :: l, i + 1, x, h => by
    have h' : l[i]? = some x := by simpa using h
    obtain ⟨a, b, e1, e2⟩ := cut_at l i x h'
    exact ⟨y :: a, b, by rw [e1]; rfl, by rw [List.length_cons, e2]⟩

theorem elem_toy (en : Fmt.Entry) (n k : Nat) (hk : k < en.drawE) :
    ((shown en n).elems.map E.ofTriple).getD k zeroE = E.ofTriple (wordOf n, 0, 0) := by
  show ((List.replicate en.drawE (wordOf n, (0 : UInt64), (0 : UInt64))).map E.ofTriple).getD k
    zeroE = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_replicate, if_pos hk]
  rfl

theorem zero_of_shows (en : Fmt.Entry) (e : Event) (hk : e.spot.draw < en.drawE) (n : Nat)
    (hn : n < M) (h : e.shows (shown en n) = true) : n = 0 := by
  unfold Event.shows at h
  rw [elem_toy en n _ hk] at h
  unfold Event.test at h
  cases ho : e.atOne with
  | false =>
    rw [ho] at h
    have h1 : isZeroE (E.ofTriple (wordOf n, 0, 0)) = true := h
    rw [w_nz ⟨n, hn⟩] at h1
    cases h1
  | true =>
    rw [ho] at h
    exact w_one ⟨n, hn⟩ h

/-- Of a round's 101 challenges at most one shows an event. -/
theorem share_toy (d : RDT) (e : Event) (hk : e.spot.draw < d.entry.drawE) :
    shareAt kit d (fun R => e.shows R = true) ≤ 1 / (M : ℝ≥0∞) := by
  have hcard : Nat.card (kit.Ch d.entry d.kind) = M := by
    show Nat.card (Fin (sizeOf d.entry)) = M
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    unfold sizeOf
    rw [if_neg (by omega)]
  have hcnt : Prob.cnt (fun c : kit.Ch d.entry d.kind =>
      e.shows (kit.dr d.entry d.kind c) = true) ≤ 1 := by
    refine le_trans (cnt_mono (Q := fun c : Fin (sizeOf d.entry) => c = ⟨0, sizeOf_pos _⟩)
      fun c hc => ?_) (le_of_eq (cnt_eq_const _))
    exact Fin.ext (zero_of_shows d.entry e hk _ (lt_of_lt_of_le (Fin.isLt c) (sizeOf_le _)) hc)
  unfold shareAt
  rw [hcard]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcnt) _

theorem fewAll_toy (f : LFace) (h : memberOk f = true) :
    FewAll kit f (dsbOf f) (1 / (M : ℝ≥0∞)) := by
  intro e he
  have h1 := List.all_eq_true.1 (parts_ok f h).2 e he
  cases hz : (declOf f)[e.round f]? with
  | none =>
    rw [hz] at h1
    cases h1
  | some z =>
    rw [hz] at h1
    have hk : e.spot.draw < z.entry.drawE := of_decide_eq_true h1
    have hd : (dsbOf f)[e.round f]? = some (dataOf z) := by
      unfold dsbOf
      rw [List.getElem?_map, hz]
      rfl
    obtain ⟨a, b, e1, e2⟩ := cut_at _ _ _ hd
    exact ⟨a, dataOf z, b, e1, e2, share_toy (dataOf z) e hk⟩

/-! ## 4 The instance -/

/-- **Both hypotheses, at every face that passes the test.** -/
theorem member (f : LFace) (h : memberOk f = true) :
    CanAll kit f (dsbOf f) ∧ FewAll kit f (dsbOf f) (1 / (M : ℝ≥0∞)) :=
  ⟨canAll_toy f h, fewAll_toy f h⟩

theorem small_ok : memberOk Toy.f₁ = true := by decide +kernel

/-- The example has fewer events than the kit's rounds have challenges. -/
theorem small_below : events Toy.f₁ < M := by decide +kernel

/-- **The frame's `MarkDebt` at the example's face, at this kit.** No hypothesis. -/
theorem debt_small (a : Place) :
    MarkDebt kit (markK3 a Toy.f₁) (dsbOf Toy.f₁) (fun _ => True)
      ((events Toy.f₁ : ℝ≥0∞) * (1 / (M : ℝ≥0∞))) :=
  markK3_debt kit a Toy.f₁ (dsbOf Toy.f₁) _ (member Toy.f₁ small_ok).1 (member Toy.f₁ small_ok).2

-- the example's face passes, and its count as written
#guard memberOk Toy.f₁ && events Toy.f₁ == 37
-- the test itself can reject: the example's face with one plane, or none: by its second clause.
-- With two planes it accepts. How these faces were found: eleven altered faces were tried by
-- evaluation, in a trial that is not kept; the guesses written first were right at nine, these
-- three among them. The first clause (every round's name has a kind) held at all eleven: the names
-- are the library's own: no face at which it rejects was found
#guard !memberOk { Toy.f₁ with planes := 1 } && !memberOk { Toy.f₁ with planes := 0 }
#guard memberOk { Toy.f₁ with planes := 2 }
-- that it is the second clause which rejects there: the first clause's text, written anew, holds
#guard [1, 0].all fun k =>
  (declOf { Toy.f₁ with planes := k }).all fun z => (Fmt.kindOf z.entry.name).isSome
-- the two of the eleven at which the guess failed. It is no test of the face: it accepts faces that
-- the verifier's own test `Face.ok` rejects: no part; a part of 0 bits
#guard memberOk { Toy.f₁ with parts := [] } && !({ Toy.f₁ with parts := [] } : LFace).ok
#guard memberOk { Toy.f₁ with parts := [0] } && !({ Toy.f₁ with parts := [0] } : LFace).ok
-- the next line does not call `memberOk`: it is the second clause's text, written anew, over the
-- example's rounds less the last three
#guard !((eventsOf Toy.f₁).all fun e =>
  ((declOf Toy.f₁).dropLast.dropLast.dropLast[e.round Toy.f₁]?).any fun z =>
    decide (e.spot.draw < z.entry.drawE))

end ProofFile.Honest.K3.Good.MarkToy

#print axioms ProofFile.Honest.K3.Good.MarkToy.sizeOf_pos
#print axioms ProofFile.Honest.K3.Good.MarkToy.sizeOf_le
#print axioms ProofFile.Honest.K3.Good.MarkToy.w_lt
#print axioms ProofFile.Honest.K3.Good.MarkToy.w_ne
#print axioms ProofFile.Honest.K3.Good.MarkToy.w_nz
#print axioms ProofFile.Honest.K3.Good.MarkToy.w_one
#print axioms ProofFile.Honest.K3.Good.MarkToy.z_lt
#print axioms ProofFile.Honest.K3.Good.MarkToy.drawFit_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.fits_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.bears
#print axioms ProofFile.Honest.K3.Good.MarkToy.parts_ok
#print axioms ProofFile.Honest.K3.Good.MarkToy.canAll_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.cut_at
#print axioms ProofFile.Honest.K3.Good.MarkToy.elem_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.zero_of_shows
#print axioms ProofFile.Honest.K3.Good.MarkToy.share_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.fewAll_toy
#print axioms ProofFile.Honest.K3.Good.MarkToy.member
#print axioms ProofFile.Honest.K3.Good.MarkToy.small_ok
#print axioms ProofFile.Honest.K3.Good.MarkToy.small_below
#print axioms ProofFile.Honest.K3.Good.MarkToy.debt_small
