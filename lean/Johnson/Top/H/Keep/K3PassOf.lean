-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/K3PassOf.lean: The kind "lookup" (K3): WHAT AN ACCEPT OF ITS SUB-PROTOCOL's
DECISION TURNS IN THE VERIFIER's STATE, AS AN EQUATION (the footprint), at both seats; THAT IT IS A
K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean); and that the lookup's own run "objects" answers
behind such a pass what it answered in front (RunSame). Statements and proofs.

OBJECT: K3.block's decide at K3.seatCalls and K3.seatDigits; objectsRun.
Used by Johnson/Desc/First/Look/K3DigitsPass.lean, Johnson/Top/H/Keep/AttCallersStay.lean,
  Johnson/Top/H/Keep/CallersStay.lean and 9 more.
LETTERS: claim, piece, laid, before, p, guests, s, s', rs, cols free.
Compiled with the whole library.

Main names:
  decide_ledger: of decide at any seat: the state behind is the seat's put; and, where the ledger in
    front has its sizes: which slots are filled (PadExact), a later ledger, the same arrays, three
    debts more and no other turn of the debts.
  unpaid_push: a debt more turns no debt to paid.
  k3_calls_footprint, k3_digits_footprint: THE FOOTPRINTS.
  putCalls_rest, putDigits_rest: the two seats' put leaves the slot of the merge's end value, and
    the approximate range proof's parameters are still there.
  k3_calls_pass, k3_digits_pass: K3Pass.
  objects_same: RunSame of "objects" at a seat whose ledger is the state's and whose mark is
    putFork, where what was heard at that seat is the same at both states.

Limits. OVER THE DECISION's OWN ACCEPT ALONE: the step without a round that stands behind the
digits' rounds in the seated sub-protocol is not crossed here (K3Pass.trans carries it, once that
step is shown to be a K3Pass). Sized F is a premise. "planes" and "join": not here.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Top.H.Keep.PadExact
import Johnson.Top.H.Keep.ReaderIsRun
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.First.Look.K3DigitsTurns
import Johnson.Desc.First.Look.K3DigRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits unpaid)
open VerifiableInference.Desc.K9 (mergeOf lateOf)

/-- **Of K3.block's decide: the ledger behind.** -/
theorem decide_ledger {T Cl : Type} (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl))
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧
      (Sized F → _root_.Fo.Tp.PadExact x.1.shape F x.2 x.1 ∧ Later F x.2 ∧
        x.2.trees = F.trees ∧
        x.2.owed = ((F.owed.push { what := "look-up-mask-claims" }).push
          { what := "look-up-plane-claims" }).push { what := "look-up-join" }) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, hn, rfl, fun hS => ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      obtain ⟨_, _, _, hlaw⟩ :=
        _root_.Fo.Tp.lkPad_law Reading.gl p.calls p.pub p.lid 5 F x.2 t [] x.1 hl
      obtain ⟨_, P, _⟩ := hlaw hS
      exact ⟨_root_.Fo.Tp.lkPad_exact p.calls p.pub p.lid F x.2 t [] x.1 hl hS,
        ⟨by rw [P.next]; exact Nat.le_add_right _ _, P.rest.2.1, fun _ => P.fit, P.keep⟩,
        P.rest.1, P.owed⟩
    · exact absurd hx (by simp)

/-- A debt more turns no debt to paid. -/
theorem unpaid_push (A : Array Owed) (o : Owed) (ho : o.added = false) (i : ℕ)
    (h : (((A[i]?).map (·.added)) != some true) = true) :
    ((((A.push o)[i]?).map (·.added)) != some true) = true := by
  rw [Array.getElem?_push]
  by_cases hi : i = A.size
  · rw [if_pos hi]
    simp [ho]
  · rw [if_neg hi]
    exact h

/-- What the ledger behind is to the ledger in front. -/
structure LedgerPass (F G : Fork) : Prop where
  later : _root_.Fo.Later F G
  sized : Sized G
  trees : G.trees = F.trees
  below : ∀ j, j < F.next → Filled G j → Filled F j
  owed : ∀ i, unpaid F i = true → unpaid G i = true

theorem ledgerPass_of {h : Forest.Shape} {F G : Fork} {g : Forest.Heard} (hS : Sized F)
    (E : _root_.Fo.Tp.PadExact h F G g) (L : Later F G) (ht : G.trees = F.trees)
    (ho : G.owed = ((F.owed.push { what := "look-up-mask-claims" }).push
      { what := "look-up-plane-claims" }).push { what := "look-up-join" }) : LedgerPass F G where
  later := ⟨L.next, L.ns, L.keep⟩
  sized := L.sized hS
  trees := ht
  below := fun j hj hf => ((E.marks j).1 hf).elim id fun y => absurd y.1 (Nat.not_le.2 hj)
  owed := fun i hi => by
    unfold unpaid at hi ⊢
    rw [ho]
    exact unpaid_push _ _ rfl i (unpaid_push _ _ rfl i (unpaid_push _ _ rfl i hi))

/-! ## The footprints -/

/-- **THE FOOTPRINT AT THE CALLS.** -/
theorem k3_calls_footprint {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F G : Fork) (g : Forest.Heard), s.fork? = some F ∧ s.lookHeard? = none ∧
      s' = (s.putFork G).hearLook g ∧ (Sized F → LedgerPass F G) := by
  obtain ⟨F, x, hF, hn, e, hE⟩ :=
    decide_ledger (seatCalls claim) piece laid before p guests s s' rs cols hd
  exact ⟨F, x.2, x.1, hF, hn, e, fun hS => by
    obtain ⟨E, L, ht, ho⟩ := hE hS
    exact ledgerPass_of hS E L ht ho⟩

theorem tl_of_fork {s : S} {F : Fork} (h : s.fork? = some F) : ∃ tl, s.tl? = some tl := by
  cases hh : s.here with
  | between => simp [S.fork?, hh] at h
  | fin _ => simp [S.fork?, hh] at h
  | mem _ => simp [S.fork?, hh] at h
  | lay a => exact ⟨a.tl, by simp [S.tl?, hh]⟩
  | att a => exact ⟨a.tl, by simp [S.tl?, hh]⟩
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at h
    | true => exact ⟨a.tl, by simp [S.tl?, hh, ho]⟩

/-- **THE FOOTPRINT AT THE DIGITS.** -/
theorem k3_digits_footprint {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') :
    ∃ (F G : Fork) (g : Forest.Heard) (tl : HTailF2), s.fork? = some F ∧ s.tl? = some tl ∧
      s' = (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G ∧ (Sized F → LedgerPass F G) := by
  obtain ⟨F, x, hF, _, e, hE⟩ :=
    decide_ledger (seatDigits claim) piece laid before p guests s s' rs cols hd
  have hF' : s.fork? = some F := hF
  obtain ⟨tl, htl⟩ := tl_of_fork hF'
  refine ⟨F, x.2, x.1, tl, hF', htl, ?_, fun hS => ?_⟩
  · rw [e]
    simp only [seatDigits, htl, hF']
  · obtain ⟨E, L, ht, ho⟩ := hE hS
    exact ledgerPass_of hS E L ht ho

/-! ## What the two seats' put leaves -/

theorem putCalls_rest {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (F Gk : Fork)
    (hF : (seatCalls claim).fork s = some F) (hn : (seatCalls claim).heard s = none) :
    mergeOf ((seatCalls claim).put s g Gk) = mergeOf s ∧
      ((seatCalls claim).put s g Gk).tl? = s.tl? := by
  simp only [seatCalls] at hF hn ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hF
  | fin _ => simp [S.fork?, hh] at hF
  | mem _ => simp [S.fork?, hh] at hF
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    constructor <;> simp [mergeOf, S.tl?, S.putFork, S.hearLook, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    constructor <;> simp [mergeOf, S.tl?, S.putFork, S.hearLook, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hF
    | true =>
      have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh, ho] using hn
      constructor <;> simp [mergeOf, S.tl?, S.putFork, S.hearLook, hh, ho, hn']

theorem putDigits_rest {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (F Gk : Fork)
    (hF : (seatDigits claim).fork s = some F) :
    mergeOf ((seatDigits claim).put s g Gk) = mergeOf s ∧
      ((seatDigits claim).put s g Gk).tl?.isSome = true := by
  simp only [seatDigits] at hF ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hF
  | fin _ => simp [S.fork?, hh] at hF
  | mem _ => simp [S.fork?, hh] at hF
  | lay a => constructor <;> simp [mergeOf, S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | att a => constructor <;> simp [mergeOf, S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hF
    | true => constructor <;> simp [mergeOf, S.tl?, S.fork?, S.putTl, S.putFork, hh, ho]

/-! ## K3Pass -/

/-- **An accept at the calls is a K3Pass.** -/
theorem k3_calls_pass {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) : ∃ G, K3Pass s s' F G := by
  obtain ⟨F0, x, hF0, hn, e, hE⟩ :=
    decide_ledger (seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
  obtain ⟨E, L, ht, ho⟩ := hE hS
  have Q := ledgerPass_of hS E L ht ho
  obtain ⟨m1, m2⟩ := putCalls_rest claim s x.1 F x.2 hF0 hn
  refine ⟨x.2, k3_calls_sameBut claim piece laid before p guests s s' rs cols hd, hF, ?_, Q.later,
    hS, Q.sized, Q.trees, Q.below, Q.owed, by rw [e]; exact m1, fun h => by rw [e, m2]; exact h⟩
  rw [e]
  exact seatCalls_keeps claim s x.1 x.2 (by rw [hF0]; rfl) hn

/-- **An accept at the digits is a K3Pass.** -/
theorem k3_digits_pass {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) : ∃ G, K3Pass s s' F G := by
  obtain ⟨F0, x, hF0, hn, e, hE⟩ :=
    decide_ledger (seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
  obtain ⟨E, L, ht, ho⟩ := hE hS
  have Q := ledgerPass_of hS E L ht ho
  obtain ⟨m1, m2⟩ := putDigits_rest claim s x.1 F x.2 hF0
  refine ⟨x.2, k3_digits_sameBut claim piece laid before p guests s s' rs cols hd, hF, ?_, Q.later,
    hS, Q.sized, Q.trees, Q.below, Q.owed, by rw [e]; exact m1, fun _ => by rw [e]; exact m2⟩
  rw [e]
  exact seatDigits_keeps claim s x.1 x.2 (by rw [hF0]; rfl) hn

/-! ## "objects" -/

/-- **"objects" answers behind a pass what it answered in front.** -/
theorem objects_same (seat : Seat S Claim) (hA : AtS2 seat) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G) (hh : seat.heard s' = seat.heard s) :
    RunSame (objectsRun seat) s s' := by
  intro cl t F1 G1 hr hF1 hG1
  obtain rfl : F = F1 := Option.some.inj (P.front.symm.trans hF1)
  obtain ⟨F2, g, e1, e2, rfl⟩ := objects_cut seat hr
  obtain rfl : F = F2 := Option.some.inj (P.front.symm.trans ((hA.fork s).symm.trans e1))
  have hr0 : objectsRun seat 0 s =
      .ok (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) := by
    unfold objectsRun
    rw [e1, e2]
    rfl
  have hcl : cl = g.rows.toList.map seat.claim :=
    (congrArg Prod.fst (Except.ok.inj (hr.symm.trans hr0)))
  have hr' : objectsRun seat 0 s' =
      .ok (g.rows.toList.map seat.claim, seat.mark s' (G.paid g.owedObjects)) := by
    unfold objectsRun
    rw [(hA.fork s').trans P.behind, hh, e2]
    rfl
  have hG1' : G1 = F.paid g.owedObjects := by
    rw [hA.mark, fork_putFork s F _ P.front] at hG1
    exact (Option.some.inj hG1).symm
  refine ⟨seat.mark s' (G.paid g.owedObjects), G, G.paid g.owedObjects, by rw [hcl]; exact hr',
    P.behind, by rw [hA.mark]; exact fork_putFork s' G _ P.behind, ?_, P.trees⟩
  rw [hG1', lateOf_same G (G.paid g.owedObjects) rfl, lateOf_same F (F.paid g.owedObjects) rfl]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_ledger
#print axioms VerifiableInference.OnPublicFiles.k3_calls_footprint
#print axioms VerifiableInference.OnPublicFiles.k3_digits_footprint
#print axioms VerifiableInference.OnPublicFiles.k3_calls_pass
#print axioms VerifiableInference.OnPublicFiles.k3_digits_pass
#print axioms VerifiableInference.OnPublicFiles.objects_same
