-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsHeadStays.lean: the lookup on the digits of a segment's approximate
range proof, AT THE OUTPUT HEAD's SEGMENT: WHICH FIELDS OF THE SEGMENT's OWN PART OF THE VERIFIER's
STATE (HeadOwn, Johnson/Desc/First/State.lean) AN ACCEPT WRITES: THREE: tl, F, claim: every other
field is left. Definitions, statements, proofs. NO SOUNDNESS IS CLAIMED.

Why. SameBut (K3CallsTurns.lean) says of the open segment's own part its sort alone. An item that
rides past the head's digits reads what the head's own rounds heard (the field x): so that field's
keeping is wanted, from the sub-protocol's own text.

Main names.
  HeadKept a a': a and a' are one but for tl, F, claim: said as: with these three laid anew at any
    values the two are equal. HeadKept.eq: a' = { a with tl := a'.tl, F := a'.F, claim := a'.claim
    }.
  HeadStays s s': where s stands in the head's segment with the part a, s' stands there with a part
    a' and HeadKept a a'. HeadStays.trans.
  putFork_headStays, putTl_headStays, headClaim_headStays, putDigits_headStays: the four writes.
  k3_digits_headStays: an .ok of K3.block's decide at seatDigits.
  k3_digits_seated_headStays: AN ACCEPT OF A PIECE THAT HOLDS «below B'», B' narrowing
    K3.theStated's value at the digits' address: the whole seated sub-protocol, the step without a
    round behind it (quietHead, which lays claim) among it.
  k3_digits_head_x: so a'.x = a.x and a'.t = a.t.
OBJECT. Desc.K3.seatDigits' put (K3Seat.lean), Desc.K3.quietHead and quietDigits (K3Whole.lean),
through their laws (decide_ok; K3QuietLaws.lean); Desc.K3.theStated through theStated_yes_digits
(K3DigitsSeatedYes.lean).
USER. Whoever carries an item that reads HeadOwn.x past the head's digits. K3DigitsStep.lean and
Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean call k3_digits_headStays; outside this file nothing
calls k3_digits_seated_headStays or k3_digits_head_x.
LETTERS. Those of k3_digits_seated_turns, less the place's.
IS IT EMPTY? Where s does not stand in the head's segment HeadStays says nothing.
Limits. Nothing on the three fields that are written (for F: DigLeft, K3DigitsSeatedLeaves.lean).
Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- The two are one but for tl, F, claim. -/
def HeadKept (a a' : Desc.First.HeadOwn) : Prop :=
  ∀ (tl : HTailF2) (F : Fork) (c : Option WsClaim),
    ({ a' with tl := tl, F := F, claim := c } : Desc.First.HeadOwn) =
      { a with tl := tl, F := F, claim := c }

theorem HeadKept.eq {a a' : Desc.First.HeadOwn} (h : HeadKept a a') :
    a' = { a with tl := a'.tl, F := a'.F, claim := a'.claim } := h a'.tl a'.F a'.claim

/-- Where s stands in the head's segment, s' does, and the part is kept but for the three. -/
def HeadStays (s s' : Desc.First.S) : Prop :=
  ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ HeadKept a a'

theorem HeadStays.trans {s t u : Desc.First.S} (h : HeadStays s t) (h' : HeadStays t u) :
    HeadStays s u := by
  intro a ha
  obtain ⟨a', h1, k1⟩ := h a ha
  obtain ⟨a'', h2, k2⟩ := h' a' h1
  exact ⟨a'', h2, fun tl F c => (k2 tl F c).trans (k1 tl F c)⟩

theorem putFork_headStays (s : Desc.First.S) (G : Fork) : HeadStays s (s.putFork G) := by
  intro a ha
  by_cases ho : a.opened = true
  · exact ⟨{ a with F := G }, by simp [Desc.First.S.putFork, ha, ho], fun _ _ _ => rfl⟩
  · exact ⟨a, by simp [Desc.First.S.putFork, ha, ho], fun _ _ _ => rfl⟩

theorem putTl_headStays (s : Desc.First.S) (tl : HTailF2) : HeadStays s (s.putTl tl) := by
  intro a ha
  by_cases ho : a.opened = true
  · exact ⟨{ a with tl := tl }, by simp [Desc.First.S.putTl, ha, ho], fun _ _ _ => rfl⟩
  · exact ⟨a, by simp [Desc.First.S.putTl, ha, ho], fun _ _ _ => rfl⟩

theorem headClaim_headStays (s : Desc.First.S) (a : Desc.First.HeadOwn) (c : WsClaim)
    (ha : s.here = .head a) :
    HeadStays s { s with here := .head { a with claim := some c } } := by
  intro a₀ h₀
  obtain rfl : a = a₀ := by
    have e := ha.symm.trans h₀
    injection e
  exact ⟨_, rfl, fun _ _ _ => rfl⟩

theorem putDigits_headStays {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatDigits claim).fork s = some F) :
    HeadStays s ((Desc.K3.seatDigits claim).put s g Gk) := by
  intro a ha
  have hF' : s.fork? = some F := hF
  cases ho : a.opened with
  | false => simp [Desc.First.S.fork?, ha, ho] at hF'
  | true =>
    have htl : s.tl? = some a.tl := by simp [Desc.First.S.tl?, ha, ho]
    have e : (Desc.K3.seatDigits claim).put s g Gk =
        (s.putTl { a.tl with
          foldDrawn := a.tl.foldDrawn + 1, slotA := F.next, slotB := Gk.next,
          heard := some g }).putFork Gk := by
      simp only [Desc.K3.seatDigits, htl, hF']
    rw [e]
    exact (putTl_headStays s _).trans (putFork_headStays _ _) a ha

/-- **An .ok of decide at the digits.** -/
theorem k3_digits_headStays {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : HeadStays s s' := by
  obtain ⟨F, y, hF, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putDigits_headStays claim s y.1 F y.2 hF

section
variable {Cl : Type} {Fr : Frame}

/-- **AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL.** -/
theorem k3_digits_seated_headStays {W : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (q : Piece (ckP .two) Fr Desc.First.S Cl W) (hq : q.b = below B') (hback : q.back = [])
    (u v : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out u τ = some v) : HeadStays u.1 v.1 := by
  obtain ⟨-, -, -, cols, hd⟩ := piece_hears_below q B' hq hback u τ v hout
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc u.1 v.1 _ cols
      (hN.2 _ _ _ _ hd)
  have hS := k3_digits_headStays claim a.piece laid sent _ [] u.1 s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' v.1 hfs
      rw [e]
      exact hS.trans (headClaim_headStays s' ah c ha)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' v.1 hfs
         exact hS.trans (e ▸ putFork_headStays s' _))

/-- **What the head's own rounds heard, and its tables, are left.** -/
theorem k3_digits_head_x {W : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (q : Piece (ckP .two) Fr Desc.First.S Cl W) (hq : q.b = below B') (hback : q.back = [])
    (u v : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out u τ = some v) (o : Desc.First.HeadOwn) (ho : u.1.here = .head o) :
    ∃ o', v.1.here = .head o' ∧ o'.x = o.x ∧ o'.t = o.t := by
  obtain ⟨o', h1, k⟩ := k3_digits_seated_headStays claim readers X codes shape a B B' h hOk hN i hi
    hpc q hq hback u v τ hout o ho
  exact ⟨o', h1, congrArg (·.x) (k o.tl o.F o.claim), congrArg (·.t) (k o.tl o.F o.claim)⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.putDigits_headStays
#print axioms VerifiableInference.OnPublicFiles.k3_digits_headStays
#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated_headStays
#print axioms VerifiableInference.OnPublicFiles.k3_digits_head_x
