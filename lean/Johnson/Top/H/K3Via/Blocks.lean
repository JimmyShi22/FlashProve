-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/Blocks.lean: the kind "lookup" (K3): the block with the hearing exchanged says
yes only where the block of Johnson/Desc/First/Look/K3Lookup.lean does, with the same record behind.
Theorems, over hearV_hear (Johnson/Top/H/K3Via/BridgeProof.lean).

Why. Whatever holds wherever K3.block's decide says .ok s' then holds wherever the new decide says
.ok s'. The definitions (hearVia, fitsVia, decideVia, blockVia) stand in
Johnson/Desc/First/Look/Via/Via.lean, which imports no proof.

Two forms.
  (1) The swap. `decideVia_decide`: decideVia's .ok s' gives (K3.block ...).decide's .ok s'.
    Premises: the plan's entries pass entriesFit and the entry-alone tests (both public).
    `blockVia_same`: every field of blockVia but planOk and decide is the old block's, by rfl.
    `blockVia_decide`: the swap as blocks: no premise but the new block's own planOk.
  (2) The general block. `decideV_decide`: (blockV seatV ...).decide's .ok s' gives (K3.block seat
    ...).decide's .ok s', under named relations of the two seats and places: they read one ledger,
    one count of rows owed and "nothing heard yet" alike; the place has shape h, with several calls;
    the general place's face is faceOf h and its first slot is p's; seatV's put lays what seat's put
    lays of the record led back (hput); and toHeard says yes wherever hearV does (hled): blockV
    itself does not ask toHeard's two counts. `decideV_ok`: what blockV's decide's yes says, test by
    test.

Limits. One way only. That the relations of form (2) can be met together by a seat over one carried
record is not shown here. The theorems are of K3.lean's decide and block as they lie beneath this
file: if these turn, the proofs must be run again. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.BridgeProof
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.Law
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)

/-! ## Named tests, one after the other -/

theorem namedS {α β : Type} {n : String} {x : Option α} {f : α → Except String β} {r : β}
    (h : (named n x >>= f) = .ok r) : ∃ a, x = some a ∧ f a = .ok r := by
  cases x with
  | none =>
    have h' : (Except.error n : Except String β) = .ok r := h
    cases h'
  | some a => exact ⟨a, rfl, h⟩

theorem needS {β : Type} {n : String} {b : Bool} {f : Unit → Except String β} {r : β}
    (h : (need n b >>= f) = .ok r) : b = true ∧ f () = .ok r := by
  cases b with
  | false =>
    have h' : (Except.error n : Except String β) = .ok r := h
    cases h'
  | true => exact ⟨rfl, h⟩

/-! ## (1) The swap -/

/-- **hearVia's yes gives hear's, with the same values.** -/
theorem hearVia_hear {p : First.Look.P} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView}
    {g' : Model.Forest.Heard}
    (hfit : ∀ h, p.shape = some h → entriesFit (faceOf h) es = true) (hst : es.all staticT = true)
    (hv : hearVia p F rs = some (g', G)) : hear p es F rs = some (g', G) := by
  unfold hearVia at hv
  cases hp : p.shape with
  | none =>
    rw [hp] at hv
    have h' : (none : Option (Model.Forest.Heard × Fork)) = some (g', G) := hv
    cases h'
  | some h =>
    rw [hp] at hv
    have hv1 : (if 1 < h.NC then (hearV (faceOf h) F rs).bind fun x =>
      (toHeard h (toHeardG x.1)).map fun g => (g, x.2)
        else none) = some (g', G) := hv
    split at hv1
    · rename_i hN
      cases hh : hearV (faceOf h) F rs with
      | none =>
        rw [hh] at hv1
        have h' : (none : Option (Model.Forest.Heard × Fork)) = some (g', G) := hv1
        cases h'
      | some x =>
        obtain ⟨gv, G0⟩ := x
        rw [hh] at hv1
        have hv2 : ((toHeard h (toHeardG gv)).map fun g => (g, G0)) = some (g', G) := hv1
        cases ht : toHeard h (toHeardG gv) with
        | none =>
          rw [ht] at hv2
          have h' : (none : Option (Model.Forest.Heard × Fork)) = some (g', G) := hv2
          cases h'
        | some g0 =>
          rw [ht] at hv2
          have h' : some (g0, G0) = some (g', G) := hv2
          cases h'
          exact hearV_hear hp hN (hfit h hp) hst hh ht
    · cases hv1

/-- K3.block's decide says yes where its tests hold. -/
theorem decide_mk {S Cl : Type} {seat : Seat S Cl} {piece : Nat} {laid : Array Nat}
    {before : List (Nat × Nat)}
    {p : First.Look.P} {guests : List (First.Look.Guest S Cl)} {s : S} {rs : List Fmt.RoundView} {gs : _}
      {F G : Fork}
    {g' : Model.Forest.Heard}
    (hall : seat.fork s = some F ∧ (seat.heard s).isNone = true ∧ (seat.owed s).noneWaits = true ∧
      (F.next == p.first) = true)
    (e5 : hear p (p.entries.getD []) F rs = some (g', G)) :
    (block seat piece laid before p guests).decide s rs gs = .ok (seat.put s g' G) := by
  obtain ⟨e1, e2, e3, e4⟩ := hall
  show (named "K3: no sub-proof is open" (seat.fork s) >>= fun F =>
      need "K3: nothing is heard yet" (seat.heard s).isNone >>= fun _ =>
      need "K3: rows are owed in front" (seat.owed s).noneWaits >>= fun _ =>
      need "K3: the ledger's count of slots" (F.next == p.first) >>= fun _ =>
      named "K3: the hearing" (hear p (p.entries.getD []) F rs) >>= fun x =>
      (pure (seat.put s x.1 x.2) : Except String S)) = _
  rw [e1]
  show (need "K3: nothing is heard yet" (seat.heard s).isNone >>= fun _ =>
      need "K3: rows are owed in front" (seat.owed s).noneWaits >>= fun _ =>
      need "K3: the ledger's count of slots" (F.next == p.first) >>= fun _ =>
      named "K3: the hearing" (hear p (p.entries.getD []) F rs) >>= fun x =>
      (pure (seat.put s x.1 x.2) : Except String S)) = _
  rw [e2, e3, e4, e5]
  rfl

/-- **(1) THE SWAP: the decide with the new hearing says .ok s' only where K3.lean's own block's
decide says .ok s'.** -/
theorem decideVia_decide {S Cl : Type} {seat : Seat S Cl} {piece : Nat} {laid : Array Nat}
    {before : List (Nat × Nat)}
    {p : First.Look.P} {guests : List (First.Look.Guest S Cl)} {s s' : S} {rs : List Fmt.RoundView}
      {gs : _}
    (hfit : ∀ h, p.shape = some h → entriesFit (faceOf h) (p.entries.getD []) = true)
    (hst : (p.entries.getD []).all staticT = true) (hd : decideVia seat p s rs = .ok s') :
    (block seat piece laid before p guests).decide s rs gs = .ok s' := by
  unfold decideVia at hd
  obtain ⟨F, e1, hd⟩ := namedS hd
  obtain ⟨e2, hd⟩ := needS hd
  obtain ⟨e3, hd⟩ := needS hd
  obtain ⟨e4, hd⟩ := needS hd
  obtain ⟨x, e5, hd⟩ := namedS hd
  obtain ⟨g', G⟩ := x
  have e6 : (Except.ok (seat.put s g' G) : Except String S) = .ok s' := hd
  cases e6
  exact decide_mk ⟨e1, e2, e3, e4⟩ (hearVia_hear hfit hst e5)

/-- The runs of claims are the old block's. -/
theorem blockVia_claims {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat))
    (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    (blockVia seat piece laid before p guests).claims =
      (block seat piece laid before p guests).claims := rfl

/-- **Every field but planOk and decide is the old block's.** -/
theorem blockVia_same {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat))
    (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    (blockVia seat piece laid before p guests).name = (block seat piece laid before p guests).name ∧
    (blockVia seat piece laid before p guests).place =
      (block seat piece laid before p guests).place ∧
    (blockVia seat piece laid before p guests).rounds =
      (block seat piece laid before p guests).rounds ∧
    (blockVia seat piece laid before p guests).oracles =
      (block seat piece laid before p guests).oracles ∧
    (blockVia seat piece laid before p guests).before =
      (block seat piece laid before p guests).before ∧
    (blockVia seat piece laid before p guests).claims =
      (block seat piece laid before p guests).claims ∧
    (blockVia seat piece laid before p guests).after =
      (block seat piece laid before p guests).after :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Its test on the plan gives the old block's. -/
theorem blockVia_planOk {S Cl : Type} {seat : Seat S Cl} {piece : Nat} {laid : Array Nat}
    {before : List (Nat × Nat)}
    {p : First.Look.P} {guests : List (First.Look.Guest S Cl)}
      (h : (blockVia seat piece laid before p guests).planOk = true) :
    (block seat piece laid before p guests).planOk = true ∧ fitsVia p = true := by
  have h' : ((block seat piece laid before p guests).planOk && fitsVia p) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'

/-- **THE SWAP, AS BLOCKS: where the new block's test on the plan says yes, its decide says .ok s'
only where K3.lean's own block's decide says .ok s'.** No other premise. -/
theorem blockVia_decide {S Cl : Type} {seat : Seat S Cl} {piece : Nat} {laid : Array Nat}
    {before : List (Nat × Nat)}
    {p : First.Look.P} {guests : List (First.Look.Guest S Cl)} {s s' : S} {rs : List Fmt.RoundView}
      {gs : _}
    (hplan : (blockVia seat piece laid before p guests).planOk = true)
    (hd : (blockVia seat piece laid before p guests).decide s rs gs = .ok s') :
    (block seat piece laid before p guests).decide s rs gs = .ok s' := by
  have hf := (blockVia_planOk hplan).2
  unfold fitsVia at hf
  cases hp : p.shape with
  | none =>
    rw [hp] at hf
    cases hf
  | some h =>
    rw [hp] at hf
    have hf' : (entriesFit (faceOf h) (p.entries.getD []) && (p.entries.getD []).all staticT) =
      true := hf
    rw [Bool.and_eq_true] at hf'
    refine decideVia_decide (fun h1 e => ?_) hf'.2 hd
    have e1 : h = h1 := Option.some.inj (hp.symm.trans e)
    subst e1
    exact hf'.1

/-! ## (2) The general block -/

/-- **What blockV's decide's yes says, test by test.** -/
theorem decideV_ok {S Cl : Type} {seat : SeatV S Cl} {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (First.Look.Guest S Cl)} {p : PG} {s s' : S} {rs : List Fmt.RoundView} {gs : _}
    (h : (blockV seat before bits guests p).decide s rs gs = .ok s') :
    ∃ F gv G, seat.fork s = some F ∧ (seat.heard s).isNone = true ∧ (seat.owed s).noneWaits = true ∧
      (F.next == p.first) = true ∧ (F.ns == p.ns) = true ∧ hearV p.face F rs = some (gv, G) ∧ s' =
        seat.put s gv G := by
  have h0 : (named "K3: no ledger is open" (seat.fork s) >>= fun F =>
      need "K3: nothing is heard yet" (seat.heard s).isNone >>= fun _ =>
      need "K3: rows are owed in front" (seat.owed s).noneWaits >>= fun _ =>
      need "K3: the ledger's count of slots" (F.next == p.first) >>= fun _ =>
      need "K3: the ledger's room" (F.ns == p.ns) >>= fun _ =>
      named "K3: the hearing" (hearV p.face F rs) >>= fun x =>
      (pure (seat.put s x.1 x.2) : Except String S)) = .ok s' := h
  obtain ⟨F, e1, h0⟩ := namedS h0
  obtain ⟨e2, h0⟩ := needS h0
  obtain ⟨e3, h0⟩ := needS h0
  obtain ⟨e4, h0⟩ := needS h0
  obtain ⟨e5, h0⟩ := needS h0
  obtain ⟨x, e6, h0⟩ := namedS h0
  obtain ⟨gv, G⟩ := x
  have e7 : (Except.ok (seat.put s gv G) : Except String S) = .ok s' := h0
  cases e7
  exact ⟨F, gv, G, e1, e2, e3, e4, e5, e6, rfl⟩

/-- **(2) blockV's decide says .ok s' only where K3.lean's own block's decide says .ok s'**, under
the named relations of the two seats and places. -/
theorem decideV_decide {S Cl : Type} {seatV : SeatV S Cl} {seat : Seat S Cl}
    {beforeV before : List (Nat × Nat)} {bits piece : Nat}
    {laid : Array Nat} {guestsV guests : List (First.Look.Guest S Cl)} {pg : PG} {p : First.Look.P}
      {h : Shape} {s s' : S}
    {rs : List Fmt.RoundView} {gs : _} (hp : p.shape = some h) (hN : 1 < h.NC) (hface : pg.face = faceOf h)
      (hfirst : pg.first = p.first)
    (hfork : seatV.fork s = seat.fork s) (howed : seatV.owed s = seat.owed s)
    (hheard : (seatV.heard s).isNone = (seat.heard s).isNone)
    (hput : ∀ gv G g', toHeard h (toHeardG gv) = some g' → seatV.put s gv G = seat.put s g' G)
    (hled : ∀ F gv G, hearV (faceOf h) F rs = some (gv, G) → ∃ g', toHeard h (toHeardG gv) =
      some g')
    (hfit : entriesFit (faceOf h) (p.entries.getD []) = true)
      (hst : (p.entries.getD []).all staticT = true)
    (hd : (blockV seatV beforeV bits guestsV pg).decide s rs gs = .ok s') :
    (block seat piece laid before p guests).decide s rs gs = .ok s' := by
  obtain ⟨F, gv, G, e1, e2, e3, e4, -, e6, e7⟩ := decideV_ok hd
  rw [hface] at e6
  obtain ⟨g', ht⟩ := hled F gv G e6
  rw [e7, hput gv G g' ht]
  rw [hfork] at e1
  rw [hheard] at e2
  rw [howed] at e3
  rw [hfirst] at e4
  exact decide_mk ⟨e1, e2, e3, e4⟩ (hearV_hear hp hN hfit hst e6 ht)

end VerifiableInference.Desc.K3.Law

#print axioms VerifiableInference.Desc.K3.Law.hearVia_hear
#print axioms VerifiableInference.Desc.K3.Law.decideVia_decide
#print axioms VerifiableInference.Desc.K3.Law.blockVia_decide
#print axioms VerifiableInference.Desc.K3.Law.decideV_ok
#print axioms VerifiableInference.Desc.K3.Law.decideV_decide
