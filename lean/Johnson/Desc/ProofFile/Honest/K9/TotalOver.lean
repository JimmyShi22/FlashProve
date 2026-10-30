-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalOver.lean: FOR THE ITEM "totalB": `SeatOver` (Honest/K9/TotalFront.lean), THE
SEAT's HALF OF THE CONVERSE OF THE LIBRARY's TIE AT A RUN BEHIND THE BATCHING: FROM "THE HEARING BLOCK IS THE LOT's
BLOCK ALONE". A statement and its proof ON THE VERIFIER's TEXT; no goal is stated.
  **`seatOver_of_alone`**   where entry number j of the link's order behind is o; the link's hearing block number o.1
      is b; b seats a block b' alone (`IM.LaidAlone ProofFile.sameReply`, Johnson/IMR/SeatForm.lean); and b' lists the run r
      under the name o.2: `SeatOver Lk j r`: the run that the link's list holds at o returns wherever r returns and
      the reply is left
  **`seatOver_k8`**, **`seatOver_k4`**   AT THE WRITTEN DESCRIPTION's OWN SEAT (the base is made, the blocks are laid,
      the chain is made of them: the premises of the library's `LPFK9.k8_ties`, `LPFK9.k4_ties`): at the segment number
      l: `SeatOver Lk j r` at every entry of the order behind that names the approximate range proof's hearing block
      (the feed-forward kind's), for the run r that the KIND's OWN BLOCK lists under that name: `K8.whole (ProofFile.k8ParW Z
      B.G₀ X l)`, at the built segment X; `blockAtC p4`, at what `LPFK9.k4ParAt` names
The library's `IM.after_lookup` and `IM.guardAfter_yes` (an "if and only if"), called; which block of the lot is
seated: `IM.chain_hear_alone`, `IM.lot_of_kind`, `LPFK9.k8_member`, `LPFK9.k4_lists`, `LPFK9.k4ParAt_of_mem`, as in
the library's own two theorems on the ties, which go the other way.
No member. `seatOver_of_alone` is called by the other two; these are called by no line.
WHAT IS NOT CLAIMED. The premises at any description. `KindOver`: the kind's half. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.IMR.SeatForm
import Johnson.IMR.LaidFirst
import Johnson.LPFK9R.K8Ties
import Johnson.LPFK9R.K4Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **The seat's half.** -/
theorem seatOver_of_alone (Lk : Link S Claim) (j : ℕ) (o : ℕ × String) (b b' : Block S Claim) (name : String)
    (a : Place) (r : S → Except String S) (ho : Lk.orderAfter[j]? = some o) (hb : Lk.hear[o.1]? = some b)
    (h : IM.LaidAlone ProofFile.sameReply b b' name a) (hr : b'.after.lookup o.2 = some r) : SeatOver Lk j r := by
  refine ⟨o, IM.guardAfter ProofFile.sameReply r, ho, ?_, fun e x h1 h2 => (IM.guardAfter_yes r e x).2 ⟨h1, h2⟩⟩
  show ((Lk.hear[o.1]?).bind fun x => x.after.lookup o.2) = some _
  rw [hb]
  show b.after.lookup o.2 = some _
  rw [IM.after_lookup h, hr]
  rfl

variable {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}

/-- **At the seat, for the approximate range proof's runs behind**: pW is that kind's own numbers at the built
segment X and its number l. -/
theorem seatOver_k8 (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K8)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ X, B.G₀.built.toList[l]? = some X ∧
      ∀ j name r, Lk.orderAfter[j]? = some (i, name) →
        (First.K8.whole (ProofFile.k8ParW Z B.G₀ X l)).after.lookup name = some r → SeatOver Lk j r := by
  obtain ⟨Lk, b, e1, e2, sp, _, L, hL, b', hb', _, ep, ha⟩ :=
    IM.chain_hear_alone hB hb hc l sub hl i .K8 hk (by decide) (by decide) hi
  obtain rfl : L = ProofFile.P1K8.lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨X, l', hX, rfl⟩ := LPFK9.k8_member hb'
  have e : (some l' : Option ℕ) = some l := congrArg Place.link ep
  obtain rfl := Option.some.inj e
  exact ⟨Lk, e1, X, hX, fun j name r ho hr => seatOver_of_alone Lk j (i, name) b _ _ _ r ho e2 ha hr⟩

/-- **At the seat, for the feed-forward kind's run behind**: p4 is what `LPFK9.k4ParAt` names at the segment. -/
theorem seatOver_k4 (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (hk : (kindsBeforeBatching sub (l == 0))[2]? = some KindName.K4) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ p4, LPFK9.k4ParAt Z B.G₀ l = some p4 ∧
      ∀ j name r, Lk.orderAfter[j]? = some (2, name) →
        (OnBytes.Desc.First.K4.blockAtC p4).after.lookup name = some r → SeatOver Lk j r := by
  obtain ⟨Lk, b, e1, e2, sp, _, L, hL, b', hb', _, ep, ha⟩ :=
    IM.chain_hear_alone hB hb hc l sub hl 2 .K4 hk (by decide) (by decide) (by decide)
  obtain rfl : L = ProofFile.k4Lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨x, hx, c0, _, c2⟩ := LPFK9.k4_lists hb'
  have e : (some x.2.link : Option ℕ) = some l := congrArg Place.link (c0.symm.trans ep)
  refine ⟨Lk, e1, _, LPFK9.k4ParAt_of_mem hx (Option.some.inj e), fun j name r ho hr => ?_⟩
  exact seatOver_of_alone Lk j (2, name) b b' _ _ r ho e2 ha (by rw [c2]; exact hr)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seatOver_k8
#print axioms ProofFile.Honest.K9.seatOver_k4
#print axioms ProofFile.Honest.K9.seatOver_of_alone
