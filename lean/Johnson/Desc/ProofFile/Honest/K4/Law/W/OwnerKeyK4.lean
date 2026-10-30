-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OwnerKeyK4.lean: CONDITIONAL. On public data alone.
AT EACH OF THE TWELVE GROUPS.

What is here. THE KEY UNDER WHICH THE HONEST SIDE OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4) READS MATRIX NUMBER i OF ITS LIST (`k4Owner`, Honest/K4/Part.lean) IS, AT EVERY
GROUP OF LAYERS: THE NUMBER OF THE SEGMENT OF WHOEVER COMMITTED THE MATRIX (the first of the
library's `ownerW g i`, Johnson/Road/K4/K4PlanNine.lean), THE LABEL OF THAT OWNER's NAME IN THE
FULL-SIZE EXAMPLE's TYPED SIZES (`Sz.ref.owner`, `MatName.label`), AND COLUMN 0. It is the premise
hOwn of `k4SymsRaw_all` (Law/W/SymsOfLaysCells.lean). Two statements with their proofs. The first is
on the verifier's own list `tailsOf` (OnBytes/Model/LayerPlan.lean) where af has three parts and ad
one: by unfolding, then number by number, in the first group and in a later one. The second lays the
letters under h: the member's public numbers' lists are `tailsOf`'s (`IM.k4_seated`,
Johnson/IMR/K4Seat.lean); the parts are three and one (`Hd.parts_ref`, Johnson/Road/HeadZ.lean, at
`Hd.eleven_of_core`, as Johnson/IMR/OwnKinds.lean draws it).

  `tails_entry`   an entry of a group's list: its name is the label; it begins at column 0; it is of
      kind 1 just at the stream that comes in of a later group, and its field aId (in `TMat`'s words
      256 times the owning sub-proof's number, plus the matrix's index there; group g - 1 bears the
      number g) is then 256 g + 7.
  `k4Owner_at`   **the key, at each group.**

Not shown here. Nothing on what a cell holds. h: the library's hypothesis `P5J.AtMgA` on the public
files; Lh (`LaidK4`, Law/SeatedHead.lean) follows from it; hQ: Qp is what `k4PubOf` returns at the
member's parameters (`k4Pub_head`, Law/FrontCount.lean, has that it returns). `k4Owner_at` RESTS ON
A LAW OF A FILE UNDER Johnson/Goal/, CALLED BY NAME (`Hd.core_of_scope`), as the library's own files
call it. All limits of the heads of the files that it imports hold here; among them: closed facts by
evaluation in Lean's kernel lie beneath; no independent checker that its writers know of has
replayed them; through its imports it stands over files under Johnson/Goal/. THE FULL SIZE ALONE,
and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MatsAreHead
import Johnson.HonestTrace.Packed
import Johnson.IMR.OwnKinds
import Johnson.IMR.K4Seat
import Johnson.Road.K4.Names.BorderKinds
import Johnson.Road.K4.K4PlanNine

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model.Layer (tailsOf matIx)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_eq_some_iff no?_lt)
open OnBytes.Road.K4 (ownerW)
open OnBytes.Road.K4.Names (getD_map_range)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- CONDITIONAL: af has three parts and ad one; g is a group; μ is the name with the number i. **An
entry of a group's list.** -/
theorem tails_entry {y : OnBytes.Model.Layer.Lay} (p0 : y.parts.getD 0 0 = 3)
    (p1 : y.parts.getD 1 0 = 1) {g : ℕ} (hg : g < y.NGr) {i : ℕ} {μ : MatName}
    (hμ : Sz.ref.nameNo (.ff g) i = some μ) :
    (((tailsOf y).getD g {}).mats.getD i {}).name = μ.label ∧
      (((tailsOf y).getD g {}).mats.getD i {}).ttOff = 0 ∧
      (¬ (i = 8 ∧ g ≠ 0) → (((tailsOf y).getD g {}).mats.getD i {}).kind = 0) ∧
      (i = 8 ∧ g ≠ 0 → (((tailsOf y).getD g {}).mats.getD i {}).kind = 1 ∧
        (((tailsOf y).getD g {}).mats.getD i {}).aId = g * 256 + 7) := by
  have hi : i < 9 := no?_lt Sz.ref ((nameNo_eq_some_iff Sz.ref _ _ _).1 hμ)
  have e8 : (matIx y).iXI = 8 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 = 8
    rw [p0, p1]
  have e7 : (matIx y).iXO = 7 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 = 7
    rw [p0, p1]
  unfold tailsOf
  dsimp only
  rw [getD_map_range _ hg]
  dsimp only
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, p0, p1, e8, e7]
  by_cases h0 : g = 0
  · subst h0
    simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    interval_cases i
    · obtain rfl : MatName.af 0 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.af 1 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.af 2 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.ad 0 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.ar = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.b = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.qa = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.xbO = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
    · obtain rfl : MatName.xbI = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd rfl c.2⟩
  · have hb : (g != 0) = true := bne_iff_ne.2 h0
    simp only [hb, Bool.and_true]
    interval_cases i
    · obtain rfl : MatName.af 0 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.af 1 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.af 2 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.ad 0 = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.ar = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.b = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.qa = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.xbO = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun _ => rfl, fun c => absurd c.1 (by decide)⟩
    · obtain rfl : MatName.xbI = μ := Option.some.inj hμ
      exact ⟨rfl, rfl, fun c => absurd ⟨rfl, h0⟩ c, fun _ => ⟨rfl, rfl⟩⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh, hQ and hμ. **THE KEY UNDER WHICH K4's HONEST SIDE READS MATRIX i, AT EACH
GROUP.** -/
theorem k4Owner_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {i : ℕ} {μ : MatName}
    (hμ : Sz.ref.nameNo (.ff g) i = some μ) :
    k4Owner Qp i = ((ownerW g i).1, (Sz.ref.owner (.ff g) μ).2.label, 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    O.W ▸ O.public
  have B := (OnBytes.Road.Hd.eleven_of_core hpub
    (OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub) (OnBytes.Road.Hd.npOf Zp.p.X.hS)).1
  obtain ⟨p0, p1⟩ := OnBytes.Road.Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨G₀, hG, hx'⟩ := Lh.lot
  have hT := (IM.k4_seated O.pub hG hx').2.1
  have ey : x.2.P.y = Zp.p.X.y := (nine_head h Lh).Sx.y
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
  have hN : g < Zp.p.X.y.NGr := by
    rw [B.groups]
    exact Lh.lt
  obtain ⟨t1, t2, t3, t4⟩ := tails_entry p0 p1 hN hμ
  unfold k4PubOf at hQ
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
  unfold k4Owner
  dsimp only
  rw [hT, ey, Lh.grp]
  by_cases c : i = 8 ∧ g ≠ 0
  · obtain ⟨k1, k2⟩ := t4 c
    obtain ⟨rfl, h0⟩ := c
    obtain rfl : MatName.xbI = μ := Option.some.inj hμ
    have hN' : g - 1 < Zp.p.X.y.NGr := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN
    have u1 := (tails_entry p0 p1 hN' (i := 7) (μ := .xbO) rfl).1
    have ea : (g * 256 + 7) / 256 - 1 = g - 1 := by omega
    have eb : (g * 256 + 7) % 256 = 7 := by omega
    have own : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
    have ow : ownerW g 8 = (2 * (g - 1), 7) := by
      unfold ownerW
      rw [if_pos ⟨rfl, h0⟩]
    rw [if_pos (by rw [k1]; rfl), k2, ea, eb, u1, t2, own, ow]
  · have ow : ownerW g i = (2 * g, i) := by
      unfold ownerW
      rw [if_neg c]
    have own : Sz.ref.owner (.ff g) μ = (.ff g, μ) := by
      by_cases hx : μ = .xbI
      · subst hx
        have e8 : 8 = i := Option.some.inj hno
        exact if_pos (by
          by_contra h0
          exact c ⟨e8.symm, h0⟩)
      · clear hμ hno t1 t2 t3 t4
        cases μ with
        | xbI => exact absurd rfl hx
        | _ => rfl
    rw [if_neg (by rw [t3 c]; decide), t1, own, ow]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.tails_entry
#print axioms ProofFile.Honest.K4.W.k4Owner_at
