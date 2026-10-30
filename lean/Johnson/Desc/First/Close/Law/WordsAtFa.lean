-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/WordsAtFa.lean (kind K10): THE PREMISE hW OF
k10_rows_at_cube (RowsAtCube.lean, beside this file), TO THE LETTER, AT THE CONCRETE fa (`faK10`,
FaK10.lean), THE TYPED GROUP OF A WRITTEN LIST (`groupLayK`, CubeOfShapes.lean), THE RULED READER
(`wordsAtFirst arr`, FillRowFirst.lean) AND ANY WITNESS AT WHICH EVERY MEMBER OF THE LIST IS PINNED
IN THE TABLE's SENSE (`PinAt`, Johnson/Desc/Sound/MsgSig.lean). A joining of ViewText.lean
(wordsAre_of_msgs), MsgsAtFa.lean (fa_msgs_of_pin) and ShapesBegun.lean. Statements
and proofs.


WHY THE PREMISE IS THE PIN. THE TABLE's EXTRACTOR AT A
CLOSING DOES NOT LAY THE KEPT MEMBERS (Johnson/Desc/First/Borders.lean: laysSeats: "its group's but
the kept ones"). SO A PREMISE AT THAT EXTRACTOR's VALUE WOULD BE FALSE AT A KEPT MEMBER AND THE THEOREM IDLE
AT EVERY LINK THAT KEEPS ONE. Here the premise is the pin itself, a member: whoever calls
pays it at a member that is not kept by fa_pin_ext, and at a kept one from the item
"pinKept" behind the closing, ridden back: `pin_kept_behind` (PinKeptBack.lean), under its own
premises (two tests on the plan, run at no data there; the reader answers alike; the pin behind);
`k10_hpin` (HpinAtTable.lean) joins the two and spends hCar (`CarriedAt`) and hV (`SameVal`): an
assembly: nothing is shown of any state.

What is said.
  `wordsAre_congr`: WordsAre reads the words at the members' numbers alone.
  `wordsAre_of_pins`: **hW, TO THE LETTER**, at a letter R that IS the written list's typed group
    (hR: at the call: rfl), at every witness w.

PREMISES, each named.
  hc    the state's statement has the codes cs
  hs    the state's book places the statement's message number no i at the plan's seat of member i
  hSh   `ShapesAre` at the statement in front (members · flags · shapes)
  hpin  every member with a main row is pinned at w, at the statement in front.
ALL ARE ON THE STATE a (hpin: AND ON w): SHOWN OF NO STATE HERE.

Limits. OVER THE LIST's MEMBERS ALONE (the messages with a main row): of a message without one (at
the first link: the index masks') nothing is asked and nothing said. General in cs, lo, the stage,
N, num, pull, mW and the joint. Nothing on the carried claim or the public ties. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.ViewText
import Johnson.Desc.First.Close.Law.MsgsAtFa
import Johnson.Desc.First.Close.Law.ShapesBegun
import Johnson.Desc.First.Close.Law.FillRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open OnBytes.Means (Words extends_begun)
open VerifiableInference.Desc (FileDescription Strs Wit)

/-- WordsAre reads the words at the members' numbers alone. -/
theorem wordsAre_congr {S : Sig GE} (R : RowsK S) (T : Statement) (no : R.G.A → ℕ)
    (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (m m' : Words GE) (h : WordsAre R T no u m)
    (e : ∀ a part i, m' (no a) part i = m (no a) part i) : WordsAre R T no u m' where
  main := fun a idx hi hx => (e a .main idx).trans (h.main a idx hi hx)
  mask := fun a idx hi hx => (e a .mask idx).trans (h.mask a idx hi hx)

variable {Xi : Type} (Gd : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))

local notation "S1" => VerifiableInference.Desc.First.S

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **hW OF k10_rows_at_cube, TO THE LETTER, AT ANY WITNESS AT WHICH EVERY MEMBER IS PINNED.** -/
theorem wordsAre_of_pins (hR : R = groupLayK cs lo s e kb hM hZ) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (z : Pz) (a : S1 × F.E.Str) (no : Fin lo.length → ℕ) (r : R.G.C.Q → GE)
    (w : Wit Cells Tok MsgT) (hc : a.1.st.codes = cs)
    (hs : ∀ i, memMain lo i → seatBy noFirst a.1.book (no i) = some (seat i))
    (hSh : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr →
      ShapesAre (rdK a.1).2.2 Gr lo kb no)
    (hpin : ∀ i, memMain lo i →
      PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1) (strsOf F a.2) w) :
    ∀ μ : (sigOf cs lo).Msg, (∀ i, (sigOf cs lo).decs
      (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some (μ i)) →
    ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr →
      WordsAre R (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) (fun b => no b.1)
        (R.G.msg μ, r) (wordsAtFirst arr (z, a.1) (strsOf F a.2) w) := by
  subst hR
  intro μ hμ Gr hGr
  have H := shapesAre_begun (rdK a.1).2.1.group (hSh Gr hGr)
  have hE := extends_begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr
  refine wordsAre_congr _ _ _ _ _ _
    (wordsAre_of_msgs cs lo (memMain lo) s e _ _ hM hZ _
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) (fun b => no b.1)
      (seatBy noFirst a.1.book) seat arr w r
      (hE.codes.trans hc) (fun b => hs b.1 b.2)
      (fun b => Option.map_eq_some_iff.1 (H.shape b.1 (mem_members.2 b.2))) μ
      fun b => ?_) fun b part i => ?_
  · exact (fa_msgs_of_pin Gd cs lo seat _ N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW
      arr b.1 z a w (hpin b.1 b.2) (μ b.1) (hμ b.1)).symm
  · exact wordsBy_congr arr (seatBy noFirst a.1.book) (seatBy noFirst a.1.book)
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) a.1.st _ (no b.1) (no b.1) hE.codes.symm rfl
      (closeLedgers_shape Gr.members.toList (rdK a.1).2.2 (no b.1)).symm part i

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.wordsAre_congr
#print axioms VerifiableInference.Desc.First.Close.wordsAre_of_pins
