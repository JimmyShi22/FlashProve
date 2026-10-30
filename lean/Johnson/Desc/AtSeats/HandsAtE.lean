--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
HandsAtE.lean: `IM.Hands` (Johnson/IMR/HandsDef.lean: another
house's light file) WHOLE, ALL SIX FIELDS, AT THREE SUB-PROTOCOLS OF OURS, AT THE FURTHER TEST
THAT IS RULED FOR IT: the promise's public test at the border (`First.ePubAt`,
Johnson/Desc/First/EPubAt.lean: another house's), read at one public part z. A definition, and
statements with their proofs. How it parts from HandsMore.lean: there the further test
has "in order" beside the public test; here it has not. So nothing on "in order" is in hand in
front, and nothing on it is owed behind.
  `EAt z Mg links ps k s` := `First.ePubAt Mg.pub Mg.more links ps k (z, s)`.
  `eAt_parts`, `eAt_of`: what it gives; how it is shown. `hands_M3_e`, `hands_M4_e`: **`IM.Hands N
  links ps (EAt z Mg links ps) ft k b`** at kind K13's batching and at W's commitment: from
    `RowM3` | `RowM4` and `FillM3` | `FillM4`, as in HandsMore.lean: the proofs there spend "in
    order" for "in order" alone.
  `hands_G_e`: at the first segment's opening: ONE PREMISE MORE (hin): "in order" holds in front:
  the
    tie's own clauses on what the sub-protocol makes are handed it (`FillG.made`), and so is hown.
What is not claimed. A member of the `Row…` | `Fill…`; hin. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.HandsMore
import Johnson.Desc.First.EPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers More Pub Item Meaning)
open VerifiableInference.Desc.K13 (Where atM3 atM4)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open ProofFile (Cl)

variable {Pp W : Type}

/-- **The promise's public test at border k**, at one public part. -/
def EAt (z : Pp) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ) (s : S) : Bool :=
  First.ePubAt Mg.pub Mg.more links ps k (z, s)

/-- What it gives. -/
theorem eAt_parts {z : Pp} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {s : S} (h : EAt z Mg links ps k s = true) :
    (∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q (z, s) = true) ∧
      ∀ q ∈ First.pubOfItems (openAt links ps k), Mg.pub q (z, s) = true :=
  ⟨fun q hq => First.ePubAt_mem _ _ _ _ _ _ h q (Or.inl hq),
    fun q hq => First.ePubAt_mem _ _ _ _ _ _ h q (Or.inr hq)⟩

/-- And how it is shown. -/
theorem eAt_of {z : Pp} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ} {s : S}
    (h2 : ∀ q ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q (z, s) = true)
    (h3 : ∀ q ∈ First.pubOfItems (openAt links ps k), Mg.pub q (z, s) = true) :
    EAt z Mg links ps k s = true := by
  unfold EAt First.ePubAt
  refine List.all_eq_true.2 fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · exact h2 q hq
  · exact h3 q hq

/-- **Kind K13's batching.** -/
theorem hands_M3_e {nR : ℕ} (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (z : Pp) (ft k : ℕ) (P : Where)
    (rw : Pp × S → W → Wit GE nR P.lin.kCol) (hT : RowM3 N Mg.more links ps k)
    (hF : FillM3 Cl P N Mg rw ((First.pubSets Mg.more links ps)[k]?.getD [])) :
    IM.Hands N links ps (EAt z Mg links ps) ft k (atM3 P : Block S Cl) :=
  hands_M3 N Mg.more links ps _ ft k P hT fun s s' hy _ _ hx => by
    obtain ⟨hQ, hTd⟩ := eAt_parts (IM.xk_parts hx).2.2.2.2
    obtain ⟨rs, gs, hd⟩ := yes_decides hy
    have hst : StepM3 Cl P (z, s) (z, s') := ⟨rfl, rs, gs, hd⟩
    refine eAt_of (fun q hq => ?_) fun q hq => ?_
    · rcases hT.pubs q hq with rfl | hq'
      · exact hF.frontOk _ ((frontOkB_iff P _ y₀).2 (atM3_front y₀ hd))
      · exact hF.pubRide _ _ q hst hq' (hQ q hq')
    · rcases hT.tied q hq with rfl | rfl
      · exact hF.indexIs _ _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inl rfl)))
      · exact hF.indexThere _ _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inr rfl)))

/-- **W's commitment.** -/
theorem hands_M4_e (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (z : Pp) (ft k : ℕ) (P : Where) (P' : K1.Par)
    (hT : RowM4 N Mg.more links ps k (K1.layOf P').shapes.size P'.sent.size)
    (hF : FillM4 Cl P P' N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?)
    (hPl : wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      planSitsB P P' = true ∧ planSeatB N ps[k]? P' = true) :
    IM.Hands N links ps (EAt z Mg links ps) ft k (atM4 P (K1.sendAtS P') : Block S Cl) :=
  hands_M4 N Mg.more links ps _ ft k P P' hT fun s s' hy _ _ hx => by
    obtain ⟨hQ, hTd⟩ := eAt_parts (IM.xk_parts hx).2.2.2.2
    have hbk := (IM.xk_parts hx).2.2.2.1
    obtain ⟨rs, cols, n, e⟩ := hy
    have hst : StepM4 Cl P P' (z, s) (z, s') := ⟨rfl, ft, rs, cols, n, e⟩
    obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
    have hon := (frontOkB_iff P s y₀).1 ((hF.frontOk (z, s)).1 (hQ _ hT.frontIn))
    obtain ⟨hE, hFr⟩ := atM4_laid hd y₀ y₀ hon
    refine eAt_of (fun q hq => ?_) fun q hq => ?_
    · rcases hT.pubs q hq with rfl | rfl | rfl | hq'
      · exact (hF.frontOk _).2 ((frontOkB_iff P _ y₀).2 hFr)
      · exact hF.evalLaid _ ((evalLaidB_iff P s').2 hE)
      · have hbk' := hbk
        unfold First.bookAt at hbk'
        simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
        obtain ⟨⟨b1, b2⟩, _⟩ := hbk'
        have hp1 := (planSitsB_iff P P').1 (hPl hq).1
        have hp2 : N.w = _ := eq_of_beq (hPl hq).2
        have hs := atM4_seat hd b2 hp1.pos
        rw [b1, ← hp2] at hs
        exact (hF.wSits _).2 ⟨atM4_sits hd y₀ hon hp1, hs⟩
      · exact hF.pubRide _ _ q hst hQ hbk hq'
    · rcases hT.tied q hq with rfl | rfl
      · exact hF.indexIs _ _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inl rfl)))
      · exact hF.indexThere _ _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inr rfl)))

/-- **The first segment's opening.** -/
theorem hands_G_e (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (ft k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (mk : List Pub)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hF : FillG Cl q gp nm X fvs kCol N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?
      mk)
    (hin : ∀ s, IM.XK N links ps (EAt z Mg links ps) k s = true → Mg.inOrder (z, s) = true)
    (hgroups : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown : ∀ x, Mg.inOrder x = true → First.bookAt N ps[k]? x.2 = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true) :
    IM.Hands N links ps (EAt z Mg links ps) ft k
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) :=
  hands_G N Mg.more links ps _ ft k q gp nm X fvs kCol mk hT
    (fun s hx => hgroups (z, s) ((eAt_parts (IM.xk_parts hx).2.2.2.2).1 _ hT.noneSent))
    (fun s hx => hown (z, s) (hin s hx) (IM.xk_parts hx).2.2.2.1)
    fun s s' hy _ _ hx => by
      obtain ⟨hQ, _⟩ := eAt_parts (IM.xk_parts hx).2.2.2.2
      have hbk := (IM.xk_parts hx).2.2.2.1
      have hio := hin s hx
      obtain ⟨rs, cols, n, e⟩ := hy
      have hst : StepG Cl q gp nm X fvs kCol (z, s) (z, s') := ⟨rfl, ft, rs, cols, n, e⟩
      refine eAt_of (fun i hi => ?_) fun i hi => ?_
      · rcases hT.pubs i hi with hi' | ⟨hi', hne⟩
        · exact hF.made _ _ i hst hQ hbk hio (Or.inl hi')
        · exact hF.pubRide _ _ i hst hQ hbk hi' hne
      · rcases hT.tied i hi with rfl | rfl
        · exact hF.made _ _ _ hst hQ hbk hio (Or.inr (Or.inl rfl))
        · exact hF.made _ _ _ hst hQ hbk hio (Or.inr (Or.inr rfl))

end HashBuild
