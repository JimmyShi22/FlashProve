-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/Model/Denom.lean: identity at3 of an attention segment, tested on the
challenges of the lookup of a sub-proof.

Statements and proofs. No protocol of its own. The term forB and its counts are those of
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; the rule is `forB_ride`
(OnBytes/Tie/Pv/Lookup/Rider/ForB.lean); the array and its extension are those of
Cb/G6/Rider/Model/Denom.lean; `denOut` is that of Cb/Pv/Att/Mean/DenStep.lean.
Main names:
  `AttFits h D C`: what ties the lookup's record of public numbers h to the sizes D and the calls C
    of the segment: the first part of the key point has C.Dk places and the second C.sg; call 2 of h
    has 2^(C.a 2) keys; call 2 has whole trees, no more than 2^C.sg; a piece of the family w3 fits
    into call 2; the D.nb pieces have numbers of C.a 2 - D.lW bits; the point has a place. Of the
    other calls of h, and of where call 2's trees lie, nothing is asked.
  `attFits_nc`, `attFits_io`: with the lookup's own test `FoNums.ok`, the record has a call 2, and
    C.e 2 is the record's own number of bits of that call's trees' numbers. `zC_outZk`: so the key
    point of call 2, as the segment cuts it from pt (`Calls.zC`), is the list `outZk h (C.e 2) b`.
  `attFits_ref`: `AttFits` at the reference sizes and calls (`Dim.ref`, `Calls.ref`), from h.dT =
    25, h.rK = 4 and 2^26 keys in call 2.
  `den_sel`: the pick `selAtt` is lawful under `AttFits`.
  `denOut_pick`, `den_target_out`: `denOut` at z is the extension of `denVec` at the pick of z; so
    `AtCoords` of the family `denFam` at the pick says `denOut` = 0.
  `den_forB`: from `KnowAt` of forB between any two joints JA and JB, `KnowAt` of the same
    reduction, with the same extractor and the same counts, from JA and "`idnVal` is 0 at every
    valid `Idn.at3 b g i`" to JB and "`denOut D C z t` = 0", z the point pt of the claim on the keys
    in the output statement. `cells`, how the cells are read off the caller's state and the tuple of
    messages, is a free letter.
  `denOut_congr`: `denOut` reads the places 0, .., v' of z alone. `den_forB_rho`: so the same holds
    with z the list `outRho` read by `Blocks.ofList`.
  `den_forB_in`: `den_forB` at forB's own joints, the first clause laid inside the relation R0 that
    rides along, at the input alone.
Limits: JA, JB, R0 and `cells` are free letters. If JA's relaxed relation without the first clause,
or JB's, already gives the first clause, the statement follows from its premise alone and says
nothing (`knowAt_hollow_own`, `knowAt_hollow_out`, Cb/G6/Rider/KnowAt.lean; `forB_hollow`). So a
caller whose R0 is a record of the segment's relation has to leave at3 out of it. No value of the
letters is given here at which the first clause fails while JA's relaxed relation holds. Nothing on
whether the programs test this target, on whether a later block takes it up, or on an honest prover.
-/
import OnBytes.Tie.Pv.Lookup.Rider.ForBCalls
import Cb.G6.Rider.Model.Denom

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Inst.Model Inst.Model.AttSeg Cb.Pv.Att

/-- The lookup's public numbers fit the segment's sizes and calls. -/
structure AttFits (h : Sh) (D : Dim) (C : Calls) : Prop where
  /-- the first part of the key point -/
  dk : C.Dk = h.dT
  /-- the second part -/
  sg : C.sg = h.rK
  /-- call 2 of the lookup's record has as many keys as call 2 of C -/
  n2 : FoNums.nOf h 2 = C.a 2
  /-- call 2 consists of whole trees -/
  le : C.Dk ≤ C.a 2
  /-- the numbers of its trees are part of the second part -/
  e2 : C.e 2 ≤ C.sg
  /-- a piece of the family w3 fits into call 2 -/
  lw : D.lW ≤ C.a 2
  /-- the pieces' numbers -/
  nb : D.nb ≤ 2 ^ (C.a 2 - D.lW)
  /-- the point has a place -/
  v1 : 1 ≤ h.v

/-- The pick is lawful. -/
theorem den_sel {h : Sh} {D : Dim} {C : Calls} (F : AttFits h D C) :
    SelIn (FoNums.v' h) (fun _ : Unit => C.a 2 - D.lW + D.lg + D.lT)
      fun _ => selAtt C.Dk C.sg (C.e 2) (C.a 2 - D.lW) := by
  have e : C.e 2 = C.a 2 - C.Dk := rfl
  have w : D.lW = 1 + D.lg + D.lT + D.ln := rfl
  have h1 := F.le
  have h2 := F.lw
  obtain ⟨s1, s2⟩ := selAtt_ok (dT := C.Dk) (rK := C.sg) (iota := C.e 2) (nb := C.a 2 - D.lW)
    (lgk := D.lg) (lt := D.lT) (ldh := D.ln) F.e2 (by omega)
  refine fun _ => ⟨s1, fun t ht => ?_⟩
  have h3 := s2 t ht
  have h4 := sh_v_eq F.v1
  have h5 := F.dk
  have h6 := F.sg
  show selAtt C.Dk C.sg (C.e 2) (C.a 2 - D.lW) t ≤ FoNums.v' h
  omega

/-- With the lookup's own test on its record, the record has a call 2. -/
theorem attFits_nc {h : Sh} {D : Dim} {C : Calls} (F : AttFits h D C) (H : FoNums.ok h = true) :
    2 < h.NC := by
  by_contra hn
  have hs := (ok_parts H).1.2.2.2.2.2.2
  have h10 := (ok_parts H).1.1
  have z : FoNums.nOf h 2 = 0 := by
    unfold FoNums.nOf
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  have a := F.n2
  have l := F.le
  have d := F.dk
  omega

/-- With the lookup's own test on its record, the number of bits of the trees' numbers of call 2 is
the record's own. -/
theorem attFits_io {h : Sh} {D : Dim} {C : Calls} (F : AttFits h D C) (H : FoNums.ok h = true) :
    C.e 2 = FoNums.io h 2 := by
  have p := ((ok_parts H).2.2.1 2 (attFits_nc F H)).2.2.1
  have e : C.e 2 = C.a 2 - C.Dk := rfl
  have a := F.n2
  have d := F.dk
  omega

/-- At the reference sizes and calls, from three numbers of the record. -/
theorem attFits_ref {h : Sh} (h1 : h.dT = 25) (h2 : h.rK = 4) (h3 : FoNums.nOf h 2 = 26) :
    AttFits h Dim.ref Calls.ref :=
  ⟨h1.symm, h2.symm, h3, by decide, by decide, by decide, by decide, by
    show 1 ≤ h.dT + h.rK
    omega⟩

section Congr
variable {E : Type} [Field E]

/-- The key point of call 2, as the segment cuts it from the point pt, is the list `outZk`. -/
theorem zC_outZk {St J : Type} {h : Sh} {D : Dim} {C : Calls} (F : AttFits h D C) (b : TX St E J)
    {j : ℕ} (hj : j < C.e 2 + h.dT) : (outZk h (C.e 2) b).getD j 0 = C.zC 2 b.2.1.pt j := by
  rw [outZk_at h F.v1 b (by rw [← F.sg]; exact F.e2) hj, zC_keyIx C 2 F.e2, F.dk, F.sg]

/-- `denOut` at z is the extension of `denVec` at the pick of z. -/
theorem denOut_pick {D : Dim} {C : Calls} (he : C.e 2 ≤ C.sg) (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW))
    (z : ℕ → E) (t : Raw → E) :
    denOut D C z t = ext (C.a 2 - D.lW + D.lg + D.lT) (denVec D t)
      (fun s => z (selAtt C.Dk C.sg (C.e 2) (C.a 2 - D.lW) s)) := by
  rw [← den_out D C hN z t]
  exact ext_congr_point (fun s _ => zC_keyIx C 2 he z _) _

/-- The target at the pick, in the names of the field relation. -/
theorem den_target_out {St M : Type} {D : Dim} {C : Calls} (he : C.e 2 ≤ C.sg)
    (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW)) (cells : St → M → Raw → E) (st : St) (pt : ℕ → E) (m : M) :
    AtCoords (fun _ : Unit => C.a 2 - D.lW + D.lg + D.lT)
        (fun _ => selAtt C.Dk C.sg (C.e 2) (C.a 2 - D.lW)) (denFam D cells) st pt m ↔
      denOut D C pt (cells st m) = 0 := by
  rw [den_target, denOut_pick he hN]

/-- `denOut` reads the places 0, .., v' of z alone. -/
theorem denOut_congr {h : Sh} {D : Dim} {C : Calls} (F : AttFits h D C) {z z' : ℕ → E}
    (hz : ∀ s, s ≤ FoNums.v' h → z s = z' s) (t : Raw → E) :
    denOut D C z t = denOut D C z' t := by
  rw [denOut_pick F.e2 F.nb, denOut_pick F.e2 F.nb]
  exact ext_congr_point (fun s hs => hz _ ((den_sel F ()).2 s hs)) _

end Congr

section Rule
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type}

/-- at3 on the challenges of forB, between any two joints between which forB has KnowAt. Warning: JA
and JB are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem den_forB {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e)
    {D : Dim} {C : Calls} (F : AttFits h D C) (cells : St₀ → M → Raw → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider JA fun m a =>
        ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells a.1 m) (.at3 b g i) = 0)
      (withRider JB fun m b => denOut D C b.1.2.1.pt (cells b.1.1.1 m) = 0)
      xt (forB E h L V₀ V₀C (Ex := Ex)).e := by
  have G := forB_ride hK _ _ (den_sel F) (denFam D cells)
  exact knowAt_congr_rider (fun m a => den_source D cells F.nb a.1 m)
    (fun m b => den_target_out F.e2 F.nb cells b.1.1.1 b.1.2.1.pt m) G

/-- The same, the point read off the list of its places. -/
theorem den_forB_rho {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e)
    {D : Dim} {C : Calls} (F : AttFits h D C) (cells : St₀ → M → Raw → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider JA fun m a =>
        ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells a.1 m) (.at3 b g i) = 0)
      (withRider JB fun m b => denOut D C (ofList (outRho h b.1)) (cells b.1.1.1 m) = 0)
      xt (forB E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_congr_rider (fun _ _ => Iff.rfl)
    (fun _ b => Eq.congr_left (denOut_congr F (fun _ hs => (outRho_at h b.1 hs).symm) _))
    (den_forB hK F cells)

variable {R0 : IOR.Rels Kc St₀ Ex (M × Wp)} {msg₀ : M → J₀ → E}

/-- at3 on the challenges of forB, at forB's own joints: the first clause comes in inside R0 and
does not come out. Warning: R0 is free (forB_hollow): it has to be without at3. -/
theorem den_forB_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {D : Dim} {C : Calls} (F : AttFits h D C) (cells : St₀ → M → Raw → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a =>
        ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells a.1 m) (.at3 b g i) = 0) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b => denOut D C b.1.2.1.pt (cells b.1.1.1 m) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (den_forB hK F cells)

end Rule

end Cb.Rider

#print axioms Cb.Rider.den_sel
#print axioms Cb.Rider.attFits_nc
#print axioms Cb.Rider.attFits_io
#print axioms Cb.Rider.attFits_ref
#print axioms Cb.Rider.zC_outZk
#print axioms Cb.Rider.denOut_congr
#print axioms Cb.Rider.den_forB
#print axioms Cb.Rider.den_forB_rho
#print axioms Cb.Rider.den_forB_in
