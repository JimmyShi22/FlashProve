-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/AllThereAt.lean: AN ATTACK ON THE COMPOSED MEANING, ONE STOREY ABOVE
Johnson/P5J/AllFilledAt.lean: IS THERE A PUBLIC ITEM THAT THE FIRST CHAIN's PROMISE ASKS AT THE
FULL SIZE WHOSE LAYER ANSWERS THROUGH AN OPTION OFF THE PUBLIC DATA THAT IS none, SO THAT ITS
ANSWER IS false AT EVERY STATE (`pubAll_false_of_notThere`, Johnson/Desc/First/AllThereLaw.lean)?
NO: FROM THE HEAD: `allThere` (Johnson/Desc/First/AllThere.lean) SAYS YES AT THE COMPOSED
MEANING's OWN DATA. WHAT THIS DOES NOT SAY STANDS FIRST: ONE DIRECTION ALONE: where the option is
there the layer's test may still say false at every state for another reason; and `dataThere`
covers six sorts of item: that these are all whose tests read an option is said by nobody.
  `patNs` … `patPl`, `allThereP_full`: BY THE KERNEL: the test at a written PATTERN of answers:
    the number of slots at the 25 segments; the feed-forward caller's slot at the 12 even segments
    below 24; the attention caller's slot and the attention plan at the 12 odd ones; a place with
    a shape at all 25, both sorts of lookup. `bendP_ns`, `bendP_nx`, `bendP_f5`, `bendP_a5`,
    `bendP_pl`: NEGATIVE TESTS: with one of the five answers "never" the test says false: each
    bites.
  `shape_calls_at`: wherever the reader of the public files returns: at a place of a lookup on the
    calls the kind's own parameters make the place's own numbers (three landed `Fo.ShapeOf` laws
    and `shape_of_made`). `k03_placeThere`: from the head: a place with a shape at each of the
    fifty.
  `allThere_at`: THE THEOREM THAT COUNTS: `allThere h.𝔇.pubD (mgAtAll h).more fullLinks At.ps =
    true`.
Limits. The head h is a premise: a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/). At
OnBytes.secondHashFunction. The full size alone. No soundness is claimed.

-/
import Johnson.Desc.First.AllThereP
import Johnson.Desc.First.K4NextOf
import Johnson.Desc.First.Look.K3CallerCellsLaw
import Johnson.Goal.Meaning.OkScope
import Johnson.P5J.K03AsksAt
import Johnson.P5J.K03RidesDigLeft
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open OnBytes.Model.Verify (publicOf Public)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (allThere allThereP allThere_by allThereBy_P allThereP_mono
  hdOf)
open VerifiableInference.Desc.First.Look (lookAt placeAt P shape_of_made)

/-! ## 1 The pattern, by the kernel -/

def patNs (m : ℕ) : Bool := decide (m < 25)
def patNx (m : ℕ) : Bool := decide (m < 24) && m % 2 == 0
def patF5 (m : ℕ) : Bool := decide (m < 24) && m % 2 == 1
def patPl (m : ℕ) (_ : Bool) : Bool := decide (m < 25)

theorem allThereP_full : allThereP patNs patNx patF5 patF5 patPl 24 fullLinks fullLinks mgMore
    fullLinks At.ps = true := by decide +kernel

/-- **A negative test**: no segment has a number of slots. -/
theorem bendP_ns : allThereP (fun _ => false) patNx patF5 patF5 patPl 24 fullLinks fullLinks mgMore
    fullLinks At.ps = false := by decide +kernel

/-- **A negative test**: the feed-forward caller's slot is nowhere. -/
theorem bendP_nx : allThereP patNs (fun _ => false) patF5 patF5 patPl 24 fullLinks fullLinks mgMore
    fullLinks At.ps = false := by decide +kernel

/-- **A negative test**: the attention caller's slot is nowhere. -/
theorem bendP_f5 : allThereP patNs patNx (fun _ => false) patF5 patPl 24 fullLinks fullLinks mgMore
    fullLinks At.ps = false := by decide +kernel

/-- **A negative test**: no attention plan. -/
theorem bendP_a5 : allThereP patNs patNx patF5 (fun _ => false) patPl 24 fullLinks fullLinks mgMore
    fullLinks At.ps = false := by decide +kernel

/-- **A negative test**: no place with a shape. -/
theorem bendP_pl : allThereP patNs patNx patF5 patF5 (fun _ _ => false) 24 fullLinks fullLinks
    mgMore fullLinks At.ps = false := by decide +kernel

/-! ## 2 The options are there -/

/-- **At a place of a lookup on the calls the kind's own parameters make the place's numbers.** -/
theorem shape_calls_at {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (set : Params.Setting) {i : ℕ}
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt X i false = some x) :
    (P.ofPlace set false x).shape = some x.fs := by
  unfold lookAt at hx
  simp only [Bool.false_eq_true, ↓reduceIte] at hx
  repeat' split at hx
  all_goals first
    | (obtain rfl := Option.some.inj hx
       exact shape_of_made (Fo.Pub2.shapeOf_headLayout (Fo.Pub.publicOf_headLayout h)).1)
    | (obtain ⟨hp, -, e⟩ := Option.bind_eq_some_iff.1 hx
       obtain rfl := Option.some.inj e
       exact shape_of_made (Fo.layout_shape (Meaning.P34.layout_of_public h)))
    | (obtain ⟨a, ha, e⟩ := Option.bind_eq_some_iff.1 hx
       obtain rfl := Option.some.inj e
       exact shape_of_made
         (Fo.Pub2.lookPubA_ok (M₀ := Unit) (fun _ _ => 0) h _ a ha 0 0 Unit).shape)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **A place with a shape at each of the fifty, from the head.** -/
theorem k03_placeThere (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (d : Bool) : ((placeAt (At.X Zp) l d).any fun p => p.shape.isSome) = true := by
  cases d with
  | true =>
    obtain ⟨y, tl, hdig⟩ := k03_digAt_some h hl
    unfold VerifiableInference.Desc.First.Look.digAt at hdig
    obtain ⟨x', hx', hd1⟩ := Option.bind_eq_some_iff.1 hdig
    obtain ⟨tl', -, hd2⟩ := Option.bind_eq_some_iff.1 hd1
    obtain ⟨s, hs', -⟩ := Option.map_eq_some_iff.1 hd2
    unfold placeAt
    rw [hx']
    show (P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x').shape.isSome = true
    rw [hs']
    rfl
  | false =>
    obtain ⟨b', hb'⟩ := k03_const_some h hl false
    obtain ⟨-, p, hp, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
      Zp.first.codes Zp.first.shape l false b' hb'
    unfold placeAt at hp ⊢
    obtain ⟨x', hx', -⟩ := Option.map_eq_some_iff.1 hp
    rw [hx']
    show (P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x').shape.isSome = true
    rw [shape_calls_at h.pubOne _ hx']
    rfl

/-- Where the place has a shape, the slot behind the lookup on the calls is there. -/
theorem next_of_there {X : Public} {m : ℕ}
    (h : ((placeAt X m false).any fun p => p.shape.isSome) = true) :
    ((placeAt X m false).bind fun p => p.shape.map fun k => p.first + Forest.elems k).isSome =
      true := by
  cases hp : placeAt X m false with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    have h' : p.shape.isSome = true := h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h'
    show (p.shape.map fun k => p.first + Forest.elems k).isSome = true
    rw [hk]
    rfl

/-- **THE THEOREM THAT COUNTS: AT THE COMPOSED MEANING's OWN DATA, FROM THE HEAD.** -/
theorem allThere_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    allThere h.𝔇.pubD (mgAtAll h).more fullLinks At.ps = true := by
  obtain ⟨p4, ng, -, hA⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have eM : (mgAtAll h).more = mgMore := mgAll_more_base h.𝔇
  have e1 : hdOf h.𝔇.pubD.d3.X = 24 := by
    show (if (At.X Zp).p4 then 2 else 1) * (At.X Zp).NGr = 24
    rw [p4, ng]
    rfl
  rw [eM, allThere_by, allThereBy_P, e1]
  refine allThereP_mono (ns := patNs) (nx := patNx) (f5 := patF5) (a5 := patF5) (pl := patPl)
    ?_ ?_ ?_ ?_ ?_ 24 _ _ mgMore fullLinks At.ps allThereP_full
  · intro m hm
    have hm' : m < 25 := of_decide_eq_true hm
    have h0 := h.opts.builtAt m hm'
    obtain ⟨Xl, hX⟩ := Option.isSome_iff_exists.1 h0
    show ((Zp.made.p.built.links[m]?).map (·.ns)).isSome = true
    rw [hX]
    rfl
  · intro m hm
    have hm' : m < 24 := of_decide_eq_true (Bool.and_eq_true_iff.1 hm).1
    exact next_of_there (k03_placeThere h (by omega) false)
  · intro m hm
    have hm' : m < 24 := of_decide_eq_true (Bool.and_eq_true_iff.1 hm).1
    exact next_of_there (k03_placeThere h (by omega) false)
  · intro m hm
    have hm' : m < 24 := of_decide_eq_true (Bool.and_eq_true_iff.1 hm).1
    obtain ⟨a, ha, -⟩ := hA (m / 2) (by omega)
    show ((At.X Zp).A[m / 2]?).isSome = true
    rw [ha]
    rfl
  · intro m dg hm
    exact k03_placeThere h (of_decide_eq_true hm) dg

end P5J

#print axioms P5J.allThereP_full
#print axioms P5J.bendP_ns
#print axioms P5J.bendP_nx
#print axioms P5J.bendP_f5
#print axioms P5J.bendP_a5
#print axioms P5J.bendP_pl
#print axioms P5J.shape_calls_at
#print axioms P5J.k03_placeThere
#print axioms P5J.next_of_there
#print axioms P5J.allThere_at
