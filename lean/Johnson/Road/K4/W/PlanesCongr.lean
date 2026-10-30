-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/PlanesCongr.lean: CONDITIONAL.

What is here. THE LOOKUP's SENTENCE ON THE PLANES (`K3Planes`, Johnson/Top/H/K3RowOut.lean) READS
ITS READING ν OF THE LOOKUP's PLACES AT THE CELLS AND AT MASK ENTRIES ALONE, AND AT NO MASK ENTRY
FROM THE LOOKUP's FIRST SLOT PLUS ITS NUMBER OF MASK ENTRIES ON. So it holds of a second reading
that agrees with the first at every cell and at every mask entry below that sum (`planes_congr`).
Why that is so: the sentence reads masks through three sparse forms, whose places are all fields of
the public numbers' ledgers (`numsF`, OnBytes/Tie/Pv/Lookup/Forest/FoV.lean); each such field is the
first slot plus a clamped place of the library's ledger of mask entries; and the library has each
such place below the number of mask entries (`Fo.Slots.pEndC_lt`, `pBitC_lt`, `pTabC_lt`,
`pTieC_lt`, Ends/FoSlotNums.lean). What it is for: a caller whose mask row goes on behind the
lookup's entries (with pads, or with other sub-protocols' entries) may take its own row as ν's
masks. General in the ring and the shape; free of the honest side's frame. The proofs on forms
follow the library's `onMasks_…` (Forest/FoPlaneAt.lean), with the bound carried along.

  1  `OnLt`, `LedLt`, `ledF_lt`, `valS_congr`, `onLt_…`   a sparse form on mask entries below a
     bound; its value at two readings that agree there.
  2  `planes_congr`   **the sentence on the planes at a second reading.**

Not shown here. THAT THE SENTENCE HOLDS OF ANY READING: P is a hypothesis. hm, hc: the two readings
agree at every cell and at every mask entry below the sum, THOSE BELOW THE LOOKUP's FIRST SLOT AMONG
THEM: hypotheses; that the sentence reads none below the first slot is not shown. Nothing is said of
the lookup's other sentences (its rows: nowhere; its keys, which is its join:
Johnson/Road/K4/W/KeysCongr.lean). Nothing is said of the places `.key` and `.zero`: the sentence on
the planes does not read them. No example is written here; tests with code at one small synthetic
lookup: Johnson/Road/K4/W/PlanesCongrTest.lean. Nothing on soundness, on completeness or on any
other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, none whose name begins Cb.Bridge, and
none whose name holds RecCompile. It imports nothing of the honest side
(Johnson/Desc/ProofFile/Honest/).
-/
import Johnson.Top.H.K3RowOut
import OnBytes.Tie.Pv.Lookup.Ends.FoSlotNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.W
open TwNums TwNums.Sizes
open TwV (Led Nums Trace Rounds hide hideGo scale lineForm incTop incT0 formT dgE)
open _root_.Fo (Pl valS claimLeaves claimBits colsK ledF forN endsOf)
open Cb.Fo.Pin (pinColK)
open VerifiableInference.OnPublicFiles (K3Planes)

/-! ## 1 Sparse forms on mask entries below a bound -/

section
variable {K : Type} [CommRing K] {n : ℕ}

/-- The sparse form names mask entries below n alone. -/
def OnLt (n : ℕ) (cf : List (Pl × K)) : Prop := ∀ pc ∈ cf, ∃ j, pc.1 = Pl.mask j ∧ j < n

/-- All places of a sumcheck's ledger are mask entries below n. -/
structure LedLt (n : ℕ) (L : Led Pl) : Prop where
  pw : ∀ r t, ∃ j, L.pw r t = Pl.mask j ∧ j < n
  c0 : ∃ j, L.c0 = Pl.mask j ∧ j < n
  sh : ∀ a, ∃ j, L.sh a = Pl.mask j ∧ j < n

/-- CONDITIONAL: on hp. -/
theorem ledF_lt (jLK N : ℕ) (pl : Ent → ℕ) (hp : ∀ e, pl e < N) : LedLt (jLK + N) (ledF jLK pl) :=
  ⟨fun _ _ => ⟨_, rfl, Nat.add_lt_add_left (hp _) _⟩, ⟨_, rfl, Nat.add_lt_add_left (hp _) _⟩,
    fun _ => ⟨_, rfl, Nat.add_lt_add_left (hp _) _⟩⟩

/-- CONDITIONAL: on h and e. **The value of such a form at two readings that agree below n.** -/
theorem valS_congr {cf : List (Pl × K)} (h : OnLt n cf) {μ μ' : Pl → K}
    (e : ∀ j, j < n → μ (.mask j) = μ' (.mask j)) : valS cf μ = valS cf μ' := by
  unfold valS
  refine congrArg List.sum (List.map_congr_left fun pc hpc => ?_)
  obtain ⟨j, hj, hl⟩ := h pc hpc
  rw [hj, e j hl]

omit [CommRing K] in
theorem onLt_append {a b : List (Pl × K)} (ha : OnLt n a) (hb : OnLt n b) : OnLt n (a ++ b) :=
  fun pc h => (List.mem_append.mp h).elim (ha pc) (hb pc)

theorem onLt_scale {a : List (Pl × K)} (u : K) (ha : OnLt n a) : OnLt n (scale u a) := by
  intro pc h
  unfold scale at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact ha q hq

theorem onLt_hideGo (pw : ℕ → ℕ → Pl) (hp : ∀ r t, ∃ j, pw r t = Pl.mask j ∧ j < n) :
    ∀ (dg : List ℕ) (xs : List K) (r : ℕ), OnLt n (hideGo pw r dg xs)
  | [], _, _ => by
    intro pc h
    simp [hideGo] at h
  | _ :: _, [], _ => by
    intro pc h
    simp [hideGo] at h
  | d :: dg, x :: xs, r => by
    show OnLt n (((List.range d).map fun t => (pw r t, x ^ (t + 1))) ++ hideGo pw (r + 1) dg xs)
    refine onLt_append (fun pc h => ?_) (onLt_hideGo pw hp dg xs (r + 1))
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact hp r t

theorem onLt_hide (L : Led Pl) (hp : ∀ r t, ∃ j, L.pw r t = Pl.mask j ∧ j < n)
    (hc : ∃ j, L.c0 = Pl.mask j ∧ j < n) (dg : List ℕ) (xs : List K) : OnLt n (hide L dg xs) := by
  unfold hide
  refine onLt_append (onLt_hideGo _ hp dg xs 0) fun pc h => ?_
  rw [List.mem_singleton.mp h]
  exact hc

theorem onLt_incT0 (N : Nums Pl K) (hT : ∀ l, LedLt n (N.ledTie l)) (t : Trace K) :
    OnLt n (incT0 N t) := by
  intro pc hpc
  unfold incT0 at hpc
  obtain ⟨th, _, h2⟩ := List.mem_flatMap.mp hpc
  refine onLt_scale _ (fun q hq => ?_) pc h2
  unfold formT at hq
  split_ifs at hq
  · rw [List.mem_singleton.mp hq]
    exact (hT _).sh _
  · rw [List.mem_singleton.mp hq]
    exact (hT _).sh _
  · exact absurd hq List.not_mem_nil

theorem onLt_incTop (led : ℕ → Led Pl) (hl : ∀ l, LedLt n (led l)) {inc0 : List (Pl × K)}
    (h0 : OnLt n inc0) : ∀ L : List (TwV.Sc K × K), OnLt n (incTop led inc0 L)
  | [] => h0
  | s :: rest => by
    intro pc hpc
    have q : pc ∈ lineForm (led rest.length) s.1 s.2 := hpc
    unfold lineForm at q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at q
    rcases q with rfl | rfl
    · exact (hl _).sh 0
    · exact (hl _).sh 1

/-! ## 2 The sentence on the planes -/

/-- CONDITIONAL: on hm, hc and P. **THE SENTENCE ON THE PLANES AT A SECOND READING** that agrees
with the first at every cell and at every mask entry below the first slot plus the lookup's number
of mask entries. -/
theorem planes_congr (h : FoNums.Sh) (lm first : ℕ) {ν ν' : Pl → K}
    (hm : ∀ j, j < first + FoNums.nMasks h → ν (.mask j) = ν' (.mask j))
    (hc : ∀ r c, ν (.cell r c) = ν' (.cell r c)) (rs : Rounds K)
    (P : K3Planes h lm first ν rs) : K3Planes h lm first ν' rs := by
  have eC : ∀ z, colsK h lm z ν = colsK h lm z ν' := fun z => funext fun col => by
    unfold colsK
    exact Finset.sum_congr rfl fun row _ => by rw [hc]
  have eP : pinColK lm ν = pinColK lm ν' := funext fun col => by
    unfold pinColK
    exact Finset.sum_congr rfl fun row _ => by rw [hc]
  have lE := ledF_lt first (FoNums.nMasks h) (FoNums.S h).pEndC
    (_root_.Fo.Slots.pEndC_lt (FoNums.S h))
  have lB := ledF_lt first (FoNums.nMasks h) (FoNums.S h).pBitC
    (_root_.Fo.Slots.pBitC_lt (FoNums.S h))
  have L1 : valS (hide (forN h lm first rs).ledE (dgE (forN h lm first rs))
      (endsOf h lm first rs).lvXs) ν =
      valS (hide (forN h lm first rs).ledE (dgE (forN h lm first rs))
        (endsOf h lm first rs).lvXs) ν' :=
    valS_congr (onLt_hide _ lE.pw lE.c0 _ _) hm
  have L2 : valS (endsOf h lm first rs).lvInc ν = valS (endsOf h lm first rs).lvInc ν' :=
    valS_congr (onLt_incTop _
      (fun l => ledF_lt first (FoNums.nMasks h) _ (_root_.Fo.Slots.pTabC_lt (FoNums.S h) l))
      (onLt_incT0 _
        (fun l => ledF_lt first (FoNums.nMasks h) _ (_root_.Fo.Slots.pTieC_lt (FoNums.S h) l)) _)
      _) hm
  have L3 : ν ((forN h lm first rs).ledB.sh 0) = ν' ((forN h lm first rs).ledB.sh 0) := by
    obtain ⟨j, hj, hl⟩ := lB.sh 0
    have hj' : (forN h lm first rs).ledB.sh 0 = Pl.mask j := hj
    rw [hj', hm j hl]
  obtain ⟨p1, p2, p3⟩ := P
  refine ⟨?_, ?_, ?_⟩
  · rw [← eC]
    unfold claimLeaves at p1 ⊢
    rw [← L1, ← L2]
    exact p1
  · rw [← eC]
    unfold claimBits at p2 ⊢
    rw [← L3]
    exact p2
  · rw [← eP]
    exact p3

end

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.ledF_lt
#print axioms OnBytes.Road.K4.W.valS_congr
#print axioms OnBytes.Road.K4.W.onLt_append
#print axioms OnBytes.Road.K4.W.onLt_scale
#print axioms OnBytes.Road.K4.W.onLt_hideGo
#print axioms OnBytes.Road.K4.W.onLt_hide
#print axioms OnBytes.Road.K4.W.onLt_incT0
#print axioms OnBytes.Road.K4.W.onLt_incTop
#print axioms OnBytes.Road.K4.W.planes_congr
