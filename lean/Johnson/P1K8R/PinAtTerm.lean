-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/PinAtTerm.lean: the public half of the pin at the honest online prover, and the lot of
the smallness test in the form that Johnson/P1K8R/PinOfLots.lean asks.

  smallForm_thru   the smallness test's lot, read through, has that form
  k8_piece         the piece of the segment's place, by the segment's number
  matsOwn_fits     the seat's test on public data holds at the lists that the filling lays
  pinPublic_own    the pin's clauses on public data, at these lists

Limits. Public data alone, and one lot's form. Nothing on a run or on any other lot.
-/
import Johnson.P1K8R.PinOfLots
import Johnson.FrontRoad.PinPublic
import Johnson.FrontRoad.CellsAreTrace
import Johnson.FrontRoad.ParOwnChecks
import Johnson.FrontRoad.ProverThrough
import Johnson.HonestTrace.U3Fit.MatsAtHead
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Desc.ProofFile.Honest.Thru

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace P1K8
open ProofFile.Honest
open ProofFile.Honest.K8 (smallFits smallHalf smallLot smallStop windowShare small_parts)
open ProofFile.Honest.K9 (quietStop)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par round)
open OnBytes.FrontRoad
open AtPublicFiles.AtFiles (descZ)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (PublicFiles InScope readFiles)
open P5J

section
variable {W₀ W₀' Rc Rc' Xi : Type}

/-- An entry of an array's list with its number is the array's entry there. -/
theorem zipIdx_get {α : Type} {a : Array α} {t : α × ℕ} (h : t ∈ a.toList.zipIdx) :
    a[t.2]? = some t.1 := by
  have h' := List.mem_zipIdx_iff_getElem?.1 h
  simpa using h'

/-- And conversely. -/
theorem get_zipIdx {α : Type} {a : Array α} {l : ℕ} {x : α} (h : a[l]? = some x) :
    (x, l) ∈ a.toList.zipIdx := by
  refine List.mem_zipIdx_iff_getElem?.2 ?_
  simpa using h

/-- **The smallness test's lot, read through, has the form that the pin's lemma asks.** -/
theorem smallForm_thru (g : W₀' → W₀) (rd : Rc' → Rc) {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (M : ProofFile.Pub → ProofFile.Ground → OnBytes.Model.Stages.LinkH → ℕ → List (ℕ × String × ℕ))
    (mats : ℕ → List (ℕ × String × ℕ)) (hM : ∀ X l, M Z G X l = mats l)
    (hfit : ∀ l Xl, G.built[l]? = some Xl → smallFits (ProofFile.k8Par Z G Xl l, mats l) = true) :
    SmallForm (HLot.thru (Local.thru g rd) (Local.thru g rd)
      (smallLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (Tr := Cells) (X := Unit) id M)) Z G mats id := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    have hb := zipIdx_get ht
    refine ⟨t.2, t.1, hb, rfl, ?_⟩
    show (smallHalf id (ProofFile.k8Par Z G t.1 t.2, M Z G t.1 t.2)).parts.map (Part.thru _ _) = _
    rw [hM, small_parts W₀ Rc Xi Cells Unit id _ (hfit _ _ hb), List.map_cons, List.map_nil]
    congr 1
  · intro l Xl h
    exact ⟨_, List.mem_map_of_mem (List.mem_map_of_mem (get_zipIdx h)), rfl⟩

end

section
variable {Z : PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD}
  {r : LPFD.Full.RunPF}

/-- The piece of a segment's place. -/
theorem k8_piece (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} {Xl : OnBytes.Model.Stages.LinkH}
    (hX : G.built[l]? = some Xl) :
    (ProofFile.k8Par Zp G Xl l).piece = if l = 24 then 6 else 5 := by
  obtain ⟨alt, l₄, e₄, k₄, -⟩ := IM.ground_named scope hr L.pub hG
  have hs : G.built.size = 25 := (IM.ground_gets scope hr L.pub hG).1
  have hl : l < 25 := hs ▸ (Array.getElem?_eq_some_iff.1 hX).1
  show (if (Xl.kind == 2) = true then 6 else 5) = _
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l₄ = Xl := Option.some.inj (e₄.symm.trans hX)
    simp [k₄]
  · obtain ⟨a, b, ea, ka, -, -, eb, kb, -, -⟩ := alt (l / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · have e : 2 * (l / 2) = l := by omega
      rw [e] at ea
      obtain rfl : a = Xl := Option.some.inj (ea.symm.trans hX)
      simp [ka, h24]
    · have e : 2 * (l / 2) + 1 = l := by omega
      rw [e] at eb
      obtain rfl : b = Xl := Option.some.inj (eb.symm.trans hX)
      simp [kb, h24]

/-- **The seat's test holds at the lists that the filling lays.** -/
theorem matsOwn_fits (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} {Xl : OnBytes.Model.Stages.LinkH}
    (hX : G.built[l]? = some Xl) :
    smallFits (ProofFile.k8Par Zp G Xl l, K3.matsOwn G.W l) = true := by
  have hs : G.built.size = 25 := (IM.ground_gets scope hr L.pub hG).1
  have hl : l < 25 := hs ▸ (Array.getElem?_eq_some_iff.1 hX).1
  have hW : G.W = Zp.p.X := ProofFile.Law.blankBy_W hG
  have hP := OnBytes.HonestTrace.planMarks_in_scope scope hr (publicOf_laid Z Zp Np cF L)
  rw [fits_iff_length, tl_is_plan Z Zp Np cF scope hr L hG hl hX, hW,
    ← OnBytes.HonestTrace.U3.Fit.tlOf_planMats hP hl]
  simp [K3.matsOwn]

/-- **The pin's clauses on public data**, at the lists that the filling lays. -/
theorem pinPublic_own (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    PinPublicAt (parOwn Zp fun l => K3.matsOwn G.W l) (descZ Zp Np cF).first.blocksInOrder.dropLast := by
  intro b hb
  cases hp : parOwn Zp (fun l => K3.matsOwn G.W l) b.place with
  | none =>
    intro hk
    obtain ⟨P, hP, -⟩ := pin_first_public Z Zp Np cF scope hr L _ b hb hk
    rw [hp] at hP
    cases hP
  | some P =>
    obtain ⟨hk, l, G₀, Xl, -, hG₀, hX, rfl⟩ := parOwn_some Zp _ b.place P hp
    obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
    obtain ⟨P', hP', hr'⟩ := pin_first_public Z Zp Np cF scope hr L
      (fun l => K3.matsOwn G₀.W l) b hb hk
    rw [hp] at hP'
    obtain rfl := Option.some.inj hP'
    exact ⟨matsOwn_fits scope hr L hG hX, hr'⟩

/-- A member of the kind stands at the segment's place. -/
theorem place_at_member (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    ∀ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, ∀ l Xl, b.place.link = some l →
      G.built[l]? = some Xl → b.place.kind = KindName.K8 →
      b.place = ⟨1, some l, (ProofFile.k8Par Zp G Xl l).piece, KindName.K8⟩ := by
  intro b hb l Xl hl hX hk
  have hm : b.place ∈ ((descZ Zp Np cF).first.blocksInOrder.dropLast.map (·.place)).filter
      (fun a => a.kind == KindName.K8) :=
    List.mem_filter.2 ⟨List.mem_map_of_mem hb, by simpa using hk⟩
  rw [(k8_places_front Z Zp Np cF scope hr L).1] at hm
  obtain ⟨l', -, e⟩ := List.mem_map.1 hm
  have hll : l' = l := by
    have h := congrArg Place.link e
    rw [hl] at h
    exact Option.some.inj h
  subst hll
  rw [k8_piece scope hr L hG hX, ← e]
  rfl

end

end P1K8

#print axioms P1K8.smallForm_thru
#print axioms P1K8.k8_piece
#print axioms P1K8.matsOwn_fits
#print axioms P1K8.pinPublic_own
#print axioms P1K8.place_at_member
