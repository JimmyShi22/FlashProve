-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/HearingAtBlankRun.lean: the library's law hear_returns
(Johnson/Desc/First/K4/Returns/Whole.lean), through hear_returns_of_PB
(Johnson/Desc/First/K4/Returns/Pub/JoinPoints.lean), called at the blank run: the blank lookup's
record, the blank ledger, the blank tape of the table of the layers' own rounds, and as many tokens
0 as the layout counts. That is the run of ownOf (Johnson/Desc/First/K4/Returns/AtShape.lean).
General in the plan and the shapes; nothing is evaluated.

Why. The step of the layers' own rounds on shapes runs the hearing at blanks. This file meets each
premise of the library's law there, so that tests on the plan and on the shape before give that
the step returns.

  blankTape_hasTableShape, blankTape_coinNotZero   the blank tape has the table's shape, and a
                          round that draws one element draws no zero.
  lastOfZeros_isZeros     the last k coordinates of a point of zeros are k zeros.
  blankLookup_mergedPointPasses   the test on the merged point passes at the blank lookup's record.
  zeroTokens_fit          as many tokens 0 as the layout counts fit.
  **hearing_returnsAtBlankRun**   under the tests k4PlanB, roomB and lookB, the host's count of
                          the padding keys (hL) and 0 < V: the hearing returns at the blank run and
                          leaves what HearLeft says, and the ledger's shape after is hearLedU.
  **ownRecordOnShapes_returns**   so ownOf returns.

Limits. One way, from the tests. No test is shown to accept here. What any of this costs Lean's
kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.AtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt TableAsk)
open OnBytes.Desc.First.K4.RtPub (hearPB zkFits zkSize tokensFit tablesAt hear_returns_of_PB)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (rowBlank treeBlank ledBlank)

/-! ## What the blanks are made of -/

/-- The blank tape of a table has the table's shape. -/
theorem blankTape_hasTableShape : ∀ ds : List Rd, TapeOf ds (blankTape ds)
  | [] => trivial
  | d :: ds =>
    show At d (blankRound d) ∧ TapeOf ds (blankTape ds) from
      ⟨⟨rfl, rfl, rfl, List.length_replicate, List.length_replicate⟩, blankTape_hasTableShape ds⟩

/-- A round of the blank tape that draws one element draws no zero. -/
theorem blankTape_coinNotZero (ds : List Rd) (t₁ t₂ : Tape) (nm : Option String) (a b : Nat) (s0 :
    List E)
    (eps : E) (e : blankTape ds = t₁ ++ ⟨nm, a, b, s0, [eps]⟩ :: t₂) : isZeroE eps = false := by
  have hm : (⟨nm, a, b, s0, [eps]⟩ : FlatRound) ∈ blankTape ds := by
    rw [e]
    simp
  obtain ⟨d, -, hd⟩ := List.mem_map.1 hm
  have h2 : List.replicate d.drawn oneE = [eps] := congrArg FlatRound.drawn hd
  have h3 : eps ∈ List.replicate d.drawn oneE := by
    rw [h2]
    simp
  rw [(List.mem_replicate.1 h3).2]
  decide

/-- The last k coordinates of a point of zeros are k zeros. -/
theorem lastOfZeros_isZeros {n k : Nat} {a : Array E}
    (h : (lastOf (Array.replicate n zeroE) k).toOption = some a) : a = Array.replicate k zeroE := by
  have hs := lastOf_size h
  unfold lastOf cutLast at h
  by_cases hk : k > (Array.replicate n zeroE).size
  · rw [if_pos hk] at h
    cases h
  · rw [if_neg hk] at h
    obtain rfl : (Array.replicate n zeroE).extract ((Array.replicate n zeroE).size - k)
        (Array.replicate n zeroE).size = a := Option.some.inj h
    apply Array.ext
    · rw [hs, Array.size_replicate]
    · intro i h1 h2
      simp

/-- A list's members one by one, in Option: each member of what comes back comes of a member. -/
theorem optionMapM_fromMember {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by
    obtain rfl : [] = r := Option.some.inj h
    cases hy
  | a :: l, r, h, y, hy => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | none =>
      rw [hb] at h
      cases h
    | some b =>
      cases hbs : l.mapM f with
      | none =>
        rw [hb, hbs] at h
        cases h
      | some bs =>
        rw [hb, hbs] at h
        obtain rfl : b :: bs = r := Option.some.inj h
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact ⟨a, List.mem_cons_self, hb⟩
        · obtain ⟨x, hx, e⟩ := optionMapM_fromMember f l bs hbs y hy'
          exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- The test on the merged point passes at the blank lookup's record. -/
theorem blankLookup_mergedPointPasses (h : HeardAll) (la : Nat) {Z : Array E}
    {ends : Array (Array E)}
    (hz : (lastOf h.blank.zx la).toOption = some Z)
    (he : (h.blank.zk.mapM fun zk => (lastOf zk la).toOption) = some ends) :
    ends.all (· == Z) = true := by
  have eZ : Z = Array.replicate la zeroE := lastOfZeros_isZeros (n := h.zx) hz
  rw [Array.mapM_eq_mapM_toList] at he
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 he
  rw [← Array.all_toList, List.all_eq_true]
  intro y hy
  obtain ⟨x, hx, e⟩ := optionMapM_fromMember _ _ _ hl y hy
  have hx' : x ∈ h.zk.map fun n => Array.replicate n zeroE := by simpa [HeardAll.blank] using hx
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx'
  rw [lastOfZeros_isZeros e, eZ]
  exact beq_self_eq_true _

/-- As many tokens 0 as the layout counts fit, where the vocabulary is not empty. -/
theorem zeroTokens_fit (P : Pub) (g : Nat) (hV : 0 < P.V) :
    tokensFit { P with tokv := Array.replicate P.y.T 0 } g = true := by
  have h1 : ((Array.replicate P.y.T 0).all fun t => decide (t < P.V)) = true := by
    rw [← Array.all_toList, Array.toList_replicate, List.all_eq_true]
    intro t ht
    rw [(List.mem_replicate.1 ht).2]
    exact decide_eq_true hV
  show (g != 0 || ((Array.replicate P.y.T 0).size == P.y.T &&
    (Array.replicate P.y.T 0).all fun t => decide (t < P.V))) = true
  rw [h1, Array.size_replicate]
  simp

/-! ## The call -/

/-- **The library's law at the blank run.** The test on the plan (k4PlanB) and the host's count (hL)
meet covers, PlanNums, HearPub's pure readings and the join. The guard on the lookup's record's
shape (lookB) meets shapeFits, K3Hands, zkFits, the planes' matrix and four equations for the join.
roomB on the ledger's shape meets Room. What the blanks are made of meets TapeOf, the merged point,
the coin and the tokens (the tokens also need 0 < V, a number of the plan). -/
theorem hearing_returnsAtBlankRun (p : Par) (k : Nat) (h : HeardAll) (L : LedSh) (hP : k4PlanB p =
    true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub)
    (hR : roomB L (k4Takes p.P p.hp p.g + k) = true) (hK : lookB p.P h L = true)
    (hV : 0 < p.P.V) :
    ∃ iU3 tab o G,
      hearFl { p.P with tokv := Array.replicate p.P.y.T 0 } p.hp p.g h.blank (ledBlank L)
        (blankTape (rounds p.P p.hp p.g)) = some (o, G, []) ∧
      Room G k ∧ Below (ledBlank L) G ∧ G.next = L.next + k4Takes p.P p.hp p.g ∧
      HearLeft { p.P with tokv := Array.replicate p.P.y.T 0 } p.hp p.g h.blank iU3 tab (ledBlank L)
        G o ∧
      ledSh G = hearLedU p.P p.hp p.g L := by
  have hR' : Room (ledBlank L) (k4Takes p.P p.hp p.g + k) :=
    room_of_B (by rw [ledSh_blank]; exact hR)
  have hK' : LookFacts p.P h.blank (ledBlank L) :=
    look_of_B (by rw [heardAll_blank, ledSh_blank]; exact hK)
  obtain ⟨Z, ztF, ends, hH⟩ := hK'.hands
  unfold k4PlanB at hP
  simp only [Bool.and_eq_true] at hP
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
  obtain ⟨iU3, tab, laid, n, hu, ht, hret⟩ :=
    hear_returns_of_PB (P := { p.P with tokv := Array.replicate p.P.y.T 0 }) (hp := p.hp)
      (g := p.g) p3 (zeroTokens_fit p.P p.g hV)
  have ht' : RtPub.tablesAt p.P p.g = some (tab, laid, n) := ht
  rw [hu, ht'] at p4
  have hJ : joinB p.P p.hp p.g iU3 tab = true := p4
  have hN := planNums_of_B p2
  obtain ⟨o, G, e, a1, a2, a3, a4⟩ := hret h.blank (F := ledBlank L) (k := k)
    (t := blankTape (rounds p.P p.hp p.g)) (Z := Z) (ztF := ztF) (ends := ends) p1 hK'.fits hR'
    (blankTape_hasTableShape _)
    ⟨hN.ns, hN.np, hN.no, hN.muV, hN.endT, hN.muH9, hN.muH29, hN.muH, hN.muH2, hN.ncl⟩
    ⟨hH.depth, hH.z, hH.ends, hH.zt, hH.ztSize, hH.cEnd⟩ hK'.zk hK'.planes
    (join_pay (P := { p.P with tokv := Array.replicate p.P.y.T 0 }) hL hJ hK'.calls hK'.e
      hK'.noPub hK'.pub)
    (blankLookup_mergedPointPasses h p.P.y.h.la hH.z hH.ends)
    (fun t₁ s0 eps t₂ _ e => blankTape_coinNotZero _ t₁ t₂ _ _ _ s0 eps e)
  have hl0 : ledSh G = hearLedU { p.P with tokv := Array.replicate p.P.y.T 0 } p.hp p.g
      (ledSh (ledBlank L)) :=
    hear_ledSh (P := { p.P with tokv := Array.replicate p.P.y.T 0 }) e hR' a1 a2 a3 a4
  refine ⟨iU3, tab, o, G, e, a1, a2, a3, a4, ?_⟩
  rw [hl0, ledSh_blank]
  exact hearLedU_tokv p.P _ p.hp p.g _

/-- **So ownOf returns**, and the ledger's shape after is hearLedU. -/
theorem ownRecordOnShapes_returns (p : Par) (k : Nat) (h : HeardAll) (L : LedSh) (hP : k4PlanB p =
    true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub)
    (hR : roomB L (k4Takes p.P p.hp p.g + k) = true) (hK : lookB p.P h L = true)
    (hV : 0 < p.P.V) :
    ∃ ow fs, ownOf p h L = some (ow, fs, hearLedU p.P p.hp p.g L) := by
  obtain ⟨iU3, tab, o, G, e, -, -, -, -, hl⟩ := hearing_returnsAtBlankRun p k h L hP hL hR hK hV
  refine ⟨ownSh o, o.funs.toList.map funSh, ?_⟩
  unfold ownOf
  rw [e, ← hl]
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.blankTape_hasTableShape
#print axioms OnBytes.Desc.First.K4.Rt.blankTape_coinNotZero
#print axioms OnBytes.Desc.First.K4.Rt.lastOfZeros_isZeros
#print axioms OnBytes.Desc.First.K4.Rt.optionMapM_fromMember
#print axioms OnBytes.Desc.First.K4.Rt.blankLookup_mergedPointPasses
#print axioms OnBytes.Desc.First.K4.Rt.zeroTokens_fit
#print axioms OnBytes.Desc.First.K4.Rt.hearing_returnsAtBlankRun
#print axioms OnBytes.Desc.First.K4.Rt.ownRecordOnShapes_returns
