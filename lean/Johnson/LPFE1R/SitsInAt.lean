-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/SitsInAt.lean: K10Heavy's FIELD hCfX's LAST PREMISE (P5J/K10VCfAt.lean:
k10_hCfX_at h l lo seat hM): hM : SitsIn h.𝔇 (At.N Zp cF) (oAt k) lo seat
(Link/Law/FrontAtK10.lean), AT THE CLOSED CONSTANT, AT K10's PLACE OF A LINK l WITH 1 ≤ l < 25 AT
THE WRITTEN LIST, AND OF LINK 0 AT THE FIVE-LIST. Statements and proofs: a joining of what lies.

  openBy_at        what the closed test k10OpenBy (P5J/K10Open.lean) gives at one place of
                   the kind K10: general in the test
  pins_open_full   BY THE KERNEL, on the written lists: in front of every place of the kind K10 the
                   three pins of the place's own link are open · pins_open_no: a control: with a
                   fourth pin asked the test says no (so: not at every such place are four open)
  group_in_sampled a tenant of link l's group is among the sampled tenants whose pin is open, where
                   the three pins are open: general in the numbers
  allMain_full     BY THE KERNEL: at the links 1 … 24 every entry of the written list has a main row
  sitsIn_at        SitsIn at the written list, 1 ≤ l < 25: first half:
                   plan_seven_at's hHit · second: grp_full,
                   group_at_laid and the two above
  sitsIn_five      SitsIn at link 0's five-list (plan_seven_five · grp_five · five_allMain)

Limits. The head, "in scope" and rowsRead Z are premises, as in the theorems called. The full size
alone. At link 0's six-list nothing is said (its fourth entry has no main row). No soundness
statement.




-/
import Johnson.LPFE1R.PlanSevenFive
import Johnson.P5J.K10Open
import Johnson.Desc.First.Link.Law.FrontAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker Johnson.G
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers start openSets sampledIn)
open VerifiableInference.Desc.First.Close
open P5J (oAt k10OpenBy fullLinks)

/-- What the closed test gives at one place of the kind K10. -/
theorem openBy_at {ok : Place → List Item → Bool} (h : k10OpenBy ok = true) (i : ℕ) (a : Place)
    (ha : P5J.At.ps[i]? = some a) (hk : a.kind = KindName.K10) : ok a (oAt i) = true := by
  have hi : i < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have hl : i < (openSets fullLinks P5J.At.ps (start fullLinks)).length := by
    rw [P5J.openSets_length]
    omega
  have hm : (a, oAt i) ∈ P5J.At.ps.zip (openSets fullLinks P5J.At.ps (start fullLinks)) := by
    refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
    rw [List.getElem?_zip_eq_some]
    refine ⟨ha, ?_⟩
    unfold oAt
    rw [List.getElem?_eq_getElem hl]
    rfl
  have h1 := List.all_eq_true.1 h _ hm
  simpa [hk] using h1

/-- The three pins of the place's own link are open. -/
def pinsB (n : ℕ) (a : Place) (O : List Item) : Bool :=
  (List.range n).all fun t => O.contains (Item.pin (a.link.getD 0) t)

set_option maxRecDepth 1000000 in
theorem pins_open_full : k10OpenBy (pinsB 3) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with a fourth pin asked the test says no: not at every place of the kind K10 are four
pins open. (It does not say "at none".) -/
theorem pins_open_no : k10OpenBy (pinsB 4) = false := by decide +kernel

/-- A tenant of the group is among the sampled tenants whose pin is open. -/
theorem group_in_sampled (N : Numbers) (O : List Item) (l : ℕ)
    (hp : ∀ t, t < 3 → Item.pin l t ∈ O) {s : ℕ × ℕ} (hs : s ∈ N.group l) :
    s ∈ sampledIn N O := by
  unfold Numbers.group at hs
  simp only [List.mem_append] at hs
  unfold sampledIn
  rcases hs with (hs | hs) | hs
  · exact List.mem_flatMap.2 ⟨_, hp 0 (by omega), hs⟩
  · exact List.mem_flatMap.2 ⟨_, hp 1 (by omega), hs⟩
  · exact List.mem_flatMap.2 ⟨_, hp 2 (by omega), hs⟩

set_option maxRecDepth 1000000 in
/-- At the links 1 … 24 every entry of the written list has a main row. -/
theorem allMain_full : ((List.range 25).all fun l => l == 0 ||
    (linksFullLit.getD l []).all fun x => x.1.mainRows != 0) = true := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The three pins at K10's place. -/
theorem pins_at_k10 {k : ℕ} {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∀ t, t < 3 → Item.pin (p.link.getD 0) t ∈ oAt k := fun t ht => by
  have h := openBy_at pins_open_full k p hp hK
  have h1 := List.all_eq_true.1 h t (List.mem_range.2 ht)
  simpa using h1

/-- **SitsIn at the written list, 1 ≤ l < 25.** -/
theorem sitsIn_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hrr : P5J.rowsRead Z) {k : ℕ}
    {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (h1 : 1 ≤ p.link.getD 0) (hl : p.link.getD 0 < 25) :
    SitsIn h.𝔇 (P5J.At.N Zp cF) (oAt k) (linksFullLit.getD (p.link.getD 0) [])
      (seatK10 (linksFullLit.getD (p.link.getD 0) []) (P5J.At.pseats Zp) (p.link.getD 0)) := by
  intro i
  have hmain : memMain (linksFullLit.getD (p.link.getD 0) []) i := by
    have a := List.all_eq_true.1 allMain_full _ (List.mem_range.2 hl)
    have h0 : (p.link.getD 0 == 0) = false := by simp; omega
    rw [h0, Bool.false_or] at a
    have b := List.all_eq_true.1 a _ (List.get_mem _ i)
    simpa using b
  have S7 := plan_seven_at h.scope h.laid hrr hp hK hl
  refine ⟨S7.hHit i hmain, ?_⟩
  have e1 : P5J.At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have hg : seatK10 (linksFullLit.getD (p.link.getD 0) []) (P5J.At.pseats Zp) (p.link.getD 0) i ∈
      (P5J.At.N Zp cF).group (p.link.getD 0) := by
    rw [group_at_laid (cF := cF) h.scope h.laid (p.link.getD 0), e1]
    exact grp_full _ (by omega) i hmain
  exact group_in_sampled _ _ _ (pins_at_k10 hp hK) hg

/-- **SitsIn at link 0's five-list.** -/
theorem sitsIn_five (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hrr : P5J.rowsRead Z) {k : ℕ}
    {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (h0 : p.link.getD 0 = 0) :
    SitsIn h.𝔇 (P5J.At.N Zp cF) (oAt k) loFive (seatFiveAt (P5J.At.pseats Zp)) := by
  intro i
  have S7 := plan_seven_five h.scope h.laid hrr hp hK h0
  refine ⟨S7.hHit i (five_allMain i), ?_⟩
  have hg : seatFiveAt (P5J.At.pseats Zp) i ∈ (P5J.At.N Zp cF).group 0 := by
    rw [group_at_laid (cF := cF) h.scope h.laid 0, seatFive_at_laid h.scope h.laid]
    exact grp_five i (five_allMain i)
  exact group_in_sampled _ _ _ (h0 ▸ pins_at_k10 hp hK) hg

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.openBy_at
#print axioms VerifiableInference.Desc.LinkJoin.pins_open_full
#print axioms VerifiableInference.Desc.LinkJoin.pins_open_no
#print axioms VerifiableInference.Desc.LinkJoin.group_in_sampled
#print axioms VerifiableInference.Desc.LinkJoin.allMain_full
#print axioms VerifiableInference.Desc.LinkJoin.pins_at_k10
#print axioms VerifiableInference.Desc.LinkJoin.sitsIn_at
#print axioms VerifiableInference.Desc.LinkJoin.sitsIn_five
