-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PossWritten.lean: code switching: THE POSITIONS THAT THE CODE SWITCH INTO
GROUP m SAMPLES ARE A CLOSED NUMBER, IN SCOPE, WHERE THE VALUE FOR THE PROOF FILE IS LAID: possAt
cF.blocksInOrder 25 = posW, AS FUNCTIONS (possAt: Johnson/Desc/First/NumbersAtBlocks.lean: what the table of
joints' numbers read for the class «position» of rows). Definitions, closed facts by
Lean's kernel, and theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  posW m            THE CLOSED TERM, with code: 219 at 1 ≤ m ≤ 25, else 0 (no code switch leads into
                    group 0, nor into a group beyond 25)
  locs219B es       a test on a list of entries: every entry named "LOC" samples 219 positions
  loc_written       it accepts at the full size's first written list of rounds
                    (Johnson.G.dryProofFull.1; 48,293 entries): BY LEAN's KERNEL · loc_can_fail: a
                    negative test
  noSwitch_out      in the written list of places none of the kind K2 stands at segment 0 or beyond
                    25 (the finish counts as 25): by the kernel · noSwitch_can_fail: a negative test
  entries_laid      in scope, where the value is laid, the entries of the first chain's
                    sub-protocols' declared rounds ARE the written list's, at every o: by
                    seat_in_scope · asks_written · writtenOf_entries, off the fields of
                    LaidAt. (Kin: laidPOf_rounds, Johnson/Desc/Laid/ProofFullScope.lean, from
                    proofDataAndDecisionOfPublicFiles at «there is F»; plans_written,
                    Johnson/Goal/Numbers/PlanWrittenPlans.lean, on Z.plans. The right side is
                    LPFK10.entriesW and P5T.esFull.1 by unfolding.)
  pos_of_rounds     a sub-protocol of such a list whose declared rounds are K2.rounds p has
                    p.positions = 219: its round "LOC" is one of the list's
  k2Sits_joined · k2Sits_at   where KeepsJoined | KeepsAt hold
                    (Johnson/P1K2R/SitsDoor.lean), the sub-protocol sits over K2.codeSwitchKind p for some p
  possAt_at         the search in possAt ends at the sub-protocol number swNo g, and gives 219
  possAt_out        at m = 0 and beyond 25 the search finds nothing
  possAt_is         THE THEOREM: possAt cF.blocksInOrder 25 = posW
  possAt_written    the form in which the piece was cut: ∀ m, m ≤ 25 → possAt cF.blocksInOrder 25 m = posW m
  possAt_links      in the spender's own term (P5J.LaidAt.N_is, Johnson/P5T/CoreAtMg.lean):
                    possAt cF.blocksInOrder P5J.At.links.length = posW
THE ROAD GOES BY THE ENTRIES: neither n.positions of the numbers that P1K2.numsAt gives nor
baseCount at the written tables is read; no named test on the list of rounds is asked beside LaidAt.
219 is a numeral in posW; what is written is the list against which loc_written holds it.
CALLED, NOT TYPED: k02_sits_file (SitsDoor.lean: what sits at the 25 numbers) ·
IM.Open.unique · IM.back_numbers · IM.places_nodup · IM.reads_of_scope · K2.possAt_sits
(Tw/K2C/PossAtK2.lean) · links_25 (Johnson/Desc/First/Link/Law/K09Lens.lean) · swNo · swNo_link ·
find_by_place · findW_at · hps_scope: Johnson/P1K2R/DebtsConst.lean.
(seat_in_scope above: PlanWrittenDescScope.lean's.)
IS THERE A MEMBER? InScope VerifierAndGoals.storedPublicFiles = true is a theorem (inScope_full,
Johnson/Goal/Files/ScopeExample.lean). LaidAt AT storedPublicFiles IS SHOWN BY NO THEOREM; by evaluation alone:
an evaluation has protocolDataWellFormed (asDescriptionFiles storedPublicFiles) true, whence proofDataAndDecisionOfPublicFiles returns and
laid_opens gives LaidAt. Johnson/Loose/PVK10/PossAtFull.lean (not in this library)
evaluates the CONCLUSION at ProofFile.onlineDescription's value at storedPublicFiles; of LaidAt's fields it meets
«value» alone. So, by this project's measure: theorems with an example that was only evaluated.
LIMITS. The full size alone. possAt_at and what follows: at the second hash function OnBytes.secondHashFunction
(k02_sits_file · hps_scope · back_numbers stand there). No soundness is claimed. On hiding nothing.

-/
import Johnson.P1K2R.DebtsConst
import Johnson.P5J.LaidOpens
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.First.Link.Law.K09Lens
import Johnson.G.DataEntries
import Johnson.G.DryProofLit
import Johnson.IMR.MemberOfGate
import Johnson.IMR.BackSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S blockPlaces possAt possOf)
open Johnson.G (dryProofFull)
open H2K.JointK (Sits)
open IM (placesW)
open P1K2 (swNo)
open ProofFile (Cl)

/-- **The closed term.** -/
def posW (m : ℕ) : ℕ := if m == 0 || decide (25 < m) then 0 else 219

/-- Every entry named "LOC" samples 219 positions. -/
def locs219B (es : List Fmt.Entry) : Bool := es.all fun e => e.name != "LOC" || e.poss == 219

set_option maxRecDepth 1000000 in
/-- **By the kernel**: at the full size's first written list of rounds. -/
theorem loc_written : locs219B (dryProofFull.1.map (·.1.entry)) = true := by decide +kernel

/-- A negative test: one entry named "LOC" with 218 positions. -/
theorem loc_can_fail : locs219B [{ name := "LOC", poss := 218 }] = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **By the kernel**: no place of the kind K2 at segment 0 or beyond 25. -/
theorem noSwitch_out : placesW.all (fun q => !(q.kind == .K2 &&
    (q.link.getD 25 == 0 || decide (25 < q.link.getD 25)))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the bound at 24 the finish's code switch is caught. -/
theorem noSwitch_can_fail : placesW.all (fun q => !(q.kind == .K2 &&
    (q.link.getD 25 == 0 || decide (24 < q.link.getD 25)))) = false := by decide +kernel

/-- **The entries of the first chain's declared rounds are the written list's.** -/
theorem entries_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl}
    (hW : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    (cF.blocksInOrder.flatMap (·.rounds)).map (·.entry) = dryProofFull.1.map (·.1.entry) :=
  (Johnson.G.OfPlan.writtenOf_entries
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Z hW (LPFD.asks_written L.asks)).1).1.symm

/-- The round "LOC" of a sub-protocol of the list is one of the list's. -/
theorem pos_of_rounds {St Cl' : Type} {bs : List (Block St Cl')} {b : Block St Cl'} (hb : b ∈ bs)
    {p : K2.P2} (hr : b.rounds = K2.rounds p) {es : List Fmt.Entry}
    (hE : (bs.flatMap (·.rounds)).map (·.entry) = es) (hL : locs219B es = true) :
    p.positions = 219 := by
  obtain ⟨d, hd, hn, hp⟩ : ∃ d ∈ K2.rounds p, d.entry.name = "LOC" ∧
      d.entry.poss = p.positions := ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), rfl, rfl⟩
  have hm : d.entry ∈ es := by
    rw [← hE]
    exact List.mem_map_of_mem (List.mem_flatMap.2 ⟨b, hb, by rw [hr]; exact hd⟩)
  have h := List.all_eq_true.1 hL _ hm
  rw [hn, hp] at h
  simpa using h

theorem k2Sits_joined {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S Cl} {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : P1K2.KeepsJoined Z G a nm b f) :
    ∃ p enter leave, Sits b (K2.codeSwitchKind p : Block S Unit) enter leave := by
  obtain ⟨_, n, -, -, h⟩ := h
  rcases h with ⟨_, _, -, -, hs⟩ | ⟨_, -, hs⟩
  · exact ⟨_, _, _, hs.1⟩
  · exact ⟨_, _, _, hs.1⟩

theorem k2Sits_at {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S Cl} (h : P1K2.KeepsAt Z G a nm b) :
    ∃ p enter leave, Sits b (K2.codeSwitchKind p : Block S Unit) enter leave := by
  obtain ⟨_, n, -, -, h⟩ := h
  rcases h with ⟨-, hs⟩ | ⟨_, _, -, -, hs⟩ | ⟨_, -, hs⟩
  · exact ⟨_, _, _, hs.1⟩
  · exact ⟨_, _, _, hs.1⟩
  · exact ⟨_, _, _, hs.1⟩

/-- The search ends at the sub-protocol number swNo g, and gives 219. -/
theorem possAt_at {bs : List (Block S Cl)} (hps : blockPlaces bs = placesW) {g : ℕ} (h1 : 1 ≤ g)
    (h25 : g ≤ 25) {b : Block S Cl} (hbk : bs[swNo g]? = some b) {p : K2.P2}
    {enter : S → Except String S} {leave : S → S → Except String S}
    (hs : Sits b (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hE : (bs.flatMap (·.rounds)).map (·.entry) = dryProofFull.1.map (·.1.entry)) :
    possAt bs 25 g = 219 := by
  rw [K2.possAt_sits (P1K2.find_by_place hps IM.places_nodup hbk (P1K2.findW_at h1 h25)) hs]
  exact pos_of_rounds (List.mem_of_getElem? hbk) hs.rounds hE loc_written

/-- At m = 0 and beyond 25 the search finds nothing. -/
theorem possAt_out {bs : List (Block S Cl)} (hps : blockPlaces bs = placesW) {m : ℕ}
    (hm : m = 0 ∨ 25 < m) : possAt bs 25 m = 0 := by
  have hn : (bs.find? fun b => b.place.kind == .K2 && b.place.link.getD 25 == m) = none := by
    refine List.find?_eq_none.2 fun b hb hc => ?_
    have hq : b.place ∈ placesW := by
      rw [← hps]
      exact List.mem_map_of_mem hb
    have h0 := List.all_eq_true.1 noSwitch_out _ hq
    rw [Bool.not_eq_true'] at h0
    have hc' : (b.place.kind == .K2 && b.place.link.getD 25 == m) = true := hc
    rw [Bool.and_eq_true] at hc'
    have em : b.place.link.getD 25 = m := beq_iff_eq.1 hc'.2
    rw [hc'.1, em, Bool.true_and] at h0
    rcases hm with rfl | hm
    · simp at h0
    · simp [hm] at h0
  unfold possAt
  rw [hn]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl}

/-- **THE POSITIONS THAT THE CODE SWITCHES SAMPLE: THE FUNCTION IS THE CLOSED TERM.** -/
theorem possAt_is (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    possAt cF.blocksInOrder 25 = posW := by
  funext m
  obtain ⟨pp, hR⟩ := IM.reads_of_scope hW
  obtain ⟨Bs, base, O⟩ := L.opened
  have hps := P1K2.hps_scope hW hR O
  have hE := entries_laid hW L
  obtain ⟨Z', Bs', base', c', A', B', O', k1, k2, k3⟩ :=
    P1K2.k02_sits_file hW hR L.value L.planOk
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := O.unique O'
  by_cases ho : m = 0 ∨ 25 < m
  · rw [possAt_out hps ho]
    unfold posW
    rcases ho with rfl | ho
    · rfl
    · rw [if_pos (by simp [ho])]
  · have h1 : 1 ≤ m := by omega
    have hm : m ≤ 25 := by omega
    have e : posW m = 219 := by
      unfold posW
      rw [if_neg (by simp; omega)]
    rw [e]
    rcases Nat.lt_or_ge m 24 with h24 | h24
    · obtain ⟨b, nm, fs, f, hb, -, -, hk⟩ := k1 m h1 h24
      obtain ⟨p, en, lv, hs⟩ := k2Sits_joined hk
      exact possAt_at hps h1 hm (by rw [P1K2.swNo_link (by omega)]; exact hb) hs hE
    · rcases Nat.lt_or_ge m 25 with h25 | h25
      · obtain rfl : m = 24 := by omega
        obtain ⟨b, nm, hb, hk⟩ := k2
        obtain ⟨p, en, lv, hs⟩ := k2Sits_at hk
        exact possAt_at hps h1 hm hb hs hE
      · obtain rfl : m = 25 := by omega
        obtain ⟨b, nm, hb, hk⟩ := k3
        obtain ⟨p, en, lv, hs⟩ := k2Sits_at hk
        exact possAt_at hps h1 hm ((IM.back_numbers hW hR O).1 0 b hb)
          (b := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })
          ⟨hs.rounds, fun q => hs.plan (by
            have q' : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := q
            rw [Bool.and_eq_true] at q'
            exact q'.1), hs.step⟩ hE

/-- The form in which the piece was cut. -/
theorem possAt_written (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ m, m ≤ 25 → possAt cF.blocksInOrder 25 m = posW m := fun m _ => congrFun (possAt_is hW L) m

/-- In the spender's own term. -/
theorem possAt_links (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    possAt cF.blocksInOrder P5J.At.links.length = posW := by
  have e : P5J.At.links.length = 25 := VerifiableInference.Desc.LinkJoin.links_25
  rw [e]
  exact possAt_is hW L

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.loc_written
#print axioms VerifiableInference.Desc.First.K2Caller.loc_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.noSwitch_out
#print axioms VerifiableInference.Desc.First.K2Caller.noSwitch_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.entries_laid
#print axioms VerifiableInference.Desc.First.K2Caller.pos_of_rounds
#print axioms VerifiableInference.Desc.First.K2Caller.k2Sits_joined
#print axioms VerifiableInference.Desc.First.K2Caller.k2Sits_at
#print axioms VerifiableInference.Desc.First.K2Caller.possAt_at
#print axioms VerifiableInference.Desc.First.K2Caller.possAt_out
#print axioms VerifiableInference.Desc.First.K2Caller.possAt_is
#print axioms VerifiableInference.Desc.First.K2Caller.possAt_written
#print axioms VerifiableInference.Desc.First.K2Caller.possAt_links
