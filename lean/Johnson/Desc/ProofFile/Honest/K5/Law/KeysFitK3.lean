-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeysFitK3.lean: CONDITIONAL, under the library's hypothesis on
the public input (`P5J.AtMgA`): AT THE READER `keyOfK3` (Honest/K5/Law/KeyOfK3.lean) THE THIRD TEST
OF THE MAKER OF A PLACE's PUBLIC DATA SAYS YES AT EACH OF THE TWELVE ATTENTION SEGMENTS: each call's
key point has as many coordinates as the call has bits (`Seat5.keysFit`, Honest/K5/KeysFit.lean). So
at this reader the premise hKey of `seatAt_returns_at_head` (Honest/K5/Law/SeatReturns.lean) and of
the laws above it is a theorem.

  `ok_parts`     two clauses out of the library's test on a lookup's numbers (`FoNums.ok`): as many
                 calls as NC; for c below NC the call's number of bits is iota c + dT
  `zk_sizes`     the cut's lengths are the calls' numbers of bits. CONDITIONAL: a point of dT + rK
                 coordinates; these two clauses; iota c at most rK
  `keysFit_K3`   CONDITIONAL: **the test's yes at the blank front**, in hKey's own letters
  `seatAt_returns_K3`   CONDITIONAL: so the maker yields there (`seatAt_returns_at_head`, which has
                 the maker's two other tests under h)

Limits. Lengths alone, on public numbers. h is a hypothesis of every statement that names it.
Nothing here says that the reader's value is what the verifier's state holds. At the library's full
size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3At
import Johnson.Desc.K5.Honest.Law.FoAtHead
import Johnson.Road.Lane5AttCallsH

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Chain)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.K3 (keyPtsOf keyPtsAt)
open P5J (AtMgA TS)

/-- **Two clauses out of the library's test on a lookup's numbers.** CONDITIONAL: the test's yes. -/
theorem ok_parts (s : OnBytes.Model.Forest.Shape) (ok : FoNums.ok s = true) :
    s.calls.size = s.NC ∧ ∀ c, c < s.NC → FoNums.nOf s c = FoNums.io s c + s.dT := by
  unfold FoNums.ok at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hsz⟩, -⟩, hc⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := ok
  exact ⟨hsz, fun c h => (hc c h).1.2⟩

/-- **The cut's lengths are the calls' numbers of bits.** CONDITIONAL: see the file's head. -/
theorem zk_sizes (s : OnBytes.Model.Forest.Shape) {p : Array E} (hp : p.size = s.dT + s.rK)
    (hsz : s.calls.size = s.NC)
    (hn : ∀ c, c < s.NC → FoNums.nOf s c = s.iota.getD c 0 + s.dT)
    (hio : ∀ c, c < s.NC → s.iota.getD c 0 ≤ s.rK) :
    (keyPtsOf s p).zk.map (·.size) = s.calls.map (·.n) := by
  apply Array.ext
  · simp [keyPtsOf, hsz]
  · intro i h1 h2
    have hi : i < s.NC := by simpa [keyPtsOf] using h1
    have hc : i < s.calls.size := by
      rw [hsz]
      exact hi
    have e1 := hn i hi
    have e2 := hio i hi
    have e3 : FoNums.nOf s i = s.calls[i].n := by
      unfold FoNums.nOf
      rw [Array.getElem?_eq_getElem hc]
      rfl
    rw [Array.getD_eq_getD_getElem?] at e1 e2
    simp [keyPtsOf, Array.size_append, Array.size_extract, hp]
    omega

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **AT `keyOfK3` THE THIRD TEST SAYS YES.** CONDITIONAL: under the hypothesis h; g is below 12;
hG: G is the ground that the description's maker makes; the group's plan. -/
theorem keysFit_K3 {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    (seatOf keyOfK3 Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true := by
  obtain ⟨-, a', -, Pl, -⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨ok, nc⟩ := H2K5.Honest.fo_at_head h hg ha hx
  obtain ⟨hsz, hn⟩ := ok_parts _ ok
  have Kf := (H2K5.Honest.public_at_head h hg ha).keys
  obtain ⟨-, -, -, -, -, hcalls⟩ := OnBytes.Road.L5.hid_calls (H2K5.Honest.law_at_head h hg ha).1
  have hio : ∀ c, c < a'.fs.NC → a'.fs.iota.getD c 0 ≤ a'.fs.rK := by
    intro c hc
    rw [nc] at hc
    obtain ⟨-, e1, e2⟩ := Kf ⟨c, hc⟩
    rw [e1]
    exact e2
  unfold Seat5.keysFit
  rw [beq_iff_eq]
  show (keyOfK3 Zp G (2 * g + 1) _).map (·.size) =
    (VerifiableInference.Desc.First.Att.P.geoOf a'.S).calls.map (·.n)
  rw [keyOfK3_at_head h hg hG ha]
  unfold keyPtsAt
  have hp : ∀ (b : Nat) (hd : List Fmt.Drawn),
      ((K3.ptsOf (VerifiableInference.Desc.K3.faceOf a'.fs) b hd).keyPt 0 a'.fs.v).size =
        a'.fs.dT + a'.fs.rK := fun b hd => keyPt_size _ _ _ _ _
  rw [zk_sizes a'.fs (hp _ _) hsz hn hio, hcalls]
  simp [VerifiableInference.Desc.First.Att.P.geoOf, VerifiableInference.Desc.First.Att.P.callOf,
    Array.map_map, Function.comp_def]

/-- **SO AT `keyOfK3` THE MAKER OF THE PLACE's PUBLIC DATA YIELDS**, with two tests and with three.
CONDITIONAL: as `keysFit_K3`. By `seatAt_returns_at_head`, which has the two other tests under h. -/
theorem seatAt_returns_K3 {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    seatAt keyOfK3 Zp G (2 * g + 1) ("A" ++ toString g) g = some (seatOf keyOfK3 Zp G cF g a) ∧
      seatAtK keyOfK3 Zp G (2 * g + 1) ("A" ++ toString g) g =
        some (seatOf keyOfK3 Zp G cF g a) :=
  seatAt_returns_at_head h hg hG ha (keysFit_K3 h hg hG ha)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ok_parts
#print axioms ProofFile.Honest.K5.zk_sizes
#print axioms ProofFile.Honest.K5.keysFit_K3
#print axioms ProofFile.Honest.K5.seatAt_returns_K3
