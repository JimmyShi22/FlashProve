-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeDigitsAt.lean: the public fits of the digits' filling, under the library's head and
the opening: the premise `DigitsFit` (Pay/MadeOwnDigits.lean) holds at each address of a seat of the array "BZ".

  `ksW`, `msW`      the columns and the rows of cells of a segment's matrices, off the written view of its plan
  `bzSeatTest`, `seats_written`   by Lean's kernel, at the 25 written seats: the seat's own test, the message's, the round that
                    samples the matrix is the last in front, its count is that of the columns, the arrays' sizes
  `rng_numbers`     by Lean's kernel: the rounds "RNG" of the written list are those that the segments' places name
  `from_at_built`   a built segment's plan is what the verifier's maker returned
  `tlOf_of_tlAt`    the two readers of a segment's plan agree
  `digitsFit_at_head`   THE TOP: the premise, at every address that the digits' filling answers

Limits. The head and the opening are premises. The full size and the older hash alone. Public data alone: nothing on a run.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeDigitsPlan
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnDigits
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnABFit
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.Desc.ProofFile.Honest.K8.AddressLaw
import Johnson.Second.K08.SeatK8

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (Seat BzAt seatsOf seatAt mineOf seatFits rngAt bzAtOf bzFitsOne)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest (allRows cols_at_built matrix_at_built made_count column_at_built)
open VerifiableInference.PlanWritten (proofSizedFull TailView tailView xShapeIs_of tail_of_is)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)
open Johnson.G (layoutFull xShapeFull)
open Johnson.AtFull.Desc (spotsWritten)
open H2K5.Row (roundsBy cutPairsW)
open ProofFile.Honest.K2 (mineDigits roundNumbers)
open ProofFile.Honest.K2.Law (rngBy rngIn_by seatsBZW seatsBZW_all entryNumbers roundNumbers_entries entries_at_head
  seatsBZ_at_head built_at_head)
open ProofFile.Honest.K8 (parOfTail zzVals zzPubOf columnsOf DigitColsFit mz_allRows)
open OnBytes.HonestTrace.U3.Fit (before_at_head)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The columns of a segment's matrices, off the written view. -/
def ksW (v : TailView) : Nat := (v.2.1.map fun x => x.2.2).sum

/-- Their rows of cells. -/
def msW (v : TailView) : Nat := (v.2.1.map fun x => x.2.1).sum

/-- What the written values say of the rounds at a segment. -/
abbrev rngWAt (l : Nat) : Option (Nat × Nat) := rngBy (roundsBy cutPairsW) P5T.esFull.1 spotsWritten l

/-- **The public facts at one written seat.** -/
def bzSeatTest (s : Seat) : Bool :=
  match xShapeFull.1[s.seg]?, rngWAt s.seg with
  | some (some v), some n =>
    seatFits s && msgFits proofSizedFull.codes proofSizedFull.request layoutFull s.seg s.array.message &&
      s.heard == n.1 + 1 && s.array.sizeI == 32 && s.array.sizeC == 2048 && n.2 == ksW v * 128 &&
      ((layoutFull.link.getD s.seg []).all fun a => a.name != "ZZ" || (a.sizeI == 128 && a.sizeC == 2 * msW v))
  | _, _ => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- So they are at the 25 written seats. -/
theorem seats_written : seatsBZW.all bzSeatTest = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The rounds "RNG" of the written list are those that the segments' places name. -/
theorem rng_numbers : entryNumbers P5T.esFull.1 "RNG" =
    (List.range 25).map fun l => ((rngWAt l).map (·.1)).getD 0 := by decide +kernel

/-- What the second text of `rngIn` returns is an entry's number and count. -/
theorem rngBy_entry {before : String → Option Nat} {E : List Fmt.Entry} {sps : List ProofFile.Spot} {seg : Nat}
    {n : Nat × Nat} (h : rngBy before E sps seg = some n) : ∃ e, E[n.1]? = some e ∧ e.trits = n.2 := by
  unfold rngBy at h
  obtain ⟨sp, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨e, he, rfl⟩
  · cases h

/-- The two readers of a segment's plan agree. -/
theorem tlOf_of_tlAt {X : OnBytes.Model.Verify.Public} {k : Nat} {t : HTailF2}
    (h : VerifiableInference.Desc.First.Look.tlAt X k = some t) : K3.tlOf X k = t := by
  unfold VerifiableInference.Desc.First.Look.tlAt at h
  unfold K3.tlOf K3.linkH K3.stepOf
  dsimp only at h
  generalize (if X.p4 = true then 2 else 1) = st at h ⊢
  split at h
  · rename_i c
    rw [if_pos c]
    exact Option.some.inj h
  · rename_i c
    rw [if_neg c]
    split at h
    · rename_i c2
      rw [if_pos c2, h]
      rfl
    · rename_i c2
      rw [if_neg c2, h]
      rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- A built segment's plan is what the verifier's maker returned. -/
theorem from_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl) : Fo.ZPlan.FromPieces Xl.tl := by
  obtain ⟨tails, l24, e24, t24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [t24]
    exact Fo.ZPlan.public_H_from O.public
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans e3)
      rw [etl]
      exact Fo.ZPlan.public_G_from O.public g hp ehp
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans e3)
      rw [etl']
      exact Fo.ZPlan.public_A_from O.public g a ea

end

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening, the public fits hold at each address that the digits' filling answers.** -/
theorem digitsFit_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np))
    {a : MsgAddr} (hm : mineDigits Zp Bs.G₀ a = true) : DigitsFit Zp Bs.G₀ (K3.matsOwn Bs.G₀.W) a := by
  have hBZ := seatsBZ_at_head h O
  have hmine : mineOf (seatsOf Zp Bs.G₀ "BZ") a = true := by
    unfold mineDigits at hm
    exact (Bool.and_eq_true _ _ ▸ hm).2
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hmine
  have sm : s ∈ seatsBZW := by
    rw [hBZ] at hs
    exact List.mem_of_find?_eq_some hs
  have hl : s.seg < 25 := by
    have hm' : s.seg ∈ seatsBZW.map (·.seg) := List.mem_map_of_mem sm
    rw [eq_of_beq seatsBZW_all] at hm'
    exact List.mem_range.1 hm'
  obtain ⟨Y, hY⟩ := built_at_head h O hl
  obtain ⟨tA, t128⟩ := Second.K08.tail_at_seat h.scope h.reads O.pub O.blank (by omega) hY
  have hx := xShape_in_scope (o := OnBytes.secondHashFunction) h.scope O.pub (VerifiableInference.Desc.K1.pin1_atAll h)
  have tv := tail_of_is (xShapeIs_of hx) hl
  rw [tA] at tv
  have ht := List.all_eq_true.1 seats_written s sm
  unfold bzSeatTest at ht
  rw [tv] at ht
  cases hn : rngWAt s.seg with
  | none =>
    rw [hn] at ht
    cases ht
  | some n =>
    rw [hn] at ht
    simp only [Option.map_some, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩ := ht
    obtain ⟨g1, g2, g3⟩ := ProofFile.Honest.K2.Law.first_at_head h O
    have hE := entries_at_head h.toAtMg O
    -- the public data of the segment
    have hr : rngAt Zp spotsWritten s.seg = some n := by
      unfold rngAt
      rw [rngIn_by, before_at_head h, hE]
      exact hn
    have hb : bzAtOf Zp Bs.G₀ (K3.matsOwn Bs.G₀.W) s.seg =
        some ⟨n.1, n.2, Y.tl, K3.matsOwn Bs.G₀.W s.seg⟩ := by
      unfold bzAtOf
      rw [ProofFile.Honest.K2.Law.spots_at_head h.toAtMg O]
      show (rngAt Zp spotsWritten s.seg).bind (fun n => (Bs.G₀.built[s.seg]?).bind fun Y =>
        some ({ rng := n.1, declared := n.2, tl := Y.tl, mats := K3.matsOwn Bs.G₀.W s.seg } : BzAt)) = _
      rw [hr, hY]
      rfl
    -- the plan
    have hNM := matrix_at_built h.scope h.reads O h.laid.planOk hl hY
    have hmz := column_at_built h.scope h.reads O h.laid.planOk hl hY
    have hFP := from_at_built h.scope h.reads O hl hY
    have hfit := fit_of_from hFP t128 hmz
    have hTail := Fo.ZPlan.tailTest_from hFP
    have hMade := _root_.P1K8.made_at_built h.scope h.reads O hl hY
    have hcount := made_count hMade
    have hcols : DigitColsFit Y.tl := ⟨cols_at_built h.scope h.reads O hl hY, hNM, hcount⟩
    have hall := mz_allRows Y.tl hcols
    have eW : Bs.G₀.W = Zp.p.X := ProofFile.Law.blankBy_W O.blank
    have hlen : (K3.matsOwn Bs.G₀.W s.seg).length = Y.tl.mats.size := by
      unfold K3.matsOwn
      rw [eW, tlOf_of_tlAt tA]
      simp
    have eks : (parOfTail Y.tl).ks.sum = ksW (tailView Y.tl) := by
      show (Y.tl.mats.toList.map (·.k)).sum = ((Y.tl.mats.toList.map fun x => (x.aId, x.m, x.k)).map fun x => x.2.2).sum
      rw [List.map_map]
      rfl
    have ems : allRows (parOfTail Y.tl) = msW (tailView Y.tl) := by
      show (Y.tl.mats.toList.map (·.m)).foldl (· + ·) 0 =
        ((Y.tl.mats.toList.map fun x => (x.aId, x.m, x.k)).map fun x => x.2.1).sum
      rw [VerifiableInference.Desc.First.K8.foldl_add, Nat.zero_add, List.map_map]
      rfl
    have ewant : (⟨n.1, n.2, Y.tl, K3.matsOwn Bs.G₀.W s.seg⟩ : BzAt).wanted = n.2 := by
      show (parOfTail Y.tl).ks.sum * Y.tl.tau = n.2
      rw [eks, t128, f6]
    have hwhy : (⟨n.1, n.2, Y.tl, K3.matsOwn Bs.G₀.W s.seg⟩ : BzAt).why s.heard s.array.sizeI s.array.sizeC = none := by
      refine why_none hfit hTail f3.symm ewant.symm hlen hall f4 ?_
      show s.array.sizeC = 2 ^ (Y.tl.f9.kT + Y.tl.f9.cK)
      rw [hfit.kT, hfit.cK, f5]
      rfl
    -- the round
    have hnum : (roundNumbers Zp.D.1 "RNG")[s.seg]? = some n.1 := by
      rw [roundNumbers_entries, hE, rng_numbers, List.getElem?_map, List.getElem?_range hl]
      show some (((rngWAt s.seg).map (·.1)).getD 0) = _
      rw [hn]
      rfl
    obtain ⟨e, he, etr⟩ := rngBy_entry hn
    rw [← hE, List.getElem?_map] at he
    obtain ⟨d, hd, ed⟩ := Option.map_eq_some_iff.1 he
    have etr' : d.entry.trits = n.2 := by
      have ed' : d.entry = e := ed
      rw [ed']
      exact etr
    refine ⟨s, ⟨n.1, n.2, Y.tl, K3.matsOwn Bs.G₀.W s.seg⟩, Y.tl, d, hs, hb, ?_, ?_, ?_, f3.symm,
      ewant.trans etr'.symm, hd, ?_, hlen.trans hcount.symm, hnum, ?_, ?_⟩
    · rw [g2, g3]
      exact (Bool.and_eq_true _ _ ▸ allFit_written).1
    · rw [g1, g2, g3]
      exact f2
    · show (seatFits s && (bzAtOf Zp Bs.G₀ (K3.matsOwn Bs.G₀.W) s.seg).any fun b =>
        b.fits s.heard s.array.sizeI s.array.sizeC) = true
      rw [hb, f1]
      show ((⟨n.1, n.2, Y.tl, K3.matsOwn Bs.G₀.W s.seg⟩ : BzAt).why s.heard s.array.sizeI s.array.sizeC).isNone = true
      rw [hwhy]
      rfl
    · rw [hY]
      rfl
    · show (parOfTail Y.tl).ks.sum * Y.tl.tau = d.entry.trits
      rw [eks, t128, etr', f6]
    · unfold ArrayVals.inside
      rw [g3]
      refine List.all_eq_true.2 fun q hq => ?_
      have q1 := List.all_eq_true.1 f7 q hq
      cases c : (q.name == "ZZ") with
      | false =>
        have hz : (zzVals (zzPubOf Bs.G₀ Zp.D.1 (K3.matsOwn Bs.G₀.W))).size s.seg q.name = none := by
          show (if (q.name == "ZZ") = true then _ else none) = none
          rw [c]
          rfl
        rw [hz]
        rfl
      | true =>
        have hz : (zzVals (zzPubOf Bs.G₀ Zp.D.1 (K3.matsOwn Bs.G₀.W))).size s.seg q.name =
            some (128, 2 * msW (tailView Y.tl)) := by
          show (if (q.name == "ZZ") = true then ((Bs.G₀.built[s.seg]?).map (·.tl)).map
            (fun tl => (tl.tau, 2 * allRows (parOfTail tl))) else none) = _
          rw [c, if_pos rfl, hY]
          show some (Y.tl.tau, 2 * allRows (parOfTail Y.tl)) = _
          rw [t128, ems]
        rw [hz]
        have q2 : (q.sizeI == 128 && q.sizeC == 2 * msW (tailView Y.tl)) = true := by
          have c' : (q.name != "ZZ") = false := by simp [bne, c]
          rw [c'] at q1
          exact q1
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at q2
        show ((128, 2 * msW (tailView Y.tl)) == (q.sizeI, q.sizeC)) = true
        rw [q2.1, q2.2]
        exact beq_self_eq_true _

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ksW
#print axioms ProofFile.Honest.K10.msW
#print axioms ProofFile.Honest.K10.bzSeatTest
#print axioms ProofFile.Honest.K10.seats_written
#print axioms ProofFile.Honest.K10.rng_numbers
#print axioms ProofFile.Honest.K10.rngBy_entry
#print axioms ProofFile.Honest.K10.tlOf_of_tlAt
#print axioms ProofFile.Honest.K10.from_at_built
#print axioms ProofFile.Honest.K10.digitsFit_at_head
