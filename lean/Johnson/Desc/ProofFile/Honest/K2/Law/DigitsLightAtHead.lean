-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/DigitsLightAtHead.lean: the kind "the code switch" (K2): under
the library's head and the opening, the light test says yes at the digits' filling, at every place
of the kind: the statement `DigitsLight` (LightDebts.lean of this folder). Public data alone.
Lemmas with their proofs; no definition; none of the library's goals.

How. The light test asks of a filling where it lays an element, and only at the first place of one
block of each array. It is monotone in that. So it is enough to compare the digits' filling
(`K1.digitsFill`, Honest/K1/LotFill.lean) with a stand-in at the same seats whose values state the
size (1, 1) for both arrays (`digitsOnes`, DigitsWritten.lean of this folder), at which Lean's
kernel has run the test. The digits' filling lays wherever the stand-in does, if both arrays have a
row and a column at each segment.

  `arraysLaidLight_mono`, `lightBy_mono`   the light test is monotone in where the filling lays, and
                    falls in the set of addresses asked
  `laidData_lays`, `laidData_lays_none`    what `laidData` lays, at a seated address and at another
  `laidBack_mem`    the array that `laidBack` finds is one of the segment's, of that message
  `zzDataAt_lays`   where the filling of "ZZ" lays, as a filling of that form
  `digits_lays_of_ones`   GENERAL: the comparison, from two hypotheses on the sizes
  `foldl_add_le`, `allRows_pos`   a list of matrices whose first has a row has a row
  `seatsBZ_at_head`   under the head the seats of "BZ" are the written ones
  `built_at_head`   each of the 25 segments is built: `P1K8T.built_at` at this file's bound
  `bzAt_at_head`    the public data of "BZ" are there at each of the 25
  `zz_at_head`      "ZZ" has a row and a column at each of the 25
  `seat_seg_lt`     a written seat's segment is below 25
  `mineDigits_at_head`   the addresses that the share asks are the written ones: by reading, with
                    `digitsW_asks` and `linksW_pos` (DigitsWritten.lean) the top then asks something
                    at each place: no statement here says so
  `digits_light_at_head`   THE TOP

By, of other authors: `lightBy`, `lightAt_by`, `lightBy_take`, `addrs_written`, `first_at_head`,
`mineSwitch_at_head` (LightWritten.lean, LightAtHead.lean of this folder) · `places_at_head`,
`segments_at_head`, `spots_at_head`, `entries_at_head` (PlacesWritten.lean) · `seats_at_head`,
`before_at_head` (Johnson/HonestTrace/U3Fit/SeatsAtHead.lean): under the head the seats of every
name, and the count of rounds in front of a step, are closed terms · `IM.Open.blank`
(Johnson/IMR/SeatOpen.lean) · `P1K8T.built_at` (Johnson/P1K8R/Tied.lean) · `IM.k8_tau_128`
(Johnson/K8Q14R/TauAt.lean) · `matrix_at_built` (Johnson/Desc/K8/Honest/HeldOutright.lean) ·
`P1K8.made_sizes` (Johnson/P1K8R/MadeAtPlans.lean) · `P1K8.made_at_built`
(Johnson/P1K8R/SecondLaidAtBatch.lean). Kin of `foldl_add_le`: `foldl_add`
(OnBytes/Chain/Lists.lean), an equation where this is a bound. Kin elsewhere in the library, which
this file does not import: `laidBack_iff` (Honest/Law/LaidLists.lean): it has `laidBack_mem`'s
direction and the other, under a premise · `lays_of_back` (Honest/Law/LaidSent.lean): a general form
of the step that `digits_lays_of_ones` takes twice · `lays_says` (Honest/Law/LaidLaw.lean): that
step backwards.

Limits. It says that a public test passes: nothing on what a prover sends, nothing on a run. The
light test's yes is what the kind's public test follows from; its no would say nothing. Closed facts
by Lean's kernel lie beneath. The head is shown met by nobody here. One instance, a default table of
scales, is switched off, as in the files beneath. The full size and the format's second hash function alone.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.LightAtHead
import Johnson.Desc.K8.Honest.HeldOutright
import Johnson.K8Q14R.TauAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest (allRows matrix_at_built)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.HonestTrace (Seat seatsOf seatAt pairOf mineOf heardOf rngAt bzAtOf bzVals bzRows)
open OnBytes.HonestTrace.U3.Fit (seats_at_head before_at_head)
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open Johnson.G (layoutFull)
open Johnson.AtFull.Desc (spotsWritten)
open ProofFile.Honest.K8 (parOfTail zzDataAt zzVals zzPubOf bearsZz)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The light test is monotone -/

/-- The light test on one message is monotone in where the filling lays. -/
theorem arraysLaidLight_mono {D D' : RowData} {lay : ReqLayout} {codes : OnBytes.Codes}
    {s : OnBytes.OracleShape} {seg m : Nat} {a : MsgAddr}
    (hl : ∀ r j, D'.lays a r j = true → D.lays a r j = true)
    (h : arraysLaidLight D' lay codes s seg m a = true) :
    arraysLaidLight D lay codes s seg m a = true := by
  unfold arraysLaidLight at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro A hA
  obtain ⟨b, hb, hx⟩ := List.any_eq_true.1 (h A hA)
  refine List.any_eq_true.2 ⟨b, hb, ?_⟩
  simp only [Bool.and_eq_true] at hx ⊢
  exact ⟨⟨hx.1.1, hl _ _ hx.1.2⟩, hx.2⟩

/-- **The light test is monotone**: fewer addresses asked, and a filling that lays more there. -/
theorem lightBy_mono {D D' : RowData} {mine mine' : MsgAddr → Bool} {lay : ReqLayout}
    {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub}
    (hm : ∀ a, mine a = true → mine' a = true)
    (hl : ∀ a, mine a = true → ∀ r j, D'.lays a r j = true → D.lays a r j = true)
    (h : lightBy D' mine' lay addrs segs = true) : lightBy D mine lay addrs segs = true := by
  unfold lightBy at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro y hy
  have h1 : ((y.1.ownShapes (y.2 == 0)).zipIdx.all fun s => (addrs y.2 s.2).all fun a =>
    !mine' a || arraysLaidLight D' lay y.1.sizes.codes s.1 y.2 s.2 a) = true := h y hy
  show ((y.1.ownShapes (y.2 == 0)).zipIdx.all fun s => (addrs y.2 s.2).all fun a =>
    !mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a) = true
  rw [List.all_eq_true] at h1 ⊢
  intro s hs
  have h2 : ((addrs y.2 s.2).all fun a =>
    !mine' a || arraysLaidLight D' lay y.1.sizes.codes s.1 y.2 s.2 a) = true := h1 s hs
  show ((addrs y.2 s.2).all fun a =>
    !mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a) = true
  revert h2
  cases addrs y.2 s.2 with
  | none => exact fun _ => rfl
  | some a =>
    intro h2
    have h3 : (!mine' a || arraysLaidLight D' lay y.1.sizes.codes s.1 y.2 s.2 a) = true := h2
    show (!mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a) = true
    cases hma : mine a with
    | false => rfl
    | true =>
      rw [hm a hma] at h3
      exact arraysLaidLight_mono (hl a hma) h3

/-! ## 2 What a filling of this form lays -/

/-- At a seated address. -/
theorem laidData_lays {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout}
    {seat : MsgAddr → Option (Nat × Nat)} {heard : MsgAddr → Nat} {V : ArrayVals} {a : MsgAddr}
    {l m : Nat} (hs : seat a = some (l, m)) (r j : Nat) :
    (laidData codes s lay seat heard V).lays a r j =
      (msgFits codes s lay l m && (laidBack lay l m r j).any fun x =>
        (V.size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) := by
  simp only [laidData, hs]

/-- At an address without a seat. -/
theorem laidData_lays_none {codes : OnBytes.Codes} {s : ReqShape} {lay : ReqLayout}
    {seat : MsgAddr → Option (Nat × Nat)} {heard : MsgAddr → Nat} {V : ArrayVals} {a : MsgAddr}
    (hs : seat a = none) (r j : Nat) : (laidData codes s lay seat heard V).lays a r j = false := by
  simp only [laidData, hs]

/-- The array that `laidBack` finds is one of the segment's arrays, of that message. -/
theorem laidBack_mem {lay : ReqLayout} {l m r j : Nat} {x : OnBytes.Params.ReqArray × Nat × Nat}
    (h : laidBack lay l m r j = some x) :
    x.1 ∈ lay.link.getD l [] ∧ (x.1.message == m) = true := by
  unfold laidBack at h
  obtain ⟨A, hA, hx⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact List.mem_filter.1 hA

/-- Where the filling of "ZZ" lays: the count of challenges heard is not read. -/
theorem zzDataAt_lays (G : Ground) (D : List Fmt.DeclaredRound) (seat : MsgAddr → Option (Nat × Nat))
    (mats : Nat → List (Nat × String × Nat)) (a : MsgAddr) (r j : Nat) :
    (zzDataAt G D seat mats).lays a r j =
      (laidData G.first.codes G.first.shape G.first.layout (bearsZz G.first.layout seat)
        (fun _ => 0) (zzVals (zzPubOf G D mats))).lays a r j := rfl

/-! ## 3 The comparison -/

/-- **The digits' filling lays wherever the stand-in does**, at an address at whose segment the
public data of "BZ" are there and "ZZ" has a row and a column. -/
theorem digits_lays_of_ones (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat))
    (a : MsgAddr)
    (hB : ∀ l m, pairOf (seatsOf Z G "BZ") a = some (l, m) → (bzAtOf Z G mats l).isSome = true)
    (hZ : ∀ l m, pairOf (seatsOf Z G "BZ") a = some (l, m) →
      ∃ Y, G.built[l]? = some Y ∧ 0 < Y.tl.tau ∧ 0 < allRows (parOfTail Y.tl))
    (r j : Nat)
    (h : (digitsOnes G.first.codes G.first.shape G.first.layout (seatsOf Z G "BZ") onesVals).lays a
      r j = true) : (K1.digitsFill Z G mats).lays a r j = true := by
  unfold digitsOnes at h
  cases hp : pairOf (seatsOf Z G "BZ") a with
  | none =>
    rw [laidData_lays_none hp] at h
    cases h
  | some lm =>
    obtain ⟨l, m⟩ := lm
    rw [laidData_lays hp, Bool.and_eq_true] at h
    obtain ⟨hfit, hany⟩ := h
    cases hb : laidBack G.first.layout l m r j with
    | none =>
      rw [hb] at hany
      exact Bool.noConfusion (show false = true from hany)
    | some x =>
      rw [hb] at hany
      have hx : ((onesVals.size l x.1.name).any fun z =>
        decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = true := hany
      have hsz : onesVals.size l x.1.name =
          if (x.1.name == "BZ" || x.1.name == "ZZ") = true then some (1, 1) else none := rfl
      rw [hsz] at hx
      cases hc : (x.1.name == "BZ" || x.1.name == "ZZ") with
      | false =>
        rw [hc] at hx
        exact Bool.noConfusion (show false = true from hx)
      | true =>
        rw [hc] at hx
        have hpos : x.2.1 < 1 ∧ x.2.2 < 1 := of_decide_eq_true hx
        show ((bzRows Z G mats).lays a r j ||
          (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).lays a r j) = true
        rw [Bool.or_eq_true]
        rw [Bool.or_eq_true] at hc
        rcases hc with hbz | hzz
        · left
          obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.1 (hB l m hp)
          show (laidData G.first.codes G.first.shape G.first.layout (pairOf (seatsOf Z G "BZ"))
            (heardOf (seatsOf Z G "BZ")) (bzVals Z G mats)).lays a r j = true
          rw [laidData_lays hp, hfit, hb, Bool.true_and]
          show (((bzVals Z G mats).size l x.1.name).any fun z =>
            decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = true
          have hs : (bzVals Z G mats).size l x.1.name = some (32, b.tl.bzColumns) := by
            show (if (x.1.name == "BZ") = true then
              (bzAtOf Z G mats l).map (fun b => (32, b.tl.bzColumns)) else none) = _
            rw [if_pos hbz, hb']
            rfl
          rw [hs]
          show decide (x.2.1 < 32 ∧ x.2.2 < b.tl.bzColumns) = true
          exact decide_eq_true ⟨by omega, lt_of_lt_of_le hpos.2 Nat.one_le_two_pow⟩
        · right
          obtain ⟨Y, hY, ht, hr⟩ := hZ l m hp
          obtain ⟨hmem, hmsg⟩ := laidBack_mem hb
          have hbear : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) a = some (l, m) := by
            unfold bearsZz
            rw [hp]
            show (if ((G.first.layout.link.getD l []).any fun y =>
              y.name == "ZZ" && y.message == m) = true then some (l, m) else none) = _
            have hy : (x.1.name == "ZZ" && x.1.message == m) = true := by rw [hzz, hmsg]; rfl
            rw [if_pos (List.any_eq_true.2 ⟨x.1, hmem, hy⟩)]
          rw [zzDataAt_lays, laidData_lays hbear, hfit, hb, Bool.true_and]
          show (((zzVals (zzPubOf G Z.D.1 mats)).size l x.1.name).any fun z =>
            decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = true
          have hs : (zzVals (zzPubOf G Z.D.1 mats)).size l x.1.name =
              some (Y.tl.tau, 2 * allRows (parOfTail Y.tl)) := by
            show (if (x.1.name == "ZZ") = true then
              ((G.built[l]?).map (·.tl)).map
                (fun tl => (tl.tau, 2 * allRows (parOfTail tl))) else none) = _
            rw [if_pos hzz, hY]
            rfl
          rw [hs]
          show decide (x.2.1 < Y.tl.tau ∧ x.2.2 < 2 * allRows (parOfTail Y.tl)) = true
          exact decide_eq_true ⟨by omega, by omega⟩

/-! ## 4 A row of cells -/

/-- A sum from a is at least a. -/
theorem foldl_add_le (l : List Nat) (a : Nat) : a ≤ l.foldl (· + ·) a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl a
  | cons x xs ih => exact Nat.le_trans (Nat.le_add_right a x) (ih (a + x))

/-- Where the first matrix has a row of cells, all together have one. -/
theorem allRows_pos {tl : HTailF2} (h : 0 < (tl.mats.getD 0 {}).m) :
    0 < allRows (parOfTail tl) := by
  show 0 < (tl.mats.toList.map (·.m)).foldl (· + ·) 0
  rcases hm : tl.mats with ⟨ms⟩
  rw [hm] at h
  cases ms with
  | nil => exact absurd h (Nat.lt_irrefl 0)
  | cons y ys =>
    have hy : 0 < y.m := h
    show 0 < (ys.map (·.m)).foldl (· + ·) (0 + y.m)
    exact Nat.lt_of_lt_of_le (by omega) (foldl_add_le _ _)

/-! ## 5 Under the head -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

section
variable (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
  (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (seatZ Zp Np) (secondAt Zp Np))
include h O

/-- **The seats of "BZ" are the written ones.** -/
theorem seatsBZ_at_head : seatsOf Zp Bs.G₀ "BZ" = seatsBZW := seats_at_head h O.blank "BZ"

/-- **Each of the 25 segments is built.** -/
theorem built_at_head {l : Nat} (hl : l < 25) : ∃ Y, Bs.G₀.built[l]? = some Y :=
  P1K8T.built_at h.scope h.reads O (by omega)

/-- **The public data of "BZ" are there at each of the 25 segments.** -/
theorem bzAt_at_head (mats : Nat → List (Nat × String × Nat)) {l : Nat} (hl : l < 25) :
    (bzAtOf Zp Bs.G₀ mats l).isSome = true := by
  obtain ⟨Y, hY⟩ := built_at_head h O hl
  have hr : (rngAt Zp spotsWritten l).isSome = true := by
    unfold rngAt
    rw [rngIn_by, before_at_head h, entries_at_head h.toAtMg O]
    exact List.all_eq_true.1 rngW l (List.mem_range.2 hl)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hr
  have e : bzAtOf Zp Bs.G₀ mats l = some ⟨n.1, n.2, Y.tl, mats l⟩ := by
    unfold bzAtOf
    rw [spots_at_head h.toAtMg O]
    show (rngAt Zp spotsWritten l).bind (fun n => (Bs.G₀.built[l]?).bind fun Y =>
      some ({ rng := n.1, declared := n.2, tl := Y.tl, mats := mats l } :
        OnBytes.HonestTrace.BzAt)) = _
    rw [hn, hY]
    rfl
  rw [e]
  rfl

/-- **"ZZ" has a row and a column at each of the 25 segments.** -/
theorem zz_at_head {l : Nat} (hl : l < 25) :
    ∃ Y, Bs.G₀.built[l]? = some Y ∧ 0 < Y.tl.tau ∧ 0 < allRows (parOfTail Y.tl) := by
  obtain ⟨Y, hY⟩ := built_at_head h O hl
  have ht : Y.tl.tau = 128 := IM.k8_tau_128 h.scope h.reads O (by omega) hY
  have hN := matrix_at_built h.scope h.reads O h.laid.planOk hl hY
  have hS := _root_.P1K8.made_sizes (_root_.P1K8.made_at_built h.scope h.reads O hl hY)
  unfold _root_.P1K8.sizesB at hS
  rw [Bool.and_eq_true, List.all_eq_true] at hS
  have h0 := hS.1 0 (List.mem_range.2 hN)
  rw [Bool.and_eq_true] at h0
  exact ⟨Y, hY, by omega, allRows_pos (of_decide_eq_true h0.2)⟩

omit h O in
/-- A written seat's segment is below 25. -/
theorem seat_seg_lt {a : MsgAddr} {l m : Nat} (hp : pairOf seatsBZW a = some (l, m)) : l < 25 := by
  unfold pairOf at hp
  obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 hp
  have hmem : s ∈ seatsBZW := List.mem_of_find?_eq_some hs
  have hl : s.seg ∈ seatsBZW.map (·.seg) := List.mem_map_of_mem hmem
  rw [eq_of_beq seatsBZW_all] at hl
  have e1 : s.seg = l := congrArg Prod.fst e
  rw [← e1]
  exact List.mem_range.1 hl

/-- The addresses that the digits' share asks are the written ones. -/
theorem mineDigits_at_head : mineDigits Zp Bs.G₀ = mineDigitsW := by
  funext a
  unfold mineDigits mineDigitsW
  rw [mineSwitch_at_head h O, seatsBZ_at_head h O]

/-- **UNDER THE HEAD AND THE OPENING THE LIGHT TEST SAYS YES AT THE DIGITS' FILLING, AT EVERY PLACE
OF THE KIND.** -/
theorem digits_light_at_head : DigitsLight Zp Bs.G₀ := by
  intro p hp
  obtain ⟨e1, e2, e3⟩ := first_at_head h O
  have hs := seatsBZ_at_head h O
  rw [places_at_head h.toAtMg O] at hp
  rw [lightAt_by, addrs_written p hp, segments_at_head h.toAtMg O, e3]
  refine lightBy_mono (mine' := mineOf seatsBZW) (D' := digitsOnesW onesVals) ?_ ?_
    (lightBy_take digitsW p.link)
  · intro a ha
    unfold mineDigits at ha
    rw [Bool.and_eq_true, hs] at ha
    exact ha.2
  · intro a _ r' j hl
    refine digits_lays_of_ones Zp Bs.G₀ _ a ?_ ?_ r' j ?_
    · intro l m hq
      rw [hs] at hq
      exact bzAt_at_head h O _ (seat_seg_lt hq)
    · intro l m hq
      rw [hs] at hq
      exact zz_at_head h O (seat_seg_lt hq)
    · rw [e1, e2, e3, hs]
      exact hl

end

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.arraysLaidLight_mono
#print axioms ProofFile.Honest.K2.Law.lightBy_mono
#print axioms ProofFile.Honest.K2.Law.laidData_lays
#print axioms ProofFile.Honest.K2.Law.laidData_lays_none
#print axioms ProofFile.Honest.K2.Law.laidBack_mem
#print axioms ProofFile.Honest.K2.Law.zzDataAt_lays
#print axioms ProofFile.Honest.K2.Law.digits_lays_of_ones
#print axioms ProofFile.Honest.K2.Law.foldl_add_le
#print axioms ProofFile.Honest.K2.Law.allRows_pos
#print axioms ProofFile.Honest.K2.Law.seatsBZ_at_head
#print axioms ProofFile.Honest.K2.Law.built_at_head
#print axioms ProofFile.Honest.K2.Law.bzAt_at_head
#print axioms ProofFile.Honest.K2.Law.zz_at_head
#print axioms ProofFile.Honest.K2.Law.seat_seg_lt
#print axioms ProofFile.Honest.K2.Law.mineDigits_at_head
#print axioms ProofFile.Honest.K2.Law.digits_light_at_head
