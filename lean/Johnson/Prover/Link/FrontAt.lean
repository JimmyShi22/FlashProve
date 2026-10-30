-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontAt.lean: THE VALUES' HALF OF THE LINK's FRONT, AT A VIEW AND AT THE FULL
SIZE: front_holds (Johnson/Prover/Link/FrontWhole.lean) CALLED. That law speaks of five written
rounds of typed messages and typed challenges. Here these letters are made: from a view whose first
five rounds are the written ones (lFront, Johnson/Prover/Link/LinkAll.lean) at draws that come of
typed challenges. Behind the batching the claim then holds at the written first state's message.

Main names (namespace Johnson.Prover.Link).
  drawn_typed   entry i of what a list of typed challenges draws (drawnSL) is the draw of a typed
    challenge of round i. General.
  front_of_view   THE JOIN, general in the sizes and the six rounds: front_holds' public premises,
    the record of the link's five rounds at carried records laid as data, the group with its layout
    and the batching's equation, the stored columns, and the view's form ⟹ the claim holds at μOf of
    firstPS at lMem, whatever tN, φN, ψN.
  fr_frontItems, fr_maskPlaces   two closed facts at the full size: the first off the one closed
    fact on all rounds (fr_sorts), the second by the kernel's evaluation.
  front_at   AT THE FULL SIZE, at the draws of any typed ρ, at the instance's written keys and
    Meant's first five clauses: the claim holds at μOf (frS.sg 97) (lPS ...).

How. After the library's own join at the claim (linkClaim, Johnson/Desc/K15/K15Head.lean): the
record's pending rounds are the view's; batRan_at with ran_fresh; and the mask table's zeros as
headKeeps_ofR takes them (LinkRanR.bat_mask, OnBytes/Slice/BlkLinkHeadRec.lean). The typed messages
by rvW_onto (RoundsOnto.lean); what the typed laws read of a challenge is what the view shows by
gVec_read and gSeed_read_take (RoundsRead.lean); the keys hold the OOD samples by keyHas_written
(KeysHonest.lean); the end by muOf_front (BodyEnds.lean). That a row of the group's code has 2 ^ aP
places, which front_holds asks by itself, is LinkFit's own clause pow. At the full size:
fr_linkSizesR, fr_linkFitR, fr_batDrawsS, fr_pads, fr_recordShape
(OnBytes/Slice/FullRecBlkFacts.lean) and dsFull_eq (OnBytes/Flat/LinkSibAt.lean).

Limits. LEFT TO THE CALLER: the record of the link's five rounds (LinkRanR) · that the view's first
five rounds are lFront · the group, its layout and the batching's equation · that the dealt stored
columns are the two stored strings'. NO INSTANCE OF THESE PREMISES TOGETHER IS SHOWN HERE, at a toy
or at the full size. The end stands at stmG (frS.sg 97) and not in the letters of the loop's
invariant (stmGk at sgOf of the plan's first stage): that step is bodyInv0_full's
(BodyInv0Full.lean), which takes the claim at stmG (frS.sg 97) as a premise; front0_full
(BodyInv0Meant.lean) pays that premise from front_at. TWO SHAPES: that under its hR, hS and hF the
sizes have t0 + T.r + 1 ≤ R * C.l is said by padRoom_of_view
(Johnson/Prover/Link/PadRoomMore.lean [not in this library]): nothing in this library shows it; if
it holds, the two shapes at which membMsg (FrontMsg.lean) does not read fr at the pad's place cannot
occur there: both have t0 + T.r = R * C.l. Nothing on soundness. "mask" and "pad" are the library's
and another file's names: nothing is said of what they do.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkYesStm
import Johnson.Prover.Link.BodyEnds
import Johnson.Prover.Link.LinkView
import Johnson.Prover.Link.RoundsOnto
import Johnson.Prover.Link.RoundsRead
import Johnson.Prover.Link.KeysHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Ood Iop _root_.Run
open VerifiableInference.Desc
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Desc.K15 (frP ctxOf first)
open OnBytes.Flat (dsFull RecFull dsFull_eq)
open _root_.Run.PQ (SgX)

/-- **Entry i of what a list of typed challenges draws is the draw of a typed challenge of round
i.** -/
theorem drawn_typed : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (ρ : Rho (uL (ckP .two) ds)) (i : ℕ)
    (d : PQ.RD), ds[i]? = some (TypedOracleCompiler.Run.PQ.ofLib d) →
    ∃ c : (wRound d).Chal, Johnson.Prover.Link.drawsOf (drawnSL (ckP .two) ds ρ) i =
      (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)
  | [], _, _, _, h => nomatch h
  | d0 :: ds, (c, ρ), 0, d, h => by
    obtain rfl : d0 = TypedOracleCompiler.Run.PQ.ofLib d := Option.some.inj h
    exact ⟨c, rfl⟩
  | d0 :: ds, (c, ρ), i + 1, d, h => by
    obtain ⟨c', hc'⟩ := drawn_typed ds ρ i d h
    exact ⟨c', hc'⟩

/-- **The values' half of the link's front, at a view whose first five rounds are the written
ones.** front_holds (Johnson/Prover/Link/FrontWhole.lean) with its typed messages made. -/
theorem front_of_view (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (d1 d2 d3 d4 d5 dA : PQ.RD) (es es' : List Fmt.Entry) (d₀ d' : _root_.Desc.K15.St)
    (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn) (x : LinkRun) (DR : LinkDataR) (G' : Group)
    (L : GroupLayout) (θ : E) (row : GroupRow) (hS : LinkSizes S Λ d₀.st.codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hR : LinkRanR Λ first further (_root_.Desc.K15.ctxOf es d₀ rs cols)
      (_root_.Desc.K15.ctxOf es' d' rest cols') x DR)
    (hG : d'.st.groups[x.group]? = some G') (hL : d'.st.layout x.group = some L)
    (hrow : Bat.combine (begun d'.st x.group G') x.group ⟨L, runRows d'.st G'⟩ θ = some row)
    (hop : ∀ o ∈ cols,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hZ : S.P.Z.l ≤ 2 ^ ((linkLay Λ d₀.st).h + (linkLay Λ d₀.st).logEllZk))
    (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)
    (c1 : (wRound d1).Chal) (c2 : (wRound d2).Chal) (c3 : (wRound d3).Chal)
    (c4 : (wRound d4).Chal) (c5 : (wRound d5).Chal)
    (e1 : D 0 = (ckP .two).dr d1.entry d1.kind (GChal.old (b := d1.entry.work) c1))
    (e2 : D 1 = (ckP .two).dr d2.entry d2.kind (GChal.old (b := d2.entry.work) c2))
    (e3 : D 2 = (ckP .two).dr d3.entry d3.kind (GChal.old (b := d3.entry.work) c3))
    (e4 : D 3 = (ckP .two).dr d4.entry d4.kind (GChal.old (b := d4.entry.work) c4))
    (e5 : D 4 = (ckP .two).dr d5.entry d5.kind (GChal.old (b := d5.entry.work) c5))
    (hrs : rs.take 5 = lFront S t₀ X C D)
    (i1 : d1.items.filter (· != .root) = []) (i2 : d2.items.filter (· != .root) = [])
    (i3 : d3.items.filter (· != .root) = [.answer, .answer])
    (i4 : d4.items.filter (· != .root) = []) (i5 : d5.items.filter (· != .root) = [])
    (rec0 : ∀ ρ s, r.1.2 (ρ, s) =
      ∑ j, (recZ S.P.T.l lg n).mat r.1.1 s j * X.M₀ ρ ((S.ixR (recZ S.P.T.l lg n)).pl j))
    (rec1 : ∀ ρ s, r.2.2 (ρ, s) =
      ∑ j, (recZ S.P.T.l lg n).mat r.2.1 s j * X.M₁ ρ ((S.ixR (recZ S.P.T.l lg n)).pl j))
    (tab0 : (S.lkR (recZ S.P.T.l lg n)).tab y.1 =
      fun ρ => (S.ixR (recZ S.P.T.l lg n)).G.mulVec (X.M₀ ρ))
    (tab1 : (S.lkR (recZ S.P.T.l lg n)).tab y.2 =
      fun ρ => (S.ixR (recZ S.P.T.l lg n)).G.mulVec (X.M₁ ρ))
    (same : (S.lwR (recZ S.P.T.l lg n)).SameOn ((S.ixR (recZ S.P.T.l lg n)).view X.M₀)
      ((S.ixR (recZ S.P.T.l lg n)).view X.M₁))
    (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE) :
    (Slf.idf (E := GE) (J := (S.sg t₀).cIn.J)).Holds (stmG (S.sg t₀) row)
      (μOf (S.sg t₀) (firstPS S (lMem S X C D) tN φN ψN)) := by
  -- the five typed messages
  obtain ⟨m1, -, -, w1⟩ := rvW_onto d1 [] (by rw [i1]; rfl) default c1
  obtain ⟨m2, -, -, w2⟩ := rvW_onto d2 [] (by rw [i2]; rfl) default c2
  obtain ⟨m3, -, g3, w3⟩ := rvW_onto d3
    [.answer (ofE (smAt S t₀ (lSeed S D) (mu0 S t₀ (lMem S X C D)) false)),
      .answer (ofE (smAt S t₀ (lSeed S D) (mu0 S t₀ (lMem S X C D)) true))]
    (by rw [i3]; rfl) default c3
  obtain ⟨m4, -, -, w4⟩ := rvW_onto d4 [] (by rw [i4]; rfl) default c4
  obtain ⟨m5, -, -, w5⟩ := rvW_onto d5 [] (by rw [i5]; rfl) default c5
  rw [← e1] at w1
  rw [← e2] at w2
  rw [← e3] at w3
  rw [← e4] at w4
  rw [← e5] at w5
  -- the run's five rounds are these
  have hp := hR.pending
  change rs = _ at hp
  rw [hp] at hrs
  simp only [List.take_succ_cons, List.take_zero, lFront, List.cons.injEq, and_true] at hrs
  obtain ⟨a1, a2, a3, a4, a5⟩ := hrs
  -- the batching
  have hB := _root_.Desc.K15.batRan_at es' (es'.drop 1) d' rest (rest.drop 1) cols' x.group G' L θ
    row hG (_root_.Desc.K15.ran_fresh _ _ _ _ _ _ _ hR G' hG) hL hrow
  -- what the typed laws read is what the view shows
  have eγ : gVec S.P.v _ (valsOf d1 c1) = lGam S D := by
    rw [gVec_read d1 m1 c1, w1]
    rfl
  have eσ : gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2) = lSeed S D := by
    rw [gSeed_read_take d2 m2 c2, w2]
    rfl
  have h := front_holds S t₀ lg n Λ first further d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
    _ _ _ x DR G' L θ row hS hF hd hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hR hB (a1.trans w1.symm)
    (a2.trans w2.symm) (a3.trans w3.symm) (a4.trans w4.symm) (a5.trans w5.symm) hop
    (fun i hi => hR.bat_mask hB rdE i (Nat.lt_of_lt_of_le hi hZ)) hF.pow X.M₀ X.M₁
    (fun a j => if j = S.padJ then C.pad a else 0) rec0 rec1 tab0 tab1 same (by
      rw [eγ, eσ]
      exact g3)
  rw [eγ] at h
  rw [lMem, muOf_front]
  exact h

/-! ## At the full size -/

/-- What the link's five rounds send beside roots: off the one closed fact on all rounds. -/
theorem fr_frontItems :
    (frRd 0).items.filter (· != .root) = [] ∧ (frRd 1).items.filter (· != .root) = [] ∧
      (frRd 2).items.filter (· != .root) = [.answer, .answer] ∧
      (frRd 3).items.filter (· != .root) = [] ∧ (frRd 4).items.filter (· != .root) = [] := by
  have h := fr_sorts
  rw [dsFull_eq] at h
  simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The mask code's message is no longer than the link's layout counts places for it. -/
theorem fr_maskPlaces (x : TableKey × TableKey) :
    frS.P.Z.l ≤ 2 ^ ((linkLay frP.S (first frP.codes x).st).h +
      (linkLay frP.S (first frP.codes x).st).logEllZk) := by
  show frS.P.Z.l ≤ 2 ^ ((linkLay frP.S { codes := frP.codes, oracles := #[], groups := #[] }).h +
    (linkLay frP.S { codes := frP.codes, oracles := #[], groups := #[] }).logEllZk)
  decide +kernel

/-- **THE VALUES' HALF AT THE FIRST STAGE, AT THE FULL SIZE, AT A RUN's DRAWS**: whatever row the
batching combines behind the link's five rounds, the claim holds at the written state's message. -/
theorem front_at (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) (hM : Meant rr y M₀ M₁) (C : LCoins)
    (ρ : Rho (uL (ckP .two) dsFull)) (es es' : List Fmt.Entry) (d' : _root_.Desc.K15.St)
    (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn) (XR : LinkRun) (DR : LinkDataR)
    (hR : LinkRanR frP.S (keysOf rr).1 (keysOf rr).2
      (ctxOf es (first frP.codes (keysOf rr)) rs cols) (ctxOf es' d' rest cols') XR DR)
    (hrs : rs.take 5 = lFront frS 97 (linOf rr y M₀ M₁) C
      (Johnson.Prover.Link.drawsOf (drawnSL (ckP .two) dsFull ρ)))
    (hop : ∀ o ∈ cols,
      (o.1 = Fmt.storedKey 0 → storedOf frS.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf frS.P.T.a y 1 o.2.1 = some o.2.2))
    (G' : Group) (L : GroupLayout) (θ : E) (row : GroupRow)
    (hG : d'.st.groups[XR.group]? = some G') (hL : d'.st.layout XR.group = some L)
    (hrow : Bat.combine (begun d'.st XR.group G') XR.group ⟨L, runRows d'.st G'⟩ θ = some row) :
    (Slf.idf (E := GE) (J := (frS.sg 97).cIn.J)).Holds (stmG (frS.sg 97) row)
      (μOf (frS.sg 97) (lPS frP frS (linOf rr y M₀ M₁) C
        (Johnson.Prover.Link.drawsOf (drawnSL (ckP .two) dsFull ρ)))) := by
  obtain ⟨c1, e1⟩ := drawn_typed dsFull ρ 0 (frRd 0) (by rw [dsFull_eq]; rfl)
  obtain ⟨c2, e2⟩ := drawn_typed dsFull ρ 1 (frRd 1) (by rw [dsFull_eq]; rfl)
  obtain ⟨c3, e3⟩ := drawn_typed dsFull ρ 2 (frRd 2) (by rw [dsFull_eq]; rfl)
  obtain ⟨c4, e4⟩ := drawn_typed dsFull ρ 3 (frRd 3) (by rw [dsFull_eq]; rfl)
  obtain ⟨c5, e5⟩ := drawn_typed dsFull ρ 4 (frRd 4) (by rw [dsFull_eq]; rfl)
  obtain ⟨i1, i2, i3, i4, i5⟩ := fr_frontItems
  have hK := keyHas_written rr.1 rr.2 (frP.S.side false 1).index (frP.S.side true 1).index
    rfl fr_recordShape.2 fr_recordShape.1 rfl fr_recordShape.2 fr_recordShape.1
  exact front_of_view frS 97 29 1 frP.S (keysOf rr).1 (keysOf rr).2 (frRd 0) (frRd 1) (frRd 2)
    (frRd 3) (frRd 4) (frRd 5) es es' (first frP.codes (keysOf rr)) d' rs rest cols cols' XR DR G'
    L θ row fr_linkSizesR
    fr_linkFitR fr_batDrawsS rfl rfl rfl rfl fr_pads rr (fun _ _ => hK.1) (fun _ _ => hK.2) y hR
    hG hL hrow hop (fr_maskPlaces _) (linOf rr y M₀ M₁) C _ c1 c2 c3 c4 c5 e1 e2 e3 e4
    e5 hrs i1 i2 i3 i4 i5 hM.rec0 hM.rec1 hM.tab0 hM.tab1 hM.same _ _ _

end Johnson.Prover.Link
