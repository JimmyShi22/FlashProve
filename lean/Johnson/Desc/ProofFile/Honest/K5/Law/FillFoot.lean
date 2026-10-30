-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillFoot.lean: CONDITIONAL: WHAT THE KIND K5's JOINED LAWS TAKE
FROM "onlineProverFromPublicFiles RETURNS A", WITH THE FILLING A LETTER P. No filling is named. Five statements with
their proofs.

  lotLaid_fill · lotLaid_fill_head   the kind's lot is laid in A.H.first (LotLaid,
                      Honest/K5/Law/LotLaid.lean): of P its list of lots alone is read
  k5_lends_at_fill · k5_lends_paid_fill   the frame's Bool on the book's lending to the kind's row,
                      at A.B: of P nothing is read
  ready_trace_fill    at the frame's ReadyInput an input's trace is fullIn's: of P its trace alone
                      is read

The premises on the filling. hA: onlineProverFromPublicFiles returns A at P · hex: some lot of the filling's list has, at
A's public part and ground, the halves of K5's lot · ho: every lot of that list has there either no
half at a place of the kind K5, or these halves · hTr: P.trace = fullIn.trace. Beside these: hG: G
is the ground that is made of the head's public part · hg: g is below 12 · hPWA: at whatever
sendings bookWhole returns A.B, the pick at a plain member's parts is the wants' entries for them.
hex and ho feed atPure_first_find_kind (Honest/FirstFindKind.lean, of other authors).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That onlineProverFromPublicFiles returns at any filling is not proved here. hex, ho and hTr are
proved here at no filling. What a side does is not said. No property of a prover or a protocol is
claimed.
All limits of ReadyInput.lean hold: the condition reads the private input; its first clause bears
tests on the table's key; a law whose end states a distribution over rc or the seed may not lean on
it without more.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KeepsM
import Johnson.Desc.ProofFile.Honest.AtHeadGround
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.Desc.ProofFile.Honest.FirstFindKind
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfPick
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.Thread.ReplyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head)
open P5J (AtMgA TS CellsM)

/-! ## 1 The lot is laid -/

/-- **THE LOT OF THE KIND K5 IS LAID IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING THAT HOLDS IT.**
CONDITIONAL: hA; hex; ho. -/
theorem lotLaid_fill {W₀ Rc Tr X₀ X : Type} {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o' pol lay KL P = .ok A)
    {cells : Tr → Cells} {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK cells keyOf).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK cells keyOf).halves A.Z A.G) :
    LotLaid A.H.first (seatAtK keyOf A.Z A.G) cells A.G := by
  intro pl hk
  obtain ⟨M, hM, hMh⟩ := hex
  rw [← halves_k5LotK, ← hMh]
  cases hg : (M.halves A.Z A.G).find? (fun q => q.place == pl) with
  | some g =>
    exact atPure_first_find_kind hA hM
      (fun M' h' => (ho M' h').imp (fun e => by rw [hk]; exact e) (·.trans hMh.symm)) hg
  | none =>
    refine find_none_of_places fun y hy e => ?_
    rw [(atPure_ok hA).2.2.2.2.2.2.2.1] at hy
    obtain ⟨M', hM', hyM⟩ := List.mem_flatMap.1 hy
    rcases ho M' hM' with h1 | h2
    · exact h1 y hyM (by rw [e]; exact hk)
    · rw [h2, ← hMh] at hyM
      exact List.find?_eq_none.1 hg y hyM (beq_iff_eq.2 e)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

include h in
/-- **THE PREMISE hL OF THE KIND's JOINED LAW, IN ITS OWN LETTERS.** CONDITIONAL: under the
hypothesis h; G is the ground that is made of the head's public part; hA at the head's three files;
hex; ho, at the reader keyOfK3 of the key points. -/
theorem lotLaid_fill_head {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {cells : Tr → Cells}
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK cells keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK cells keyOfK3).halves A.Z A.G) :
    LotLaid A.H.first (seatAtK keyOfK3 Zp G) cells G := by
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have e := lotLaid_fill hA hex ho
  rw [eZ, eG] at e
  exact e

/-! ## 2 The book's lending: nothing of the filling is read -/

include h in
/-- **The frame's Bool on the lending, at the book of what onlineProverFromPublicFiles returns, from the pick.**
CONDITIONAL: hA; hPWA. -/
theorem k5_lends_at_fill {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hPWA : ∀ p0 p1 p2 : Johnson.G.ChainSends,
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2
        (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B →
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") →
      ∃ (idx : MsgAt) (a : List Want × Nat),
        ownerOf indexMaskRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
            .ok a ∧
        wantsFree (a.1 ++ (loneWants idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
          (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
            x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
        ∀ j, BookRow.pick ⟨b.place, j⟩ A.B.ahead =
          ((a.1 ++ (loneWants idx
            (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
            (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
              x.place.link.isNone).flatMap planParts) a.2).1).filter
                fun w => w.spender == ⟨b.place, j⟩).map (·.entry)) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow A.B 0 (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Row (seatOf keyOfK3 Zp A.G cF g a)) = true := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := (parts_of_atPure hA).1.book
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := (atPure_at_laid_ground h.laid hG hA).2.2
  rw [eF] at hB
  exact fun a ha => k5_lends_of_pick h hg hB (hPWA p0 p1 p2 hB) keyOfK3 A.G ha

include h in
/-- **The same with the pick paid.** CONDITIONAL: hA. -/
theorem k5_lends_paid_fill {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow A.B 0 (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Row (seatOf keyOfK3 Zp A.G cF g a)) = true :=
  k5_lends_at_fill h hg hA fun _ _ _ hB _ hb hF =>
    pick_whole hB (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) hb hF

/-! ## 3 The trace -/

include h in
/-- **At the frame's `ReadyInput` an input's trace is the one that `fullIn` makes.** CONDITIONAL:
hA; hTr: the filling's trace is `fullIn`'s. -/
theorem ready_trace_fill {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X}
    {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hTr : P.trace = fullIn.trace) :
    ∀ v, ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H v →
      fullIn.trace Zp v.w₀ v.x = some v.trace := by
  intro v hv
  have eZ : A.Z = Zp := Except.ok.inj ((parts_of_atPure hA).1.pub.symm.trans h.laid.pub)
  have h3 := hv.2.2
  rw [atPure_trace hA, eZ, hTr] at h3
  exact h3

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.lotLaid_fill
#print axioms ProofFile.Honest.K5.lotLaid_fill_head
#print axioms ProofFile.Honest.K5.k5_lends_at_fill
#print axioms ProofFile.Honest.K5.k5_lends_paid_fill
#print axioms ProofFile.Honest.K5.ready_trace_fill
