-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SmpShared.lean: **A FILLING OF THE LETTER smp₂ ON THE SHARED CHAIN, AND THAT EVERY BLOCK LEAVES IT AT THE OLDER MESSAGES.** (smp₂: Johnson/Desc/Sound/BordersSharedFill.lean:
meaningSigS | promSigS | extS.) One definition; statements and proofs.

THE READING IS NOT NEW: it is K1's smpAt (Johnson/Desc/K1/Law/GoodSendForms.lean): the first sample row that the statement holds of a message, read as a linear form on the
library's typed message, with its target; a seed whose matrix is that form, by choice. At it K1's law of a sending EARNS "no collision" (send_gives_smpAt), and where the rows are the kind's one
row at a seed its seed has that seed's sample map (smpAt_of): the form in which tuple_of_port (Johnson/Desc/Sound/CandMove.lean) asks for the sample.
  smpSt cs oNo stOf      **the filling**: smp₂ d s i := K1.smpAt cs (s.l.get i).1 (s.l.get i).2 (stOf d) (oNo ⟨s, i⟩). oNo: A LETTER OF THE PLAN: the member's number in the chain's statement.
  smpAt_congr            K1's smpAt reads of the statement, at the number o, smpPart alone (in truth the sample rows alone).
  smpSt_keeps            so KeepsSmp (Johnson/Desc/Sound/SamplesAtK14.lean) leaves the filling at every member whose number is a message of the record in front.
  smpSt_k14              K14's eight blocks.    smpSt_onGu · smpSt_onGomega   the two proximity tests (at the first: but for the mask handed in).
  smpSt_none             A CONTROL: at a member whose number is no message of the record: nothing.
Limits. oNo IS TIED TO THE SEAT (which tree, which tenant) BY NOTHING HERE. ONE ANSWER A MESSAGE (K1's own limit). At the chain's own record. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.Sound.SamplesAtK14
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack Cb
open VerifiableInference.Desc.K12.Coin (smpPart)
open _root_.Desc.K14.Law.Fence (KeepsSmp keepsSmp_k14)

/-- K1's reading of a sample reads, at the number o, smpPart alone. -/
theorem smpAt_congr (cs : Codes) (s : OracleShape) (e : ℕ) (St St' : Statement) (o : ℕ)
    (hp : (St'.oracles[o]?).map smpPart = (St.oracles[o]?).map smpPart) :
    K1.smpAt cs s e St' o = K1.smpAt cs s e St o := by
  have hr : (St'.oracles[o]?).map (·.sampleRows) = (St.oracles[o]?).map (·.sampleRows) := by
    have := congrArg (Option.map fun q : OracleShape × Bool × Array OnBytes.Row => q.2.2) hp
    rwa [Option.map_map, Option.map_map] at this
  have hf : K1.formsAt cs s St' o = K1.formsAt cs s St o := by
    unfold K1.formsAt
    cases hx : St.oracles[o]? with
    | none =>
      rw [hx] at hr
      cases hx' : St'.oracles[o]? with
      | none => rfl
      | some x' =>
        rw [hx'] at hr
        cases hr
    | some x =>
      rw [hx] at hr
      cases hx' : St'.oracles[o]? with
      | none =>
        rw [hx'] at hr
        cases hr
      | some x' =>
        rw [hx'] at hr
        have e' : x'.sampleRows = x.sampleRows := Option.some.inj hr
        simp only [Option.bind_some]
        rw [e']
  have ha : K1.ansAt St' o = K1.ansAt St o := by
    unfold K1.ansAt
    cases hx : St.oracles[o]? with
    | none =>
      rw [hx] at hr
      cases hx' : St'.oracles[o]? with
      | none => rfl
      | some x' =>
        rw [hx'] at hr
        cases hr
    | some x =>
      rw [hx] at hr
      cases hx' : St'.oracles[o]? with
      | none =>
        rw [hx'] at hr
        cases hr
      | some x' =>
        rw [hx'] at hr
        have e' : x'.sampleRows = x.sampleRows := Option.some.inj hr
        simp only [Option.bind_some]
        rw [e']
  unfold K1.smpAt
  simp only [hf, ha]

/-- **THE FILLING OF smp₂.** oNo: the member's number in the chain's statement, by the plan. -/
def smpSt {S₂ : Type} (cs : Codes) (oNo : Mem → ℕ) (stOf : S₂ → Statement) :
    S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp :=
  fun d s i => K1.smpAt cs (s.l.get i).1 (s.l.get i).2 (stOf d) (oNo ⟨s, i⟩)

abbrev stSh : _root_.Desc.K14.St → Statement := fun e => e.st

/-- A block that keeps the samples leaves the filling. -/
theorem smpSt_keeps (cs : Codes) (oNo : Mem → ℕ) (d d' : _root_.Desc.K14.St) (h : KeepsSmp d d')
    (x : Mem) (ho : oNo x < d.st.oracles.size) :
    smpSt cs oNo stSh d' x.1 x.2 = smpSt cs oNo stSh d x.1 x.2 :=
  smpAt_congr cs _ _ d.st d'.st _ (h.2.2 _ ho)

/-- **K14's eight blocks.** -/
theorem smpSt_k14 (cs : Codes) (oNo : Mem → ℕ) (P : _root_.Desc.K14.P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
    (hbl : _root_.Desc.K14.blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (b : Block _root_.Desc.K14.St Unit) (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8])
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : b.decide d rs gs = .ok d') (x : Mem) (ho : oNo x < d.st.oracles.size) :
    smpSt cs oNo stSh d' x.1 x.2 = smpSt cs oNo stSh d x.1 x.2 :=
  smpSt_keeps cs oNo d d' (keepsSmp_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d d' rs gs h) x ho

open VerifiableInference.Desc.K12 in
/-- **The test on G_u.** -/
theorem smpSt_onGu (cs : Codes) (oNo : Mem → ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d') (x : Mem)
    (ho : oNo x < d.st.oracles.size) (hm : d.loc.firstMask ≠ some (oNo x)) :
    smpSt cs oNo stSh d' x.1 x.2 = smpSt cs oNo stSh d x.1 x.2 := by
  obtain ⟨_, b, _⟩ := VerifiableInference.Desc.K12.Coin.onGu_leaves p he ha d d' rs gs h
  exact smpAt_congr cs _ _ d.st d'.st _ (b _ ho hm)

open VerifiableInference.Desc.K12 in
/-- **The test on G_omega.** -/
theorem smpSt_onGomega (cs : Codes) (oNo : Mem → ℕ) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d') (x : Mem)
    (ho : oNo x < d.st.oracles.size) :
    smpSt cs oNo stSh d' x.1 x.2 = smpSt cs oNo stSh d x.1 x.2 := by
  obtain ⟨_, b, _⟩ := VerifiableInference.Desc.K12.Coin.onGomega_leaves p he ha d d' rs gs h
  exact smpAt_congr cs _ _ d.st d'.st _ (b _ ho)

/-- A control: at a member whose number is no message of the record: nothing. -/
theorem smpSt_none (cs : Codes) (oNo : Mem → ℕ) (d : _root_.Desc.K14.St) (x : Mem)
    (h : d.st.oracles.size ≤ oNo x) : smpSt cs oNo stSh d x.1 x.2 = none :=
  K1.smpAt_none cs _ _ d.st _ (Array.getElem?_eq_none h)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.smpAt_congr
#print axioms VerifiableInference.Desc.Sound.smpSt_k14
#print axioms VerifiableInference.Desc.Sound.smpSt_onGu
#print axioms VerifiableInference.Desc.Sound.smpSt_onGomega
#print axioms VerifiableInference.Desc.Sound.smpSt_none
