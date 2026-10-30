-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K4AtFront.lean: AT EVERY STATE REACHED IN FRONT OF A LAYERS' LINK's
BATCHING, WHOSE LEDGER IS OPEN AND HAS ITS SIZES: K4's OWN HEARING's EQUATION, WITH WHAT THE LEMMAS
ON THAT HEARING ASK IN FRONT OF IT. Theorems: joins of other files' lemmas.

Why. Four clauses of a layers' link's Ok (OkOne.lean: front, back, entsFront, entsBack) speak of
what K4's hearing returned. The lemmas that have them (Johnson/Road/K4/Slots/,
Johnson/Road/K4/Reads/) take the hearing's equation, the sizes of the ledger in front of it, and
that the forms which the lookup on the calls left name filled slots (`PadNames`). This file has all
three from a state four sub-protocols further on.
  `theStated_yes_calls`: a yes of `K3.theStated`'s value at the calls' address, its test on the plan
    passed, is a yes of `K3.block (seatCalls claim) ..`: the step without a round behind it
    (`quietLook`) leaves the state. The sister of `theStated_yes_digits`
    (Johnson/Desc/First/Look/K3DigitsSeatedYes.lean). `piece_at_calls`: the address's piece is the
    calls'.
  `padNames_behind_calls`: such a yes from s to c, c's ledger G with its sizes: c has heard some fo
    at the calls' seat, and `PadNames fo G`. By `decide_named` (Johnson/Top/H/Keep/K3Named.lean);
    the sizes in front by `decide_sizedBack` (Johnson/Top/H/Keep/PadSizes.lean).
  `k4_heard_at_front`: **the root lemma.** One walk from 28 g + 9 back to 28 g + 5
    (`laterSized_layers`, SizesDigits.lean, at `SameOwn`, OwnStay.lean); K4's step to 28 g + 4
    (`IM.k4_of`, `kept_atS`, `k4_sizesS`); the calls' step to 28 g + 3 (`IM.k3_of`).
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; hB: the ledger at the state is open and has its sizes.
Limits. hp, hB are shown of nothing here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SizesDigits
import Johnson.Desc.First.Link.Law.FlSizes
import Johnson.Desc.First.Link.Law.OwnStay
import Johnson.IMR.K4Seat
import Johnson.Top.H.Keep.K3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.OnPublicFiles (pieceAt_neD decide_named decide_sizedBack seatCalls_keeps)
open OnBytes.Desc.First.K4 (hearFl)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (reach_pred kept_atS)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open _root_.Fo.Tp (PadNames)

/-- **What a yes of the seated block is, at the calls' address.** -/
theorem theStated_yes_calls {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i false) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) :
    ∃ P sent laid n gs', placeAt X i false = some P ∧
      (K3.block (K3.seatCalls claim) a.piece laid sent P []).decide s (rs.take n) gs' = .ok c := by
  obtain ⟨B₁, hB₁, -, e2, -, e4⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', hP, -, -, -, r2, -, hpl⟩ :=
    K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | true => exact absurd (hpc.symm.trans hpc') (pieceAt_neD X i)
  | false =>
    rw [e2] at hd
    rw [e4] at hOk
    rcases hW with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
    · rw [r2] at hd
      refine ⟨P, sent, laid, rs.length, gs, hP, ?_⟩
      rw [List.take_length]
      exact K3.Law.blockVia_decide (hpl hOk) hd
    · have hOk' : b.planOk = true := by
        have h0 : (b.planOk && true) = true := hOk
        simpa using h0
      have hd' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
          (fun s' => f s') = .ok c := hd
      cases hb' : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
      | error e =>
        rw [hb'] at hd'
        cases hd'
      | ok s' =>
        rw [hb'] at hd'
        rw [r2] at hb'
        have hne : (K3.pieceAt X i false == K3.pieceAt X i true) = false := by
          simpa using pieceAt_neD X i
        have hf' : K3.quietAt X i false = some f := by
          rw [hi, hpc] at hf
          simpa [hne] using hf
        have hc : c = s' := by
          have hd2 : f s' = .ok c := hd'
          unfold K3.quietAt at hf'
          simp only [Bool.false_eq_true, if_false] at hf'
          repeat' split at hf'
          all_goals first
            | (obtain rfl := Option.some.inj hf'
               exact (K3.quietLook_ok _ s' c hd2).1)
            | cases hf'
        subst hc
        exact ⟨P, sent, laid, _, _, hP, K3.Law.blockVia_decide (hpl hOk') hb'⟩

/-- The address's piece is the calls'. -/
theorem piece_at_calls {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (i : ℕ) (hi : a.link = some i)
    (h3 : a.piece ≤ 3) : a.piece = K3.pieceAt X i false := by
  obtain ⟨B₁, hB₁, -⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, -⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', -⟩ := K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | false => exact hpc'
  | true =>
    exfalso
    unfold K3.pieceAt at hpc'
    split at hpc' <;> simp at hpc' <;> omega

/-- Where nothing was heard yet, the hearing lays its value in the field that K4's hearing reads. -/
theorem fo_of_hearLook (s : S) (g : Forest.Heard) (hn : s.lookHeard? = none) {a : First.LayOwn}
    (ha : (s.hearLook g).here = .lay a) : a.fo = some g := by
  have hm : ∀ n, (s.mark n).here = s.here := fun n => by
    unfold S.mark
    split <;> rfl
  cases hh : s.here with
  | lay a0 =>
    have h0 : a0.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    have e : s.hearLook g =
        { s with here := .lay { a0 with fo := some g, lookHeard := some g } } := by
      simp [S.hearLook, hh, h0]
    rw [e] at ha
    obtain rfl := First.Here.lay.inj ha
    rfl
  | att a0 =>
    exfalso
    simp only [S.hearLook, hh] at ha
    split at ha
    · rw [hm, hh] at ha
      cases ha
    · cases ha
  | head a0 =>
    exfalso
    simp only [S.hearLook, hh] at ha
    split at ha
    · rw [hm, hh] at ha
      cases ha
    · split at ha
      · rw [hm, hh] at ha
        cases ha
      · cases ha
  | between =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha
  | fin _ =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha
  | mem _ =>
    exfalso
    simp only [S.hearLook, hh] at ha
    rw [hm, hh] at ha
    cases ha

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE CALLS.** -/
theorem padNames_behind_calls {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i false) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) {G : Fork}
    (hG : c.fork? = some G) (hz : Sized G) :
    ∃ fo, c.lookHeard? = some fo ∧ PadNames fo G ∧ ∀ a, c.here = .lay a → a.fo = some fo := by
  obtain ⟨P', sent, laid, n, gs', -, hyes⟩ :=
    theStated_yes_calls claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨F, y, hF, hn, e, hN⟩ :=
    decide_named (K3.seatCalls claim) a.piece laid sent P' [] s c _ gs' hyes
  obtain ⟨F', y', hF', e', hb⟩ :=
    decide_sizedBack (K3.seatCalls claim) a.piece laid sent P' [] s c _ gs' hyes
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  have hsome : ((K3.seatCalls claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have k1 : c.fork? = some y.2 := by
    rw [e]
    exact seatCalls_keeps claim _ _ _ hsome hn
  have k2 : c.fork? = some y'.2 := by
    rw [e']
    exact seatCalls_keeps claim _ _ _ hsome hn
  obtain rfl : y.2 = G := Option.some.inj (k1.symm.trans hG)
  have hzF : Sized F := hb (by rw [← Option.some.inj (k1.symm.trans k2)]; exact hz)
  refine ⟨y.1, ?_, hN hzF, fun a ha => ?_⟩
  · rw [e]
    exact K3.seatCalls_reads claim _ _ _ hsome hn
  · rw [e] at ha
    exact fo_of_hearLook (s.putFork y.2) y.1 ((S.look_putFork s y.2).trans hn) ha

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **THE ROOT LEMMA OF THE LAYERS' FOUR CLAUSES.** -/
theorem k4_heard_at_front (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ (x : Bool × OnBytes.Desc.First.K4.Par) (tokv : _) (fo : Forest.Heard) (F₄ : Fork) (o : Own)
      (G F' : Fork) (t u : Tape),
      x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none ∧ x.2.g = g ∧
      x.2.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[g]? = some x.2.hp ∧
      hearFl { x.2.P with tokv := tokv } x.2.hp x.2.g fo F₄ t = some (o, G, u) ∧ Sized F₄ ∧
      PadNames fo F₄ ∧ o.H.fo = fo ∧ s'.own? = some o ∧ s'.fork? = some F' ∧
      PscRun.Later G F' ∧ Sized F' := by
  -- the walk
  obtain ⟨s₅, F₅, F', r5, hF5, hz5, hF', hl, hown⟩ := laterSized_layers
    (walk_of_stretch sameOwn_stretch quietLayers_sameOwn) hS hR O hp hg h hB
  -- K4's step
  obtain ⟨Lk, b, x, e1, e2, hx, hla, -, a2, a3, a4, -⟩ := IM.k4_of hS hR O g hg
  obtain ⟨z', s₄, s'', b₀, e, r4, hb, hy⟩ := reach_pred (k := 28 * g + 4) r5
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[28 * g + 4]? = some b := by
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2] at k
    rw [show 28 * g + 4 = 14 * (2 * g) + 2 + 2 by omega]
    exact k
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.k4_yes hla s₄ _ rs gs).1 hd).1
  obtain ⟨a, fo, o, G, ha, hfo, hG, -, ho, -, -, -, -, hofo, -, t, u, hh⟩ := kept_atS hd'
  obtain rfl : G = F₅ := Option.some.inj (hG.symm.trans hF5)
  have h4 : s₄.fork? = some a.F := by simp [S.fork?, ha]
  obtain ⟨G₄, hG₄, hz₄⟩ := (k4_sizesS _ s₄ rs gs _ hd').pulls ⟨G, hF5, hz5⟩
  obtain rfl : G₄ = a.F := Option.some.inj (hG₄.symm.trans h4)
  -- the calls' step
  obtain ⟨Lk', b₃, b', f1, f2, f3, f4⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have i3 : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  obtain ⟨z₃, s₃, s₃', c₀, e', r3, hb3, hy3⟩ := reach_pred (k := 28 * g + 3) r4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  have hf3 : c.blocksInOrder[28 * g + 3]? = some b₃ := by
    have k := IM.hear_at_flat f1 f2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) (IM.k3Ix (2 * g) false), i3] at k
    rw [show 28 * g + 3 = 14 * (2 * g) + 1 + 2 by omega]
    exact k
  obtain rfl : b₃ = c₀ := Option.some.inj (hf3.symm.trans hb3)
  obtain ⟨rs3, gs3, hd3⟩ := stepYes_decide hy3
  have hd3' := ((IM.yes_alone f4 (fun h => nomatch h) s₃ _ rs3 gs3).1 hd3).1
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk f4]
    exact hp b₃ (List.mem_of_getElem? hf3)
  have hp3 : (IM.k3Place (2 * g) false).piece ≤ 3 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) + 1 ≤ 3
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    decide
  obtain ⟨fo', -, hN, hlay⟩ := padNames_behind_calls _ _ _ _ _ _ b' f3 hOk (2 * g) rfl
    (piece_at_calls _ _ _ _ _ _ b' f3 (2 * g) rfl hp3) s₃ _ rs3 gs3 hd3' h4 hz₄
  obtain rfl : fo' = fo := Option.some.inj ((hlay a ha).symm.trans hfo)
  exact ⟨x, _, fo', a.F, o, G, F', t, u, hx, a2, a3, a4, hh, hz₄, hN, hofo, hown.trans ho, hF', hl,
    hl.sized hz5⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.theStated_yes_calls
#print axioms VerifiableInference.Desc.LinkJoin.piece_at_calls
#print axioms VerifiableInference.Desc.LinkJoin.fo_of_hearLook
#print axioms VerifiableInference.Desc.LinkJoin.padNames_behind_calls
#print axioms VerifiableInference.Desc.LinkJoin.k4_heard_at_front
