-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/SecondFourAtLast.lean: the linear claim's second part ("K14,
second part", the first member of a proof file's last chain): PlaysS, BehindS, ExchangeS AND
RidesPastS (Honest/Thread/PaysS.lean) AT THE MEMBER 0 OF THE LAST CHAIN's THREAD AT THE PROOF FILE's
OWN DESCRIPTION (lettersLast, Honest/Thread/LastHead.lean), at any prover H, at three letters laid:
the form is the library's closed test fillZ at the library's own parameters, read at the first
chain's own last state; keeps at the member's place is what the member has laid (kpSecond); order is
"the statement is in order".

  second_four_last    **the four**, general in the witness's type, the reading and the readers of
                      words: four calls of Honest/K14/SecondFour.lean
  second_four_open    **the four at the library's closed family of readers** (wordsLast, omWW, wvW,
                      OkW: Honest/K14/SecondWords.lean), where the witness's type is the library's
                      Wit and the letter ML is the library's closed sentence rowsOpen
                      (Johnson/LLT25R/LastRowsOpen.lean): hR, hOk and hRows are shown there

TWO LIMITS THAT A READER MUST KNOW FIRST (Honest/K14/SecondFour.lean's head has them at length).
(1) NEITHER THIS FILE NOR ANY FILE THAT IT IMPORTS SHOWS THE ITEMS ev AND dot, which ExchangeS takes
from the invariant in front of the
member. (2) BehindS AND ExchangeS HOLD VACUOUSLY WHEREVER fillZ's TEST AT BORDER 0 IS FALSE, and
neither this file nor any file that it imports evaluates that test at a state.

Why fillZ's reader of the first chain's state is laid and no letter. lettersLast lets the chain
begin at what the description's own start returns of the first chain's last state. At another reader
the form at border 0 and the chain's first state would speak of two different starts, and the
statements would hold for nothing.

WHAT STAYS A PREMISE. hR, hOk, hEv, hDot, hRows: five sentences that tie the letters Mg.ev, Mg.dot,
the witness and ML.rows to words in a field. hPin₁, hPin: a pin that holds at the tables at hand
still holds when rounds are added to them. hr, h₀, hst, hl: the clause of BehindS on the letter
rides, handed on to the caller. R, the own test's declared rounds, which fillZ reads at border 2
alone, every other letter of lettersLast, the prover, the book and `Said` are free.

What is not claimed. That any premise holds. That the thread's invariant holds at any state. The
fifth statement, AcceptedS: second_acceptedS_last (Honest/K14/SecondDoor.lean), under a premise of
its own. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondWords
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Place Chain Wit)
open VerifiableInference.Desc.Sound (MsgT wordsLast)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (RowsHold DotSem RowsThere Reads OkW omWW wvW reads_atWords)
open VerifiableInference.Desc.Last (fillZ MeaningL)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : MeaningL S₃ Wt) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (ProofFile.InstPub × P5J.TS) × St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → Nat) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr) (R : List Fmt.DeclaredRound)

/-- **PlaysS, BehindS, ExchangeS and RidesPastS at the member 0 of the last chain's thread at the
proof file's own description.** L stands for the letters, by the equation hL. BehindS and ExchangeS
hold vacuously wherever fillZ's test at border 0 is false; ExchangeS takes the items ev and dot from
the invariant in front. hR: the library's Reads, at every handed part. hOk: the fence holds on both
sides of a yes. hEv: ev gives that every open row of the own group in front holds. hDot: dot gives
the semantic (Dot). hRows: where fillZ's test at border 1 says yes, RowsThere gives the item rows.
hPin₁, hPin: a pin still holds when rounds are added. hr, h₀, hst, hl: on the letter rides. -/
theorem second_four_last
    {L : LastThread.Letters Bk St S₃ ProofFile.Cl W₀ Rc ProofFile.Inst Tr X (ProofFile.InstPub × P5J.TS) Wt}
    (hL : L = LastThread.lettersLast Zp Np cF H N Mg ML
      (fillZ (ToldDesc.p14At Zp) R fun q => q.2)
      (fun s => OnBytes.Means.InOrder s.st) taken ends wit table fixed item n₁ n₂ Vd Rd
      (kpSecond (ToldDesc.p14At Zp) Kp) w)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (words : S₃ → Wt → Words K)
    (Ok : (ProofFile.InstPub × P5J.TS) × St → S₃ → S₃ → Prop)
    (omW wv : (ProofFile.InstPub × P5J.TS) × St → Wt → Nat → K)
    (hR : ∀ u, Reads (ToldDesc.p14At Zp) (Ok u) words (omW u) (wv u))
    (hOk : ∀ a e s s', (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 0 a e s = true →
      (∃ rs gs, (batchLinearConstraintsSecondPart (ToldDesc.p14At Zp) : Block S₃ ProofFile.Cl).decide s rs gs = .ok s') →
      Ok (a, e) s s')
    (hEv : ∀ inp a e s y v, (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 0 a e s = true →
      (Mg inp).ev a y v → RowsHold ρ s (words s v))
    (hDot : ∀ inp a e s y v, (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 0 a e s = true →
      (Mg inp).dot a e y v → DotSem ρ (ToldDesc.p14At Zp) (omW (a, e)) (wv (a, e)) s v)
    (hRows : ∀ (a : ProofFile.InstPub × P5J.TS) e s' v,
      (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 1 a e s' = true →
      RowsThere ρ s' (words s' v) → ML.rows s' v)
    (hPin₁ : ∀ inp a b q E ps v, (Mg inp).pin₁ a b q (L.thread.strs E) v →
      (Mg inp).pin₁ a b q (L.thread.strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v, (Mg inp).pin a b e (L.thread.strs E) v →
      (Mg inp).pin a b e (L.thread.strs (E.add ps)) v)
    {R₀ : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop}
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s)
    (h₀ : ∀ blk, L.thread.bs[0]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said 0 k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (0 + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ 0 → 0 + 1 ≤ c.hi → StaysBy L.thread 0 c)
    (hl : ∀ c ∈ cs, c.lo = 0 + 1 → LaysAtS L.thread Said 0 c) :
    PlaysS L.thread Said 0 ∧ BehindS L.thread Said 0 ∧ ExchangeS L.thread Said 0 ∧
      RidesPastS L.thread Said 0 := by
  subst hL
  refine ⟨second_playsS _ Said (first_of_last Zp Np cF) rfl rfl,
    second_behindS _ (ToldDesc.p14At Zp) R (fun q => q.2) Said rfl
      (fun blk hb => like_at_last Zp Np cF blk hb) ?_
      (fun x e s' h => inOrder_of_form _ R (fun q => q.2) x e s' h) hr h₀ hst hl,
    second_exchangeS _ (ToldDesc.p14At Zp) R (fun q => q.2) Said ρ words Ok omW wv rfl
      (fun blk hb => like_at_last Zp Np cF blk hb) hR hOk hEv hDot hRows,
    second_ridesPastS _ Said hPin₁ hPin⟩
  intro s s' hL q hq
  obtain rfl : (⟨3, none, 0, .K14⟩ : Place) = q := Option.some.inj hq
  show (if (⟨3, none, 0, .K14⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
  rw [if_pos rfl]
  exact hL

/-- **The four at the library's closed family of readers, where the letter ML is rowsOpen.** L
stands for the letters, by the equation hL. BehindS and ExchangeS hold vacuously wherever fillZ's
test at border 0 is false; ExchangeS takes the items ev and dot from the invariant in front. hEv: ev
gives that every open row of the own group in front holds of wordsLast's words. hDot: dot gives the
semantic (Dot) at Omega's and W's readers. hPin₁, hPin: a pin still holds when rounds are added. hr,
h₀, hst, hl: on the letter rides. -/
theorem second_four_open {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)
    (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS St (ProofFile.InstPub × P5J.TS) (Wit Cells Tok MsgT))
    (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wit Cells Tok MsgT)
    {L : LastThread.Letters Bk St S₃ ProofFile.Cl W₀ Rc ProofFile.Inst Tr X (ProofFile.InstPub × P5J.TS)
      (Wit Cells Tok MsgT)}
    (hL : L = LastThread.lettersLast Zp Np cF H N Mg
      ⟨LLT25.rowsOpen (ToldDesc.p14At Zp).codes arr t₁ t₂⟩
      (fillZ (ToldDesc.p14At Zp) R fun q => q.2)
      (fun s => OnBytes.Means.InOrder s.st) taken ends wit table fixed item n₁ n₂ Vd Rd
      (kpSecond (ToldDesc.p14At Zp) Kp) w)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hEv : ∀ inp a e s y v, (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 0 a e s = true →
      (Mg inp).ev a y v → RowsHold OnBytes.Model.Reading.gl s (wordsLast arr t₁ t₂ s v))
    (hDot : ∀ inp a e s y v, (fillZ (ToldDesc.p14At Zp) R fun q => q.2).shape 0 a e s = true →
      (Mg inp).dot a e y v → DotSem OnBytes.Model.Reading.gl (ToldDesc.p14At Zp)
        (omWW arr t₁ (ToldDesc.p14At Zp) (fun q => q.2) (a.1, a.2, e))
        (wvW arr (ToldDesc.p14At Zp) (fun q => q.2) a) s v)
    (hPin₁ : ∀ inp a b q E ps v, (Mg inp).pin₁ a b q (L.thread.strs E) v →
      (Mg inp).pin₁ a b q (L.thread.strs (E.add ps)) v)
    (hPin : ∀ inp a b e E ps v, (Mg inp).pin a b e (L.thread.strs E) v →
      (Mg inp).pin a b e (L.thread.strs (E.add ps)) v)
    {R₀ : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop}
    {cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) S₃)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s)
    (h₀ : ∀ blk, L.thread.bs[0]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said 0 k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (0 + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ 0 → 0 + 1 ≤ c.hi → StaysBy L.thread 0 c)
    (hl : ∀ c ∈ cs, c.lo = 0 + 1 → LaysAtS L.thread Said 0 c) :
    PlaysS L.thread Said 0 ∧ BehindS L.thread Said 0 ∧ ExchangeS L.thread Said 0 ∧
      RidesPastS L.thread Said 0 :=
  second_four_last Zp Np cF H N Mg _ taken ends wit table fixed item n₁ n₂ Vd Rd Kp w R hL Said
    OnBytes.Model.Reading.gl (wordsLast arr t₁ t₂)
    (fun u => OkW (fun q => q.2) (u.1.1, u.1.2, u.2))
    (fun u => omWW arr t₁ (ToldDesc.p14At Zp) (fun q => q.2) (u.1.1, u.1.2, u.2))
    (fun u => wvW arr (ToldDesc.p14At Zp) (fun q => q.2) u.1)
    (fun u => reads_atWords arr t₁ t₂ (ToldDesc.p14At Zp) (fun q => q.2) (u.1.1, u.1.2, u.2))
    (fun _ _ _ _ h hy => fence_of_fillZ h hy) hEv hDot
    (fun _ _ _ v h1 h => rowsOpen_of_there (ToldDesc.p14At Zp) R (fun q => q.2) arr t₁ t₂ h1 v h)
    hPin₁ hPin hr h₀ hst hl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.second_four_last
#print axioms ProofFile.Honest.K14.second_four_open
