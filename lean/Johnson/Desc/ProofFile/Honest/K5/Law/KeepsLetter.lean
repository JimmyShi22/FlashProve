-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeepsLetter.lean: THE FIVE SENTENCES THAT A KIND OWES AT A
NUMBER OF THE FIRST CHAIN's THREAD (`Plays`, `Behind`, `Exchange`, `RidesPast`, `Accepted`,
Honest/Thread/Pays.lean), CARRIED FROM ONE VALUE OF THE LETTER Kp OF `lettersHead`
(Honest/Thread/FirstHead.lean) TO ANOTHER. Kp fills the thread's field keeps, by that field's own
words "what the sub-protocol after a border leaves unchanged in the verifier's state". Seven
theorems; no definition. General in the number: no kind is named.

  `plays_at_any_kp`, `exchange_at_any_kp`, `accepted_at_any_kp`, `exchangeAtS_at_any_kp`
        the same sentence at every Kp: no premise
  `ridesPast_kp_of`   from Kp to Kp', if at the number's place, under the invariant in front, Kp'
        gives Kp
  `behind_kp_of`      from Kp to Kp', if at the number's place Kp, with the invariant in front, the
        step, the form behind the step and the riders behind it, gives Kp'
  `five_kp_of`        the five together, under both

What it is for. A law that has the five at one Kp, fixed by an equation, can be called where the
letter is laid at a richer clause: what the richer clause adds is asked where `Behind` has to pay
it, and dropped where `RidesPast` spends it.

Why it is so. Kp enters this thread through the one field keeps. Of the five sentences `Behind`
reads that field in its end's third part and `RidesPast` in a premise; at this thread the invariant
in front of the step (`Thr`), the step, the items and their meaning do not read it.

Limits. Transports: each takes the sentence at one letter as a premise and shows it of none. Each of
the five is an implication from the invariant in front of the step: where no state meets that, it
says nothing at either letter. The first chain's thread under the library's head alone, at the
format's second hash function: h is typed there. Through its imports the file stands above the library's
folder ThirdParty/.
NOT IN FRONT OF A LAW OVER COINS: the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. The label goes over with the sentence that is carried. This
file's ground: of the first kind, the run's coins k, the state s, the mid-run m and the strings E
under the invariant Thr, in each of the five and in hS and hP; the bar is flat.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp Kp' : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`Plays` is the same sentence at every Kp.** No premise but the sentence. -/
theorem plays_at_any_kp {b : Nat}
    (e : Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) :
    Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b :=
  e

/-- **`Exchange` is the same sentence at every Kp.** No premise but the sentence. -/
theorem exchange_at_any_kp {b : Nat}
    (e : Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) :
    Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b :=
  e

/-- **`Accepted` is the same sentence at every Kp.** No premise but the sentence. -/
theorem accepted_at_any_kp {fall : Nat → TS → List Fmt.Drawn → Option String} {b : Nat}
    (e : Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread fall b) :
    Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread fall b :=
  e

/-- **"This item is exchanged at this number", from the pair `ThrS`, is the same sentence at every
Kp.** No premise but the sentence. The items' type is written with its whole name. -/
theorem exchangeAtS_at_any_kp (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {j : VerifiableInference.Desc.First.Item}
    (e : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b
      j) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b j :=
  e

/-- **`RidesPast` goes from Kp to Kp' if at the number's place, under the invariant in front, Kp' gives
Kp.** hS: that implication. -/
theorem ridesPast_kp_of {b : Nat}
    (hS : ∀ p, P5J.At.ps[b]? = some p → ∀ k s m E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b k s m E →
      Kp' p s s' → Kp p s s')
    (e : RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) :
    RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b :=
  fun k s m E s' ps i v hT hk hi h1 h2 hm =>
    e k s m E s' ps i v hT (fun p hp => hS p hp k s m E s' hT (hk p hp)) hi h1 h2 hm

/-- **`Behind` goes from Kp to Kp' if at the number's place Kp, with the invariant in front, the step, the
form behind the step and the riders behind it, gives Kp'.** hP: that implication; the form is the
thread's clause `Thread.Form` at the border behind, which `Behind` has in its end's first part. -/
theorem behind_kp_of {b : Nat}
    (hP : ∀ p, P5J.At.ps[b]? = some p → ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.Form (b + 1) k s' y.2 →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.rides (b + 1) y.2.st.input s' →
      Kp p s s' → Kp' p s s')
    (e : Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) :
    Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b :=
  fun blk hblk k s m E ds y cols s' hT hd hSt =>
    have q := e blk hblk k s m E ds y cols s' hT hd hSt
    ⟨q.1, q.2.1, fun p hp => hP p hp blk hblk k s m E ds y cols s' hT hd hSt q.1 q.2.1 (q.2.2 p hp)⟩

/-- **The five together go from Kp to Kp'** under hS and hP. -/
theorem five_kp_of {b : Nat}
    (hS : ∀ p, P5J.At.ps[b]? = some p → ∀ k s m E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b k s m E →
      Kp' p s s' → Kp p s s')
    (hP : ∀ p, P5J.At.ps[b]? = some p → ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.Form (b + 1) k s' y.2 →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.rides (b + 1) y.2.st.input s' →
      Kp p s s' → Kp' p s s')
    (e : (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread fall b) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread fall b :=
  ⟨⟨plays_at_any_kp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Kp' w e.1.1,
      behind_kp_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Kp' w hP e.1.2.1,
      exchange_at_any_kp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Kp' w e.1.2.2.1,
      ridesPast_kp_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Kp' w hS e.1.2.2.2⟩,
    fun fall => accepted_at_any_kp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Kp' w (e.2 fall)⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.plays_at_any_kp
#print axioms ProofFile.Honest.K5.exchange_at_any_kp
#print axioms ProofFile.Honest.K5.accepted_at_any_kp
#print axioms ProofFile.Honest.K5.exchangeAtS_at_any_kp
#print axioms ProofFile.Honest.K5.ridesPast_kp_of
#print axioms ProofFile.Honest.K5.behind_kp_of
#print axioms ProofFile.Honest.K5.five_kp_of
