-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ExchangeAtFirst.lean: the smallness test's items at the first thread itself: the items
that the draw's row owes and that are not open in front, at a return of the maker whose script is the
join of a senders' record. What the thread's values pay: the head, the opening, the prover, the book,
the ground, the keeps, the riders, the falls, ReadyInput, and the debt «behind» (k8_behindS). What
stays named: what is written in each of the premises below.

  k8_exchange_first   ExchangeAtS at firstThread, at each of the 25 draws

Premises that stay: hA, that the return is onlineProverFromPublicFiles's at a filling P · hlot, that the record's rows are
K1's lot · hO, that the other senders are the code switches and the proximity test · hT, ReadyLaws ·
hex, ho, that the filling holds the kind's one lot · hR, that the record's reader gives the input's
trace · hD, that an accepted start reads light · hOk, that what is said is below the prime.

Limits. The pins that the row owes are exempted here as in k8_exchange_by_kind. That a stand exists is
not shown.
-/
import AtFullSide.K8.ExchangeAtFill
import AtFullSide.K8.KeepsBehind
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest
open ProofFile.Honest.K8
open ProofFile.Honest.FirstThread
open VerifiableInference.Desc.K2.Honest (carryExact)

variable {W₀ Rc X₀ X X₂ : Type} {files : VerifierAndGoals.PublicFiles} {P : OnlineProverParts W₀ Rc Cells X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}

/-- **The items that the draw's row owes, at the first thread.** -/
theorem k8_exchange_first (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (hT : ReadyLaws h.description A) (parts : FirstThreadParts A) (r : SendersRecord A ProofFile.Inst)
    (hq : parts.script = SendersRecord.script h r) (hlot : r.lotData = K1.lotData Sz.ref)
    (w : Local W₀ Rc ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Cells)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Cells) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Cells → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Cells))
    (hO : r.others = (K2.switchShareAt A.B h.firstChain.blocksInOrder 0 A.Z (seatGround A)
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) A.Z (seatGround A))
        (fun v => (r.reader v).R) rest).add
      (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr A.Z) ok codes sh sh₁ 354 rest₂))
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G =
      (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K8) ∨
      M.halves A.Z A.G = (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
    (hR : ∀ v, v = w ∧ ReadyInput h.description A.H v → (r.reader v).R.cells = v.trace)
    (hD : ∀ ξ, h.description.okStart ξ = true → K2.Law.ReadsLight A.Z (seatGround A) ξ) :
    ∀ b (p : Place), P5J.At.ps[b]? = some p → p.kind = KindName.K8 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((firstThread h parts w).row b).owes →
      (j ∈ (firstThread h parts w).opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧ ∀ m q, q ∈ P5J.parts4 → j ≠ .constr m q) →
      ExchangeAtS (firstThread h parts w) Said b j := by
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have eG : seatGround A = Bs.G₀ := seatGround_of_base O.made
  obtain ⟨sc, nb⟩ := parts
  have hS : sc = joinQ h.firstChain.blocksInOrder 0 r.cells r.token (P5J.At.arr A.Z) r.reader
      A.H.own₀ (byNo h.firstChain.blocksInOrder
        (K1.lotJobs r.number (K1.lotData Sz.ref) A.Z Bs.G₀ ++
          OnBytes.SendSim.Seat.wJobs r.number r.sendingWData A.Z Bs.G₀)) r.others := by
    have e : sc = SendersRecord.script h r := hq
    rw [e]
    unfold SendersRecord.script
    rw [eG, hlot]
  subst hS
  rw [eG] at hO hD
  refine k8_exchange_at_fill h.head (fallsAfterBatching (firstFalls A nb) h.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w hA hT rfl hOk O r.number r.sendingWData
    r.cells r.token r.reader A.H.own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ r.others hO hex ho
    hR hD fun l hl => ?_
  have t := List.all_eq_true.1 k8_draws l (List.mem_range.2 hl)
  cases hp : P5J.At.ps[VerifiableInference.Desc.First.K8.drawAt l]? with
  | none =>
    rw [hp] at t
    exact absurd t (by simp)
  | some pl =>
    have hk : pl.kind = KindName.K8 := by
      rw [hp] at t
      simpa using t
    rw [← P1K8T.drawAt_place]
    exact k8_behindS h.head A.H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said hp hk

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_exchange_first
