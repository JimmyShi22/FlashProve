-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/BegunAtHeads.lean: WHERE THE TWO EARLIER CHAINS BEGAN, AT THE
LIBRARY's DESCRIPTION. `begun` at `lettersHead` and `lettersShared` names the description's own
`start₁` and `start₂` at the instance, wherever the thread's `valid` holds. So the premises `hb₁`
and `hb₂` of `baseOfEnds_at_door` (Honest/Thread/BaseAtDoor.lean) fall at these two terms.

  `Letters.begun_of_valid`   at the first chain's letters, and at the shared chain's
  `baseOfEnds_at_heads`   `baseOfEnds_at_door` at the two terms

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.

Limits.
  * `hw₁` and `hw₂` are premises: the input that `valid` names has the run's instance, and its key
    is the key of the instance's public part. They are shown here of no run.
  * Nothing here says that any state meets `Thr`, or that the two ends are the ends of one run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BaseAtDoor
import Johnson.Desc.ProofFile.Honest.Thread.LastHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread

/-- **At the first chain's letters the chain begins at `first` of the instance's public part**,
where `valid` fixes the instance. -/
theorem Letters.begun_of_valid {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
    (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {x : Xi}
    (hv : ∀ v, L.valid v → v.x = x) {k : Coins Bk} {v : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {s₀ : VerifiableInference.Desc.First.S} (h₁ : L.thread.valid v)
    (h₂ : L.thread.begun k v hd s₀) : s₀ = L.first (L.pubOf x) := by
  have e : v.x = x := hv v h₁
  have h : s₀ = L.first (L.pubOf v.x) := h₂
  rw [e] at h
  exact h

end ProofFile.Honest.FirstThread

namespace ProofFile.Honest.SharedThread

/-- **At the shared chain's letters the chain begins at `first` of the key**, where `valid` fixes
the key. -/
theorem Letters.begun_of_valid {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Ky X₀ P₁ Wt : Type}
    (L : Letters Bk S₂ Cl W₀ Rc Ky X₀ P₁ Wt) {y : Ky}
    (hv : ∀ v, L.valid v → v.key = y) {k : Coins Bk} {v : Common W₀ Rc Ky}
    {hd : List Fmt.Drawn} {s₀ : S₂} (h₁ : L.thread.valid v) (h₂ : L.thread.begun k v hd s₀) :
    s₀ = L.first y := by
  have e : v.key = y := hv v h₁
  have h : s₀ = L.first v.key := h₂
  rw [e] at h
  exact h

end ProofFile.Honest.SharedThread

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {p₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF p₀) {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X P₁ Wt₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
  (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St P₁ Wt₂)
  (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
  (order : Desc.K14.St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt₂)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (m₁ m₂ : Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
  (Kp₂ : Place → Desc.K14.St → Desc.K14.St → Prop) (w₂ : Common W₀ Rc OnBytes.TableKey)

local notation "𝕋₁" => Letters.thread (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
local notation "𝕋₂" => SharedThread.Letters.thread (SharedThread.lettersShared Zp Np cF H N Mg shape
  nothingLeft order wit table fixed m₁ m₂ Vd₂ Rd₂ Kp₂ w₂)
local notation "𝔽" => F0T OnBytes.secondHashFunction Zp Np cF

/-- **`hB` of `door_field`, at `BaseOfEnds`, at the two terms.** `hx`: the run's own instance. `hw₁`,
`hw₂`: the input that each `valid` names has that instance and its public part's key. -/
theorem baseOfEnds_at_heads
    {T₃ : Thread Bk (𝔽).S₃ (𝔽).Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    (sits : Sits (𝔽) H 𝕋₁ 𝕋₂ T₃) {x : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X} (hx : R.own.x = x) (hw₁ : w.x = x)
    (hw₂ : w₂.key = x.pub.key) :
    ∀ e₁ u₁ E₁ e₂ u₂ E₂ s₃ o₁ o₂,
      ThrS 𝕋₁ (SaidField 𝕋₁ BaseNil) (𝔽).first.blocksInOrder.length k e₁ u₁ E₁ →
      ThrS 𝕋₂ (SaidField 𝕋₂ BaseNil) (𝔽).shared.blocksInOrder.length k e₂ u₂ E₂ →
      (𝔽).start₃ ((𝔽).pub x) e₁ e₂ = .ok s₃ → u₁.opened = some o₁ → u₂.opened = some o₂ →
      BaseOfEnds (𝔽) k { R.start₃ H u₁ u₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂) :=
  baseOfEnds_at_door sits rfl rfl hx
    (fun _ _ _ _ u g =>
      Letters.begun_of_valid (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (x := x)
        (fun v hv => by
          have e : v = w ∧ Vd v := hv
          rw [e.1]
          exact hw₁)
        u.2.2.2.2.2.2 g)
    (fun _ _ _ _ u g =>
      SharedThread.Letters.begun_of_valid
        (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed m₁ m₂
          Vd₂ Rd₂ Kp₂ w₂) (y := x.pub.key)
        (fun v hv => by
          have e : v = w₂ ∧ Vd₂ v := hv
          rw [e.1]
          exact hw₂)
        u.2.2.2.2.2.2 g)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.Letters.begun_of_valid
#print axioms ProofFile.Honest.SharedThread.Letters.begun_of_valid
#print axioms ProofFile.Honest.FirstThread.baseOfEnds_at_heads
