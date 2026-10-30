-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SharedHead.lean: the shared chain's parameters at the library's
description, with what has a definition supplied, as a family in the chain's own input: the
counterpart of `lettersHead` (Honest/Thread/FirstHead.lean). Of the nineteen fields of
`SharedThread.Letters` (Honest/Thread/Shared.lean) nine get their definition or their form: the two
messages differ in code (`split := true`); the flat list is the description's own shared chain's
(`P5J.F0T`); the prover's sides and the stored table's columns are a prover's own; the first state
and the item's number are the description's (`Desc.K14.first`, `Desc.K14.p14Of`: the very terms from
which the function that builds the description builds the chain's start); `valid` is "the input is
this run's" and a parameter; `rides` is a parameter; `keeps` goes by the sub-protocol's place
(`sharedPlaces true`), a parameter by place, as in the first chain. The table's numbers, the items'
meaning, the form's three parameters, the witness, the trees' tables and the two counts of trees
stay parameters, and so does the witness's type: the author of the chain's eight inner sub-protocols
supplies most of them (its `letters2`, not in the sealed library). One definition, a term; equations
by unfolding; and `Sits` without the shared chain's two hypotheses.

  `lettersShared`   the term
  `shared_bs`, `shared_hs`, `shared_stored`, `shared_valid`, `shared_keeps`, `shared_start`   what
     each parameter is there: by unfolding
  `sits_at_heads`   `sits_at_head` at that term

Limits.
  * It is not proved that the invariant holds at any run.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SitsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SharedThread
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS sharedPlaces)
open P5J (TS F0T)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St P₁ Wt)
  (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
  (order : Desc.K14.St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
  (Kp : Place → Desc.K14.St → Desc.K14.St → Prop) (w : Common W₀ Rc OnBytes.TableKey)

/-- **The shared chain's parameters at the library's description.** `w`: the run's own input of that
chain. `Vd`, `Rd`, `Kp`: what is still to be supplied of `valid`, `rides`, `keeps`. -/
noncomputable def lettersShared :
    Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀ P₁ Wt :=
  { split := true, N := N, Mg := Mg, shape := shape, nothingLeft := nothingLeft, order := order
    bs := (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
    hs := H.shared
    wit := wit, table := table, fixed := fixed
    stored := fun v => H.storedWords v.w₀ v.rc
    first := Desc.K14.first (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes
    item := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).item
    n₁ := n₁, n₂ := n₂
    valid := fun v => v = w ∧ Vd v
    rides := Rd
    keeps := fun b s s' => ∀ p, (sharedPlaces true)[b]? = some p → Kp p s s' }

theorem shared_bs :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs =
      (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder := rfl

theorem shared_hs :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).hs =
      H.shared := rfl

theorem shared_stored (v : Common W₀ Rc OnBytes.TableKey) :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).thread.stored v = H.storedWords v.w₀ v.rc := rfl

theorem shared_valid (v : Common W₀ Rc OnBytes.TableKey) :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).thread.valid v ↔ v = w ∧ Vd v := Iff.rfl

theorem shared_keeps (b : Nat) (s s' : Desc.K14.St) :
    (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w).thread.keeps b s s' ↔ ∀ p, (sharedPlaces true)[b]? = some p → Kp p s s' := Iff.rfl

/-- **The chain's first state is the description's own start, from the public part's key.** -/
theorem shared_start (y : ProofFile.InstPub) :
    (F0T OnBytes.secondHashFunction Zp Np cF).start₂ y =
      (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).first y.key := rfl

end ProofFile.Honest.SharedThread

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`Sits` with the first two chains' parameters supplied**: the shared chain's two hypotheses are
gone. -/
theorem sits_at_heads (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X P₁ Wt₂ Wt₃ : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
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
    (fixed : Fmt.TreeSource → Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
    (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
    (Kp₂ : Place → Desc.K14.St → Desc.K14.St → Prop) (w₂ : Common W₀ Rc OnBytes.TableKey)
    (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
      Tr X P₁ Wt₃)
    (t₃ : L₃.ft = (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber)
    (b₃ : L₃.bs = (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder) (h₃ : L₃.hs = H.second)
    (f₁ : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fits
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (f₂ : (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd₂ Rd₂ Kp₂ w₂).thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = true)
    (f₃ : L₃.thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length = true) :
    Sits (F0T OnBytes.secondHashFunction Zp Np cF) H
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd₂
        Rd₂ Kp₂ w₂).thread L₃.thread :=
  sits_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ L₃ rfl rfl t₃ b₃ h₃ f₁ f₂ f₃

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.SharedThread.shared_bs
#print axioms ProofFile.Honest.SharedThread.shared_hs
#print axioms ProofFile.Honest.SharedThread.shared_stored
#print axioms ProofFile.Honest.SharedThread.shared_valid
#print axioms ProofFile.Honest.SharedThread.shared_keeps
#print axioms ProofFile.Honest.SharedThread.shared_start
#print axioms ProofFile.Honest.FirstThread.sits_at_heads
