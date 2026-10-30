-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondAtRun.lean: kind K14: "K14, second part" (the place ⟨3,
none, 0, .K14⟩): secondDoor (Honest/K14/SecondDoor.lean) WITH THE FOLD's RETURN READ OFF THE FRAME's
OWN SENTENCES: once off the frame's sentence on the first chain at its last border, once off the
frame's player. Statements with their proofs: calls. No definition.

Why. second_door_fold (Honest/K14/SecondAll.lean) has the premise hF: the first chain's last state
s₁ is what foldBlocks 0 cF.blocksInOrder returns of the first chain's own start. The frame has two lemmas
that end in that equation: head_fold_end (Honest/Thread/HeadFold.lean) and runC_hands_head
(Honest/Law/RunCHead.lean).

  rest5_at_fold   the whole list secondRest5 (Honest/K14/OmegaJoin.lean) is true at the fold. ITS
                  FIFTH TEST IS LISTED ONLY WHERE THE TAKING-OVER AND linDotRow RETURN; that they
                  return is not shown. A join of rest2_at_fold (Honest/K14/SecondAll.lean),
                  fifth_at_fold and rest3_of_two (Honest/K14/SecondTerms.lean), rows_at_head
                  (Honest/K14/SecondBlocksAtFold.lean), blocks_at_border and rest5_of_three
                  (Honest/K14/SecondBlocks.lean). Its premise on the shared chain is Thr, which ThrS
                  gives
  second_door_thr   **secondDoor with Thr of the first chain at its last border at s₁ in hF's
                  place**; the other four premises of second_door_fold stay
  second_door_run   **secondDoor OF EVERY RUN THAT THE FRAME's PLAYER runC RETURNS with both earlier
                  chains' ends states and the last chain's door a state s**; the head, ThrS at the
                  shared chain's last border and sW stay. hF IS READ OFF THE RUN. THE START's RETURN
                  IS NOT PAID: IT IS A PREMISE IN ANOTHER FORM: at these two ends "the door is some
                  s" says just that the start returns s, at the run's own instance's public part

What stays a premise. In both: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean); ThrS at the
shared chain's last border at s₂; sW (where W's pad lies). In second_door_thr besides: Thr of the
first chain at its last border at s₁; the start's return s at s₁ and s₂. In second_door_run besides:
runC's return r; r.ends.1 = some s₁; r.ends.2.1 = some s₂; the door = some s.

WHAT TIES THE LETTERS TOGETHER: the one head, so the public part, the places and the first chain;
and the states. NOTHING ELSE. In second_door_thr the book, the types, the prover, the input, the
coins, the stand and the tables of the first chain's Thr and those of the shared chain's ThrS are
free of each other, and so is the instance's public part x at which the start returns. In
second_door_run the fold's and the start's public part are both the run's; nothing ties the shared
chain's ThrS to the run r but the state s₂; the two premises on the ends name s₁ and s₂: that both
ends are states follows from the premise on the door.

What is not claimed. That runC returns; that an end or the door is a state; that Thr or ThrS holds
at any run; that these premises can hold together. That the head holds at other files than those at
which the library shows it. That the sub-protocol accepts: secondDoor is a list of this kind's own
(door_owed, Honest/K14/SecondDoor.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondAll
import Johnson.Desc.ProofFile.Honest.Thread.HeadFold
import Johnson.Desc.ProofFile.Honest.Law.RunCHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linLayW)
open VerifiableInference.Desc (Chain Place foldBlocks OpenedColumn Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

section top
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **The whole list secondRest5 is true** (its fifth test is listed only where the taking-over and
linDotRow return): under the library's head, Thr at the shared chain's last border at s₂, the
start's return s at s₁ and s₂, and where foldBlocks 0 cF.blocksInOrder returns s₁ of the first chain's own
start. -/
theorem rest5_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    ok (secondRest5 (ToldDesc.p14At Zp) s) = true :=
  rest5_of_three _ s
    (blocks_at_border Zp Np cF x s₁ s₂ s hs
      (rows_at_head h _ (LPFK9.start_rows h.laid.pub p) rs cols s₁ r' cl hF))
    (rest3_of_two _ s
      (fifth_at_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
        x s₁ s hs p rs cols r' cl hF)
      (rest2_at_fold h x s₁ s₂ s hs p rs cols r' cl hF))

/-- **secondDoor, with Thr of the first chain at its last border in the fold's place**: from the
library's head; Thr of the first chain at its last border at s₁; ThrS at the shared chain's last
border at s₂; the start's return s at s₁ and s₂; and sW: where W's pad lies. The two sentences'
books, inputs, coins, stands and tables are free of each other, and so is x. -/
theorem second_door_thr {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {Bk₁ : ProverCoinCounts} {V₀ Rc₁ Ky₁ Tr₁ Y₀ Y : Type} (H₁ : Prover V₀ Rc₁ ProofFile.Inst Ky₁ Tr₁ Y₀ Y)
    (Q : FirstThread.Script Bk₁ (Local V₀ Rc₁ ProofFile.Inst Tr₁) (P5J.CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT)
    (test : Nat → P5J.TS → Option String)
    (carryX : Nat → ProofFile.InstPub × P5J.TS → Strs → FirstThread.WtF → Prop)
    (item m₁ m₂ b₀ : Nat) (Vd₁ : Local V₀ Rc₁ ProofFile.Inst Tr₁ → Prop)
    (Rd₁ : Nat → Local V₀ Rc₁ ProofFile.Inst Tr₁ → P5J.TS → Prop) (Kp₁ : Place → P5J.TS → P5J.TS → Prop)
    (w₁ : Local V₀ Rc₁ ProofFile.Inst Tr₁)
    {k₁ : Coins Bk₁} {s₁ : P5J.TS} {mid₁ : Mid (Local V₀ Rc₁ ProofFile.Inst Tr₁) Y} {E₁ : Env}
    (hT₁ : Thr (FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).thread
      cF.blocksInOrder.length k₁ s₁ mid₁ E₁)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol)) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨cols, hF⟩ := FirstThread.head_fold_end h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁ hT₁
  exact second_door_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    Said hA x s₁ s hs _ _ cols [] [] hF sW

/-- **secondDoor of every run that the frame's player returns with both earlier chains' ends states
and the last chain's door a state**: from the library's head; runC's return r; r.ends.1 = some s₁;
r.ends.2.1 = some s₂; the door = some s; ThrS at the shared chain's last border at s₂; and sW: where
W's pad lies. The fold's return is read off the run; the premise on the door is the start's return
in another form. Nothing ties that ThrS to the run but the state s₂. -/
theorem second_door_run {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {B : ProverCoinCounts} {V₀ Rc₁ Ky₁ Tr₁ Y₀ Y : Type} {H₁ : Prover V₀ Rc₁ ProofFile.Inst Ky₁ Tr₁ Y₀ Y} {w₀ : V₀}
    {rc : Rc₁} {x : ProofFile.Inst} {c : Coins B} {ρ : Draws}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hr : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) B H₁ w₀ rc x c ρ = .ok r) {s₁ : P5J.TS} {s₂ : St}
    (h₁ : r.ends.1 = some s₁) (h₂ : r.ends.2.1 = some s₂) {s : S₃}
    (hd : door₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) x r.ends.1 r.ends.2.1 = some s)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol)) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  obtain ⟨hF, hdoor⟩ := runC_hands_head hr h₁ h₂
  have hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x.pub s₁ s₂ = .ok s := by
    have e := hdoor.symm.trans hd
    cases hq : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x.pub s₁ s₂ with
    | error msg =>
      rw [hq] at e
      cases e
    | ok t =>
      rw [hq] at e
      exact congrArg Except.ok (Option.some.inj e)
  exact second_door_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    Said hA x.pub s₁ s hs _ _ _ [] [] hF sW

end top

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rest5_at_fold
#print axioms ProofFile.Honest.K14.second_door_thr
#print axioms ProofFile.Honest.K14.second_door_run
