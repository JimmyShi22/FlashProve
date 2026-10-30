-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/PadsWAtEnd.lean: the linear claim's second part ("K14, second part", the first member
of a proof file's last chain): WHERE THE PAD OF THE MESSAGE W LIES, AT THE STATE THAT THE LAST
CHAIN's START RETURNS; and so, under the library's hypothesis at the full size (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean), at the format's second hash function, the eleven tests of secondDoor
(Johnson/Desc/ProofFile/Honest/K14/SecondDoor.lean) there WITHOUT THE PREMISE sW of second_door_thr
(Honest/K14/SecondAtRun.lean).

  padOwn_behind_356   behind an accepting step of the first chain's member 356 (W's commitment, the
                      own group and (Eval)) the state names W's number, and the message there bears
                      its own shape's pad (atM4_pad, Honest/K14/PadsW.lean)
  padOwn_of_reach     the same at every state that the verifier's own steps reach behind member 357,
                      which hands its state on as it is
  padsW_at_return     **sW**: at such a state s₁, where the last chain's start returns s of s₁ and a
                      state of the shared chain: PadsBehind at W in s
  second_door_ends    **secondDoor's eleven tests at s**, from the invariants of the two earlier
                      chains at their last borders and the start's return: second_door_thr with sW
                      shown

WHICH STATEMENT STANDS UNDER WHAT. padOwn_behind_356: files in the goals' scope that are read, and
an opening of the description (IM.Open), at the format's second hash function. padOwn_of_reach,
second_door_ends: the library's hypothesis. padsW_at_return: no such hypothesis: the start's return
and hp.

A LIMIT. UNDER THE LIBRARY's HYPOTHESIS sW RUNS OVER NOTHING: PadsBehind speaks of the pad's places
in the main table alone; there W's shape has a mask row (k13_wRow_at_head,
AtFullSide/K13/WFillAtHead.lean), so a sending lays every place of its pad in the mask table. sW is
true there because W's pad lies in the mask table; what shows it is the equation PadOwn, which these
files carry from W's sending to the start's return.

What is not claimed. That either invariant holds at any state, or that the start returns, or that
second_door_ends' premises can hold together: the two invariants' books, types, provers, inputs,
coins, stands and tables are free of each other, and so is x, as in second_door_thr. That the
sub-protocol accepts: secondDoor is a list of this kind's own (door_owed,
Honest/K14/SecondDoor.lean). Nothing on completeness, soundness or hiding. Terms. border:
lean/GLOSSARY.md. A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.PadsW
import Johnson.Desc.ProofFile.Honest.K14.SecondAtRun
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.IMR.LastFour
import Johnson.Desc.Last.IndexAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block OpenedColumn FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ firstOfS)
open VerifiableInference.Desc.Third.Law (start₃E_inv firstOutFrom_inv numbersOk_inv)
open VerifiableInference.Desc.K13.Law (linAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open Desc.K14 (St)

/-- **Behind an accepting step of the first chain's member 356** the state names W's number, and the
message there, where it is there with a shape that has answers, bears its own shape's pad. -/
theorem padOwn_behind_356 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) : ∃ l, linAt s' = some l ∧ PadOwn s'.st l.w := by
  obtain ⟨w, hw, ⟨rs', gs, y⟩, -, -⟩ := IM.at_356 hS hR O hb hy
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  exact atM4_pad y

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **At every state that the verifier's own steps reach behind number 357.** -/
theorem padOwn_of_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Pz : Type} {ft : ℕ}
    {start : Pz → TS} {z : Pz} {s : TS} (hr : Reach ft cF.blocksInOrder start (356 + 1 + 1) (z, s)) :
    ∃ l, linAt s = some l ∧ PadOwn s.st l.w := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases hr with
  | succ hr₁ hb₁ hy₁ =>
    cases hr₁ with
    | succ _ hb₀ hy₀ =>
      obtain ⟨_, _, _, e₁⟩ := hy₁
      obtain ⟨_, _, _, e₀⟩ := hy₀
      rw [IM.at_357 h.scope h.reads O hb₁ e₁]
      exact padOwn_behind_356 h.scope h.reads O hb₀ e₀

/-- **Where W's pad lies, at the state that the last chain's start returns.** hp: the first chain's
last state names W's number, and the message there bears its own shape's pad. -/
theorem padsW_at_return (x : ProofFile.InstPub) (s₁ : TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hp : ∃ l, linAt s₁ = some l ∧ PadOwn s₁.st l.w) :
    PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol) := by
  obtain ⟨f, e, -, hf, -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  refine padsW_at_start Zp Np cF x s₁ s₂ s hs f hf _ ?_
  obtain ⟨-, hlin, -, -, e5, -, -, -, e9, -⟩ := start_gives _ f _ s hst
  obtain ⟨fo, hfo, -⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
  obtain ⟨hn, q1, q2, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hfo
  obtain ⟨y, G, hy, -, hsh, hm, -⟩ := numbersOk_inv _ _ hn
  rw [q1, q2] at hy
  rw [q2] at hm
  have hc : f.st.codes = (ToldDesc.p14At Zp).codes := by rw [← e5]; exact e9
  obtain ⟨l, hl, hpo⟩ := hp
  -- what firstOfS takes: the state's own statement, and W's number as the state names it
  obtain ⟨en, hen, rfl⟩ := Option.map_eq_some_iff.1 hf
  have hw : en.lin = l := by
    unfold VerifiableInference.Desc.First.S.firstEnd? at hen
    unfold linAt at hl
    split at hl
    · rename_i a ha
      rw [ha] at hen
      simp only [hl, Option.bind_some] at hen
      split at hen
      · rw [← Option.some.inj hen]
      · cases hen
    · cases hl
  refine padsBehind_of_own _ _ _ y G hy hsh hm (by rw [hc]; exact hlin) ?_
  show PadOwn s₁.st en.lin.w
  rw [hw]
  exact hpo

section door
variable (Zp Np cF) {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X P₁ Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) (N : NumbersS)
  (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt) (shape : Nat → St → Bool)
  (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **secondDoor's eleven tests at the state that the last chain's start returns**: from the
library's hypothesis; the first chain's invariant at its last border at s₁; the shared chain's at
its last border at s₂; and the start's return s at s₁ and s₂. It is second_door_thr's statement with
the premise sW struck. The two invariants are tied to each other by the states s₁ and s₂ alone. -/
theorem second_door_ends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Bk₁ : ProverCoinCounts} {V₀ Rc₁ Ky₁ Tr₁ Y₀ Y : Type} (H₁ : Prover V₀ Rc₁ ProofFile.Inst Ky₁ Tr₁ Y₀ Y)
    (Q : FirstThread.Script Bk₁ (Local V₀ Rc₁ ProofFile.Inst Tr₁) (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → FirstThread.WtF → Prop)
    (item m₁ m₂ b₀ : Nat) (Vd₁ : Local V₀ Rc₁ ProofFile.Inst Tr₁ → Prop)
    (Rd₁ : Nat → Local V₀ Rc₁ ProofFile.Inst Tr₁ → TS → Prop) (Kp₁ : Place → TS → TS → Prop)
    (w₁ : Local V₀ Rc₁ ProofFile.Inst Tr₁)
    {k₁ : Coins Bk₁} {s₁ : TS} {mid₁ : Mid (Local V₀ Rc₁ ProofFile.Inst Tr₁) Y} {E₁ : Env}
    (hT₁ : Thr (FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).thread
      cF.blocksInOrder.length k₁ s₁ mid₁ E₁)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  have hlen : cF.blocksInOrder.length = 356 + 1 + 1 := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    exact VerifiableInference.Desc.Last.flat_358 h.scope h.reads O
  have hT' : Thr (FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).thread
      (356 + 1 + 1) k₁ s₁ mid₁ E₁ := hlen ▸ hT₁
  have hr := thr_reach_of
    (FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).thread
    (FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).first
    ((FirstThread.lettersHead h H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁).pubOf
      mid₁.st.input.x) (le_of_eq hlen.symm) (fun _ h0 => h0) hT'
  exact second_door_thr Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    H₁ Q test carryX item m₁ m₂ b₀ Vd₁ Rd₁ Kp₁ w₁ hT₁ Said hA x s hs
    (padsW_at_return x s₁ s₂ s hs (padOwn_of_reach h hr))

end door

end AtFullSide.K14

#print axioms AtFullSide.K14.padOwn_behind_356
#print axioms AtFullSide.K14.padOwn_of_reach
#print axioms AtFullSide.K14.padsW_at_return
#print axioms AtFullSide.K14.second_door_ends
