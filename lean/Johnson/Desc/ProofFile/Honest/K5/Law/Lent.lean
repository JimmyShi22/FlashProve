-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Lent.lean: CONDITIONAL: THE BOOK's LENDING TO THE ROW OF AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) RETURNS, AT ALL COINS: the frame's own law on a member of
the first chain at whose place a half stands (lent_first, Honest/Thread/Laid.lean), called at the
member at which K5's half is seated. Statements with their proofs.

  k5_lent        CONDITIONAL: at every run's coins the lending to K5's row returns
  k5_lent_head   the same at the first chain's thread at the library's head (lettersHead,
                 Honest/Thread/FirstHead.lean): the three premises on the thread's letters hold
                 there by unfolding

The premises. ONE RETURN OF ready, at any one input and coin · K5Seated
(Honest/K5/Law/Seated.lean) · of the thread's letters: its chain's number is 0; its halves are the
prover's; its list of members is the description's first chain's.

What it is for. The tie on the mask row (K5Script.maskTie, Honest/K5/Law/Script.lean) speaks of
every c that the lending returns: wherever ready returns once there is such a c at every coin, so
that tie is not met for nothing on that side.

Limits. That ready returns anywhere is not shown. What is lent is not said: that the lending
returns, and no more. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.Desc.ProofFile.Honest.Thread.Laid
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block FileDescription Chain Strs Place)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.Sound (MsgT)

/-- **The lending to K5's row returns, at all coins.** CONDITIONAL: see the head. -/
theorem k5_lent {Xi W₀ Rc Ky Tr X₀ X Pb : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (h : ready F B H w₀ rc x c = .ok R)
    {T : Thread B F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {cells : Tr → Cells} {Z : Seat5} {p : P.Par} {blk : Block F.S₁ F.Cl}
    (Hs : K5Seated T b cells Z p blk) (hc : T.chain = 0) (hh : T.hs = H.first)
    (hb : T.bs = F.first.blocksInOrder) (k : Coins B) :
    ∃ u, lendRow B (B.rowsOf T.chain) (k.look T.chain) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok u := by
  have hj : F.first.blocksInOrder[b]? = some blk := hb ▸ Hs.member
  have hf : (H.first.find? fun g => g.place == blk.place) = some (k5Half cells Z) :=
    hh ▸ Hs.half
  obtain ⟨u, hu⟩ := lent_first h hj hf k
  rw [hc, ← Hs.place]
  exact ⟨u, hu⟩

section
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM F0T)

variable {Z₀ : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The same at the first chain's thread at the library's head.** CONDITIONAL: one return of
ready at the head's description; K5Seated at that thread. -/
theorem k5_lent_head (h : AtMgA OnBytes.secondHashFunction Z₀ D r Zp Np cF x₀) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc x c = .ok R) {b : Nat}
    {cells : Tr → Cells} {Z : Seat5} {p : P.Par} {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b cells Z p blk)
    (k : Coins Bk) :
    ∃ u, lendRow Bk (Bk.rowsOf 0) (k.look 0) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells Z).parts 0 = .ok u :=
  k5_lent hr Hs rfl rfl rfl k

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lent
#print axioms ProofFile.Honest.K5.k5_lent_head
