-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeByKind.lean: CONDITIONAL. One statement with its proof.

What is here. THE WHOLE DEBT OF THE KIND K4 (the feed-forward layers' own rounds) IN "THE EXCHANGE",
IN THE FORM IN WHICH A GATHER OVER THE FIRST CHAIN ASKS IT BY THE PLACE's KIND, BROUGHT DOWN TO TWO
FAMILIES OF SENTENCES: at every number b at which the library's written list of places names the
kind K4, and at every item j that the thread's forward row owes there and that is not, being open in
front, a pin, pinI, pinW or a constraint at one of the four parts of `P5J.parts4`: `ExchangeAtS` at
b and j. The thread is a thread of the first chain, at the public files' own data, any prover H, any
Script Q and the ten parameters behind them as letters (`lettersHead`,
Honest/Thread/FirstHead.lean); Said is a letter.

  `k4_exchange_by_kind`   **from `ExchangeAtS` at the items "own" and wo at each laid member (hOwn,
      hWo) to the kind's whole debt.**

How. The library's `k04_places_full` (Johnson/Road/K4/K04Places.lean; by Lean's kernel) has that the
kind stands at the twelve numbers 28 g + 4 alone; `atK4_full` (Johnson/Road/K4/K04Tied.lean) and
`laid_head` (Law/SeatedHead.lean) lay the member there; `owes_k4` (Law/TableAt.lean) lists the eight
items that the row owes. At "planes" and "join": `k4_exchange_planes_head`, `k4_exchange_join_head`
(Law/PlanesHead.lean). At pin, pinW, the constraint at the part small, and pinI: each is asked by
the row (`asks_k4`) and so open in front (`open_k4` at `onePass_full`; Law/W/OpenAtHead.lean,
Law/W/OnePassFull.lean), which refutes the gather's own clause.

Not shown here. hOwn AND hWo ARE HYPOTHESES, AND THEY HOLD ALL THE CONTENT: the two items "planes"
and "join" are true and empty (the data list no run there: `runs_planes`, `runs_join`,
Law/TableAt.lean), and the four others are let off. Laws that end in hOwn's and hWo's sentences at a
prover that is a letter stand in files of these writers (`k4_exchange_own_at`,
Law/ExchangeOwnAt.lean; `k4_exchange_wo_lot`, Law/WoTopLot.lean), EACH UNDER HYPOTHESES FOR WHICH NO
PAYER LIES: ties of the coins that K4's row spends to entries of the Script's witness (`K4MaskTieAt`
at both items, `K4IndexTieAt` at wo) and ties on what the witness holds (`CellIsList` and
`K4IndexIs` at "own", `K4WeightsTieK` at wo). THE LAW AT "own" ALSO BINDS TWO OF THE LETTERS: b₀ ≠ k
+ 1, so that whoever pays hOwn by it at all twelve members lays b₀ at none of the numbers 28 g + 5;
and Rd = `ridersOf` (`csHead` …). THAT THE HYPOTHESIS h ON THE PUBLIC FILES HOLDS OF ANY FILES. THE
FULL SIZE ALONE, AND THE OLDER HASH (secondHashFunction) ALONE. This file gives no example of its hypotheses
together. Nothing on soundness, on completeness, on what is hidden or on any other property.

A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PlanesHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpenAtHead
import Johnson.Road.K4.K04Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open OnBytes.Road.K4 (k04_places_full atK4_full)
open VerifiableInference.Desc (Place Chain Strs Block KindName)
open VerifiableInference.Desc.First (Item flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_head)
open ProofFile.Honest.K4.W (asks_k4 open_k4 onePass_full)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, hOwn and hWo. **THE KIND K4's WHOLE DEBT IN "THE EXCHANGE", FROM THE TWO
ITEMS "own" AND wo AT EACH LAID MEMBER.** -/
theorem k4_exchange_by_kind
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    (hOwn : ∀ (k m g : ℕ) (x : Bool × Par) (blk₀ : Block TS ProofFile.Cl), LaidK4 Zp cF k m g x blk₀ →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
        (Item.formsT m 3 "own"))
    (hWo : ∀ (k m g : ℕ) (x : Bool × Par) (blk₀ : Block TS ProofFile.Cl), LaidK4 Zp cF k m g x blk₀ →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
        (Item.wo m)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K4 →
      ∀ j : Item,
      j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said b j := by
  intro b p hb hk j hj hx
  have hb' : (flatPlacesOf linksFull true)[b]? = some p := hb
  obtain ⟨g, hg, rfl, rfl⟩ := k04_places_full b p hb' hk
  have A := atK4_full g hg
  obtain ⟨g', x, blk, Lh⟩ := laid_head h A
  have ho : ∀ i : Item,
      i ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row (28 * g + 4)).asks →
      i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened (28 * g + 4) :=
    fun i hi => open_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full hi
  rw [asks_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A] at ho
  rw [owes_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A] at hj
  unfold restK4 at hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact hOwn _ _ _ _ _ Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · exact k4_exchange_planes_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · exact k4_exchange_join_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · exact hWo _ _ _ _ _ Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · exact absurd rfl ((hx (ho _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).1 _ _)
  rcases List.mem_cons.1 hj with rfl | hj
  · exact absurd rfl (hx (ho _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).2.2.1
  rcases List.mem_cons.1 hj with rfl | hj
  · exact absurd rfl ((hx (ho _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _))))))))).2.2.2 _ _ (by decide))
  rcases List.mem_cons.1 hj with rfl | hj
  · exact absurd rfl (hx (ho _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _)))))))))).2.1
  · cases hj

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exchange_by_kind
