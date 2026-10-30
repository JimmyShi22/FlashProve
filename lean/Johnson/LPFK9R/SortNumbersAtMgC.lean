-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SortNumbersAtMgC.lean: THE FIELD Anumbers OF WHAT IS LEFT OF K9 ON THE SECOND ROAD
(`CoreLeftC`; `OwesNumbers`), AT THE CLOSED CONSTANT AND THE WRITTEN LETTERS,
ASSEMBLED. Theorems: one call each.

What is laid in: hd := rows_le (RowsLe.lean: p.rows ≤ 2 ^ 60 at the constant) · hP := hP_layers,
hP_att, hP_head (SortLook.lean: at t3 := t3All, l3 := l3All). Kx IS A LETTER, with hK
: Kx q gives NumbersThree q (a reading of the lookup's
"planes" and "join" shows that the term for Kx will grow: so the assembly must serve any term that
holds the three clauses; at kxAll3: hK := kxAll3_numbers).

What is said. `numbers_layersC_at`, `numbers_attC_at`, `numbers_headC_at`: **OwesNumbers L (phiAll
u psiAll) (fun q => (‹the named Ok› q ∧ Kx q) ∧ rowsLen p.rows pi8 (the link's own runs' number) q)
‹the sort's terms at t3All› ‹the sort's lengths at l3All› p.rows.**

PREMISES THAT ARE LEFT: h : AtMg OnBytes.secondHashFunction .. (THE HEAD's part) · m < 25 · kp : IM.k9At Zp m =
some p · hL : the link is a segment of the sort · hK. FREE LETTERS: Kx, u, nU, tlD, the sort's own
(p4; c; hS, iU3, p6), lmC, jC, lmD, jD, and bv, pv, kv (the worths of the caller's forms at
"planes" and "join": whoever pays the lookups' premises chooses them).

Limits. IT SAYS WHAT FOLLOWS FROM THE PROMISE: the terms' exponents differ and are at most p.rows
WHERE the promise and the public sentence hold of the fixed part: that these hold is the fields
AreadyS's and hR1's. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters3
import Johnson.Desc.First.Link.Law.SortLook
import Johnson.LPFK9R.RowsLe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open P5J (AtMg)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- **Anumbers AT A LAYERS' LINK OF THE CONSTANT, ON THE SECOND ROAD.** -/
theorem numbers_layersC_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (kp : IM.k9At Zp m = some p) {L : Link S Claim} (hL : SegAt m .layers L)
    (u : HTailF2) (p4 : OnBytes.Desc.First.K4.Par)
    (nU : Array ℕ) (tlD : HTailF2)
    (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (Kx : Phi BetaAll × Option Pub9 → Prop) (hK : ∀ q, Kx q → NumbersThree q) :
    OwesNumbers L (phiAll u psiAll) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsLen
      p.rows pi8 (fun q => lenRuns q (rlOf L (tmL p4 entUnit tmFour (t3All lmC jC
      lmD jD bv pv kv)) (lenL p4 (l3All lmC jC lmD jD))))) q) (tmL p4 entUnit tmFour (t3All lmC jC
      lmD jD bv pv kv)) (lenL p4 (l3All lmC jC lmD jD)) p.rows :=
  numbers_layersC hL u psiAll p4 nU tlD Kx
    (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) p (rows_le h m hm p kp) hK
    (fun s y _ => hP_layers lmC jC lmD jD bv pv kv p4 entUnit tmFour
      (fixed9 (phiAll u psiAll) s) y)

/-- **Anumbers AT AN ATTENTION LINK OF THE CONSTANT, ON THE SECOND ROAD.** -/
theorem numbers_attC_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (kp : IM.k9At Zp m = some p) {L : Link S Claim} (hL : SegAt m .attention L)
    (u : HTailF2) (c : VerifiableInference.Desc.First.Att.P.ParC)
    (nU : Array ℕ) (tlD : HTailF2)
    (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (Kx : Phi BetaAll × Option Pub9 → Prop) (hK : ∀ q, Kx q → NumbersThree q) :
    OwesNumbers L (phiAll u psiAll) (fun q => (fun q => OkAtt rdAll c nU tlD q ∧ Kx q) q ∧ (rowsLen
      p.rows pi8 (fun q => lenRuns q (rlOf L (tmA rdAll c entUnit tmFour (t3All
      lmC jC lmD jD bv pv kv)) (lenA rdAll c (l3All lmC jC lmD jD))))) q) (tmA rdAll c entUnit
      tmFour (t3All lmC jC lmD jD bv pv kv)) (lenA rdAll c (l3All lmC jC lmD jD)) p.rows :=
  numbers_attC hL u psiAll rdAll c nU tlD Kx
    (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) p (rows_le h m hm p kp) hK
    (fun s y _ => hP_att lmC jC lmD jD bv pv kv rdAll c entUnit tmFour
      (fixed9 (phiAll u psiAll) s) y)

/-- **Anumbers AT THE HEAD's LINK OF THE CONSTANT, ON THE SECOND ROAD.** -/
theorem numbers_headC_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (kp : IM.k9At Zp m = some p) {L : Link S Claim} (hL : SegAt m .head L)
    (u : HTailF2) (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 :
      VerifiableInference.Desc.Kinds.Head.Par)
    (nU : Array ℕ) (tlD : HTailF2)
    (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (Kx : Phi BetaAll × Option Pub9 → Prop) (hK : ∀ q, Kx q → NumbersThree q) :
    OwesNumbers L (phiAll u psiAll) (fun q => (fun q => OkHead hS iU3 p6 kapAll nU tlD q ∧ Kx q) q
      ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L (tmH hS iU3 p6 kapAll
      entUnit tmFour (t3All lmC jC lmD jD bv pv kv)) (lenH hS iU3 p6 kapAll (l3All lmC jC lmD
      jD))))) q) (tmH hS iU3 p6 kapAll entUnit tmFour (t3All lmC jC lmD jD bv pv kv)) (lenH hS iU3
      p6 kapAll (l3All lmC jC lmD jD)) p.rows :=
  numbers_headC hL u psiAll hS iU3 p6 kapAll nU tlD Kx
    (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) p (rows_le h m hm p kp) hK
    (fun s y _ => hP_head lmC jC lmD jD bv pv kv hS iU3 p6 kapAll entUnit tmFour
      (fixed9 (phiAll u psiAll) s) y)

end LPFK9

#print axioms LPFK9.numbers_layersC_at
#print axioms LPFK9.numbers_attC_at
#print axioms LPFK9.numbers_headC_at
