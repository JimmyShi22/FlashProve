-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackPort.lean: the two forms Alin and Blin that the end of the verifier's batched
sumcheck leaves are worth the two form parts of the library's typed batched sumcheck at the end
point; so the verifier's two claims on the sides' hidden end values give two of the three claims
that the typed chain owes at its end for that sumcheck.

The chain of the layers' own rounds (Cb/Pv/Lay/) owes, for the batched sumcheck, the ledger stackCl
(Cb/Pv/Lay/End/StackA.lean): the sumcheck's own first output row, and rowF at the two form parts.
That file's head says: "The programs' claims on the two form parts read tables that are sent late.
That these, pulled back to the early entries, are the claims of this file is not said here." Here it
is said of the two rows rowF, on values, in a world whose reads are true.

Main names:
  `forms_blocks`: Alin | Blin as sums over all places of the typed form parts' summands.
  `forms_extAt`: the same as extensions, at a point zp that reads as the verifier's challenges
    turned round.
  `forms_typed`: so Alin | Blin are worth P.inn.F st m at the two form parts, at zp.
  `rowF_zero`: one row rowF is worth 0, if a number x is the typed map at the output's point, the
    hidden value is what was shown less the factor times the mask entry, and the two are equal.
  `rowF_port`: both rows, from the two equations that forms_typed concludes (premises ea, eb here)
    and the verifier's two claims Aff.slot sA0 - Alin and Aff.slot sB0 - Blin worth 0.
  `stack_port`: forms_typed and rowF_port in one, at the typed sumcheck's output o.
What is asked. SigFits (Johnson/Road/FormsKeysPortSig.lean) at the typed sizes, tables and cells
P.rd m: among its fields, that the tables which the panels read are true of these cells. StackTies
(Johnson/Road/K4/StackTyped.lean). The verifier's two lists and stackEnd return; the calls of the
second walk; the weight of claim 0 is 1; the number of rounds is the typed kS; one challenge for
each round; the point (hpt). For the rows: P.rd is linear in the entries (hrd), as stack_pull asks.
Limits. All of these are premises: that a run of K4's text and the typed chain's value at that run
meet them is not shown here. The sumcheck's own first output row (the first member of stackCl) is
not spoken of. Implications in one world: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.PanelSidesAll
import Johnson.Road.K4.StackTyped
import Johnson.Road.K4.FormParts
import Cb.Pv.Lay.End.StackA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff WsClaim WsShape)
open OnBytes.Model.Layer (Panels PanelEnv ClaimEnv StackEnd stackEnd placePanels panelsA panelsT)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell pans)
open Cb.Pv.Lay.At (InnPar0 isVirt kS extAt IA IB)
open Cb.Pv.Lay.End (rowF rowF_iff a0_aff b0_aff)
open Blocks (Form)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {P : InnPar0 K} {ρ : Reading K}
  {Wo : World K} {p : PanelEnv} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {lk : ℕ} {cc : Cells K} {low z zh ζ : ℕ → K}

/-- Alin and Blin are worth the sums, over all places, of the place's equality weight times the
summands of the typed form parts. -/
theorem forms_blocks {st : P.St} {m : P.J → K}
    (S : SigFits ρ Wo p c h pc s P.D lk P.L0 cc (P.rd m) low z zh ζ P.tb) {om : Array E}
    (T : StackTies P st ρ p.v.y p.shownT om z zh) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) (hom : ρ.val (om.getD 0 zeroE) = 1) {rs H1 V : Array E}
    {shownA shownB : E} {s' : StackEnd} {lam : ℕ}
    (hl : (ceilLog2 (placePanels pans'.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s') :
    s'.Alin.value ρ Wo = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p Y).sum ∧
      s'.Blin.value ρ Wo = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p Y).sum := by
  have F2 := placed_sides S (fun _ _ => 0) (P.rw m) hTS hp hc hom hst
  obtain ⟨fa, fb⟩ := forms_ext_own (ρ := ρ) (W := Wo) hp hl hrs hst
  refine ⟨?_, ?_⟩
  · rw [fa]
    refine sum_congr rfl fun Y _ => ?_
    rw [(vecs_of_sides pans'.bl F2 Y).1, typed_A T m _ Y]
  · rw [fb]
    refine sum_congr rfl fun Y _ => ?_
    rw [(vecs_of_sides pans'.bl F2 Y).2, typed_B T m _ Y]

omit [Fintype K] scl in
/-- The verifier's equality weights are the typed ones, at a point that reads as the challenges
turned round. -/
theorem eqR_typed {rs : Array E} {k : ℕ} (zp : Fin k → K)
    (hpt : ∀ j, j < k → Blocks.nat zp j = ρ.val (rs.getD (k - 1 - j) zeroE)) (Y : ℕ) :
    eqR ρ rs 0 k Y = Blocks.eqN k (k - k) (Blocks.nat zp) Y := by
  unfold eqR
  rw [Nat.sub_zero, Nat.sub_self]
  exact eqN_congr' _ _ (fun j hj => by rw [Nat.zero_add]; exact (hpt j hj).symm) Y

/-- Alin and Blin are worth the extensions of the typed form parts' long vectors. k: the number of
rounds. -/
theorem forms_extAt {st : P.St} {m : P.J → K}
    (S : SigFits ρ Wo p c h pc s P.D lk P.L0 cc (P.rd m) low z zh ζ P.tb) {om : Array E}
    (T : StackTies P st ρ p.v.y p.shownT om z zh) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) (hom : ρ.val (om.getD 0 zeroE) = 1) {rs H1 V : Array E}
    {shownA shownB : E} {s' : StackEnd} {k : ℕ}
    (hl : (ceilLog2 (placePanels pans'.bl).2 == k) = true) (hrs : k ≤ rs.size)
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs k om H1 V shownA shownB = some s')
    (zp : Fin k → K)
    (hpt : ∀ j, j < k → Blocks.nat zp j = ρ.val (rs.getD (k - 1 - j) zeroE)) :
    s'.Alin.value ρ Wo = extAt k (k - k)
        (fun y => ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p y).sum)
        (Blocks.nat zp) ∧
      s'.Blin.value ρ Wo = extAt k (k - k)
        (fun y => ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p y).sum)
        (Blocks.nat zp) := by
  obtain ⟨fa, fb⟩ := forms_blocks S T hTS hp hc hom hl hrs hst
  rw [fa, fb]
  unfold extAt
  exact ⟨sum_congr rfl fun Y _ => by rw [eqR_typed zp hpt], sum_congr rfl fun Y _ => by
    rw [eqR_typed zp hpt]⟩

/-- **Alin and Blin are worth the typed form parts.** -/
theorem forms_typed {st : P.St} {m : P.J → K}
    (S : SigFits ρ Wo p c h pc s P.D lk P.L0 cc (P.rd m) low z zh ζ P.tb) {om : Array E}
    (T : StackTies P st ρ p.v.y p.shownT om z zh) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) (hom : ρ.val (om.getD 0 zeroE) = 1) {rs H1 V : Array E}
    {shownA shownB : E} {s' : StackEnd}
    (hl : (ceilLog2 (placePanels pans'.bl).2 == kS P.D) = true) (hrs : kS P.D ≤ rs.size)
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs (kS P.D) om H1 V shownA shownB = some s')
    (zp : Fin (kS P.D) → K)
    (hpt : ∀ j, j < kS P.D → Blocks.nat zp j = ρ.val (rs.getD (kS P.D - 1 - j) zeroE)) :
    s'.Alin.value ρ Wo = P.inn.F st m (.inl (.inl ())) zp ∧
      s'.Blin.value ρ Wo = P.inn.F st m (.inr (.inl ())) zp :=
  forms_extAt S T hTS hp hc hom hl hrs hst zp hpt

/-- One row of the typed ledger from its value: if x is the typed map a at the output's point, the
hidden value sl is what was shown less the factor times the mask entry, and sl - x = 0. -/
theorem rowF_zero [DecidableEq P.J] {J₂ : Type} [DecidableEq J₂] [Fintype J₂]
    (o : P.inn.toSum.T.par.Out) (a : IA P.D ⊕ IB P.D)
    (ha : Cb.Pv.Lay.End.IsAff fun m => P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o))
    (m : P.J → K) (u : J₂ → K) {x sl : K}
    (hx : x = P.inn.F o.st m a (P.inn.Kp.outPt P.inn.Mk o))
    (hs : sl = o.vals a - P.inn.Kp.outB P.inn.Mk o * m (P.cI a)) (c0 : sl - x = 0) :
    Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o a) = 0 := by
  refine (rowF_iff P o a ha m u).2 ((P.inn.ev_iff o m a).2 ?_)
  rw [← hx]
  show x + m (P.cI a) * P.inn.Kp.outB P.inn.Mk o = o.vals a
  linear_combination hs - c0

/-- **The two rows of the typed ledger.** o: the typed sumcheck's output; u: any late entries. -/
theorem rowF_port [DecidableEq P.J] {J₂ : Type} [DecidableEq J₂] [Fintype J₂]
    (hrd : ∀ (a b : K) (m m' : P.J → K) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (o : P.inn.toSum.T.par.Out) {m : P.J → K} (u : J₂ → K) {s' : StackEnd}
    (ea : s'.Alin.value ρ Wo = P.inn.F o.st m (.inl (.inl ())) (P.inn.Kp.outPt P.inn.Mk o))
    (eb : s'.Blin.value ρ Wo = P.inn.F o.st m (.inr (.inl ())) (P.inn.Kp.outPt P.inn.Mk o))
    {sA0 sB0 : ℕ}
    (hA : Wo.slot sA0 = o.vals (.inl (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inl (.inl ()))))
    (hB : Wo.slot sB0 = o.vals (.inr (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inr (.inl ()))))
    (cA : (Aff.slot sA0 - s'.Alin).value ρ Wo = 0) (cB : (Aff.slot sB0 - s'.Blin).value ρ Wo = 0) :
    Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inl (.inl ()))) = 0 ∧
      Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inr (.inl ()))) = 0 := by
  rw [Aff.value_sub, Aff.value_slot] at cA cB
  exact ⟨rowF_zero o _ (a0_aff P hrd o.st _) m u ea hA cA,
    rowF_zero o _ (b0_aff P hrd o.st _) m u eb hB cB⟩

/-- **The port of the batched sumcheck's two form parts**, at the typed sumcheck's output o. -/
theorem stack_port [DecidableEq P.J] {J₂ : Type} [DecidableEq J₂] [Fintype J₂]
    (hrd : ∀ (a b : K) (m m' : P.J → K) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (o : P.inn.toSum.T.par.Out) {m : P.J → K} (u : J₂ → K)
    (S : SigFits ρ Wo p c h pc s P.D lk P.L0 cc (P.rd m) low z zh ζ P.tb) {om : Array E}
    (T : StackTies P o.st ρ p.v.y p.shownT om z zh) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) (hom : ρ.val (om.getD 0 zeroE) = 1) {rs H1 V : Array E}
    {shownA shownB : E} {s' : StackEnd}
    (hl : (ceilLog2 (placePanels pans'.bl).2 == kS P.D) = true) (hrs : kS P.D ≤ rs.size)
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs (kS P.D) om H1 V shownA shownB = some s')
    (hpt : ∀ j, j < kS P.D → Blocks.nat (P.inn.Kp.outPt P.inn.Mk o) j =
      ρ.val (rs.getD (kS P.D - 1 - j) zeroE))
    {sA0 sB0 : ℕ}
    (hA : Wo.slot sA0 = o.vals (.inl (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inl (.inl ()))))
    (hB : Wo.slot sB0 = o.vals (.inr (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inr (.inl ()))))
    (cA : (Aff.slot sA0 - s'.Alin).value ρ Wo = 0) (cB : (Aff.slot sB0 - s'.Blin).value ρ Wo = 0) :
    Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inl (.inl ()))) = 0 ∧
      Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inr (.inl ()))) = 0 :=
  have e := forms_typed (st := o.st) S T hTS hp hc hom hl hrs hst (P.inn.Kp.outPt P.inn.Mk o) hpt
  rowF_port hrd o u e.1 e.2 hA hB cA cB

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.forms_typed
#print axioms OnBytes.Road.K4.rowF_zero
#print axioms OnBytes.Road.K4.rowF_port
#print axioms OnBytes.Road.K4.stack_port
