-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ValsTSAtStand.lean: CONDITIONAL: THE PREMISE OF THE FIVE ATTENTION ROWS OF A
BATCHING (BatchCellsAtt.lean: "first", "keys", "join", "second", "planes": valsTS A, Johnson/Desc/K5/
Honest/Law/TabsChain.lean) AT THE STATE IN FRONT OF THE BATCHING, the member 14 (2 g + 1) + 9 of the
first chain, before its draw. Under the head P5J.AtMgA, at any thread whose rides give
ridersOf (csHead ν st R) (Johnson/Desc/ProofFile/Honest/Thread/CsHead.lean), where R g o gives lookR
at the group's plan.

WHERE THE TWO PREMISES ON THE RIDER ARE MET. At lettersHead's thread with
Rd := ridersOf (csHead ν st R): hRides is the second half of rides (head_rest, Thread/FirstHead.lean).
At R := heardByAttention of Thread/TheFirstThread.lean hHeard is that definition's text. Neither file
lies under this one; a file over TheFirstThread.lean types the instance (valsTS_at_first).

Main names:
  lookOn_of_rides   the rider, at a border inside its span, gives LookOn
  plan_tie          the group's plan in the head's spelling
  step_returns      where the run on shapes returns past b and the family holds, the step at b returns
  gather_cons, batchG_of_cellG    the gathering on shapes, one row at a time; the member's step
  tabsGC_of_first   a return of "first" on shapes has the one Bool tabsGC
  draw_parts, objects_parts, tabsGC_in_front    ON SHAPES, A YES OF tabsGC BEHIND THE DRAW AND
    "objects" IS A YES IN FRONT OF THEM: these two steps leave the numbers and marks of the slots,
    what the segment's rounds handed on and what the lookup returned. One direction.
  valsTS_at_stand   **valsTS A s AT THE STATE s IN FRONT OF THE BATCHING**

How. The member's step on shapes, at the shape of s, runs the draw, "objects", "guests", then "first",
which tests tabsGC: hyes makes that step return. tabsGC says yes at the shape behind these, and by
tabsGC_in_front in front of them. valsTS_of_tabsGC (Johnson/Desc/K5/Honest/Law/PlanRAtHead.lean) joins
it with LookOn, which the rider's clause holds up to and at the border 14 (2 g + 1) + 9, and with the
facts on the plan (planR_at_head).

Limits. hyes (the run on shapes returns over the 358 members) IS A PREMISE: a closed question at given
public files, answered by no theorem here; if it fails the statement is empty. THE STATEMENT IS ALSO
EMPTY AT A THREAD WITH NO STATE AT WHICH Thr HOLDS AT THIS BORDER, AND NO THEOREM HERE SHOWS SUCH A
STATE. hJ CAN BE EMPTY TOO: the family must begin at the chain's start (first_chain_start,
RuleAtTable.lean, asks that the request passes its test) and be carried on member by member. The
rider's clause is no premise by name: it lies inside hT, the sixth part of Thr. That the clause is
laid (k5_lays_lookR_att, Johnson/Desc/ProofFile/Honest/K5/Law/LaysLookRAtt.lean, laid at one plan, the
list's clause being the form for every plan of the group) and stays past the members
14 (2 g + 1) + 4 to + 8 is owed by whoever builds Thr at this border: not shown here. The step on
shapes is read, not the state's own run: nothing here says that the draw returns at s. Nothing here
carries the premise from s to the state at which a row is called. At the format's second, fixed hash
function OnBytes.secondHashFunction alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.AtFull.Shape.TableBatch
import Johnson.Desc.K5.Honest.Law.PlanRAtHead
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh LedSh)
open VerifiableInference.Desc.K9 (SegSort Where)
open VerifiableInference.Desc.K9.Shape
open H2K5.Honest (LookOn valsTS tabsGC tabsG lookR valsTS_of_tabsGC k5FirstG)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)
open ProofFile.Honest (Thread Thr shapeJ run_front ridersOf riders_at csHead csHead_mem)
open ProofFile.Honest.K3.Shape (objectsG)

/-- The clause of the rider, at a border inside its span, gives LookOn. -/
theorem lookOn_of_rides {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option Forest.Heard → Prop} {w : W} {s : S} {g b : Nat} {A : Attention.Plan}
    (hg : g < 12) (hlo : 14 * (2 * g + 1) + 4 ≤ b) (hhi : b ≤ 14 * (2 * g + 1) + 9)
    (hr : ridersOf (csHead ν st R) b w s) (hR : ∀ o, R g o → lookR A o) : LookOn A s := by
  obtain ⟨a, ha, hP⟩ := riders_at hr
    ((csHead_mem ν st R _).2 (.inl (.inr ⟨g, hg, rfl⟩))) hlo hhi
  exact ⟨a, ha, hR _ hP⟩

/-- Where the run on shapes returns past b and the family holds at s, the step at b returns at s's
shape. -/
theorem step_returns {σ : Type} (Zs : ProofFile.Honest.Shape σ) {a₀ : Zs.Sh} {n b : Nat} {s : σ}
    (hb : b < n) (hyes : Zs.yes a₀ n = true) (hJ : shapeJ Zs a₀ b s) :
    ∃ t, Zs.g b (Zs.sh s) = .ok t := by
  obtain ⟨t, ht⟩ := run_front Zs a₀ n (b + 1) hb hyes
  have ht' : (Zs.run b a₀).bind (Zs.g b) = .ok t := ht
  rw [show Zs.run b a₀ = .ok (Zs.sh s) from hJ] at ht'
  exact ⟨t, ht'⟩

/-- The gathering on shapes, one row at a time. -/
theorem gather_cons {k : SegSort}
    {gT : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    {o : Nat × String} {os : List (Nat × String)} {x y : List ClaimSh × ChainSh}
    (h : gatherFrom k gT (o :: os) x = .ok y) :
    ∃ z, gT o x.1.length x.2 = .ok z ∧ gatherFrom k gT os (x.1 ++ z.1, z.2) = .ok y := by
  have h' : (VerifiableInference.Desc.K9.Shape.stepG k gT x o).bind (gatherFrom k gT os) = .ok y := h
  cases hs : VerifiableInference.Desc.K9.Shape.stepG k gT x o with
  | error e =>
    rw [hs] at h'
    exact nomatch h'
  | ok x' =>
    rw [hs] at h'
    unfold VerifiableInference.Desc.K9.Shape.stepG at hs
    cases hq : gT o x.1.length x.2 with
    | error e =>
      rw [hq] at hs
      exact nomatch hs
    | ok z =>
      rw [hq] at hs
      have hs' : (if eachS k o z.1 z.2 then (.ok (x.1 ++ z.1, z.2) :
          Except String (List ClaimSh × ChainSh)) else
            .error (o.2 ++ ": behind the run: the shape")) = .ok x' := hs
      split at hs'
      · obtain rfl := Except.ok.inj hs'
        exact ⟨z, rfl, h'⟩
      · cases hs'

/-- The batching's step on the whole, from the member's step on the whole shape. -/
theorem batchG_of_cellG {p : Where} {k : SegSort} {rows : List ((Nat × String) × Row)}
    {order : List (Nat × String)} {x t : ShA} (h : cellG p k rows order x = .ok t) :
    ∃ v, batchG p.rows k (fun o => (tabOf rows o).g) order x.1 = .ok v := by
  unfold cellG liftQ at h
  cases hb : batchGS p.rows k (fun o => (tabOf rows o).g) order x.1 with
  | error e =>
    rw [hb] at h
    simp [Except.map] at h
  | ok u =>
    unfold batchGS at hb
    cases hc : batchG p.rows k (fun o => (tabOf rows o).g) order x.1 with
    | error e =>
      rw [hc] at hb
      exact nomatch hb
    | ok v => exact ⟨v, rfl⟩

/-- A return of "first" on shapes has the one Bool. -/
theorem tabsGC_of_first {A : Attention.Plan} {n : Nat} {a : ChainSh}
    {y : List ClaimSh × ChainSh} (h : k5FirstG A n a = .ok y) : tabsGC A a = true := by
  unfold k5FirstG at h
  split at h
  · assumption
  · cases h

/-- What the draw on shapes does to what tabsGC reads. -/
theorem draw_parts {rows : Nat} {a a₁ : ChainSh} (hd : drawG rows a = .ok a₁) :
    ∃ F n, a.led = some F ∧ a₁.led = some (drawnLed F n) ∧ a₁.att = a.att ∧ a₁.look = a.look := by
  unfold drawG at hd
  split at hd
  · rename_i L F t u eL eF et eu
    split at hd
    · obtain rfl := Except.ok.inj hd
      refine ⟨F, L.list.nt.size, eF, ?_, rfl, rfl⟩
      show (a.led.map fun _ => drawnLed F L.list.nt.size) = _
      rw [eF]
      rfl
    · cases hd
  · cases hd

/-- What "objects" on shapes does to what tabsGC reads. -/
theorem objects_parts {d : Bool} {n : Nat} {c : ChainSh} {z : List ClaimSh × ChainSh}
    (h : objectsG d n c = .ok z) :
    ∃ L o, c.led = some L ∧ z.2.led = some (LedSh.setOwed L o) ∧ z.2.att = c.att ∧
      z.2.look = c.look := by
  unfold objectsG at h
  split at h
  · rename_i L hh eL eh
    obtain rfl := Except.ok.inj h
    refine ⟨L, VerifiableInference.Desc.First.Shape.paidB L.owed hh.owedObjects, eL, ?_, rfl, rfl⟩
    show (c.led.map fun _ =>
      LedSh.setOwed L (VerifiableInference.Desc.First.Shape.paidB L.owed hh.owedObjects)) = _
    rw [eL]
    rfl
  · cases h

/-- **ON SHAPES, A YES OF THE ONE BOOL BEHIND THE DRAW AND "objects" IS A YES IN FRONT OF THEM.** -/
theorem tabsGC_in_front {A : Attention.Plan} {rows n : Nat} {a a₁ : ChainSh}
    {z : List ClaimSh × ChainSh} (hd : drawG rows a = .ok a₁)
    (ho : objectsG false n a₁ = .ok z) (hG : tabsGC A z.2 = true) : tabsGC A a = true := by
  obtain ⟨F, m, eF, e1, e2, e3⟩ := draw_parts hd
  obtain ⟨L, o, e4, e5, e6, e7⟩ := objects_parts ho
  obtain rfl : drawnLed F m = L := Option.some.inj (e1.symm.trans e4)
  unfold tabsGC at hG ⊢
  rw [e5, e6, e7, e2, e3] at hG
  rw [eF]
  cases h1 : (a.att.bind (·.heard5)) with
  | none =>
    rw [h1] at hG
    exact hG
  | some H =>
    rw [h1] at hG
    cases h2 : a.look with
    | none =>
      rw [h2] at hG
      exact hG
    | some K =>
      rw [h2] at hG
      exact hG

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- The group's plan, in the head's spelling. -/
theorem plan_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : Nat} {A : Attention.Plan}
    (e : Bs.G₀.W.A[g]? = some A) : (P5J.At.X Zp).A[g]? = some A := by
  obtain ⟨B', base, O⟩ := h.laid.opened
  obtain rfl := base_one hB O.made
  have eW := O.W
  rw [eW] at e
  exact e

/-- **valsTS A s AT THE STATE s IN FRONT OF THE BATCHING 14 (2 g + 1) + 9.** CONDITIONAL: the head; a
thread whose rides give the list csHead at an R that gives lookR at the group's plan; the run on
shapes hyes; Thr and the family of the run on shapes at s. See the file's head on emptiness. -/
theorem valsTS_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProofFile.Honest.ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option Forest.Heard → Prop}
    (hRides : ∀ b w s, T.rides b w s → ridersOf (csHead ν st R) b w s)
    (hHeard : ∀ g o, R g o → ∀ a, (P5J.At.X Zp).A[g]? = some a → lookR a o) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    {g : Nat} (hg : g < 12) {A : Attention.Plan} (hA : Bs.G₀.W.A[g]? = some A)
    {k : ProofFile.Honest.Coins Bk} {s : S} {m : ProofFile.Honest.Mid W X} {E : _}
    (hT : Thr T (14 * (2 * g + 1) + 9) k s m E)
    (hJ : shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀ (14 * (2 * g + 1) + 9) s) :
    valsTS A s = true := by
  obtain ⟨B', Lk, p, w, A', q, e1, eL, e2, e3, e4, e5, -⟩ := att_batch h g hg
  obtain rfl := base_one hB e1
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans e4)
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hsub : subAt (2 * g + 1) = .attention := by
    unfold subAt
    rw [if_neg h24, if_neg (by omega)]
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * g + 1) + 9) = Tab.batch Zp Bs.G₀ (2 * g + 1) :=
    cells_link Zp Bs.G₀ (2 * g + 1) 8 (by omega) (by omega) rfl
  unfold Tab.batch at hc
  rw [e2, e3] at hc
  simp only [show (2 * g + 1 == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * g + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega), Bool.false_eq_true,
    if_false, show (2 * g + 1) / 2 = g from by omega, e4, e5] at hc
  have ea := plan_tie h hB e4
  have hL : LookOn A s := lookOn_of_rides hg (by omega) (by omega)
    (hRides _ _ _ hT.2.2.2.2.2.1) (fun o ho => hHeard g o ho A ea)
  obtain ⟨unit₁, unit₂, unit₃, unit₄, unit₅, unit₆, unit₇, Q⟩ := H2K5.Honest.planR_at_head h hg ea
  obtain ⟨t, hg1⟩ := step_returns (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀))
    (b := 14 * (2 * g + 1) + 9) (n := 358) (by omega) hyes hJ
  have hg1' : Tab.g Zp Bs.G₀ (14 * (2 * g + 1) + 9) (shA s) = .ok t := hg1
  rw [cell_g hc] at hg1'
  dsimp only at hg1'
  obtain ⟨v, hv⟩ := batchG_of_cellG hg1'
  have hv' : (drawG p.rows (shA s).1).bind (addsG w.1 (fun o => (tabOf (rowsAtt A q.lm) o).g)
      (VerifiableInference.Desc.First.orderOf (subAt (2 * g + 1)))) = .ok v := hv
  cases hd : drawG p.rows (shA s).1 with
  | error e =>
    rw [hd] at hv'
    exact nomatch hv'
  | ok a₁ =>
    rw [hd] at hv'
    have hv2 : addsG w.1 (fun o => (tabOf (rowsAtt A q.lm) o).g)
        (VerifiableInference.Desc.First.orderOf (subAt (2 * g + 1))) a₁ = .ok v := hv'
    unfold addsG at hv2
    split at hv2
    · cases hga : gatherG w.1 (fun o => (tabOf (rowsAtt A q.lm) o).g)
          (VerifiableInference.Desc.First.orderOf (subAt (2 * g + 1))) a₁ with
      | error e =>
        rw [hga] at hv2
        exact nomatch hv2
      | ok yg =>
        rw [hsub] at hga
        have hga' : gatherFrom w.1 (fun o => (tabOf (rowsAtt A q.lm) o).g)
            ((1, "objects") :: (1, "guests") :: (2, "first") ::
              [(2, "keys"), (2, "join"), (2, "second"), (1, "planes"), (6, "objects"),
                (6, "guests"), (4, "K8.equations")]) ([], a₁) = .ok yg := hga
        obtain ⟨z₁, c₁, r₁⟩ := gather_cons hga'
        obtain ⟨z₂, c₂, r₂⟩ := gather_cons r₁
        obtain ⟨z₃, c₃, -⟩ := gather_cons r₂
        have c₂' : (Except.ok ([], z₁.2) : Except String (List ClaimSh × ChainSh)) = .ok z₂ := c₂
        obtain rfl := Except.ok.inj c₂'
        have hG : tabsGC A z₁.2 = true := tabsGC_of_first (n := 0) c₃
        exact valsTS_of_tabsGC A Q (tabsGC_in_front (n := 0) hd c₁ hG) hL
    · exact nomatch hv2

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.valsTS_at_stand
#print axioms Johnson.AtFull.Shape.tabsGC_in_front
