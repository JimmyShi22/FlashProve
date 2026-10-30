-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/QuietFall.lean: ANY FALL AT THE MEMBER WITHOUT A ROUND BEHIND A SEGMENT's BATCHING,
WHOSE TEST READS THE STATE ALONE: ITS SENTENCE `FallDebt`
(Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean) FROM A BOUND AT THE BATCHING's OWN STEP; AND ONE
SUCH SENTENCE WITHOUT A TEST ON THE STATE AMONG ITS PREMISES. Definitions and lemmas; NONE OF THE
LIBRARY's GOALS. Nothing on completeness, soundness or hiding. The walk of `share_event`
(Johnson/P1K8R/DebtsK8.lean), the fall a letter.

l < 25; o := 1 at the head's segment, else 0; K := 14 l + 9, or 347: the batching's number; b: the
member at K. f: a fall whose place is `quietPlace l o` and whose test at a state and whatever
challenges is T of the state.
  **`quiet_event`**   in the goals' scope: the wide event of f at b and the members behind it, at
      one drawn value, at whatever first tree, gives: b's own step returns a state at which T speaks
      (`behindT`, Johnson/P1K8R/CountAtStep.lean)
  **`quiet_fallDebt_of`**   the kit a letter: IF Q gives that the measure of the round's messages at
      which b's step returns a state at which T speaks is at most q: THEN `FallDebt` of f at b, the
      members behind it, and q
  `unitsOnlyT`, `unitsOnlyFall`   the test "an entry of the vector of reads has the weight 0" alone,
      as a fall at that place
  **`units_fallDebt`**, **`units_fallDebt_blocks`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL
      25 SEGMENTS (`RowsAsked Z`): `FallDebt` of `unitsOnlyFall` at the plan's number of entries
      times (the batching's rows - 1) over p ^ 3 (at strings of hash blocks: times kapSl 128 ^ 3),
      at every Q that gives that the state in front is the end of the verifier's fold from the
      chain's start
Limits. `unitsOnlyFall` IS IN NO LIST OF FALLS: it is made to show that the form can be met at the
proof file's description with no test on the state among the premises. Its stated share is a free
letter. `RowsAsked Z` is a premise. No number is evaluated.
-/
import Johnson.P1K8R.DebtsK8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open ProofFile.Honest (Odds Fall FallDebt localFall chainFall frontsOf fallOf)
open ProofFile.Honest.K8 (quietPlace frontsOf_step frontsOf_zero frontsOf_place)
open _root_.Run.PQ (CK)
open Iop
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The wide event of a fall at the member behind the batching.** -/
theorem quiet_event (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (f : Fall S)
    (T : S → Option String) (hp : f.place = quietPlace l (if l = 24 then 1 else 0))
    (ht : ∀ s ds, f.test s ds = T s) (ft : ℕ) (s' : S) (dr : Fmt.Drawn)
    (h : localFall [f] ft (b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) s' [dr]) :
    behindT b (fun t => (T t).isSome) s' [dr] = true := by
  obtain ⟨rs, cols, hrs, hc⟩ := h
  obtain ⟨⟨a, w⟩, hcw⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨i, e, hi, hpl, hfall⟩ := chainFall_at _ ft _ s' _ a w hcw
  obtain ⟨r, rfl, hrd⟩ : ∃ r, rs = [r] ∧ r.drawn = dr := by
    cases rs with
    | nil => simp at hrs
    | cons r t =>
      cases t with
      | nil => exact ⟨r, rfl, by simpa using hrs⟩
      | cons _ _ => simp at hrs
  have hb1 := batch_round hS hR O hl b hb
  have hplace := frontsOf_place ft _ _ _ _ i e hi
  obtain ⟨f', hf, hfp, hft⟩ := ProofFile.Honest.K8.fallOf_mem _ a _ _ w hfall
  obtain rfl := List.mem_singleton.1 hf
  rw [← drop_batch b hb, List.getElem?_drop, hpl, ← hfp, hp] at hplace
  have hi1 : i = 1 := by
    have := quiet_place hS hR O hl hplace
    omega
  subst hi1
  obtain ⟨e₀, b₀, cols', m, g1, g2, -, g4⟩ := frontsOf_step ft _ _ _ _ 0 e hi
  obtain rfl : b = b₀ := Option.some.inj g2
  have hs0 := frontsOf_zero ft _ _ _ _ e₀ g1
  rw [hs0, hb1] at g4
  have g4' : b.step ft s' [r] cols' = .ok (e.2.1, m) := g4
  obtain ⟨-, p, -, -, -, hp9, -⟩ := (IM.k9_of hS hR O).2 l hl
  have hd := batch_decl hS hR O hl b hb p hp9
  have g5 := step_ft hd (batch_items p) rfl rfl g4'
  rw [behindT_one, ← hrd, g5]
  show (T e.2.1).isSome = true
  rw [← ht e.2.1 e.2.2, hft]
  rfl

/-- **Its sentence from a bound at the batching's own step.** -/
theorem quiet_fallDebt_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (Ck : CK)
    (d : RDT) (f : Fall S) (T : S → Option String)
    (hp : f.place = quietPlace l (if l = 24 then 1 else 0))
    (ht : ∀ s ds, f.test s ds = T s) (ft : ℕ) (q : ℝ≥0∞) (Q : List Fmt.Drawn → S → Prop)
    (hQ : ∀ fr s', Q fr s' → Iop.prRho {ρ : Iop.Rho (uLT Ck [d]) |
      behindT b (fun t => (T t).isSome) s' (drawnT Ck [d] ρ) = true} ≤ q) :
    FallDebt Ck f ft b (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q q := by
  intro fr s' hq
  refine le_trans (Prob.pr_mono _ ?_) (hQ fr s' hq)
  intro ρ hρ
  obtain ⟨a, u⟩ := ρ
  have hρ' : localFall [f] ft (b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) s'
      [Ck.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)] := hρ
  exact quiet_event hS hR O hl b hb f T hp ht ft s' _ hρ'

/-- "An entry of the vector of reads has the weight 0", alone. -/
def unitsOnlyT (nU : Array Nat) (s : S) : Option String :=
  if zeroUnitAt nU s = true then
    some "the smallness test: an entry of the vector of reads has the weight 0"
  else none

theorem unitsOnly_some (nU : Array Nat) (t : S) :
    (unitsOnlyT nU t).isSome = zeroUnitAt nU t := by
  unfold unitsOnlyT
  cases zeroUnitAt nU t <;> rfl

/-- That test as a fall at the member behind the batching. In no list of falls. -/
def unitsOnlyFall (link o : Nat) (nU : Array Nat) (share : Odds) : Fall S :=
  ⟨quietPlace link o, fun s _ => unitsOnlyT nU s, share⟩

/-- **A sentence of the form with no test on the state among its premises: at typed challenges.** -/
theorem units_fallDebt (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → FoldEnd Z c l s') →
        FallDebt (_root_.Run.ck .two)
          (unitsOnlyFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  obtain ⟨b, p, X, hb, hp, hX, hU⟩ := units_of_fold hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 ft share Q hQ
  refine quiet_fallDebt_of hS hR O hl b hb (_root_.Run.ck .two) d _
    (unitsOnlyT (ProofFile.k8NU Bs.G₀ X)) rfl (fun _ _ => rfl) ft _ Q ?_
  intro fr s' hq
  obtain ⟨zp, rs, r, cs, c', hfold⟩ := hQ fr s' hq
  simp only [unitsOnly_some, behindT_units]
  exact hU d he h5 h6 zp s' rs r cs c' hfold

/-- **The same at strings of hash blocks.** -/
theorem units_fallDebt_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → FoldEnd Z c l s') →
        FallDebt (_root_.Run.ckP .two)
          (unitsOnlyFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  obtain ⟨b, p, X, hb, hp, hX, hU⟩ := units_of_fold_blocks hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 ft share Q hQ
  refine quiet_fallDebt_of hS hR O hl b hb (_root_.Run.ckP .two) d _
    (unitsOnlyT (ProofFile.k8NU Bs.G₀ X)) rfl (fun _ _ => rfl) ft _ Q ?_
  intro fr s' hq
  obtain ⟨zp, rs, r, cs, c', hfold⟩ := hQ fr s' hq
  simp only [unitsOnly_some, behindT_units]
  exact hU d he h5 h6 zp s' rs r cs c' hfold

end

end P1K8

#print axioms P1K8.quiet_event
#print axioms P1K8.quiet_fallDebt_of
#print axioms P1K8.unitsOnlyT
#print axioms P1K8.unitsOnly_some
#print axioms P1K8.unitsOnlyFall
#print axioms P1K8.units_fallDebt
#print axioms P1K8.units_fallDebt_blocks
