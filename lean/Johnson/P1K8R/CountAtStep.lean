-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CountAtStep.lean: THE SMALLNESS TEST: A COUNT FOR A TEST BEHIND THE BATCHING
(`CountFrom`, Johnson/Desc/K8/Honest/CountFrom.lean), THE TEST A LETTER, CARRIED TO THE SEATED
BATCHING BLOCK's STEP AT ALL 25 SEGMENTS, TO THE MEASURE OVER THE ROUND's MESSAGES AT TYPED
CHALLENGES AND AT STRINGS OF HASH BLOCKS, AND TO THE STATE THAT THE VERIFIER's FOLD RETURNS.
Definitions and lemmas; none of the library's goals. Nothing on completeness, soundness or hiding.
An assembly: the proofs are those of Johnson/P1K8R/FallAtStepAll.lean, BoundAtBatch.lean,
UnitsGate.lean, UnitsTest.lean, UnitsBlocks.lean, with the test a letter.

ok, no, N: `CountFrom`'s letters. l < 25; K := 14 l + 9, or 347 at the head's: the batching's
number. (hok): whatever data and ledger the state s holds pass ok, with N tl ≤ n.
  **`count_at_step`**   in the goals' scope: b the member at K, p the batching's numbers: AT
      WHATEVER STATE s, n, d with (hok) and (hd) d bounds the exponents at what s holds: at most n *
      d field elements x are such that b's step says yes from s at a round that has drawn x, and no
      says yes of the state that it returns
  **`count_at_step_rows`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked
      Z`): at a state reached at K, with (hok): at most n * (p.rows - 1)
  `behindT b no s`   with code: at one drawn value: b's own step at the round without a message that
      has drawn it, at no columns; then no at what it returns; `behind_iff`: at the seated batching
      it says yes just if b's step says yes at SOME round that has drawn the value, at some columns,
      and no says yes of what it returns; `behindT_units`: at the test on the vector of reads it is
      `unitsT` (Johnson/P1K8R/UnitsTest.lean)
  **`count_gate`**, **`count_gate_blocks`**   under `RowsAsked Z`, at a reached state with (hok); d
      a round's data with the batching's entry: the measure (Iop.prRho, uniform on that one round's
      messages) of the messages at which `behindT b no s` says yes of what is shown is at most n *
      (p.rows - 1) / p ^ 3 at Run.ck .two, and kapSl 128 ^ 3 times that at Run.ckP .two
  **`count_of_fold`**, **`count_of_fold_blocks`**   the same at the state that the verifier's fold
      over the first K members returns from the chain's start
Limits. THREE PREMISES ARE PAID NOWHERE HERE: `RowsAsked Z`; (hok)'s share on public numbers;
(hok)'s share on challenges drawn in front. SO NO NUMBER HERE IS A SHARE THAT IS HELD. n is a
letter. The uniform law on one round's messages is named, not derived. No number is evaluated.

-/
import Johnson.P1K8R.PlainAtSeat
import Johnson.P1K8R.UnitsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open _root_.Run.PQ (CK)
open Iop
open scoped ENNReal

/-- The block's own step at the round without a message that has drawn dr, at no columns; then the
test at what it returns. -/
def behindT (b : Block S Claim) (no : S → Bool) (s : S) : List Fmt.Drawn → Bool
  | [dr] =>
    match b.step 0 s [⟨[], dr⟩] [] with
    | .ok (t, _) => no t
    | .error _ => false
  | _ => false

theorem behindT_one (b : Block S Claim) (no : S → Bool) (s : S) (dr : Fmt.Drawn) :
    behindT b no s [dr] =
      match b.step 0 s [⟨[], dr⟩] [] with
      | .ok (t, _) => no t
      | .error _ => false := rfl

/-- At the test on the vector of reads it is `unitsT` (Johnson/P1K8R/UnitsTest.lean). -/
theorem behindT_units (b : Block S Claim) (nU : Array Nat) (s : S) (own : List Fmt.Drawn) :
    behindT b (zeroUnitAt nU) s own = unitsT b nU s own := by
  cases own with
  | nil => rfl
  | cons dr t =>
    cases t with
    | nil => rfl
    | cons _ _ => rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
  {ok : HTailF2 → Fork → Bool} {no : S → Bool} {N : HTailF2 → ℕ}

/-- **The count at the step, at all 25 segments, at whatever state.** -/
theorem count_at_step (C : CountFrom ok no N) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (s : S) (n d : Nat),
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        (∀ tl F' funs, s.tl? = some tl → s.fork? = some F' → s.funs? = some funs →
          F'.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧ no t = true) ≤
          n * d := by
  obtain ⟨Lk, p, -, e2, hflat, hplain, same, name, a, hk, hb⟩ := plain_at_seat hS hR O hl
  refine ⟨_, p, hflat, e2, fun s n d hok hd => ?_⟩
  have hcount := count_at_link C Lk hplain p
    (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs []) s n d
    (fun rs t ht => ((IM.yes_alone hb hk s t rs []).1 ht).1) hok hd
  refine (Prob.cnt_mono fun x hx => ?_).trans hcount
  obtain ⟨r, cols, t, k, hel, hst, hz⟩ := hx
  have hdec := step_chi hb hk 0 s t r cols k x hel hst
  unfold K8.Honest.askBehind
  simp only [List.map_cons, List.map_nil]
  rw [hdec]
  exact hz

/-- **With the plan's number of rows.** -/
theorem count_at_step_rows (C : CountFrom ok no N) (hE : RowsAsked Z)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (z : ProofFile.InstPub) (s : S) (n : Nat),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧ no t = true) ≤
          n * (p.rows - 1) := by
  obtain ⟨b, p, hb, hp, hcount⟩ := count_at_step C hS hR O hl
  obtain ⟨p', hp', hbound⟩ := bound_at_batch hE hS hR O hl
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  refine ⟨b, p, hb, hp, fun z s n hr hok => hcount s n (p.rows - 1) hok ?_⟩
  intro tl F' funs h1 h2 h3
  have h := hbound z s hr tl F' funs h1 h2 h3
  omega

/-- **The test with code is the event that is counted.** -/
theorem behind_iff (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    (no : S → Bool) (s : S) (dr : Fmt.Drawn) :
    behindT b no s [dr] = true ↔
      ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
        b.step 0 s [r] cols = .ok (t, m) ∧ no t = true := by
  obtain ⟨-, p, -, -, -, hp, -⟩ := (IM.k9_of hS hR O).2 l hl
  have hd := batch_decl hS hR O hl b hb p hp
  constructor
  · intro h
    rw [behindT_one] at h
    cases hst : b.step 0 s [⟨[], dr⟩] [] with
    | error x =>
      rw [hst] at h
      cases h
    | ok y =>
      obtain ⟨t, m⟩ := y
      rw [hst] at h
      exact ⟨_, [], t, m, rfl, hst, h⟩
  · rintro ⟨r, cols, t, m, rfl, hst, hz⟩
    rw [behindT_one, step_plain hd (batch_items p) rfl rfl hst]
    exact hz

/-- The measure, at whatever kit whose challenges show one field element. -/
theorem count_gate_any (C : CountFrom ok no N) (hE : RowsAsked Z)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (Ck : CK) (d : RDT) (el : Ck.Ch d.entry d.kind → Cb.Gl.E) (w : ℕ)
        (_ : ∀ y, Prob.cnt (fun a => el a = y) ≤ w)
        (_ : ∀ a, (Ck.dr d.entry d.kind a).elems = [Slice.ofE (el a)])
        (z : ProofFile.InstPub) (s : S) (n : Nat),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Iop.prRho {ρ : Iop.Rho (uLT Ck [d]) | behindT b no s (drawnT Ck [d] ρ) = true} ≤
          ((n * (p.rows - 1) * w : ℕ) : ℝ≥0∞) / (Nat.card (Ck.Ch d.entry d.kind) : ℝ≥0∞) := by
  obtain ⟨b, p, hb, hp, hcount⟩ := count_at_step_rows C hE hS hR O hl
  refine ⟨b, p, hb, hp, ?_⟩
  intro Ck d el w hw hel z s n hr hok
  have k := prRho_elem_le Ck d el w hw hel
    (fun dr => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
      b.step 0 s [r] cols = .ok (t, m) ∧ no t = true)
    (fun x => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧ no t = true)
    (by
      rintro dr x ⟨r, cols, t, m, rfl, h1, h2⟩ hx
      exact ⟨r, cols, t, m, hx, h1, h2⟩) _ (hcount z s n hr hok)
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans k
  obtain ⟨a, u⟩ := ρ
  refine ⟨Ck.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a), rfl, ?_⟩
  exact (behind_iff hS hR O hl b hb no s _).1 hρ

/-- **At typed challenges.** -/
theorem count_gate (C : CountFrom ok no N) (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (z : ProofFile.InstPub) (s : S) (n : Nat),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          behindT b no s (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
          ((n * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, hb, hp, h⟩ := count_gate_any C hE hS hR O hl
  refine ⟨b, p, hb, hp, ?_⟩
  intro d he h5 h6 z s n hr hok
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have k := h (_root_.Run.ck .two) d (elOf d.entry d.kind) 1 (elOf_one _ _ h1)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind a).elems = _
      rw [shows_chi _ _ h1]
      rfl) z s n hr hok
  rw [Nat.mul_one] at k
  rw [← card_one_elem d.entry d.kind h1]
  exact k

/-- **At strings of hash blocks.** -/
theorem count_gate_blocks (C : CountFrom ok no N) (hE : RowsAsked Z)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (z : ProofFile.InstPub) (s : S) (n : Nat),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          behindT b no s (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
          kapSl 128 ^ 3 * ((n * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, hb, hp, h⟩ := count_gate_any C hE hS hR O hl
  refine ⟨b, p, hb, hp, ?_⟩
  intro d he h5 h6 z s n hr hok
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have hlog : d.entry.logN ≤ 64 := by
    rw [he]
    exact Nat.zero_le _
  have k := h (_root_.Run.ckP .two) d
    (fun u => elOf d.entry d.kind ((_root_.Run.bsRound .two d.entry d.kind).φ u))
    (_root_.Run.bsRound .two d.entry d.kind).w (blocks_el _ _ h1 hlog)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind
        ((_root_.Run.bsRound .two d.entry d.kind).φ a)).elems = _
      rw [shows_chi _ _ h1]
      rfl) z s n hr hok
  exact k.trans (blocks_bound _ _ h1 hlog _)

/-- **At the state that the verifier's fold returns: typed challenges.** -/
theorem count_of_fold (C : CountFrom ok no N) (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (zp : ProofFile.InstPub) (s : S) (n : Nat) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) (ProofFile.startS Z zp) rs cs =
          .ok (s, r, c') →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          behindT b no s (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
          ((n * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, hb, hp, h⟩ := count_gate C hE hS hR O hl
  refine ⟨b, p, hb, hp, ?_⟩
  intro d he h5 h6 zp s n rs r cs c' hfold hok
  exact h d he h5 h6 zp s n
    (reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s rs r cs c' hfold) hok

/-- **At the state that the verifier's fold returns: strings of hash blocks.** -/
theorem count_of_fold_blocks (C : CountFrom ok no N) (hE : RowsAsked Z)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (zp : ProofFile.InstPub) (s : S) (n : Nat) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) (ProofFile.startS Z zp) rs cs =
          .ok (s, r, c') →
        (∀ tl F', s.tl? = some tl → s.fork? = some F' → ok tl F' = true ∧ N tl ≤ n) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          behindT b no s (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
          kapSl 128 ^ 3 * ((n * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, hb, hp, h⟩ := count_gate_blocks C hE hS hR O hl
  refine ⟨b, p, hb, hp, ?_⟩
  intro d he h5 h6 zp s n rs r cs c' hfold hok
  exact h d he h5 h6 zp s n
    (reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s rs r cs c' hfold) hok

end

end P1K8

#print axioms P1K8.behindT_units
#print axioms P1K8.count_at_step
#print axioms P1K8.count_at_step_rows
#print axioms P1K8.behind_iff
#print axioms P1K8.count_gate_any
#print axioms P1K8.count_gate
#print axioms P1K8.count_gate_blocks
#print axioms P1K8.count_of_fold
#print axioms P1K8.count_of_fold_blocks
