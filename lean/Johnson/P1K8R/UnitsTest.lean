-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsTest.lean: THE SMALLNESS TEST: "`selfUnits` SAYS NO BEHIND THE BATCHING" AS A
TEST WITH CODE ON THE STATE IN FRONT OF THE BATCHING AND ON WHAT ITS ONE ROUND SHOWS, AND THE BOUND
OF Johnson/P1K8R/UnitsGate.lean FOR THAT TEST; THE NUMBER OF TYPED CHALLENGES OF A ROUND THAT DRAWS
ONE FIELD ELEMENT. Lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding. An assembly: no new argument.

  `unitsT b nU s ds`   ds is one round's drawn value dr; the block b's own step from s, at the round
      without a message that has drawn dr, at no columns, says yes; and `selfUnits` says no at the
      state that it returns
  `card_one_elem`   a round that draws one field element and nothing else has p ^ 3 typed
      challenges, p the size of the base field (Fmt.Fld.two.p)
  `step_plain`   general: a block whose one declared round states no item and opens nothing: a yes
      of its step at one round and whatever columns is a yes at the round without a message, at no
      columns, with the same return
  `unitsT_one`, `batch_items`   the test's text at one round; the batching's declared round states
      no item (a round's items are cut out of its entry's words: Fmt.Entry.cut, Decl/Declared.lean)
  `batch_decl`   in the goals' scope the seated batching block of each of the 25 segments declares
      one round: the batching's entry, no item, nothing opened
  **`units_iff`**   so at that block `unitsT b nU s [dr]` says yes JUST IF the step says yes from s
      at SOME round that has drawn dr and SOME columns, and `selfUnits` says no at what it returns:
      the test with code is the event that `units_gate` counts
THE TWO THAT FOLLOW BEGIN: IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked
Z`).
  **`units_gate_test`**   the letters and the bound of `units_gate`, for the measure of the round's
      messages at which `unitsT b nU s` says yes of what is shown, b the seated batching block, s
      reached at its number
  **`units_gate_p3`**   at typed challenges (Run.ck .two) and a round with the batching's entry: at
      most nU[2] * (p.rows - 1) / p ^ 3
By: `units_gate` · `shows_chi`, `elOf_one`, `oneElem_bat` (Johnson/Desc/K8/Honest/ChiTyped.lean) ·
card_vals_all (OnBytes/Slice/Rates.lean) · Sound.step_ok_iff (Johnson/Desc/Sound/RunIsDecide.lean) ·
IM.k9_of (Johnson/IMR/LinkSeat.lean), IM.alone_rounds (Johnson/IMR/SeatForm.lean).
Limits. Those of UnitsGate.lean: `RowsAsked Z` IS A PREMISE; one of the tests on the ledger's
weights. That a run's verifier steps at the batching's member from the state s that is named is not
said here. No number is evaluated.

-/
import Johnson.P1K8R.UnitsGate
import OnBytes.Slice.Rates
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach)
open scoped ENNReal

/-- The block's own step at the round without a message that has drawn dr, at no columns; then
`selfUnits` at what it returns. -/
def unitsT (b : Block S Claim) (nU : Array Nat) (s : S) : List Fmt.Drawn → Bool
  | [dr] =>
    match b.step 0 s [⟨[], dr⟩] [] with
    | .ok (t, _) => zeroUnitAt nU t
    | .error _ => false
  | _ => false

theorem unitsT_one (b : Block S Claim) (nU : Array Nat) (s : S) (dr : Fmt.Drawn) :
    unitsT b nU s [dr] =
      match b.step 0 s [⟨[], dr⟩] [] with
      | .ok (t, _) => zeroUnitAt nU t
      | .error _ => false := rfl

/-- The batching's declared round states no item. -/
theorem batch_items (p : K9.Where) : ({ entry := K9.entry p } : Fmt.DeclaredRound).items = [] := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K9.entry]

/-- A round that draws one field element has p ^ 3 typed challenges. -/
theorem card_one_elem (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) :
    Nat.card (_root_.Run.Ch .two e k) = Fmt.Fld.two.p ^ 3 := by
  have e0 : Fmt.dsOf e k = [.elem, .trits 0] := h
  show Nat.card (_root_.Run.Vals .two (Fmt.dsOf e k)) = _
  rw [card_vals_all, e0]
  show Fmt.Fld.two.p ^ 3 * (4 ^ 0 * 1) = _
  rw [pow_zero, Nat.mul_one, Nat.mul_one]

/-- A block whose one declared round states no item and opens nothing: a yes of its step at one
round and whatever columns is a yes at the round without a message, at no columns. -/
theorem step_plain {T Cl : Type} {ft : ℕ} {b : Block T Cl} {d : Fmt.DeclaredRound} (hb : b.rounds = [d])
    (hi : d.items = []) (hs : d.stored = []) (ho : d.opens = []) {s t : T} {r : Fmt.RoundView}
    {cols : List Desc.OpenedColumn} {m : ℕ} (h : b.step ft s [r] cols = .ok (t, m)) :
    b.step ft s [⟨[], r.drawn⟩] [] = .ok (t, m) := by
  obtain ⟨h1, h2, h3, h4⟩ := (Sound.step_ok_iff ft b s t [r] cols m).1 h
  have hv : r.vals = [] := by
    rw [hb] at h1
    simp only [roundsFit, hi, List.filter_nil, Bool.and_eq_true, beq_iff_eq] at h1
    exact List.map_eq_nil_iff.1 h1.1.1.1.1.1.1.1
  have hr : (⟨[], r.drawn⟩ : Fmt.RoundView) = r := by
    obtain ⟨v, dr⟩ := r
    obtain rfl : v = [] := hv
    rfl
  have hm : m = 0 := by
    rw [h3, hb]
    simp [groupsOf, hs, ho]
  subst hm
  rw [hr]
  refine (Sound.step_ok_iff ft b s t [r] [] 0).2 ⟨h1, ?_, h3, ?_⟩
  · rw [List.take_zero] at h2 ⊢
    exact h2
  · rw [List.take_zero] at h4 ⊢
    exact h4

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The seated batching block declares one round: the batching's entry, no item, nothing opened. -/
theorem batch_decl (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    (p : K9.Where) (hp : IM.k9At Z l = some p) : b.rounds = [{ entry := K9.entry p }] := by
  obtain ⟨Lk', p', w, T, e1', hp', -, -, -, -, hbL, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  have key : ∀ Lk : Link S Claim, c.links[l]? = some Lk →
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) →
      b.rounds = [{ entry := K9.entry p' }] := by
    intro Lk e1 hflat
    obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
    obtain rfl := Option.some.inj (hflat.symm.trans hb)
    rw [IM.alone_rounds (hbL _)]
    rfl
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached_head hS hR O
    exact key Lk e1 hflat
  · rw [if_neg h24] at key
    by_cases he : l % 2 = 0
    · obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_pos he])
      exact key Lk e1 hflat
    · obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached_att hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_neg he])
      exact key Lk e1 hflat

/-- **At the seated batching block the test with code IS the event that is counted.** -/
theorem units_iff (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    (nU : Array Nat) (s : S) (dr : Fmt.Drawn) :
    unitsT b nU s [dr] = true ↔
      ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
        b.step 0 s [r] cols = .ok (t, m) ∧ zeroUnitAt nU t = true := by
  obtain ⟨-, p, -, -, -, hp, -⟩ := (IM.k9_of hS hR O).2 l hl
  have hd := batch_decl hS hR O hl b hb p hp
  constructor
  · intro h
    rw [unitsT_one] at h
    cases hst : b.step 0 s [⟨[], dr⟩] [] with
    | error x =>
      rw [hst] at h
      cases h
    | ok y =>
      obtain ⟨t, m⟩ := y
      rw [hst] at h
      exact ⟨_, [], t, m, rfl, hst, h⟩
  · rintro ⟨r, cols, t, m, rfl, h1, h2⟩
    rw [unitsT_one, step_plain hd (batch_items p) rfl rfl h1]
    exact h2

/-- **The local bound for the test with code.** -/
theorem units_gate_test (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (C : CK) (d : RDT) (el : C.Ch d.entry d.kind → Cb.Gl.E) (w : ℕ)
        (_ : ∀ y, Prob.cnt (fun a => el a = y) ≤ w)
        (_ : ∀ a, (C.dr d.entry d.kind a).elems = [Slice.ofE (el a)])
        (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Iop.prRho {ρ : Iop.Rho (uLT C [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ X) s (drawnT C [d] ρ) = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) /
            (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro C d el w hw hel z s hr
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans (h C d el w hw hel z s hr)
  obtain ⟨a, u⟩ := ρ
  refine ⟨C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a), rfl, ?_⟩
  have hρ' : unitsT b (ProofFile.k8NU Bs.G₀ X) s
      [C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)] = true := hρ
  rw [unitsT_one] at hρ'
  cases hst : b.step 0 s [⟨[], C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)⟩] [] with
  | error x =>
    rw [hst] at hρ'
    cases hρ'
  | ok y =>
    obtain ⟨t, m⟩ := y
    rw [hst] at hρ'
    exact ⟨_, [], t, m, rfl, hst, hρ'⟩

/-- **At typed challenges, over p ^ 3.** -/
theorem units_gate_p3 (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ X) s (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate_test hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 z s hr
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have k := h (_root_.Run.ck .two) d (elOf d.entry d.kind) 1 (elOf_one _ _ h1)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind a).elems = _
      rw [shows_chi _ _ h1]
      rfl) z s hr
  rw [Nat.mul_one] at k
  rw [← card_one_elem d.entry d.kind h1]
  exact k

end

end P1K8

#print axioms P1K8.card_one_elem
#print axioms P1K8.step_plain
#print axioms P1K8.batch_decl
#print axioms P1K8.units_iff
#print axioms P1K8.units_gate_test
#print axioms P1K8.units_gate_p3
