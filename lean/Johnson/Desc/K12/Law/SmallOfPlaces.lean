-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K12.Law.CodesJoh
import Johnson.Bridge.FoldPriced
import OnBytes.Slice.PricedRound
/-
Johnson/Desc/K12/Law/SmallOfPlaces.lean: K12's condition, its field «small», at the Johnson letters and the bar 2^-128: from one Boolean on natural numbers that is handed the radii and the brackets. The bridge from the comparison of natural numbers (Johnson/Bridge/BasePriced.lean: below_of_num; Johnson/Bridge/BaseCodesAt.lean: Br) to K12's files' field (ChainHolds.lean: K12Condition.small). Nothing on hiding. **No soundness of the release is claimed.**
It calls two names of Johnson/Bridge/'s files (below_of_num · Br, with Br.ok | Br.le) and follows the form of FoldedPlace | LastPlace (.priced) in its clauses.
  roundB · below_of_roundB     one written round and a count: the entry's own numbers and one comparison of natural numbers ⇒ RoundBelow count w.rd (2⁻¹ ^ 128). N is the round's own number of typed values (nVals of its draws): no form of the round is asked.
  brB · flC_le · flZ_le        two brackets at a stage and its radius ⇒ the letters flC | flZ are at most written numbers.
  [plainAt_chainFrom: the place's chain at Letters.at has the letters' counts: K12's files' own (ChainJoh.lean): called.]
  smallCl · smallAll · smallOk the gate: at a stage that is folded and switched: the brackets · five or six comparisons (the fold's first round · its repeated round, without and with mask rows · the switch's seed · the switch's positions); at the last stage: the brackets · two.
  smallAt_walk                 the gate's yes ⇒ the library's Chain.SmallAt at lstJ · flC · flZ · flZ.
  small_of_ok                  smallOk rad B p = true ⇒ K12Condition's field «small», to the letter, at L := Sg.lstJ · mC := Sg.flC · mS := mW := Sg.flZ · the handed rad · εs := 2⁻¹ ^ 128.
  condition_of                 the four fields laid together.
  k12Condition_of_four         K12's condition at the Johnson letters and the bar, from four Booleans: pubOk p K · spendOk p · johOk p r (the three of K12's files; CodesJoh.lean: k12Condition_joh) · smallOk (fun s => r s.st) B p: no premise beside them.
The two silly members, read for a gate. A gate that says yes to all: the law is false of it (a last stage with t = 1 at the radius 0 and no work: all positions but one are bad). A gate that says no to all: the law holds and says nothing: that smallOk says yes at a real place is a run's word.
Limits. (1) rad and B are letters: nothing ties them to a planner's radius; none is needed, which is stated and not shown here: no program reads a radius. That the same rad pays «codes» is the caller's: condition_of takes both at one rad. (2) A share of a round's written verifier messages, test bits among them: of the 128 bits a round's bits of work are work: what that is worth against a prover who tries many times is not said. (3) Round by round: no sum. (4) The batching's round «BAT» stands in front of the chain and is not in c.err (stated, not shown here; the gate drops the first written round). (5) Nothing on the plan's prices. (6) The proved count behind flC | flZ rests on ThirdParty/, adapted from ArkLib and Mathlib (lean/LIMITS.md, L15); this file's own statements are arithmetic.
Nothing is left open and nothing is laid down by decree.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Br below_of_num)
open scoped ENNReal

/-! ## One round -/

/-- **One written round and a count**: the entry's positions have at most 64 bits; no more elements other than 0 than elements; at most 62 bits of work where an element is drawn; and the comparison of Johnson/Bridge/BasePriced.lean's below_of_num, at the round's own number of typed values. -/
def roundB (w : WR) (count : Nat) : Bool :=
  decide (w.entry.logN ≤ 64) && decide (w.entry.drawNZ ≤ w.entry.drawE) &&
    (decide (w.entry.drawE = 0) || decide (w.entry.work + 66 ≤ 128)) &&
    decide (0 < nVals (Fmt.dsOf w.entry w.kind)) &&
    decide (count * 2 ^ 193 + 3 * (w.entry.drawE + w.entry.drawNZ) * nVals (Fmt.dsOf w.entry w.kind) ≤
      nVals (Fmt.dsOf w.entry w.kind) * 2 ^ (w.entry.work + 65))

theorem below_of_roundB {w : WR} {count : ℕ} (h : roundB w count = true) :
    RoundBelow count w.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  simp only [roundB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact below_of_num w.rd h1 h2 (fun h0 => h3.resolve_left h0) count _ rfl h4 h5

/-! ## The letters against written numbers -/

/-- The two brackets at a stage and a radius say yes. -/
def brB (s : Sg) (e : ℕ) (b : Br × Br) : Bool :=
  b.1.ok (2 ^ s.C.a) (s.C.r + s.C.l - 1) e &&
    b.2.ok (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e

/-- The written bound for a table of mask rows. -/
def bZof (s : Sg) (e : ℕ) (b : Br × Br) : ℕ := b.2.N + listMax (2 ^ s.C.a) s.dZ e

theorem flC_le {s : Sg} {e : ℕ} {b : Br × Br} (h : brB s e b = true) : s.flC e ≤ b.1.N := by
  unfold brB at h
  exact Br.le (Bool.and_eq_true_iff.1 h).1

theorem flZ_le {s : Sg} {e : ℕ} {b : Br × Br} (h : brB s e b = true) : s.flZ e ≤ bZof s e b := by
  unfold brB at h
  exact Nat.add_le_add_right (Br.le (Bool.and_eq_true_iff.1 h).2) _

/-! ## The gate -/

/-- The clauses at a last stage s with the radius e and the brackets b. -/
def lastCl (s : Sg) (e : ℕ) (b : Br × Br) (dL dB : WR) : Clauses :=
  [("small.brackets", brB s e b), ("small.lambda", roundB dL (b.1.N + bZof s e b + s.lstJ e)),
   ("small.base", roundB dB ((2 ^ s.C.a - e - 1) ^ s.t))]

/-- The clauses at a stage s that is folded and switched into s', with the radii e and e'. -/
def stepCl (s s' : Sg) (e e' : ℕ) (b : Br × Br) (dE dT dS dC : WR) : Clauses :=
  [("small.brackets", brB s e b), ("small.eps", roundB dE (s.lstJ e)),
   ("small.two", roundB dT (b.1.N + s.lstJ e * 2)),
   ("small.two with mask rows",
     decide (s.h = 0) || roundB dT (b.1.N + (bZof s e b + bZof s e b) + s.lstJ e * 2)),
   ("small.seed", roundB dS ((s'.lstJ e').choose 2 * clashSeeds (Fmt.Fld.two.p ^ 3) s'.st.na)),
   ("small.cs", roundB dC ((2 ^ s.C.a - e - 1) ^ s.t * Fmt.Fld.two.p ^ 3 +
     (2 ^ s.C.a) ^ s.t * (s'.lstJ e' * (1 + 3 * s.t))))]

/-- **THE GATE's CLAUSES**, along the cut of chainFrom. rad: a radius for each stage. B: two brackets for each stage. -/
def smallCl (rad : Sg → ℕ) (B : Sg → Br × Br) : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → List WR → Clauses
  | j, a, [], l =>
    match l with
    | [dL, dB] => tag j (lastCl (sgOf a) (rad (sgOf a)) (B (sgOf a)) dL dB)
    | _ => [(toString j ++ ":cut at the last stage", false)]
  | j, a, b :: rest, l =>
    match l with
    | dE :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | dS :: dC :: l'' =>
        tag j (stepCl (sgOf a) (sgOf b) (rad (sgOf a)) (rad (sgOf b)) (B (sgOf a)) dE dT dS dC) ++
          smallCl rad B (j + 1) b rest l''
      | _ => [(toString j ++ ":cut: no two rounds behind the fold's", false)]
    | _ => [(toString j ++ ":cut: no two rounds of a fold", false)]

/-- The clauses at the numbers of a place. -/
def smallAll (rad : Sg → ℕ) (B : Sg → Br × Br) (N : H2U.TestNums) : Clauses :=
  match N.stages, writtenOf N with
  | a :: rest, some (_ :: l) => smallCl rad B 0 a rest l
  | _, _ => [("no stage, or the declared rounds cannot be written", false)]

/-- THE GATE. It reads the place's numbers alone. -/
def smallOk (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) : Bool := ok (smallAll rad B p.nums)

def smallNo (rad : Sg → ℕ) (B : Sg → Br × Br) (N : H2U.TestNums) : List String :=
  ((smallAll rad B N).filter (!·.2)).map (·.1)

/-! ## From the gate to the library's clause -/

theorem smallAt_walk (rad : Sg → ℕ) (B : Sg → Br × Br) : ∀ (rest : List Fmt.M1.Stage) (j : Nat) (a : Fmt.M1.Stage)
    (l : List WR) (c : Chain (sgOf a)),
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c →
    ok (smallCl rad B j a rest l) = true →
    c.SmallAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ ((2 : ℝ≥0∞)⁻¹ ^ 128)
  | [], j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · rename_i dL dB
      cases hc
      unfold smallCl at h
      dsimp only at h
      rw [ok_tag] at h
      simp only [lastCl, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨RoundBelow.mono (Nat.add_le_add_right (Nat.add_le_add (flC_le h1) (flZ_le h1)) _)
        (below_of_roundB h2), below_of_roundB h3⟩
    · cases hc
  | b :: rest, j, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · rename_i dE dT l'
      split at hc
      · split at hc
        · rename_i dS dC l'' hd
          unfold smallCl at h
          dsimp only at h
          rw [hd] at h
          dsimp only at h
          rw [ok_append, ok_tag, Bool.and_eq_true] at h
          obtain ⟨h0, hrest⟩ := h
          simp only [stepCl, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
            Bool.or_eq_true, decide_eq_true_eq] at h0
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h0
          cases hn : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            have ih := smallAt_walk rad B rest (j + 1) b l'' next hn hrest
            have hr : next.rad = rad (sgOf b) := rad_chainFrom _ rest b l'' next hn
            have k2 : RoundBelow ((sgOf a).flC (rad (sgOf a)) + (sgOf a).lstJ (rad (sgOf a)) * 2) dT.rd
                ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
              RoundBelow.mono (Nat.add_le_add_right (flC_le h1) _) (below_of_roundB h3)
            have k3 : (sgOf a).h ≠ 0 → RoundBelow ((sgOf a).flC (rad (sgOf a)) +
                ((sgOf a).flZ (rad (sgOf a)) + (sgOf a).flZ (rad (sgOf a))) +
                (sgOf a).lstJ (rad (sgOf a)) * 2) dT.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun h0 =>
              RoundBelow.mono (Nat.add_le_add_right (Nat.add_le_add (flC_le h1)
                (Nat.add_le_add (flZ_le h1) (flZ_le h1))) _) (below_of_roundB (h4.resolve_left h0))
            have k4 : ∀ hf : CsFit (sgOf a) (sgOf b),
                RoundBelow ((csSw hf).W.err1 ((sgOf b).lstJ next.rad)) dS.rd ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
              fun hf => by
                rw [cs_err1, card_GE, hr]
                exact below_of_roundB h5
            have k5 : ∀ hf : CsFit (sgOf a) (sgOf b),
                RoundBelow ((csSw hf).W.err2 (rad (sgOf a)) ((sgOf b).lstJ next.rad)) dC.rd
                  ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
              fun hf => by
                rw [cs_err2, card_GE, hr]
                exact below_of_roundB h6
            split
            · exact ⟨below_of_roundB h2, k2, k3, k4 _, k5 _, ih⟩
            · exact ⟨below_of_roundB h2, k2, k3, k4 _, k5 _, ih⟩
        · cases hc
      · cases hc
    · cases hc

/-- **THE GATE's YES GIVES K12Condition's FIELD «small»**, to the letter, at the Johnson letters, the handed radii and the bar 2^-128. -/
theorem small_of_ok (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) (h : smallOk rad B p = true) :
    ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest → writtenOf p.nums = some (w0 :: l) →
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad) rest a l = some c →
      Err.Below c.err ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  intro a rest w0 l c hs hw hc
  unfold smallOk smallAll at h
  rw [hs, hw] at h
  exact c.err_below_at _ (plainAt_chainFrom _ _ _ _ rad rest a l c hc)
    (smallAt_walk rad B rest 0 a l c hc h)

/-- The four fields laid together, at one rad. -/
theorem condition_of (rad : Sg → ℕ) (B : Sg → Br × Br) (p : P12) (K : Codes)
    (hp : pubOk p K = true) (hs : spendOk p = true)
    (hc : CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p.nums.stages) (h : smallOk rad B p = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨hp, hs, hc, small_of_ok rad B p h⟩

/-- **K12's CONDITION AT THE JOHNSON LETTERS AND THE BAR 2^-128, FROM FOUR BOOLEANS.** r: a radius for each stage. B: two brackets for each stage. -/
theorem k12Condition_of_four (r : Fmt.M1.Stage → ℕ) (B : Sg → Br × Br) (p : P12) (K : Codes)
    (hp : pubOk p K = true) (hs : spendOk p = true) (hj : johOk p r = true)
    (h : smallOk (fun s => r s.st) B p = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_joh r p K _ hp hs hj (small_of_ok _ B p h)

end H2K.Pub

/-- OUTSIDE ANY NONCOMPUTABLE SECTION: Lean compiles this call of the gate, or the file does not compile: so the gate has code. -/
def H2K.Pub.smallOk_hasCode (p : VerifiableInference.Desc.K12.P12) : Bool :=
  H2K.Pub.smallOk (fun _ => 0) (fun _ => (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩)) p

#print axioms H2K.Pub.small_of_ok
#print axioms H2K.Pub.condition_of
#print axioms H2K.Pub.k12Condition_of_four
