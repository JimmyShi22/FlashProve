-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/WholeTest.lean: the definition of Hiop/Whole.lean bites, and the budget of `Spec.hvzk_whole`
cannot be dropped. (The definition: `HVZKWhole`, honest-verifier zero knowledge of the whole object.
"Cannot be dropped" in this sense: `leaky_fails` (`1 ≤ B.reads 0` and
`HVZKWhole leaky Ryes B S z` give 1 ≤ 2·z); see Limits.)

Two tests that the definition can fail ("bites"): two statements with their proofs (`bites`,
`bites_off`), and for each an interface of its kind. An interface is an `Iop.BatchProtocol` (Iop/Batch.lean),
whose offline IOP is `offline`, with the honest side `honestOfflineProver`; simulator, bounds, environment and budget
(`Bounds.Fits`) are those of Hiop/Whole.lean.

Main names:
  Through a read. `Spec.bites`: let L be any interface in which one position p of an encoded index
    tells two indices i, i' apart (whatever the encoding randomness). Then as soon as the bounds
    allow one read of the first encoded index, no simulator has an error below 1/2:
    `HVZKWhole L Ryes B S z` implies 1 ≤ 2·z. (The environment reads position p and says which of
    the two it saw. The simulator is not given the index, so its answer has one law for both.)
  `leaky`: such an interface exists: indices are bits, the encoded index is the bit itself, the
    three protocols have no rounds (`leaky_tells`).
  Through a run. `Spec.bites_off`: if what is shown of the offline IOP tells two indices apart (a
    function f of what is shown is 1 on every run for i and 0 on every run for i'), then no
    simulator has an error below 1/2, for any bounds: no read, no link, no session is needed. So the
    definition would not pass if it showed nothing of the runs (the test: `Spec.bites_off`; no
    variant of `HVZKWhole` is defined in this file).
  `chatty`: such an interface exists: the encoded index is one constant symbol, and the offline
    prover says the index in a plain message (`chatty_fails`).

Limits:
  Not tested: the link's and the sessions' channels (same shape).
  That the hypotheses of `Spec.hvzk_whole` can be met together with errors below 1 is not shown
    here.
  That the hypotheses of `Spec.hvzk_whole` other than the budget (`BatchProtocol.Wired`, `BatchProtocol.Reads`,
    `Sims.Good`) are met at `leaky` is not stated in this file.
  The two tests do not show that every interface that tells two indices apart otherwise than by the
    premises of `Spec.bites` or of `Spec.bites_off` fails the definition.

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeProof

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

namespace Spec

def bites : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (B : Bounds) (S : Simulator L) (z : ℝ≥0∞)
      (i i' : I) (p : Fin L.wordLength),
    (∀ r r', L.encodeIndex i r p ≠ L.encodeIndex i' r' p) → 1 ≤ B.reads 0 → HVZKWhole L Ryes B S z → 1 ≤ 2 * z

def bites_off : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (B : Bounds) (S : Simulator L) (z : ℝ≥0∞)
      (i i' : I) (f : Sess L.offline → Bool),
    (∀ r a, a ∈ (sess L.honestOfflineProver (i, r) ()).support → f a = true) →
    (∀ r a, a ∈ (sess L.honestOfflineProver (i', r) ()).support → f a = false) → HVZKWhole L Ryes B S z → 1 ≤ 2 * z

end Spec

open Classical in
theorem bites : Spec.bites := by
  intro I X L Ryes B S z i i' p hne hB h
  let E : Sess L.offline → Env L Bool := fun _ =>
    .read 0 p fun y => .stop (decide (∃ r, y = L.encodeIndex i r p))
  have hE : ∀ j : I, ∀ a, (E a).Adm B (Ryes j) 0 (fun _ => 0) fun _ => 0 := fun _ _ =>
    ⟨le_rfl, hB, fun _ => trivial⟩
  have hv : ∀ (j : I) (v : Bool), (∀ r, decide (∃ r', L.encodeIndex j r p = L.encodeIndex i r' p) = v) →
      (realHost L j).view E = PMF.pure v := by
    intro j v hj
    rw [realHost_eq, view_host]
    have e1 : ∀ (r : L.EncodingRandomness) (a : Sess L.offline),
        (E a).run (realLaws L j).host (0, fun _ => r) = PMF.pure v := by
      intro r a
      show (Env.read 0 p fun y => Env.stop (decide (∃ r, y = L.encodeIndex i r p))).run
          (realLaws L j).host (0, fun _ => r) = _
      rw [run_read, run_stop]
      exact congrArg PMF.pure (hj r)
    simp only [e1, PMF.bind_const]
  have h1 := h i Bool E (hE i)
  have h2 := h i' Bool E (hE i')
  rw [hv i true fun r => decide_eq_true ⟨r, rfl⟩] at h1
  rw [hv i' false fun r => decide_eq_false fun ⟨r', hr⟩ => hne r' r hr.symm, tv_comm] at h2
  have h3 := (tv_triangle _ _ _).trans (add_le_add h1 h2)
  rw [tv_pure_pure, if_neg (by simp), ← two_mul] at h3
  exact h3

/-! ## Such an interface exists -/

/-- A protocol without rounds that reads nothing and accepts. -/
def noRounds (Y : Type) (E : ExtSpec) : InteractiveOracleProof Y E where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

def noHonest (Y : Type) (E : ExtSpec) (Wt : Type) (ext : Wt → E.Str) :
    Honest (noRounds Y E) Wt where
  Coin := Unit
  ext := ext
  strat := fun _ _ _ => ()
  Bad := ∅
  Hid := fun _ _ => ∅

/-- Indices are bits; the encoded index is the bit. -/
def leaky : BatchProtocol Bool Unit where
  wordLength := 1
  Symbol := Bool
  EncodingRandomness := Unit
  encodeIndex := fun i _ _ => i
  decodeIndex := fun y => some (y 0)
  offline := noRounds Unit _
  link := noRounds Unit _
  maxBatchSize := 1
  onlineBatch := ⟨noRounds Unit _, PUnit.unit⟩
  honestOfflineProver := noHonest Unit _ _ fun w _ => w.1
  honestLinkProver := noHonest Unit _ _ fun w => (fun _ => w.1, fun _ => w.1)
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w _ => w.1, strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- its one position -/
def pos0 : Fin leaky.wordLength := (0 : Fin 1)

theorem leaky_tells : ∀ r r', leaky.encodeIndex true r pos0 ≠ leaky.encodeIndex false r' pos0 := fun _ _ h =>
  Bool.noConfusion h

/-- No simulator of the leaky interface has an error below 1/2 once one read is allowed. (`hB`: one
read of the encoded index number 0) -/
theorem leaky_fails (Ryes : Bool → Unit → Prop) (B : Bounds) (S : Simulator leaky) (z : ℝ≥0∞)
    (hB : 1 ≤ B.reads 0) (h : HVZKWhole leaky Ryes B S z) : 1 ≤ 2 * z :=
  bites Bool Unit leaky Ryes B S z true false pos0 leaky_tells hB h

/-! ## Through a run -/

theorem bind_eq_pure {α β : Type} {p : PMF α} {g : α → PMF β} {v : β}
    (h : ∀ a ∈ p.support, g a = PMF.pure v) : p.bind g = PMF.pure v := by
  have e : p.bind g = p.bind (fun _ => PMF.pure v) := by
    ext b
    simp only [PMF.bind_apply]
    refine tsum_congr fun a => ?_
    by_cases ha : p a = 0
    · simp [ha]
    · rw [h a ((PMF.mem_support_iff _ _).2 ha)]
  rw [e, PMF.bind_const]

theorem bites_off : Spec.bites_off := by
  intro I X L Ryes B S z i i' f h1 h2 h
  let E : Sess L.offline → Env L Bool := fun a => .stop (f a)
  have hE : ∀ j : I, ∀ a, (E a).Adm B (Ryes j) 0 (fun _ => 0) fun _ => 0 := fun _ _ => trivial
  have hv : ∀ (j : I) (v : Bool), (∀ r a, a ∈ (sess L.honestOfflineProver (j, r) ()).support → f a = v) →
      (realHost L j).view E = PMF.pure v := by
    intro j v hj
    refine bind_eq_pure fun p hp => ?_
    obtain ⟨r, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hp
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hr
    show (Env.stop (f a)).run (realHost L j) _ = _
    rw [Env.run, hj r a ha]
  have g1 := h i Bool E (hE i)
  have g2 := h i' Bool E (hE i')
  rw [hv i true h1] at g1
  rw [hv i' false h2, tv_comm] at g2
  have g3 := (tv_triangle _ _ _).trans (add_le_add g1 g2)
  rw [tv_pure_pure, if_neg (by simp), ← two_mul] at g3
  exact g3

/-- One round: a plain bit from the prover, nothing from the verifier. -/
abbrev bitRound : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := Bool,
    Chal := Unit, dOrc := (), dPlain := false }

def talk (E : ExtSpec) : InteractiveOracleProof Unit E where
  shape := [bitRound]
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- The encoded index says nothing (one constant symbol); the offline prover says the index in a
plain message. -/
def chatty : BatchProtocol Bool Unit where
  wordLength := 1
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => none
  offline := talk _
  link := noRounds Unit _
  maxBatchSize := 1
  onlineBatch := ⟨noRounds Unit _, PUnit.unit⟩
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun w _ _ => (((), w.1), fun _ => ()),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := noHonest Unit _ _ fun _ => (fun _ => (), fun _ => ())
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- the bit that was said -/
def said : Sess chatty.offline → Bool := fun a => match a.2 with
  | some v => v.plains.1
  | none => false

theorem said_eq (i : Bool) (r : chatty.EncodingRandomness) (a : Sess chatty.offline)
    (ha : a ∈ (sess chatty.honestOfflineProver (i, r) ()).support) : said a = i := by
  obtain ⟨ρ, _, hρ⟩ := (PMF.mem_support_bind_iff _ _ _).1 ha
  obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hρ
  have hn : ρ ∉ chatty.honestOfflineProver.withheld (i, r) () := fun h => h.elim (fun x => x) (fun x => x)
  unfold Iop.Honest.output at ho
  rw [if_neg hn] at ho
  obtain ⟨c, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
  rfl

/-- No simulator of the chatty interface has an error below 1/2, for any bounds. -/
theorem chatty_fails (Ryes : Bool → Unit → Prop) (B : Bounds) (S : Simulator chatty)
    (z : ℝ≥0∞) (h : HVZKWhole chatty Ryes B S z) : 1 ≤ 2 * z :=
  bites_off Bool Unit chatty Ryes B S z true false said (fun r a ha => said_eq true r a ha)
    (fun r a ha => said_eq false r a ha) h

end Hiop
