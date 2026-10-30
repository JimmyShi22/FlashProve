-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Toy/Trivial.lean: the 14 named hypotheses of Johnson/Top/OnFilesAt.lean hold together at
a toy description, with nothing assumed; so its theorem fires there.

A guard against a hollow theorem: `verify_sound_at` takes `HolesAt a`; if no description met these
hypotheses together, it would say nothing. Definitions, statements and proofs.
The toy: one index, one instance, one seed, one answer; no word has a collision; every word decodes
to the one index; the relaxed relation is True; each of the three protocols has one round in which
nothing is said, reads nothing and accepts; one slot. It is passed as the compiler asks (verifier
messages made from blocks of digests, no work). The wires are the library's generic ones
(`okc_passed`, Johnson/RecCompile/Wire.lean), the wire of the record is `exists_seedW`'s
(Johnson/RecCompile/SeedBS.lean), the coding `exists_impl_passed`'s
(Johnson/RecCompile/OneAny.lean), the key's code `codeUnderTag`
(VerifiableInference/KeyCode.lean). The model: the next token is always 0. An instance is built
from a prompt with output tokens if and only if all output tokens are 0.
Main names:
  `toy_holes`: there is a description a with `HolesAt a`, at the stated bound εs = 0 on a round's
    error, whose `build` is as said.
  `toy_sound`: so there is a description at which the conclusion of `verify_sound_at` holds with no
    hypothesis left.
  `jointLaw_false`: state functions that are 0 everywhere meet the law on verifier messages.
Limits: THE TOY SHOWS THE FORM ALONE. Its three hypotheses on soundness hold because their languages
are all of the space (every word decodes, to the one index; the relation is True): no verifier is
tested by them. What carries the claim at the toy is `build`, which refuses every output that is not
the model's. Nothing is proved here on whether `verifyAt` accepts anything. Completeness of the
compiled verifier with a record is stated in Johnson/RecCompile/HonestComplete.lean
[not in this library] and is not put to this toy; so here read: not proved in this library. The wire
of the record and the coding are existences by choice. It says nothing on any description of a
program.

-/
import Johnson.Top.OnFilesAt
import Johnson.RecCompile.OneAny
import Johnson.RecCompile.JoinAll
import CompileK.FitExists
import Iop.GrindCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles.Toy
open Rom ZKCP Iop Prob Compile Compile.Batch Compile.Batch.Cms

/-- A round in which nothing is said: no oracle position, one plain value, one verifier message. -/
def r1 : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun p => p.elim
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := Unit
  dOrc := ()
  dPlain := ()

def s1 : Shape := [r1]
def pt1 : s1.IsPoint :=
  (⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩, ())

/-- A protocol of the shape s that reads nothing and accepts. -/
def yes {Y : Type} {E : ExtSpec} (s : Shape) : InteractiveOracleProof Y E where
  shape := s
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- One index, one instance, one seed, one answer; no word has a collision; every word decodes. -/
def L0 : HolographicProtocol Unit Unit where
  wordLength := 1
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  OutOfDomainSeed := Unit
  OutOfDomainAnswer := Unit
  honestOutOfDomainAnswer := fun _ _ _ => ()
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => some ()
  offline := yes s1
  link := yes s1
  maxBatchSize := 1
  onlineBatch := ⟨yes s1, RoundSplits.allLocal s1⟩
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => Strat.dflt _ (),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()),
                        strat := fun _ _ _ => Strat.dflt _ (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (),
                               strat0 := fun _ _ => SStrat.hollow _ _, strat := fun _ _ _ _ => LStrat.hollow _ _,
                               Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

theorem yes_local {Y : Type} {E : ExtSpec} (s : Shape) : (yes s : InteractiveOracleProof Y E).IsLocal :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- A family of state functions that are 0 everywhere meets the law on verifier messages. -/
theorem jointLaw_false (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (ε : Err s)
    (Sf : Fin N → Option (PTr s → Bool)), (∀ j S, Sf j = some S → ∀ τ, S τ = false) →
    JointLaw N s A ε Sf
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), Sf, h => by
      intro m0 m
      refine ⟨?_, fun v => jointLaw_false N s A ε _ ?_⟩
      · cases hk : a.kind with
        | lo =>
            intro j S hS _
            exact le_of_eq_of_le (Prob.cnt_false fun c => by simp [h j S hS]) (Nat.zero_le _)
        | sh =>
            refine le_of_eq_of_le (Prob.cnt_false fun c => ?_) (Nat.zero_le _)
            rintro ⟨j, S, hS, -, h2⟩
            simp [h j S hS] at h2
      · intro j S hS τ
        cases hj : Sf j with
        | none => simp [hj] at hS
        | some S' =>
            simp only [hj, Option.map_some, Option.some.injEq] at hS
            subst hS
            exact h j S' hj _

/-- the list of errors 0 -/
def zeroErr : (s : Shape) → Err s
  | [] => ()
  | _ :: s => (0, zeroErr s)

theorem below_zeroErr : ∀ (s : Shape) (c : ℝ≥0∞), Err.Below (zeroErr s) c
  | [], _ => trivial
  | _ :: s, c => ⟨by simp, below_zeroErr s c⟩

def d1 : s1.Draws 256 := drawsOf 256 64 s1
def σ1 : Samplers s1 := Samplers.ofDraws _ d1

/-- The toy, passed: its verifier messages made from blocks of digests, no work. -/
def Lp : HolographicProtocol Unit Unit :=
  (L0.pull σ1 σ1 σ1).grind (Fin (2 ^ 64)) (GBits.zero _) (GBits.zero _) (GBits.zero _)

theorem key_sound : ∃ ε, Err.Below ε 0 ∧
    Lp.offline.Sound (fun rec y => Lp.hasCollisionAt y rec.1 ∨ Lp.decodeIndex y rec ≠ none) ε :=
  ⟨zeroErr _, below_zeroErr _ _, fun _ _ h => absurd (Or.inr (Option.some_ne_none ())) h⟩

theorem entry_sound : ∃ ε, Err.Below ε 0 ∧ Lp.link.Sound
    (fun rr y =>
      Lp.decodeIndex y.1 rr.1 = none ∨ Lp.hasCollisionAt y.2 rr.2.1 ∨ Lp.decodeIndex y.2 rr.2 = Lp.decodeIndex y.1 rr.1) ε :=
  ⟨zeroErr _, below_zeroErr _ _, fun _ _ h => absurd (Or.inr (Or.inr rfl)) h⟩

theorem proof_sound :
    ∃ (wit : Unit × Lp.Rec → (oneExternalString Lp.wordLength Lp.Symbol).Str → Tr Lp.onlineBatch.loc.shape → Unit) (ε : _),
      Err.Below ε 0 ∧ ∀ rec, (Lp.batAt rec).SndBKT Lp.maxBatchSize Lp.early Lp.late
        (Lp.relB (fun _ _ (_ : Unit) => True) rec) (fun x y τ => wit (x, rec) y τ) ε := by
  refine ⟨fun _ _ _ => (), zeroErr _, below_zeroErr _ _, fun rec => ?_⟩
  refine (sndBP_iff Unit _ (Lp.batAt rec) Lp.maxBatchSize _ _).2
    ⟨fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ _ => Or.inr ⟨(), rfl, trivial⟩, fun y x => jointLaw_false _ _ _ _ _ ?_⟩
  intro j S hS τ
  cases hj : x j with
  | none => simp [hj] at hS
  | some x' =>
      simp only [hj, Option.map_some, Option.some.injEq] at hS
      subst hS
      rfl

def K1 : ℕ := Shape.Draws.maxB _ d1

/-- The library's generic wires at the passed toy. -/
def W1 : QueryLayout 256 Lp.carrierC :=
  wireOf (K1 + 1)
    ((ProtocolQueryLayout.ofLocalD 256 K1 L0.offline pt1 d1 (numPosOf _ pt1) (WireE.one L0.wordLength L0.Symbol ()) 0
      (Nat.clog 2 L0.wordLength)).grindLocal cap64 (GBits.zero _))
    ((ProtocolQueryLayout.ofLocalD 256 K1 L0.link pt1 d1 (numPosOf _ pt1) (WireE.two L0.wordLength L0.Symbol ()) 0
      (Nat.clog 2 L0.wordLength)).grindLocal cap64 (GBits.zero _))
    ((ProtocolQueryLayout.ofDraws 256 K1 L0.onlineBatch pt1 d1 (numPosBOf _ _ pt1) (WireE.one L0.wordLength L0.Symbol ()) 0
      (Nat.clog 2 L0.wordLength)).grind cap64 (GBits.zero _))
    (Nat.clog 2 L0.wordLength) 0

instance : Countable Lp.Rec := inferInstanceAs (Countable (Unit × Unit))
instance : Countable L0.Rec := inferInstanceAs (Countable (Unit × Unit))

theorem seed_exists : ∃ Sd : OutOfDomainSampleQueryLayout 256 W1.K Lp, Sd.OK ∧ Sd.Law 0 := by
  obtain ⟨Sd, hSd, hLaw⟩ := exists_seedW (lam := 256) Lp (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (K1 + 1) 0 0 0 0 (Nat.zero_le _)
    (by show Fintype.card Unit * 2 ^ 0 ≤ 2 ^ (256 * 0); simp)
    (fun y => le_of_eq (Prob.cnt_false fun _ h => h)) (by simp)
  exact ⟨Sd, hSd, hLaw.mono (by simp)⟩

theorem wires_ok (Sd : OutOfDomainSampleQueryLayout 256 W1.K Lp) (hSd : Sd.OK) : OKC W1 Sd :=
  okc_passed (Fin (2 ^ 64)) L0 pt1 pt1 pt1 d1 d1 d1 (numPosOf _ pt1) (numPosOf _ pt1)
    (numPosBOf _ _ pt1) () 0 0 0 K1 0 le_rfl le_rfl le_rfl (fun _ _ _ => le_rfl)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) rfl cap64 0 (cap64_ok_le (Nat.zero_le _))
    (Nat.zero_le _) (GBits.zero _) (GBits.zero _) (GBits.zero _) ⟨le_rfl, trivial⟩
    ⟨le_rfl, trivial⟩ ⟨le_rfl, trivial⟩ Sd hSd

theorem ctb1 : CtbSh s1 :=
  ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable Unit)⟩, trivial⟩

theorem impl_exists : ∃ m : OracleCoding (spec 256 W1.K Lp.carrierC) 256,
    m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 :=
  exists_impl_passed 256 W1.K (Fin (2 ^ 64)) L0 (inferInstanceAs (Countable Unit)) ctb1 ctb1
    (ctbS_allLocal ctb1) σ1 σ1 σ1 (GBits.zero _) (GBits.zero _) (GBits.zero _)

theorem key_countable : Countable (KeyRoot 256 Lp) :=
  Function.Injective.countable (f := fun k : KeyRoot 256 Lp => (k.cm, k.rcd)) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases h
    rfl)

def dig0 : Dig 256 := fun _ => false
def key0 : KeyRoot 256 Lp := ⟨dig0, ((), ())⟩
def prf0 : PrfRoot 256 Lp := ⟨none, (dig0, ((), ()), none), none⟩

/-- The toy description, at a wire of the record and a coding. The model: the next token is always
0. An instance is built from a prompt with output tokens if and only if all output tokens are 0. -/
def toyAt (Sd : OutOfDomainSampleQueryLayout 256 W1.K Lp) (m : OracleCoding (spec 256 W1.K Lp.carrierC) 256) : DescriptionAt where
  I := Unit
  X := Unit
  L := Lp
  Wn := Unit
  Rno := fun _ _ _ => True
  W := W1
  Sd := Sd
  p := ⟨0, 0, 0, 0⟩
  m := m
  enc := codeUnderTag 0 key_countable
  ext := (Special.extOf (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W1))).digestKey (codeUnderTag 0 key_countable)
  εId := fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
  build := fun x' _ => if x'.2.all (· == 0) then some () else none
  nextToken := fun _ _ => some 0
  ISK := Unit
  commit := fun _ => OComp.pure (key0, ())
  prove := fun _ b => OComp.pure ⟨b.map fun _ => prf0, List.length_map _⟩
  bound := 0
  π₀ := (key0, prf0)
  x₀ := ()
  εs := 0

/-- All fourteen, at the toy. -/
theorem toy_holes : ∃ a : DescriptionAt, HolesAt a ∧ a.εs = 0 ∧
    (∀ p o b, (a.build (p, o) b).isSome ↔ ∀ t ∈ o, t = 0) := by
  obtain ⟨Sd, hSd, hLaw⟩ := seed_exists
  obtain ⟨m, -, -⟩ := impl_exists
  have hW := wires_ok Sd hSd
  refine ⟨toyAt Sd m, ⟨⟨fun _ _ h => h.elim, key_sound, entry_sound, proof_sound, rfl,
    ((yes_local s1).pull σ1).grind _, ((yes_local s1).pull σ1).grind _,
    ((yes_local s1).pull σ1).grind _,
    BatchGrind.coherent_grind _ (BatchPull.coherent_pull σ1 (BatchOne.BAnn.allLocal_coherent s1)),
    hLaw, ⟨hW.base, hW.T, hW.Lk, hW.B⟩, hW.seed.inj,
    HoleAt.commitment_of_code _ (codeUnderTag_oneToOne 0 key_countable) rfl fun _ => rfl⟩, ?_⟩,
    rfl, ?_⟩
  · intro i x' b x hb _ position hpos
    have hall : x'.2.all (· == 0) = true := by
      by_contra hc
      have : (toyAt Sd m).build x' b = none := if_neg hc
      rw [this] at hb
      cases hb
    have h0 := List.all_eq_true.1 hall _ (List.getElem_mem hpos)
    show some 0 = some x'.2[position]
    rw [beq_iff_eq.1 h0]
  · intro p o b
    show (if o.all (· == 0) then some () else none : Option Unit).isSome ↔ _
    by_cases hc : o.all (· == 0) = true
    · rw [if_pos hc]
      exact ⟨fun _ t ht => beq_iff_eq.1 (List.all_eq_true.1 hc t ht), fun _ => rfl⟩
    · rw [if_neg hc]
      exact ⟨fun h => Bool.noConfusion h,
        fun h => absurd (List.all_eq_true.2 fun t ht => beq_iff_eq.2 (h t ht)) hc⟩

/-- The theorem fires: no hypothesis is left. -/
theorem toy_sound : ∃ a : DescriptionAt,
    SoundForWith (systemAt a) (extractorAt a) (systemAt a).IsModelOutput (soundnessErrorAt a) :=
  let ⟨a, h, _⟩ := toy_holes
  ⟨a, verify_sound_at a h⟩

end VerifiableInference.OnPublicFiles.Toy

#print axioms VerifiableInference.OnPublicFiles.Toy.toy_holes
#print axioms VerifiableInference.OnPublicFiles.Toy.toy_sound
