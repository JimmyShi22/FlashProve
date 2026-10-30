-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Toy/Teeth.lean: the 14 named hypotheses of Johnson/Top/OnFilesAt.lean hold together at a
toy description in which the relation does the work, with nothing assumed.

In the toy of Johnson/Top/Toy/Trivial.lean the relaxed relation is True and `build` itself refuses
every output that is not the model's; so the hypothesis `sound` holds there without a look at the
relation. Here `build` builds an instance from every prompt with output tokens (the list of the
output tokens), the relaxed relation says "all tokens are 0", and the proof file's verifier decides
it: it rejects every other instance. Definitions, statements and proofs.
Main names:
  `teeth_holes`: there is a description a with `HolesAt a` at εs = 0, whose `build` refuses nothing,
    at which some instance is not true, and whose proof file's verifier rejects something.
  `teeth_sound`: the conclusion of `verify_sound_at` there, with no hypothesis left.
Limits: still a toy of the form. There is one index, every word decodes to it and no word has a
collision: the hypotheses on the key file and the entry file hold because their languages are all of
the space. The proof file's protocol has one silent round and a verifier that decides the relation
by itself: no oracle is read, no error is paid (εs = 0). Nothing is proved here on whether
`verifyAt` accepts anything. The wire of the record and the coding are existences by choice.

-/
import Johnson.Top.Toy.Trivial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles.Toy.Teeth
open Rom ZKCP Iop Prob Compile Compile.Batch Compile.Batch.Cms

/-- A protocol of the shape s that reads nothing and accepts an instance (a list of tokens, with a
record) if and only if all its tokens are 0. -/
def zeros {R : Type} {E : ExtSpec} (s : Shape) : InteractiveOracleProof (List Token × R) E where
  shape := s
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun a _ _ => a.1.all (· == 0)

theorem zeros_local {R : Type} {E : ExtSpec} (s : Shape) :
    (zeros s : InteractiveOracleProof (List Token × R) E).IsLocal :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- One index, one seed, one answer; no word has a collision; every word decodes; an instance is a
list of tokens. -/
def T0 : HolographicProtocol Unit (List Token) where
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
  onlineBatch := ⟨zeros s1, RoundSplits.allLocal s1⟩
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => Strat.dflt _ (),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()),
                        strat := fun _ _ _ => Strat.dflt _ (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (),
                               strat0 := fun _ _ => SStrat.hollow _ _, strat := fun _ _ _ _ => LStrat.hollow _ _,
                               Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- The toy, passed: its verifier messages made from blocks of digests, no work. -/
def Tp : HolographicProtocol Unit (List Token) :=
  (T0.pull σ1 σ1 σ1).grind (Fin (2 ^ 64)) (GBits.zero _) (GBits.zero _) (GBits.zero _)

theorem key_sound : ∃ ε, Err.Below ε 0 ∧
    Tp.offline.Sound (fun rec y => Tp.hasCollisionAt y rec.1 ∨ Tp.decodeIndex y rec ≠ none) ε :=
  ⟨zeroErr _, below_zeroErr _ _, fun _ _ h => absurd (Or.inr (Option.some_ne_none ())) h⟩

theorem entry_sound : ∃ ε, Err.Below ε 0 ∧ Tp.link.Sound
    (fun rr y =>
      Tp.decodeIndex y.1 rr.1 = none ∨ Tp.hasCollisionAt y.2 rr.2.1 ∨ Tp.decodeIndex y.2 rr.2 = Tp.decodeIndex y.1 rr.1) ε :=
  ⟨zeroErr _, below_zeroErr _ _, fun _ _ h => absurd (Or.inr (Or.inr rfl)) h⟩

theorem proof_sound :
    ∃ (wit : List Token × Tp.Rec → (oneExternalString Tp.wordLength Tp.Symbol).Str → Tr Tp.onlineBatch.loc.shape → Unit) (ε : _),
      Err.Below ε 0 ∧ ∀ rec, (Tp.batAt rec).SndBKT Tp.maxBatchSize Tp.early Tp.late
        (Tp.relB (fun _ x (_ : Unit) => ∀ t ∈ x, t = 0) rec) (fun x y τ => wit (x, rec) y τ) ε := by
  refine ⟨fun _ _ _ => (), zeroErr _, below_zeroErr _ _, fun rec => ?_⟩
  refine (sndBP_iff (List Token) _ (Tp.batAt rec) Tp.maxBatchSize _ _).2
    ⟨fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ x _ _ hacc => Or.inr ⟨(), rfl, fun t ht =>
        beq_iff_eq.1 (List.all_eq_true.1 hacc t ht)⟩, fun y x => jointLaw_false _ _ _ _ _ ?_⟩
  intro j S hS τ
  cases hj : x j with
  | none => simp [hj] at hS
  | some x' =>
      simp only [hj, Option.map_some, Option.some.injEq] at hS
      subst hS
      rfl

def K1 : ℕ := Shape.Draws.maxB _ d1

/-- The library's generic wires at the passed toy. -/
def WT : QueryLayout 256 Tp.carrierC :=
  wireOf (K1 + 1)
    ((ProtocolQueryLayout.ofLocalD 256 K1 T0.offline pt1 d1 (numPosOf _ pt1) (WireE.one T0.wordLength T0.Symbol ()) 0
      (Nat.clog 2 T0.wordLength)).grindLocal cap64 (GBits.zero _))
    ((ProtocolQueryLayout.ofLocalD 256 K1 T0.link pt1 d1 (numPosOf _ pt1) (WireE.two T0.wordLength T0.Symbol ()) 0
      (Nat.clog 2 T0.wordLength)).grindLocal cap64 (GBits.zero _))
    ((ProtocolQueryLayout.ofDraws 256 K1 T0.onlineBatch pt1 d1 (numPosBOf _ _ pt1) (WireE.one T0.wordLength T0.Symbol ()) 0
      (Nat.clog 2 T0.wordLength)).grind cap64 (GBits.zero _))
    (Nat.clog 2 T0.wordLength) 0

instance : Countable Tp.Rec := inferInstanceAs (Countable (Unit × Unit))
instance : Countable T0.Rec := inferInstanceAs (Countable (Unit × Unit))

theorem seed_exists : ∃ Sd : OutOfDomainSampleQueryLayout 256 WT.K Tp, Sd.OK ∧ Sd.Law 0 := by
  obtain ⟨Sd, hSd, hLaw⟩ := exists_seedW (lam := 256) Tp (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (K1 + 1) 0 0 0 0 (Nat.zero_le _)
    (by show Fintype.card Unit * 2 ^ 0 ≤ 2 ^ (256 * 0); simp)
    (fun y => le_of_eq (Prob.cnt_false fun _ h => h)) (by simp)
  exact ⟨Sd, hSd, hLaw.mono (by simp)⟩

theorem wires_ok (Sd : OutOfDomainSampleQueryLayout 256 WT.K Tp) (hSd : Sd.OK) : OKC WT Sd :=
  okc_passed (Fin (2 ^ 64)) T0 pt1 pt1 pt1 d1 d1 d1 (numPosOf _ pt1) (numPosOf _ pt1)
    (numPosBOf _ _ pt1) () 0 0 0 K1 0 le_rfl le_rfl le_rfl (fun _ _ _ => le_rfl)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) rfl cap64 0 (cap64_ok_le (Nat.zero_le _))
    (Nat.zero_le _) (GBits.zero _) (GBits.zero _) (GBits.zero _) ⟨le_rfl, trivial⟩
    ⟨le_rfl, trivial⟩ ⟨le_rfl, trivial⟩ Sd hSd

theorem ctb1 : CtbSh s1 :=
  ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable Unit)⟩, trivial⟩

theorem impl_exists : ∃ m : OracleCoding (spec 256 WT.K Tp.carrierC) 256,
    m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 :=
  exists_impl_passed 256 WT.K (Fin (2 ^ 64)) T0 (inferInstanceAs (Countable Unit)) ctb1 ctb1
    (ctbS_allLocal ctb1) σ1 σ1 σ1 (GBits.zero _) (GBits.zero _) (GBits.zero _)

theorem key_countable : Countable (KeyRoot 256 Tp) :=
  Function.Injective.countable (f := fun k : KeyRoot 256 Tp => (k.cm, k.rcd)) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases h
    rfl)

def dig0 : Dig 256 := fun _ => false
def key0 : KeyRoot 256 Tp := ⟨dig0, ((), ())⟩
def prf0 : PrfRoot 256 Tp := ⟨none, (dig0, ((), ()), none), none⟩

/-- The toy description, at a wire of the record and a coding. The model: the next token is always
0. The instance that is built from a prompt with output tokens is the list of the output tokens,
whatever they are. -/
def teethAt (Sd : OutOfDomainSampleQueryLayout 256 WT.K Tp) (m : OracleCoding (spec 256 WT.K Tp.carrierC) 256) :
    DescriptionAt where
  I := Unit
  X := List Token
  L := Tp
  Wn := Unit
  Rno := fun _ x _ => ∀ t ∈ x, t = 0
  W := WT
  Sd := Sd
  p := ⟨0, 0, 0, 0⟩
  m := m
  enc := codeUnderTag 0 key_countable
  ext := (Special.extOf (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample WT))).digestKey (codeUnderTag 0 key_countable)
  εId := fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
  build := fun x' _ => some x'.2
  nextToken := fun _ _ => some 0
  ISK := Unit
  commit := fun _ => OComp.pure (key0, ())
  prove := fun _ b => OComp.pure ⟨b.map fun _ => prf0, List.length_map _⟩
  bound := 0
  π₀ := (key0, prf0)
  x₀ := []
  εs := 0

/-- All fourteen, at the toy with teeth. -/
theorem teeth_holes : ∃ a : DescriptionAt, HolesAt a ∧ a.εs = 0 ∧
    (∀ x' b, (a.build x' b).isSome) ∧ (∃ i x, ¬ IsTrueAt a i x) ∧
    (∃ x, ∀ y τ, a.L.onlineBatch.loc.accept x y τ = false) := by
  obtain ⟨Sd, hSd, hLaw⟩ := seed_exists
  obtain ⟨m, -, -⟩ := impl_exists
  have hW := wires_ok Sd hSd
  refine ⟨teethAt Sd m, ⟨⟨fun _ _ h => h.elim, key_sound, entry_sound, proof_sound, rfl,
    ((yes_local s1).pull σ1).grind _, ((yes_local s1).pull σ1).grind _,
    ((zeros_local s1).pull σ1).grind _,
    BatchGrind.coherent_grind _ (BatchPull.coherent_pull σ1 (BatchOne.BAnn.allLocal_coherent s1)),
    hLaw, ⟨hW.base, hW.T, hW.Lk, hW.B⟩, hW.seed.inj,
    HoleAt.commitment_of_code _ (codeUnderTag_oneToOne 0 key_countable) rfl fun _ => rfl⟩, ?_⟩,
    rfl, fun _ _ => rfl, ⟨(), [1], ?_⟩, ⟨([1], ((), ())), fun _ _ => rfl⟩⟩
  · intro i x' b x hb hx position hpos
    obtain ⟨_, hw⟩ := hx
    have hx' : x = x'.2 := (Option.some.inj hb).symm
    subst hx'
    show some 0 = some x'.2[position]
    rw [hw _ (List.getElem_mem hpos)]
  · rintro ⟨_, hw⟩
    exact absurd (hw 1 (List.mem_singleton.2 rfl)) (by decide)

/-- The theorem fires: no hypothesis is left. -/
theorem teeth_sound : ∃ a : DescriptionAt,
    SoundForWith (systemAt a) (extractorAt a) (systemAt a).IsModelOutput (soundnessErrorAt a) :=
  let ⟨a, h, _⟩ := teeth_holes
  ⟨a, verify_sound_at a h⟩

end VerifiableInference.OnPublicFiles.Toy.Teeth

#print axioms VerifiableInference.OnPublicFiles.Toy.Teeth.teeth_holes
#print axioms VerifiableInference.OnPublicFiles.Toy.Teeth.teeth_sound
