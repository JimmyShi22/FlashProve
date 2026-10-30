-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ToyLinksTie.lean: a test: "the proof file's protocol is sound, with a witness",
in the form in which each chain is a link with keys (`proofSound_at_links`,
OnBytes/TypedOracleCompiler/Joined/MidLinks.lean), is applied with every premise proved, at a small interface with
records.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.


Why. In `proofSound_at_links` the bound has no factor for the number of slots: each chain's list of
errors is taken as it is, and the second chain's clause is asked for all slots together, for the
vectors of statements with one key. All the weight lies in that list of premises
(`Links.KnowsJ`). Such a list could be one that nothing meets. This file is a guard against that.

The object. An instance is a prompt and a reply, one bit each; `early` wipes the reply; `late` is
`none`. There is one external string of one bit. A record is a seed and an answer, one bit each; it
decodes to its answer. There are 64 slots. The rounds: front | the reply's round | joining round |
the shared round | seam.
  Chain 1 (local): the prover sends the reply in the clear in a round of its own. The claim "the
    prompt is the record's answer, and the reply that was sent is the right one" goes on; a false
    claim survives at one of two drawn bits. The key that is handed on is the sum of the external
    bit and the record's seed.
  Chain 2 (shared; only the shared part speaks, in the joining round too): a false claim survives at
    the drawn bit that IS THE KEY: 1 of 2. Statements with one key have the same bad verifier
    messages: so THE ERROR IS PAID ONCE, at every number of slots (`link₂`).
  Chain 3 rejects a false claim.
The file's verifier compares the reply that was sent with the instance's. The relation of the
interface has the reply as its witness and says of the instance's OWN reply that it is this witness.

Main names:
  `G`, `C`, `k₁`, `k₂`   the rounds, the description, the keys
  `know₁`, `know₃`, `badOf`, `link₂`   the clauses of the three chains
  `knows N rec`   THE LIST `Links.KnowsJ`, record by record, at every number of slots
  `D`, `out_eq`, `ext_eq`   the file's verifier; what the three chains, and the three extractors, in
                 a row come to
  `L`, `RnW`      the interface with records; the relation
  `decides`, `tieR`   the two premises at `early x`, to the letter
  `toy_proofSound_links`   `proofSound_at_links` applied: no premise is left
  `rnW_reads_reply`, `early_blind`, `other_reply_rejected`, `yes_true`, `false_survives₂`,
  `key_speaks`, `eps₂_once`

Limits: a test: it shows that the premises can be met together, and no more. The statement is on the
interactive protocol: nothing is compiled or run here. A drawn message has one bit, so an error of
one message is the probability 1/2: no small number can be had at this object, and the bound's
value is not computed. The key is a function of the external string and the record, and a batch has
one string and one record: so within one batch all statements have one key by the form of the list;
that the key speaks is seen between strings and between records. Nothing is sent in the shared
round. No seed is a collision seed. Test and Link are idle. The statement is applied at an interface
with records, not at the object of the three files' protocols. That without one key the error is not
paid once is not shown here. Nothing here says that a real file's description has these clauses or
this tie.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.MidLinks
import Run.PlanQS

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.ToyLinks
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc plainRound)
open _root_.CompileK.Joined (KnowJ allKind_const)
open _root_.Prob
open scoped ENNReal

/-! ## The rounds -/

/-- A silent round. -/
@[reducible] def rN : Round := plainRound Unit ()

/-- The reply's round: the prover sends one bit in the clear; the verifier draws one bit. -/
@[reducible] def rP : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Bool
  Chal := Bool
  dOrc := ()
  dPlain := false

/-- The shared round: nothing is sent; the verifier draws one bit. -/
@[reducible] def rS : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := Bool
  dOrc := ()
  dPlain := ()

/-- The rounds: front | the reply's round | joining round | the shared round | seam. In the joining
round only the shared part speaks. -/
@[reducible] def G : Chains := ⟨rN, [rP], rN, [rS], rN, [], RAnn.ofShared .sh rN⟩

/-! ## Instances, records, the description -/

/-- An instance: a prompt and a reply. -/
abbrev Y2 : Type := Bool × Bool

/-- A record: a seed, one bit, and an answer, one bit. -/
abbrev Rc : Type := Bool × Bool

/-- One external string of one bit. -/
abbrev E0 : ExtSpec := oneExternalString 1 Bool

/-- the external bit -/
def bitOf (y : E0.Str) : Bool := (y : Fin 1 → Bool) 0

/-- The key of a batch: the external bit and the record's seed, added. -/
def keyOf (y : E0.Str) (rec : Rc) : Bool := xor (bitOf y) rec.1

/-- What the queries hold of an instance: the reply is wiped. -/
def early (x : Y2) : Y2 := (x.1, false)

/-- The test on the prompt: it is the record's answer. It does not read the reply. -/
def prOK (a : Y2 × Rc) : Bool := a.1.1 == a.2.2

theorem prOK_early (x : Y2) (rec : Rc) : prOK (early x, rec) = prOK (x, rec) := rfl

/-- The description. Chain 1: the claim "the prompt is right and the reply that was sent is the
right one" goes on; a false claim survives at the drawn bit true; the sum of the external bit and
the record's seed is handed on as the key. Chain 2: a false claim survives at the drawn bit that is
the key. Chain 3 rejects a false claim. The first chain's extractor yields the reply that was sent.
-/
@[reducible] def C : Links G ((Y2 × Rc) × E0.Str) where
  A₁ := Bool × Bool
  A₂ := Bool
  W₀ := Bool
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ => some (keyOf a.2 a.1.2, (prOK a.1 && τ.2.2.1.2) || τ.2.2.2.1)
  out₂ := fun b τ => some (b.2 || (τ.2.2.2.1 == b.1))
  out₃ := fun b _ => if b then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a w => prOK a.1 = true ∧ w = true
  R₁ := fun b _ => b.2 = true
  R₂ := fun b _ => b = true
  e₁ := fun _ τ _ => τ.2.2.1.2
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := (0, (1, ()))
  ε₂ := (0, (1, ()))
  ε₃ := (0, ())
  d₀ := false
  d₁ := ()

/-- The key behind chain 1: the first part of what it hands on. -/
def k₁ (b : Bool × Bool) : Bool := b.1

/-- The key behind chain 2: none. -/
def k₂ (_ : Bool) : Unit := ()

/-! ## The three clauses -/

theorem know₁ : C.K₁.Know C.on₀ C.R₀ C.R₁ C.e₁ C.ε₁ := by
  intro a _ m0
  refine le_of_eq (cnt_false fun c0 h0 => h0 ?_)
  intro m1
  have key : ∀ c : Bool, (¬ ∀ (b : Bool × Bool) (_ : Unit),
      (some (keyOf a.2 a.1.2, (prOK a.1 && m1.2) || c) : Option (Bool × Bool)) = some b →
        b.2 = true →
        prOK a.1 = true ∧ m1.2 = true) → c = true := by
    intro c h
    by_contra hn
    refine h fun b _ hb hw => ?_
    have hc : c = false := by
      cases c
      · rfl
      · exact absurd rfl hn
    subst hc
    obtain rfl := Option.some.inj hb
    simpa using hw
  exact cnt_le_one fun c c' hc hc' => (key c hc).trans (key c' hc').symm

theorem know₃ : C.K₃.Know C.on₂ C.R₂ (fun _ _ => True) C.e₃ C.ε₃ := by
  intro a _ m0
  refine le_of_eq (cnt_false fun c0 h0 => h0 ?_)
  intro b _ hb _
  cases a
  · cases hb
  · rfl

/-- The bad verifier messages of chain 2 at a key: none in the joining round; the key in the shared
round. -/
def badOf (k : Bool) : BadFam G.c₂ := (fun _ => ∅, fun _ _ => (fun _ => {c | c = k}, fun _ _ => ()))

theorem badOf_within (k : Bool) : (badOf k).Within C.ε₂ :=
  ⟨fun _ => le_of_eq (cnt_false fun _ h => h), fun _ _ =>
    ⟨fun _ => le_of_eq (cnt_eq_const k), fun _ _ => trivial⟩⟩

/-- **Chain 2 is a link with keys whose error is paid once**, at every number of slots: statements
with one key have the same bad verifier messages. -/
theorem link₂ (N : ℕ) : LinkJ C.K₂ G.A₂ N k₁ k₂ C.on₁ C.R₁ C.R₂ C.e₂ C.ε₂ := by
  refine ⟨⟨fun b => badOf (k₁ b), ?_, ?_⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  · rintro b ⟨m0, c0, m1, c1, _⟩ b' _ _ hτ hb hw
    have hne : c1 ≠ b.1 := hτ.2.1
    have hb' : (some (b.2 || (c1 == b.1)) : Option Bool) = some b' := hb
    obtain rfl := Option.some.inj hb'
    have hw' : (b.2 || (c1 == b.1)) = true := hw
    rw [beq_eq_false_iff_ne.2 hne, Bool.or_false] at hw'
    exact hw'
  · intro a ha
    by_cases hne : ∃ j aj, a j = some aj
    · obtain ⟨j₀, a₀, h₀⟩ := hne
      refine jWithin_of_same N G.c₂ C.ε₂ (badOf (k₁ a₀)) _ (badOf_within _) fun j p hp => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
      show badOf (k₁ aj) = badOf (k₁ a₀)
      rw [ha j j₀ aj a₀ haj h₀]
    · refine jWithin_of_same N G.c₂ C.ε₂ (BadFam.empty G.c₂) _ (BadFam.empty_within _ _)
        fun j p hp => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact absurd ⟨j, aj, haj⟩ hne

/-- **The list, record by record, at every number of slots.** -/
theorem knows (N : ℕ) (rec : Rc) : (C.comap fun x : Y2 => (x, rec)).KnowsJ N k₁ k₂ where
  l₁ := LinkJ.ofLocal (K := (C.comap fun x : Y2 => (x, rec)).K₁)
    (allKind_const (fun _ => rfl) G.c₁) N (fun a ha => know₁ ((a.1, rec), a.2) ha)
    (fun y => keyOf y rec) fun _ _ _ hb => by
      obtain rfl := Option.some.inj hb
      rfl
  l₂ := link₂ N
  l₃ := LinkJ.ofLocal (K := C.K₃) (allKind_const (fun _ => rfl) G.c₃) N know₃ (fun _ => ())
    fun _ _ _ _ => rfl
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-! ## The file's verifier -/

/-- the rounds, as a list -/
abbrev shL : Shape := [rN, rP, rN, rS, rN]

/-- the reply that was sent -/
def sent (τ : Tr G.sh) : Bool := (show Tr shL from τ).2.2.1.2

/-- the bit drawn in the reply's round -/
def c₁At (τ : Tr G.sh) : Bool := (show Tr shL from τ).2.2.2.1

/-- the bit drawn in the shared round -/
def c₂At (τ : Tr G.sh) : Bool := (show Tr shL from τ).2.2.2.2.2.2.2.1

/-- The file's verifier: THE REPLY THAT WAS SENT IS THE INSTANCE'S, and the claim has become true.
-/
@[reducible] def D : Desc G (Y2 × Rc) E0 where
  blinded := fun _ => false
  extReads := fun _ _ => {(0 : Fin 1)}
  reads := fun _ _ _ => ∅
  accept := fun a y τ =>
    (sent τ == a.1.2) && (((prOK a && sent τ) || c₁At τ) || (c₂At τ == keyOf y a.2))

/-- What the three chains in a row do. -/
theorem out_eq (a : Y2 × Rc) (y : E0.Str) (τ : Tr G.sh) :
    C.all.out (a, y) τ =
      if (((prOK a && sent τ) || c₁At τ) || (c₂At τ == keyOf y a.2)) = true then some ()
      else none := by
  obtain ⟨m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, u⟩ := τ
  rfl

/-- What the three extractors in a row yield: the reply that was sent. -/
theorem ext_eq (a : Y2 × Rc) (y : E0.Str) (τ : Tr G.sh) : C.ext (a, y) τ () = sent τ := by
  obtain ⟨m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, u⟩ := τ
  rfl

/-! ## The interface with records -/

/-- A protocol without a round that accepts. -/
@[reducible] def idle (X : Type) (E : ExtSpec) : InteractiveOracleProof X E where
  shape := []
  blinded := fun p => nomatch p
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- The interface: 64 slots; the index is one bit; a record decodes to its answer; no seed is a
collision seed; every query of a session holds `early x`; no later query takes in the reply. Test
and Link are idle. -/
@[reducible] def L : HolographicProtocol Bool Y2 where
  wordLength := 1
  Symbol := Bool
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => false
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i _ _ => i
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ r => some r.2
  offline := idle _ _
  link := idle _ _
  maxBatchSize := 64
  onlineBatch := D.batch
  honestOfflineProver := _root_.Run.dummyH (idle _ _) fun _ _ => false
  honestLinkProver := _root_.Run.dummyH (idle _ _) fun _ => (fun _ => false, fun _ => false)
  honestOnlineBatchProver := _root_.Run.dummyB D.batch fun _ _ => false
  early := early
  late := none

/-- The relation, with the reply as the witness: the prompt is the index, the instance's own reply
is the witness, and the witness is the right reply. -/
def RnW (i : Bool) (x : Y2) (w : Bool) : Prop := x.1 = i ∧ x.2 = w ∧ w = true

/-- Where the file's verifier accepts at x, no chain rejects at `early x`. -/
theorem decides (x : Y2) (rec : Rc) (y : E0.Str) (τ : Tr G.sh)
    (h : D.accept (x, rec) y τ = true) :
    (C.all.out ((L.early x, rec), y) τ).isSome = true := by
  have h2 : (((prOK (x, rec) && sent τ) || c₁At τ) || (c₂At τ == keyOf y rec)) = true :=
    (Bool.and_eq_true_iff.1 h).2
  show (C.all.out ((early x, rec), y) τ).isSome = true
  rw [out_eq, prOK_early, if_pos h2]
  rfl

/-- **The premise tieR.** The verifier's yes at x, and the description's relation at `early x` of
what its extractors yield, give the interface's relation AT x ITSELF, with that yield as the
witness. -/
theorem tieR (x : Y2) (rec : L.Rec) (y : E0.Str) (τ : Tr G.sh)
    (h : D.accept (x, rec) y τ = true)
    (hR : C.on₀ ((L.early x, rec), y) →
      C.R₀ ((L.early x, rec), y) (C.ext ((L.early x, rec), y) τ ())) :
    L.relB RnW rec x y (id (C.ext ((L.early x, rec), y) τ ())) := by
  have h1 : sent τ = x.2 := beq_iff_eq.1 (Bool.and_eq_true_iff.1 h).1
  obtain ⟨hp, hw⟩ := hR trivial
  have hp' : prOK (x, rec) = true := hp
  show L.relB RnW rec x y (C.ext ((early x, rec), y) τ ())
  rw [ext_eq] at hw ⊢
  exact Or.inr ⟨rec.2, rfl, beq_iff_eq.1 hp', h1.symm, hw⟩

/-- **"The proof file's protocol is sound, with a witness", in the form with links, applies with
nothing left open**, at an interface with records and 64 slots whose queries never hold the reply.
The relation of the conclusion speaks of the whole instance. The bound is the greatest entry of the
three lists as they are: no factor for the number of slots. -/
theorem toy_proofSound_links :
    ∃ (wit : Y2 × L.Rec → E0.Str → Tr L.onlineBatch.loc.shape → Bool) (ε : Err L.onlineBatch.loc.shape),
      Err.Below ε C.worstMid ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB RnW rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  proofSound_at_links L D RnW id rfl rfl (knows 64) decides tieR le_rfl

/-! ## That the test has weight -/

/-- a transcript: the reply that is sent and the two drawn bits -/
def trL (m c c' : Bool) : Tr G.sh :=
  (show Tr shL from (((), ()), (), ((), m), c, ((), ()), (), ((), ()), c', ((), ()), (), ()))

/-- The relation reads the reply: at one prompt it holds of one reply, and of the other it fails
whatever the witness. -/
theorem rnW_reads_reply : RnW true (true, true) true ∧ ∀ w, ¬ RnW true (true, false) w :=
  ⟨⟨rfl, rfl, rfl⟩, fun _ h => Bool.noConfusion (h.2.1.trans h.2.2)⟩

/-- The queries' part of an instance does not hold the reply. -/
theorem early_blind (p r r' : Bool) : early (p, r) = early (p, r') := rfl

/-- The verifier rejects a reply that is not the instance's, whatever is drawn. -/
theorem other_reply_rejected (p r : Bool) (rec : Rc) (y : E0.Str) (c c' : Bool) :
    D.accept ((p, r), rec) y (trL (!r) c c') = false := by
  cases r <;> rfl

/-- A true claim is accepted. -/
theorem yes_true (k i : Bool) (y : E0.Str) (c c' : Bool) :
    D.accept ((i, true), (k, i)) y (trL true c c') = true := by
  cases i <;> rfl

/-- A wrong reply survives in chain 2 at the drawn bit that is the key, and there alone (where chain
1's bit is false). s: the external bit. -/
theorem false_survives₂ (s k i : Bool) :
    D.accept ((i, false), (k, i)) (fun _ => s) (trL false false (xor s k)) = true ∧
      D.accept ((i, false), (k, i)) (fun _ => s) (trL false false (!xor s k)) = false := by
  cases s <;> cases k <;> cases i <;> exact ⟨rfl, rfl⟩

/-- The key speaks: two records have two keys behind chain 1, and so have two external strings. -/
theorem key_speaks (x : Y2) (s k i : Bool) (τ : Tr G.c₁) :
    (C.out₁ ((x, (!k, i)), fun _ => s) τ).map k₁ ≠ (C.out₁ ((x, (k, i)), fun _ => s) τ).map k₁ ∧
      (C.out₁ ((x, (k, i)), fun _ => !s) τ).map k₁ ≠
        (C.out₁ ((x, (k, i)), fun _ => s) τ).map k₁ := by
  refine ⟨?_, ?_⟩
  · show some (xor s (!k)) ≠ some (xor s k)
    cases s <;> cases k <;> decide
  · show some (xor (!s) k) ≠ some (xor s k)
    cases s <;> cases k <;> decide

/-- Chain 2's list has no factor for the number of slots. -/
theorem eps₂_once : C.ε₂ = (0, (1, ())) := rfl

end TypedOracleCompiler.Joined.ToyLinks
