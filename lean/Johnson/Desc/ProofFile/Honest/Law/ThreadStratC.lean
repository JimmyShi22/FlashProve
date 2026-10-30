-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean: the rules for a file, at the strategy of
`honestBatchProverOfFile` (Honest/StratC.lean). Outside the abort set of `honestBatchProverOfFile` (the library's field
`withheld`), and where the executable test on the views meets no fall, the description's `run`
accepts the three views that the library's slot reads from that strategy's transcript, and the three
rounds without a challenge send the values of the `KeyAndJoiningRoundMessages`. This is the lemma `yes_at_stratC`. It is
the counterpart of Honest/Law/ThreadStrat.lean (not in the sealed library), which has the same for
`honestB`.

What this is. A conditional lemma on this folder's own functions and strategies. It is pointwise: at
one private input, one instance, one value of the coins of `honestBatchProverOfFile` and one verifier's message.
Its conclusion is that `FileDescription.run` accepts, at a parameter F and at a parameter y for the stored
table's string. That is not a verifier's acceptance (the tests on the proof-of-work bits, on the
completeness of the draws, on the stored string's positions and on the three rounds without a
challenge are not reached), and it is not at the `ext` of `honestBatchProverOfFile` itself. Its hypothesis
`ThreadsC` is proved here of no description. It is none of the library's goals.

  `withheldC_eq`, `withheldC_iff`   the abort set of `honestBatchProverOfFile` is that of `honestB`
  `ThreadsC`        the hypotheses of the two rules that are not executable tests, as one structure
  `yes_at_stratC`   the lemma

It uses `runC_returns` (Honest/Law/RunsFile.lean), `runC_accepts_views` (Honest/Law/FallFree.lean),
`views_of_stratC` (Honest/Law/StratRunC.lean) and `withheld_iff` (Honest/Law/Stops.lean).

The rule can hold vacuously in four ways (Honest/Law/AcceptC.lean tells them in full), and nothing
here excludes any of them: invariants that cannot be entered; a fall that fires too often (always:
the rule says nothing; exactly where the sub-protocol's own step rejects, which is easy at a
sub-protocol without a round: "no fall fires" then contains the conclusion); a prover that stops at
every list of challenges; a book at which `ready` returns an error at every coin. What a fall costs
is its share (`Fall.share`), which nothing compares with the test; whoever writes a fall names the
verifier's own tests that it excuses.

Limits.
  * The hypothesis `hy` supplies one string y for every stored item that a declared round names
    (Honest/Law/StratRunC.lean, Limits).
  * Nothing is said on how likely a stop or a fall is.
  * `ThreadsC` asks the invariants at the starts at the states as `ChainProgress.start` (Honest/Walk.lean)
    lays them: the field `opened` is `some []` at the first and the shared chain, and at the second
    chain, where the two ends' fields hold columns, these joined.
  * `PlaysOn` and `SaysYes` are asked at every state that the invariant allows, at every value of
    the field `opened` too: at a prover with a part that reads the columns and errs at `none` (its
    duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant that lets `none` through
    before that part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * Hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
    description's rounds can draw; the first chain's last challenge is the empty one):
    `yes_at_stratC`; `FileDescription.planOk` (the library's executable test): `yes_at_stratC`; `sealPlain`
    (the first chain's last declared round declares no item except roots, and no root):
    `yes_at_stratC`; `halvedAll` (in each chain a prover's side is defined at every sub-protocol one
    of whose rounds declares an item other than a root): `yes_at_stratC`; `FileDescription.okStart` (the
    library's executable test, at the instance): `yes_at_stratC`; `DataFits`
    (Honest/Law/StratWords.lean): `yes_at_stratC`; `PlanServes` (Honest/Law/RunsFile.lean):
    `yes_at_stratC`; `ready … = .ok` (`ready` returns at these coins), `hk` (every `KeyAndJoiningRoundMessages`'s `keyOf`
    at the input is the prover's key at the instance) and `hsh` (`sh` at that key is the
    description's first state of the shared chain): `yes_at_stratC`; the request has a trace:
    `withheldC_iff`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallFree
import Johnson.Desc.ProofFile.Honest.Law.StratRunC
import Johnson.Desc.ProofFile.Honest.Law.Stops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
  [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- The three sets of `honestBatchProverOfFile` and of `honestB` have the same definitions: so their abort sets are
one set. -/
theorem withheldC_eq (w : W₀ × Rc × Sd) (x : Xi) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.withheld w x =
      (honestB C D tF tJ t3 F silent B H J ext).one.withheld w x := rfl

theorem withheldC_iff (w : W₀ × Rc × Sd) (x : Xi) (htr : (H.trace w.1 x).isSome = true)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    ρ ∈ (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.withheld w x ↔
      (silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ)).isSome = true := by
  rw [withheldC_eq]
  exact withheld_iff C D tF tJ t3 F silent B H J ext w x htr ρ

end

/-- **The hypotheses of the two rules that are not executable tests**, at one input, one run's coins
and what `ready` has returned: the three families of invariants, the three lists of falls, the two
conditions at every sub-protocol, the two starts, the second chain's start (each at the state as
`ChainProgress.start` lays it), the last test. Whoever builds the structure chooses the falls: whoever uses
it ties f₁ f₂ f₃ to the lists of `Sides`
(Honest/Rule.lean: the fields `falls₁` and so on). It is a structure of hypotheses. Nothing is
claimed of it, and it is none of the library's goals. -/
structure ThreadsC (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) where
  I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop
  I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  f₁ : List (Fall F.S₁)
  f₂ : List (Fall F.S₂)
  f₃ : List (Fall F.S₃)
  h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1))
  h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b → PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1))
  h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1))
  y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    SaysYes .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j)
  y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    SaysYes .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j)
  y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j)
  a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
    ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
      I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂)
  fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
    F.fin x e₁ e₂ e₃ = true

/-- **At the strategy of `honestBatchProverOfFile`.** A conditional lemma on this folder's own functions and
strategies, pointwise. Its conclusion is that `FileDescription.run` accepts, at a parameter F, and three
equations. It says nothing of a verifier's acceptance, and it is none of the library's goals.
`hfall`: no fall fires at the views of the run that `runC` returns at these arguments. -/
theorem yes_at_stratC (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd)
    (x : Xi) (c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3))
    (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R)
    (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F H = true) (h0 : F.okStart x = true) (hP : PlanServes H w.1 w.2.1 R)
    (hk : ∀ r2 r3, (J r2 r3).keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hsh : sh (H.key x) = F.start₂ (F.pub x))
    (hy : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : Nat) (h : p < 2 ^ D.a),
      H.storedWords w.1 w.2.1 s.item p = some (y ⟨p, h⟩).2)
    (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hw : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.withheld w x)
    (Thr : ThreadsC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (hfall : ∀ r, runC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) =
      .ok r → viewsFall F Thr.f₁ Thr.f₂ Thr.f₃ x r.run.views = none) :
    F.run x
      (view₁ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₂ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₃ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1) = true ∧
    ((chainsOf C D tF tJ t3).msgF
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).front w.1 w.2.1 w.2.2 x ∧
    ((chainsOf C D tF tJ t3).msgJ
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 default).join w.1 w.2.1 w.2.2 ∧
    ((chainsOf C D tF tJ t3).msg3
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨-, tr, htr, -⟩ := ready_ok hR
  have hsil : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) = none := by
    have h1 := (withheldC_iff C D tF tJ t3 F silent Bk H J sh ext w x (by rw [htr]; rfl) ρ).not.1
      hw
    cases hs : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) with
    | none => rfl
    | some z =>
      rw [hs] at h1
      exact absurd rfl h1
  obtain ⟨r, hr⟩ := runC_returns hR hq hdue hsil hP Thr.I₁ Thr.I₂ Thr.I₃ Thr.h₁ Thr.h₂ Thr.h₃
    Thr.a₁ Thr.a₂ (fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ i1 i2 hs j1 j2 => by
      obtain ⟨s, g1, g2⟩ := Thr.a₃ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ i1 i2 j1 j2
      rw [hs] at g1
      cases g1
      exact g2)
  obtain ⟨-, hyes⟩ := runC_accepts_views hr hR hp h0 hdue hsil Thr.I₁ Thr.I₂ Thr.I₃ Thr.f₁ Thr.f₂
    Thr.f₃ Thr.h₁ Thr.h₂ Thr.h₃ Thr.y₁ Thr.y₂ Thr.y₃ Thr.a₁ Thr.a₂ Thr.a₃ Thr.fin (hfall r hr)
  obtain ⟨v1, v2, v3, m1, m2, m3⟩ := views_of_stratC C D tF tJ t3 F Bk H (J c.1.2 default)
    (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 y ρ hr hp hD h4 (hk _ _) (hk _ _) hsh hy
  have e : (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1 =
      trAtC C D tF tJ t3 F Bk H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 ρ := rfl
  rw [e, v1, v2, v3]
  exact ⟨hyes, m1, m2, m3⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.withheldC_eq
#print axioms ProofFile.Honest.withheldC_iff
#print axioms ProofFile.Honest.yes_at_stratC
#print axioms ProofFile.Honest.ThreadsC
