-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_u at a run, at the committer's own key.
/-
AtFullSide/K12/OnAtRunUAtCommittersKey.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN. G with hP: a term lies at this G's own
type: `theGAtBase` with `theGAtBase_prover` (E2E/TheG.lean; not imported): its
prover at the return's prover is the return's; BUT its two arguments, the threads' parts and the
kinds' rows, have no known value. The list, a value of `ThreadsP`, ready's and runC's return and
that the part is called have no term and no law known to us: where the part is never called the ends
hold for nothing. hkey | hx alone can be met: at every index, randomness and seed the committer's
builder lays such an instance.

What is here. `onAtRun_U_at_the_returns_book` (AtFullSide/K12/OnAtRunUPaid.lean) WITH ITS ONE CLAUSE
ON VALUES, hAns, GIVEN UP FOR ONE EQUATION ON THE INSTANCE: its key is the key that the committer in
Lean makes of the run's own index (read by the filling's reader), the run's own committer's
randomness, and some seed. No definition; three statements.

  `hAns_of_key`   `OwnAnswers` at a key that is the committer's make: `answers_held` with the key
      under an equation.
  `onAtRun_U_at_the_committers_key`   the statement, from hkey : x.pub.key = `oodSh` sh Zp
      ⟨I.weights Zp w₀, rc, sd⟩, at a shape sh tied to the public part's (hsh).
  `onAtRun_U_at_the_committers_instance`   the same from hx : x = (`committerPure` shFull Zp).xi
      ⟨I.weights Zp w₀, rc, sd⟩ x₁: the shape's tie is paid under the head (`shapeOf_inScope`).

THE PREMISES, SORTED. PUBLIC: h · hb · hsh. THE MAKER: hAr. THE RUN: T · hρ · hR · hrun: the rule's
own letters. WHICH OBJECTS: hP · hA · hJs · hL. ON THE INSTANCE: hkey | hx, with the seed sd a
letter bound beside index and randomness. BESIDE THE RULE's OWN T, hρ, hR, hrun, NO PREMISE NAMES A
COIN k THAT THE BOOK LENDS, A CHALLENGE, A STAND OR A CARRIED BLOCK; hkey | hx names none: it reads
the index, the committer's randomness and the key. No relation is named here. THE FILLING. At W₀ :=
the matrices, I := `matrixInput`, S' := Sz.ref, O := openHonest, `onlineProverPartsInUse I secondHashFunction S' O`
is `baseFilling` by its text (E2E/BaseMaker.lean). Two things are not shown here or beneath: that
the own test's rows are ready, and that the lent o_sp words are tied at the tests on G_u and on
G_omega through `OnlineProverParts.through`. The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
This file does not show that the maker
returns at it.

Who could pay hx. `instance_is_committers` and `instance_is_committers_at`
 with the values named (AtFullSide/Honest/InstanceIsCommitters.lean; not
imported here): in scope, at every matrix M, online randomness and seed, the instance written of any
request and of the object's sample is (`committerPure` shFull Zp).xi ⟨⟨cellsReader M⟩, randOf …, sd⟩
x₁. That is hx at I := `matrixInput`, w₀ := M and rc := `tableCoins` of the online randomness: both
by these terms' own texts (E2E/TheHonestProver.lean). AtFullSide/K12/OnAtRunUAtWrittenInstance.lean
makes that call. WHAT IS OWED BEHIND IT [a reader's reading]: that the relation of the top statement
on index privacy, which writes the sample by another term than that law's `recOf`, writes the same
instance · a relation at this prover's types: none is typed · that law's own limit: that the two
committers' keys are one is not typed.

A LIMIT ON THE COMMITTER's RANDOMNESS, BEFORE THE OTHERS (Johnson/Bind/ForProver/FiveAt.lean's head,
"A limit on the coins"), SAID HERE OF hkey | hx: at a fixed index and key the pads that the answers
read are fixed, wherever no seed has the factor 0. AT THE FULL SIZE THESE ARE ALL PADS OF EVERY ROW
(one seed, three pads a row): the tails alone stay free. That index and key fix the pads is reckoned
by hand off the texts there; no theorem says it. THESE STATEMENTS STAND AT SINGLE VALUES: w₀, rc and
x are bound together, and there a seed may be a letter bound beside them. NO LATER LAW MAY RANGE
OVER rc WITH THE INSTANCE's KEY A LETTER UNDER SUCH A PREMISE AND SPEAK OF THE PADS AS UNIFORM: it
would range over one point in them. In a law over the committer's randomness the key is written as
the term made of index, randomness and seed, and the seed as the term made of index and randomness.
No strategy or simulator may branch on "the key is the committer's": it reads index and pads.

Through its imports this file stands over files under Johnson/Goal/ (a walk of the import lines).





Limits. All limits of Sim2/ListU.lean's and AtFullSide/K12/OnAtRunUPaid.lean's heads. The rule moves
the debt and pays none of it; these files bring the debt at one list down to hkey | hx. No later law
may take the condition On as a hypothesis on a run and then speak of the random values as sampled
anew. The row's own order of binders, for whoever states "at every coin": every (w₀, rc, x) of the
relation, every k, every return, one T, then every due list of challenges outside the silent set,
every run. Rows stay at their filling's types: no crossing to the online prover is typed here.
Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.OnAtRunUPaid
import Johnson.Desc.ProofFile.Honest.K12.HeldAtCommitter
import Johnson.Bind.ForProver.XiAt
import Johnson.Bind.ForProver.ShapeInScope
import Johnson.Bind.ColumnSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.K12
open OnBytes (E TableKey)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.First (S)
open Desc.K14 (St blocks)
open Desc.K14.Honest (OwnAnswers)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (randNow)
open Bind.ForProver (Seed oodSh shapeOf committerPure shapeOf_inScope)
open Bind.Column (shFull)

variable {W₀ : Type}

/-- CONDITIONAL: on the head, hsh and hkey. **`OwnAnswers` at a key that is the committer's make**,
at the rows as the two senders are handed them: `answers_held` (Honest/K12/HeldAtCommitter.lean)
with the key under a letter and an equation, at single values: index, randomness and seed are bound
together. sh: the committer's shape, a letter tied to the public part's by hsh. -/
theorem hAns_of_key {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (wts : W₀ → Weights)
    (c : Common W₀ (ℕ → TableRand) TableKey) (sh : Bind.Twin.Shape) (hsh : shapeOf Zp = sh)
    (key : TableKey) (sd : Seed sh × ℕ) (hkey : key = oodSh sh Zp ⟨wts c.w₀, c.rc, sd⟩)
    (csU csO : Array E) :
    OwnAnswers (K1.qAt Zp Np) key
      (heldAt (K1.qAt Zp Np)
        (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀) (fun c => randNow (K1.qAt Zp Np) c.rc) c)
        csU csO) := by
  subst hsh
  rw [hkey]
  exact answers_held h wts c sd csU csO

/-- CONDITIONAL: see the head. **The clause of the rule at the list of the test on G_u, at the
maker's return at the wide filling and at that return's own book, WHERE THE INSTANCE's KEY IS THE
COMMITTER's MAKE AT THE RUN's OWN INDEX AND RANDOMNESS, AT SOME SEED** (hkey). No clause at a stand,
on a carried block or on a coin k that the book lends is left; hkey reads the index, the committer's
randomness and the key. -/
theorem onAtRun_U_at_the_committers_key {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (A : ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit)
    (hA : jobRealU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp = some A)
    (Js : SimJob TableKey) (hJs : Js = simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8])
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtU Np L A Js)
    (sh : Bind.Twin.Shape) (hsh : shapeOf Zp = sh) (sd : Seed sh × ℕ)
    (hkey : x.pub.key = oodSh sh Zp ⟨I.weights Zp w₀, rc, sd⟩) :
    OnAtRun₂ T ρ r L :=
  onAtRun_U_at_the_returns_book h b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hP T hρ hR hrun A hA Js hJs
    L hL fun csU csO =>
      hAns_of_key h.toAtMg (I.weights Zp) ⟨w₀, rc, x.pub.key⟩ sh hsh _ sd hkey csU csO

/-- CONDITIONAL: see the head. **The same where the instance is what the committer's builder lays at
the run's own index and randomness, at the full size's shape** (hx): the form in which another
house's `instance_is_committers` ends. -/
theorem onAtRun_U_at_the_committers_instance {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (A : ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit)
    (hA : jobRealU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp = some A)
    (Js : SimJob TableKey) (hJs : Js = simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8])
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtU Np L A Js)
    (sd : Seed shFull × ℕ) (x₁ : ByteArray × ByteArray)
    (hx : x = (committerPure shFull Zp).xi ⟨I.weights Zp w₀, rc, sd⟩ x₁) :
    OnAtRun₂ T ρ r L :=
  onAtRun_U_at_the_committers_key h b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hP T hρ hR hrun A hA Js
    hJs L hL shFull (shapeOf_inScope h.scope h.laid.pub) sd (by rw [hx]; rfl)

end AtFullSide.K12

#print axioms AtFullSide.K12.hAns_of_key
#print axioms AtFullSide.K12.onAtRun_U_at_the_committers_key
#print axioms AtFullSide.K12.onAtRun_U_at_the_committers_instance
