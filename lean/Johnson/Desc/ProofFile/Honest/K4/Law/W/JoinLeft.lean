-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinLeft.lean: DEFINITIONS.

What is here. The one sentence that remains behind the step of the member of the feed-forward
layers' own rounds (sub-protocol K4) in the exchange at the member's own item (`k4_exchange_tenth`,
Law/ExchangeTenth.lean): the field join of `FootJoin` (Law/W/FootJoin.lean), in its own text; and
that field under `K4FootJoin`'s own binder (`K4FootJoin` asks four fields more, which
`k4_exchange_tenth` makes itself). The statement that ends in `K4JoinLeft` is `k4JoinLeft_of_b1`
(Law/W/JoinLeftB1.lean). General in the thread and the sizes, as Law/W/FootJoin.lean is. NOT TO BE
TAKEN FOR Law/JoinLeft.lean: there Left is the name of a hypothesis of the lookup's; here the word
says what remains.

  `JoinLeft`   what the lookup's join and the second token sumcheck's claim are worth
      (`JoinWorth`), behind each return of the run "back".
  `K4JoinLeft`   that at every state behind the member's step, at every continuation.

Not shown here. THAT EITHER HOLDS ANYWHERE: they define hypotheses. Nothing on soundness, on
completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 2 modules under Johnson/Bridge/; it saw 29 modules whose names hold RecCompile, none
under Johnson/Goal/, Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of the three
names. What lies behind the 2 is not counted: the numbers are floors. A LAW's HYPOTHESIS, NOT A
PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FootJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road.K4 (entryTrue)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **What is left behind the member's step**: the field join of `FootJoin`, in its own text. This
defines a hypothesis; the definition claims nothing. -/
structure JoinLeft (tl : HTailF2) (Q : K4Pub) (o : Own) (F₁ : Fork) (mask : ℕ → Cb.Gl.E)
    (Mm : Road.Mats Cb.Gl.E) (w : K4In) (hh ds : List Fmt.Drawn) (seen : Seen) : Prop where
  /-- behind "back": what the lookup's join and the second token sumcheck's claim are worth -/
  join : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    ∀ D', stackData Q w (ptsOf Q w (hh ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt seen.rounds (k4TermsEnds Q)) = some D' →
      ∀ weighed parts tT', o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' → JoinWorth o.H tT' parts
          (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) D'

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- That at every state behind the member's step, at every continuation: `K4FootJoin`'s own binder.
This defines a hypothesis; the definition claims nothing. -/
def K4JoinLeft (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    JoinLeft tl Q o F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))

end

end ProofFile.Honest.K4.W

