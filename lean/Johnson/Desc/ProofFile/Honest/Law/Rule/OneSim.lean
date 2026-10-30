-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OneSim.lean: one slot of `honestBatchProverOfFile` (Honest/StratC.lean)
compared with an explicit function, `simOne` (`one_exact`). Beside its parameters (the simulators,
`key`, `pubJ`, the public stops) the arguments of `simOne` are the instance, the verifier's message
and the external answers. It consists of the public stops; then the session
(Honest/Law/Rule/Session.lean) at the stored columns that the answers hold, two coins more for the
three rounds without a challenge, and `back` (Honest/Law/Rule/Back.lean).

What this is. A skeleton: a conditional lemma at `honestBatchProverOfFile`, general in the description, at no
description of the protocol. It is not to be quoted by itself: `Tied` is among its hypotheses, and
pubJ is a parameter bound before the private input. An honest side whose front round says the index
passes it: at a constant pubJ, `Tied` holds at one index alone, and the others are passed over in
silence. What excludes that is `tied` with `TiedAt.silent3` (Honest/Law/Rule/Tied.lean). The join is
`one_exact_at` (Honest/Law/Rule/OneAt.lean): rely on that.

  1  `stOff`, `simOne`   the functions
  2  `BackAt`, `StOffAt`   two hypotheses, as definitions: both are asked at a verifier's message
     whose list of challenges is such as the rounds can draw; `BackAt` outside the abort set alone
  3  `one_exact`   at a tied pair and a verifier's message outside the second set of stops (`Hid`)
     whose list is such as the rounds can draw: the library's output of one slot is `simOne`

The two hypotheses. `BackAt`: at each value of the coins of `honestBatchProverOfFile`, where `runC` returns, the
disclosed view of the strategies' transcript is `back` of what the three rounds without a challenge
send and of what the run has produced. `StOffAt`: the stored columns that the declared rounds read
are those that the external answers hold. Both are conditions on this folder's functions, the data
and the library's reduction; neither is a condition on a sub-protocol. They are proved, from
`F.planOk = true` and `DataFits F D`, in Honest/Law/BackAt.lean, Honest/Law/BackFile.lean and
Honest/Law/Rule/StOff.lean.

Limits.
  * One slot; one copy's number, which is inside pubJ.
  * `Owed` is a hypothesis here; where and how far it is proved: see the Limits of Honest/Owed.lean.
  * What meets all hypotheses of the join together: see the head of Honest/Law/Rule/OneAt.lean.
  * How likely the second set of stops is, is not said; nor that it reads no test bit of the
    verifier's message.
  * All limits of the heads of Honest/Law/Rule/Row.lean and Honest/Law/Rule/Tied.lean.
  * Hypotheses that the prose above does not name: `Sides.owns` (every entry's owner is a part of
    some side): `one_exact`.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.One
import Johnson.Desc.ProofFile.Honest.Law.Rule.Back
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 The functions -/

/-- The stored columns that the declared rounds read, from the external answers: the second half of
the symbol that is answered at the position; what is not answered is dropped. -/
def stOff (F : FileDescription Xi) (D : WholeD) (δ : Draws)
    (a : (Iop.oneExternalString (2 ^ D.a) SgX).Pos → Option (Iop.oneExternalString (2 ^ D.a) SgX).Sym) :
    List (Nat × Nat × List UInt64) :=
  (storedAsks F δ).filterMap fun q =>
    if h : q.2 < 2 ^ D.a then (a ⟨q.2, h⟩).map fun s => (q.1, q.2, s.2) else none

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) [Fintype R2] [Nonempty R2] [Fintype R3]
  [Nonempty R3]

open Classical in
/-- **The function.** `T`: the simulators. `key`: the key, computed from the instance. `pubJ`: what
the three rounds without a challenge send, computed from two coins and the instance. `BadS`: the
public stops, a set of verifier's messages. `x`: the instance. `a`: the external answers. By its
type it is given no private input and no coin of a run, except for x and a: x may hold a sample that
is computed from the index and the stored tables' pads and encoding randomness, and a holds the
external string's symbols at the positions that the protocol reads. -/
noncomputable def simOne (T : Sims Xi Ky) (key : Xi → Ky) (pubJ : R2 → R3 → Xi → TF × TJ × T3)
    (BadS : Set (Iop.Rho (chainsOf C D tF tJ t3).sh)) (x : Xi)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (a : (Iop.oneExternalString (2 ^ D.a) SgX).Pos → Option (Iop.oneExternalString (2 ^ D.a) SgX).Sym) :
    PMF (Option (Iop.DView (batchOf C D tF tJ t3 F silent).loc)) :=
  if ρ ∈ BadS then PMF.pure none
  else ((simActs x (stOff F D (drawsAt C D tF tJ t3 ρ) a) (theActs F Bk T key x (drawsAt C D tF tJ
      t3 ρ))
      (Stand.start F x)).map fun o => o.map (·.laid)).bind fun o =>
    (unif (R2 × R3)).map fun r => o.map fun L =>
      back C D tF tJ t3 F silent (pubJ r.1 r.2 x) L x ρ a

end

/-! ## 2 At every tied pair -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3]
  (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (pubJ : R2 → R3 → Xi → TF × TJ × T3)
  (Rel : W₀ → Rc → Xi → Prop)

/-- `BackAt`: a definition, meant as a hypothesis; the head says what it asks. It is asked outside
the abort set alone. -/
def BackAt : Prop :=
  ∀ w x, Tied D F H J ext pubJ sh Rel w x → ∀ ρ : Iop.Rho (chainsOf C D tF tJ t3).sh, (drawsAt C D
      tF tJ t3 ρ).due F = true →
    ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.withheld w x →
    ∀ (c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3)) (r : RunC F),
    runC F Bk (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r →
    (batchOf C D tF tJ t3 F silent).loc.dview x (ext w) (((honestBatchProverOfFile C D tF tJ t3 F silent Bk
        (G.prover H) J sh ext).one.strat w x c).run ρ).1 =
      back C D tF tJ t3 F silent (pubJ c.1.2 c.2.2 x) r.run.laid x ρ ((batchOf C D tF tJ t3 F
          silent).loc.extAns x ρ (ext w))

/-- `StOffAt`: a definition, meant as a hypothesis. -/
def StOffAt : Prop :=
  ∀ w x, Tied D F H J ext pubJ sh Rel w x → ∀ ρ : Iop.Rho (chainsOf C D tF tJ t3).sh, (drawsAt C D
      tF tJ t3 ρ).due F = true →
    storedShown (H.storedWords w.1 w.2.1) (storedAsks F (drawsAt C D tF tJ t3 ρ)) =
      stOff F D (drawsAt C D tF tJ t3 ρ) ((batchOf C D tF tJ t3 F silent).loc.extAns x ρ (ext w))

variable {C D tF tJ t3 F silent Bk H G J sh ext pubJ Rel}

/-- **A conditional lemma on one slot of `honestBatchProverOfFile`.** None of the library's goals. -/
theorem one_exact (hO : Owed F Bk H G Rel) (hE : G.owns = true)
    (hB : BackAt C D tF tJ t3 F silent Bk H G J sh ext pubJ Rel)
    (hS : StOffAt C D tF tJ t3 F silent H J sh ext pubJ Rel) (w : W₀ × Rc × Sd) (x : Xi)
    (hv : Tied D F H J ext pubJ sh Rel w x) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue :
        (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.Hid w x) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.output w x ρ =
      simOne C D tF tJ t3 F silent Bk G.sims H.key pubJ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover
                         H) J sh ext).one.Bad x ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns x ρ (ext w)) := by
  unfold simOne
  split
  · rename_i hb
    unfold Iop.Honest.output
    split
    · rfl
    · rename_i h
      exact absurd (Or.inl hb) h
  · rename_i hb
    rw [← hS w x hv ρ hdue]
    exact one_exact_of C D tF tJ t3 F silent Bk H G J sh ext hO hE pubJ w x hv.rel ρ hdue
      (fun h => h.elim hb hρ)
      (fun v L => back C D tF tJ t3 F silent v L x ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns x ρ (ext w)))
      (hB w x hv ρ hdue (fun h => h.elim hb hρ))

end

end ProofFile.Honest

#print axioms ProofFile.Honest.one_exact
