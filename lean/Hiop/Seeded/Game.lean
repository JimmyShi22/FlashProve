-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Game.lean: the experiment with named seeds as a game that a compiler can wrap: a
challenger with calls in the course of play and a lazily sampled table of oracle answers, and runs
with one slot whose verifier's randomness is read off an auxiliary value.

Definitions and statements; the proofs are in Hiop/Seeded/GameProof.lean. General theorems' types;
this file states no goal of the release.

Part 1, for any form of runs (Hiop/Seeded/Form.lean): the game `gameW H B Gs S` of a host H, as a
  `Rom.World` (Rom/World.lean).
    Calls (`GOut`), in any order: "table s": the next encoded index, at the seed s (the first such
      call makes number 0); "test e", "link e", "sess e q h", "read e p": as in
      Hiop/Seeded/Form.lean.
    Replies (`GIn`): the out-of-domain (OOD) sample; what the run shows; the symbol; or "none".
    THE GAME KEEPS THE BOUNDS ITSELF: its state counts what has been asked of each encoded index,
      and a call that names an encoded index that does not exist, a seed outside Gs, or that would
      pass the bounds B, is answered "none" and changes nothing. The test reads public data alone
      (the call, the counts), so the real game and the simulated game refuse alike. What is left to
      ask of an adversary: the instances of its sessions are in the relation with the index
      (`okCall`).
    Oracle queries are answered by lazy sampling; no call touches the table.
  `Spec.game_of_view`: the property `ViewNearF` gives the same bound for the two games.
Part 2, the form with an auxiliary value (`Kit`). A run draws a from a law μ, which may hang on the
  number of the encoded index and on the explicit instance. ρ a is the verifier's randomness of the
  run, or none. The run shows a, and beside it the honest output at ρ a (in the simulated game: the
  simulator's); at none it shows (a, none) and reads nothing. Sessions have one slot.
    Why: a compiled prover makes its verifier's randomness by hashing, with searches that may run
    out. (The use that is meant, and that no file of this folder makes: a is the outcome of a first
    pass without the witness, with its recorded answers: kitW, Johnson/WholeKey/Wrap.lean.) A ρ that
    an arbitrary caller names has no bound on the error, since the set of ρ at which a simulator
    fails hangs on the private input. So the game draws a, and the error of a run is the
    probability, over a, that ρ a falls in that set (`SimsG.Good`).
  `RecsG`, `SimsG`: for each number of an encoded index, one honest side and one simulator for
    each of the three protocols; the session's are those of the local verifier's protocol
    `L.onlineBatch.loc`.
  `gameReal`, `gameSim`: the two games. `Spec.lifeSeeded`: they are within `BoundsR.err`. (With the
    sessions counted as they are made: Hiop/Seeded/Total.lean. At one index:
    Hiop/Seeded/AtIndex.lean.)

Limits: those of Hiop/Seeded/Whole.lean; one request in a session. And: (a) THE KIT IS THE CALLER's,
AND IT IS WHAT GIVES THE STATEMENT ITS CONTENT. Of a run whose ρ a is none the statement says
nothing but that it shows (a, none) in both games. A kit whose ρ is none everywhere meets
`SimsG.Good` with error 0 for ANY provers and simulators, and nothing here bounds the probability of
none. (`Kit.plain`, Hiop/Seeded/GameMembers.lean: a kit that is never none, at which `SimsG.Good`
follows from the exact form of honest-verifier zero knowledge of each honest side: `good_plain`.)
(b) Gs IS A LETTER here too: at the empty set every call for an encoded index is refused and the two
games are alike for nothing. Whoever quotes the statement says at which seeds. (c) THE REFUSALS ARE
THE GAME's OWN. A scheme's prover keeps no such counts: whoever compiles owes a prover that refuses
alike, or the price of the difference.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Form
import Rom.World

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Rom Compile.Lifetime
open scoped ENNReal

variable {I X : Type}

/-! ## Part 1. The game of a host -/

/-- The calls. -/
inductive GOut (L : HolographicProtocol I X) (F : Form X) : Type
  /-- the next encoded index, with its OOD sample at the seed s -/
  | table (s : L.OutOfDomainSeed) : GOut L F
  | test (e : ℕ) : GOut L F
  | link (e : ℕ) : GOut L F
  | sess (e : ℕ) (q : F.QB) (h : F.HB q) : GOut L F
  | read (e : ℕ) (p : Fin L.wordLength) : GOut L F

/-- The replies. -/
inductive GIn (L : HolographicProtocol I X) (F : Form X) : Type
  /-- the OOD sample of the encoded index that was made -/
  | ood (a : L.Rec) : GIn L F
  | test (a : F.RT) : GIn L F
  | link (a : F.RL) : GIn L F
  | sess (q : F.QB) (a : F.RB q) : GIn L F
  | sym (y : L.Symbol) : GIn L F
  /-- the call is refused -/
  | none : GIn L F

variable {L : HolographicProtocol I X} {F : Form X}

/-- The state of the game, but for the table of oracle answers. none: no encoded index has been
made. Else: the number of further encoded indices, what has been asked so far, the host's state. -/
abbrev GSt (H : HostF L F) : Type := Option (ℕ × UsedR × H.σ)

open Classical in
/-- The reply to a call. -/
def gameReply (H : HostF L F) (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) :
    GSt H → GOut L F → PMF (GIn L F × GSt H)
  | none, .table s =>
    if Gs s then (H.start s).map fun p => (.ood p.1, some (0, UsedR.zero, p.2))
    else PMF.pure (.none, none)
  | none, _ => PMF.pure (.none, none)
  | some (c, u, st), .table s =>
    if Gs s ∧ c < B.nenc then (H.fresh st s).map fun p => (.ood p.1, some (c + 1, u, p.2))
    else PMF.pure (.none, some (c, u, st))
  | some (c, u, st), .test e =>
    if e ≤ c ∧ u.tests e < B.tests e then
      (H.test st e).map fun p => (.test p.1, some (c, { u with tests := bump u.tests e }, p.2))
    else PMF.pure (.none, some (c, u, st))
  | some (c, u, st), .link e =>
    if 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e then
      (H.link st e).map fun p => (.link p.1, some (c, { u with links := bump u.links e }, p.2))
    else PMF.pure (.none, some (c, u, st))
  | some (c, u, st), .sess e q h =>
    if e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown then
      (H.session st e q h).map fun p =>
        (.sess q p.1, some (c, { u with sess := bump u.sess e }, p.2))
    else PMF.pure (.none, some (c, u, st))
  | some (c, u, st), .read e p =>
    if e ≤ c ∧ u.reads e < B.reads e then
      (H.read st e p).map fun y => (.sym y.1, some (c, { u with reads := bump u.reads e }, y.2))
    else PMF.pure (.none, some (c, u, st))

/-- The game of the host H within the bounds B, with a lazily sampled table of oracle answers. It
starts from `(none, Table.empty S)`. -/
def gameW (H : HostF L F) (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) (S : OSpec) :
    World S (GOut L F) (GIn L F) where
  σ := GSt H × Table S
  answer := fun s o q => (lazyAnswer s.2 o q).map fun a => (a.1, (s.1, a.2))
  reply := fun s c => (gameReply H B Gs s.1 c).map fun p => (p.1, (p.2, s.2))

/-- A call is allowed: the instances of a session meet ok. -/
def okCall (ok : X → Prop) : GOut L F → Prop
  | .sess _ q h => F.okB ok q h
  | _ => True

namespace Spec

/-- From the property of Hiop/Seeded/Form.lean to the two games: the same bound, for every adversary
all of whose sessions are allowed. -/
def game_of_view : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : HolographicProtocol I X) (F : Form X) (H : HostF L F) (Gs : L.OutOfDomainSeed → Prop)
      (ok : X → Prop) (B : BoundsR) (Sim : SimulatorF L F) (z : ℝ≥0∞),
    ViewNearF H Gs ok B Sim z →
    ∀ (α : Type) (A : Adv S (GOut L F) (GIn L F) α), A.CallsOK (okCall ok) →
      tv ((interact (gameW H B Gs S) A (none, Table.empty S)).map Prod.fst)
          ((interact (gameW Sim.host B Gs S) A (none, Table.empty S)).map Prod.fst) ≤ z

end Spec

/-! ## Part 2. Runs with an auxiliary value, one slot -/

section One
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt A : Type}

/-- What a run shows beside a: at no verifier's randomness nothing; at r a draw from f r. -/
def showAt (a : A) : Option (Rho Q.shape) → (Rho Q.shape → PMF (Option (DView Q))) →
    PMF (A × Option (DView Q))
  | none, _ => PMF.pure (a, none)
  | some r, f => (f r).map fun o => (a, o)

/-- A run of the honest side H: draw a; at ρ a = some r show (a, the output at r); at none show
(a, none). -/
def runAt (H : Honest Q Wt) (μ : PMF A) (ρ : A → Option (Rho Q.shape)) (w : Wt) (y : Y) :
    PMF (A × Option (DView Q)) :=
  μ.bind fun a => showAt a (ρ a) (H.output w y)

/-- The simulated run: draw a; at ρ a = some r read where the verifier reads at r, and show
(a, what the simulator says); at none read nothing and show (a, none). -/
def simAt (Q : InteractiveOracleProof Y E) (Sim : SimOf Q) (μ : PMF A) (ρ : A → Option (Rho Q.shape)) (y : Y) :
    RunSim E.Pos E.Sym (A × Option (DView Q)) where
  Aux := A
  μ := μ
  reads := fun a => (ρ a).elim ∅ (Q.extReads y)
  out := fun a ans => showAt a (ρ a) fun r => Sim y r ans

end One

/-- The auxiliary values of the three kinds of runs: their types, their laws (which may hang on the
number of the encoded index and on the explicit instance), and the verifier's randomness that is
read off them, if any. -/
structure Kit (L : HolographicProtocol I X) where
  AT : Type
  AL : Type
  AB : Type
  μT : ℕ → L.Rec → PMF AT
  μL : ℕ → L.Rec × L.Rec → PMF AL
  μB : ℕ → X × L.Rec → PMF AB
  ρT : AT → Option (Rho L.offline.shape)
  ρL : AL → Option (Rho L.link.shape)
  ρB : AB → Option (Rho L.onlineBatch.loc.shape)

/-- What the runs are asked with and what they show. A session: one instance, nothing hidden. -/
abbrev Kit.form (K : Kit L) : Form X where
  RT := K.AT × Option (DView L.offline)
  RL := K.AL × Option (DView L.link)
  QB := X
  HB := fun _ => Unit
  RB := fun _ => K.AB × Option (DView L.onlineBatch.loc)
  wt := fun _ => 1
  okB := fun ok x _ => ok x

/-- The honest sides, as arguments: for each number of an encoded index one for each of the three
protocols; the session's is an honest side of the local verifier's protocol. -/
structure RecsG (L : HolographicProtocol I X) where
  T : ℕ → Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)
  Lk : ℕ → Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))
  B : ℕ → Honest L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)

/-- For each number of an encoded index one simulator for each of the three protocols. -/
structure SimsG (L : HolographicProtocol I X) where
  T : ℕ → SimOf L.offline
  Lk : ℕ → SimOf L.link
  B : ℕ → SimOf L.onlineBatch.loc

/-- The laws of the real side on the index i with the honest sides P. -/
def realLawsG (L : HolographicProtocol I X) (K : Kit L) (P : RecsG L) (i : I) : LawsF L K.form where
  rc := fun u => L.recOf i u.1 u.2
  T := fun e u =>
    runAt (P.T e) (K.μT e (L.recOf i u.1 u.2)) K.ρT (i, u.1, u.2) (L.recOf i u.1 u.2)
  Lk := fun e u u' =>
    runAt (P.Lk e) (K.μL e (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)) K.ρL (i, u, u')
      (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
  B := fun e u x _ =>
    runAt (P.B e) (K.μB e (x, L.recOf i u.1 u.2)) K.ρB (i, u.1, u.2) (x, L.recOf i u.1 u.2)
  y := fun u p => L.encodeIndex i u.1 p

/-- The simulated runs. -/
def simsFG (L : HolographicProtocol I X) (K : Kit L) (Sm : SimsG L) : SimsF L K.form where
  T := fun e x => simAt L.offline (Sm.T e) (K.μT e x) K.ρT x
  Lk := fun e x => simAt L.link (Sm.Lk e) (K.μL e x) K.ρL x
  B := fun e x rc => simAt L.onlineBatch.loc (Sm.B e) (K.μB e (x, rc)) K.ρB (x, rc)

/-- The real game on the index i. -/
def gameReal (L : HolographicProtocol I X) (K : Kit L) (P : RecsG L) (i : I) (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop)
    (S : OSpec) : World S (GOut L K.form) (GIn L K.form) :=
  gameW (realLawsG L K P i).host B Gs S

/-- The simulated game: encodings of the fixed index i₀, its own answers at the seeds that are
handed in, simulated runs. -/
def gameSim (L : HolographicProtocol I X) (K : Kit L) (Sm : SimsG L) (i₀ : I) (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop)
    (S : OSpec) : World S (GOut L K.form) (GIn L K.form) :=
  gameW (simWholeF L K.form (simsFG L K Sm) i₀).host B Gs S

/-- The numbers of positions that the three verifiers read (a session: the local verifier, one
slot), and hiding of the encoding at the seeds of Gs. -/
structure ReadsG (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (b qT qpar qch qon : ℕ) : Prop where
  cntT  : ∀ x ρ, (L.offline.extReads x ρ).card ≤ qT
  cntLp : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isRight)).card ≤ qch
  cntO  : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ qon
  hidE  : HidE L Gs b

/-- The external strings of each honest side are the encoded index(es) of its private input. -/
structure RecsG.Ext (P : RecsG L) : Prop where
  extT : ∀ e i r s, (P.T e).ext (i, r, s) = L.encodeIndex i r
  extL : ∀ e i r s r' s', (P.Lk e).ext (i, (r, s), (r', s')) = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ e i r s, (P.B e).ext (i, r, s) = L.encodeIndex i r

/-- The simulators are good for the honest sides P under the laws of the auxiliary values: at every
number, every index, EVERY value of the committer's randomness and every seed of Gs, the probability
over a that ρ a is a value at which honest output and simulator differ is at most z. -/
structure SimsG.Good (Sm : SimsG L) (K : Kit L) (P : RecsG L) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  goodT : ∀ e i r s, Gs s →
    pr (K.μT e (L.recOf i r s))
      {a | ∃ ρ, K.ρT a = some ρ ∧ (P.T e).output (i, r, s) (L.recOf i r s) ρ ≠
        Sm.T e (L.recOf i r s) ρ (L.offline.extAns (L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zT
  goodL : ∀ e i r s r' s', Gs s → Gs s' →
    pr (K.μL e (L.recOf i r s, L.recOf i r' s'))
      {a | ∃ ρ, K.ρL a = some ρ ∧
        (P.Lk e).output (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') ρ ≠
          Sm.Lk e (L.recOf i r s, L.recOf i r' s') ρ
            (L.link.extAns (L.recOf i r s, L.recOf i r' s') ρ (L.encodeIndex i r, L.encodeIndex i r'))} ≤ zL
  goodB : ∀ e i r s x, Gs s → Ryes i x →
    pr (K.μB e (x, L.recOf i r s))
      {a | ∃ ρ, K.ρB a = some ρ ∧ (P.B e).output (i, r, s) (x, L.recOf i r s) ρ ≠
        Sm.B e (x, L.recOf i r s) ρ (L.onlineBatch.loc.extAns (x, L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zO

namespace Spec

/-- The real game and the simulated game are within the error of the bounds, for every adversary all
of whose instances are in the relation with the index. -/
def lifeSeeded : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : HolographicProtocol I X) (K : Kit L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    ReadsG L Gs b qT qpar qch qon →
    ∀ P : RecsG L, P.Ext →
      ∀ Sm : SimsG L, Sm.Good K P Gs Ryes zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ (i i₀ : I) (α : Type) (A : Adv S (GOut L K.form) (GIn L K.form) α),
            A.CallsOK (okCall (Ryes i)) →
              tv ((interact (gameReal L K P i B Gs S) A (none, Table.empty S)).map Prod.fst)
                  ((interact (gameSim L K Sm i₀ B Gs S) A (none, Table.empty S)).map Prod.fst) ≤
                B.err zT zL zO

end Spec
end Hiop.Seeded
