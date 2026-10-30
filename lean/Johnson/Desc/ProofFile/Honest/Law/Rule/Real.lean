-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Real.lean: a session's steps (`Act`,
Honest/Law/Rule/Session.lean) as a list of stages (Honest/Law/Rule/Stages.lean): beside each step's
kernel, what the honest side shows there, as a function of a run's coins and of what has been
produced before. Definitions, and one main lemma: the kernels' fold over these stages is `simActs`
(`sim_is`).

  1  `partShows`, `RealAt`, `zipLen`, `Stretch.real`   what the part at an address shows, played
     alone by `play` (Honest/Side.lean: `Side.shows`), at what it is given of a run's coins
  2  `Act.shows`, `Act.tells`, `Act.add`, `Act.stage`   a step as a stage
  3  `go_eq`, `sim_is`   the kernels' fold is `simActs`, whatever is on the honest side
  4  `dryAt`, `dryEnd`, `realIn`, `realAt`   the honest side of a description's lists of parts. The
     state and the challenges before a part are computed by the fold of Honest/Law/Rule/Dry.lean: no
     coin is among its arguments, no message and no test of the verifier's

Limits.
  * The honest side here is a tool of `rule_laid`'s proof; the run is `runC`.
  * Nothing ties these functions to `runC` here (Honest/Law/Rule/Model.lean does).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stages
import Johnson.Desc.ProofFile.Honest.Law.Rule.Dry
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The honest side of a stretch -/

/-- **What the part at an address shows**, played alone, at a run's coins and at what has been
produced before. `dry`: the state and the challenges before the part; what has been shown is taken
anew, from `f`, and so are the opened columns that the part is handed: those that `f` holds for the
reads of the declared rounds `pre` (`Before.opened`, `readsBefore`, Honest/Side.lean). `ch`: the
chain's number, from 0.

The opened columns are laid from `f` by the formula of `Good.exact`'s premise, so that premise holds
here by `rfl`. That these functions, folded over a file's acts, lay what a run of `runC` shows is
`model` (Honest/Law/Rule/Model.lean), under its own hypotheses; nothing in this file says it. That
the state which `midAtW` or `midSharedAtW` returns in front of a part holds these columns, at
`Run.beforeAt`, is the proposition `Tie1` (Honest/Ties.lean), which no theorem of this library
proves; with the `Before` written out: `tie_first`, `tie_shared`, `tie_second_at`
(Honest/Law/Rule/OpenedRun.lean), under their premises. -/
def partShows {S Cl V W Y Pb : Type} (φ : Face V W Pb) (σ : Side S Cl V W Y Pb)
    (u : Member V W Y Pb) (Bk : ProverCoinCounts) (ch : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (dry : Mid W Y) (k : Coins Bk) (f : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) : Option (List Shown) :=
  (lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part).toOption.bind fun c =>
    σ.shows φ u c ⟨dry.st, dry.loc, f.seen, f.opened (readsBefore pre f)⟩ ds asks

/-- The honest side, by the chain's number and the address. -/
abbrev RealAt (Bk : ProverCoinCounts) : Type :=
  Nat → Addr → Coins Bk → Before → List Fmt.Drawn → List (List (List Nat)) → Option (List Shown)

/-- Rounds as shown, each with its challenge; `none` where they are not as many as the challenges:
the test of `Stretch.lay` (Honest/Law/Rule/Session.lean). -/
def zipLen (ds : List Fmt.Drawn) (out : List Shown) : Option (List (Shown × Fmt.Drawn)) :=
  if out.length == ds.length then some (out.zip ds) else none

/-- What the honest side produces at a stretch, through the same test as the simulator's. Where the
honest side returns `none` or fails that test, the empty list takes its place (a stage's `shows` has
no option). Where the stretch has no teller: `Stretch.bare`. Where the verifier has rejected:
`Stretch.sub`. -/
def Stretch.real {Bk : ProverCoinCounts} (s : Stretch) (R : RealAt Bk) (live : Bool) (k : Coins Bk)
    (f : Before) : List (Shown × Fmt.Drawn) :=
  if live then
    if s.teller.isSome then ((R s.chain s.addr k f s.ds s.asks).bind (zipLen s.ds)).getD []
    else s.bare
  else s.sub

/-! ## 2 A step as a stage -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts}

/- What a step shows at a run's coins: at `lay`, what the honest side produces at the stretch
(`Stretch.real`); at every other step the empty list. -/
def Act.shows (st : List (Nat × Nat × List UInt64)) (R : RealAt Bk) :
    Act F → Coins Bk → Stand F → List (Shown × Fmt.Drawn)
  | .lay s, k, Z => s.real R (Z.live s.chain) k (Z.laid.front s.chain st)
  | _, _, _ => []

/- A step's kernel: at `lay`, `Stretch.lay`; at every other step `PMF.pure (some [])`. -/
noncomputable def Act.tells (st : List (Nat × Nat × List UInt64)) :
    Act F → Stand F → PMF (Option (List (Shown × Fmt.Drawn)))
  | .lay s, Z => s.lay (Z.live s.chain) (Z.laid.front s.chain st)
  | _, _ => PMF.pure (some [])

/- The `Stand` after a step: at `lay` the new rounds are added to the chain's; at a `judge` the
chain's verifier's state goes through `judgeOff`; at `door` the second chain's state is `door₃` of
the two others. -/
def Act.add (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    Act F → Stand F → List (Shown × Fmt.Drawn) → Stand F
  | .lay s, Z, new => { Z with laid := Z.laid.add s.chain new }
  | .judge₁ b own, Z, _ => { Z with v₁ := Z.v₁.bind (judgeOff 0 0 st b own Z.laid) }
  | .judge₂ b own, Z, _ => { Z with v₂ := Z.v₂.bind (judgeOff 1 0 st b own Z.laid) }
  | .door, Z, _ => { Z with v₃ := door₃ F x Z.v₁ Z.v₂ }
  | .judge₃ b own, Z, _ => { Z with v₃ := Z.v₃.bind (judgeOff 2 F.lastChainFirstTreeNumber st b own Z.laid) }

/-- **A step as a stage.** -/
noncomputable def Act.stage (x : Xi) (st : List (Nat × Nat × List UInt64)) (R : RealAt Bk)
    (a : Act F) : Kit.Stage (Coins Bk) (Stand F) (List (Shown × Fmt.Drawn)) :=
  ⟨a.shows st R, a.tells st, a.add x st⟩

/-! ## 3 The kernels' fold -/

theorem go_eq (x : Xi) (st : List (Nat × Nat × List UInt64)) (a : Act F) (Z : Stand F) :
    a.go x st Z = (a.tells st Z).map fun o => o.map (a.add x st Z) := by
  cases a with
  | lay s => rfl
  | judge₁ b own =>
    exact (PMF.pure_map (fun o => Option.map (Act.add x st (Act.judge₁ b own) Z) o) (some [])).symm
  | judge₂ b own =>
    exact (PMF.pure_map (fun o => Option.map (Act.add x st (Act.judge₂ b own) Z) o) (some [])).symm
  | door => exact (PMF.pure_map (fun o => Option.map (Act.add x st Act.door Z) o) (some [])).symm
  | judge₃ b own =>
    exact (PMF.pure_map (fun o => Option.map (Act.add x st (Act.judge₃ b own) Z) o) (some [])).symm

/-- **The kernels' fold over a session's steps is `simActs`**, whatever is on the honest side. -/
theorem sim_is (x : Xi) (st : List (Nat × Nat × List UInt64)) (R : RealAt Bk) :
    ∀ (A : List (Act F)) (Z : Stand F), Kit.sim (A.map (Act.stage x st R)) Z = simActs x st A Z
  | [], _ => rfl
  | a :: A, Z => by
    show (a.tells st Z).bind (Kit.onSome fun v =>
        Kit.sim (A.map (Act.stage x st R)) (a.add x st Z v)) =
      (a.go x st Z).bind fun o =>
        match o with
        | none => PMF.pure none
        | some Z' => simActs x st A Z'
    rw [go_eq, PMF.bind_map]
    refine congrArg (fun f => (a.tells st Z).bind f) (funext fun o => ?_)
    cases o with
    | none => rfl
    | some v => exact sim_is x st R A (a.add x st Z v)

end

/-! ## 4 The honest side of a description's lists of parts -/

section
variable {S Cl V W Y Pb : Type}

/-- The state and the challenges before the part at an address, computed from the rounds' keys
(Honest/Law/Rule/Dry.lean), the chain's challenges and its start. Nothing shown is put in, and no
columns are handed: `partShows` reads `st` and `loc` of it alone. At an address that no key names:
the state after the chain's last round. -/
def dryAt (keys : List (Addr × Option (State W Y → Y))) (ds : List Fmt.Drawn) (m₀ : Mid W Y)
    (a : Addr) : Mid W Y :=
  ⟨dryFold ((keys.take (keys.takeWhile fun y => y.1 != a).length).map (·.2))
      (ds.take (keys.takeWhile fun y => y.1 != a).length) m₀.st,
    m₀.loc ++ ds.take (keys.takeWhile fun y => y.1 != a).length, [], none⟩

/-- The same after a chain's last round. -/
def dryEnd (keys : List (Addr × Option (State W Y → Y))) (ds : List Fmt.Drawn) (m₀ : Mid W Y) :
    Mid W Y :=
  ⟨dryFold (keys.map (·.2)) ds m₀.st, m₀.loc ++ ds, [], none⟩

/-- One chain's: the first list of parts at the address's place; its side at the description's own
sub-protocol there; the `Member` of that number. The side is taken without the chain's falls
(`Lettered.side` at its default). `firstTree`, `earlier`: as `Lettered.goodAt` (Honest/Rule.lean)
takes them: the declared rounds before the place are `preOf` of them. -/
def realIn {Bk : ProverCoinCounts} (φ : Face V W Pb) (bs : List (Block S Cl))
    (Ls : List (Lettered Bk S Cl V W Y Pb)) (ch firstTree : Nat)
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (dry : Addr → Mid W Y) (a : Addr)
    (k : Coins Bk) (f : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    Option (List Shown) :=
  (Ls.find? fun L => L.place == a.place).bind fun L =>
    (L.side bs).bind fun σ =>
      (σ.members.find? fun u => u.number == a.part).bind fun u =>
        partShows φ σ u Bk ch (preOf ch firstTree earlier bs L.place) (dry a) k f ds asks

end

/-- **The honest side of a description's lists of parts**, at the two inputs and the challenges. -/
def realAt (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (own : Local W₀ Rc Xi Tr) (common : Common W₀ Rc Ky)
    (ρ : Draws) : RealAt Bk := fun ch a =>
  let k₁ := chainKeys F.first.blocksInOrder (G.prover H).first
  let k₂ := chainKeys F.shared.blocksInOrder (G.prover H).shared
  let k₃ := chainKeys F.second.blocksInOrder (G.prover H).second
  let m₁ : Mid (Local W₀ Rc Xi Tr) X := ⟨⟨own, [], H.own₀⟩, [], [], none⟩
  let m₂ : Mid (Common W₀ Rc Ky) X₀ := startShared H common
  let e₁ := dryEnd k₁ ρ.first m₁
  let e₂ := dryEnd k₂ ρ.shared m₂
  let m₃ : Mid (Local W₀ Rc Xi Tr) X :=
    ⟨⟨own, e₁.st.heard ++ e₂.st.heard, H.meet e₁.st.own e₂.st⟩, e₁.loc, [], none⟩
  if ch == 0 then realIn .own F.first.blocksInOrder G.first 0 0 (earlierOf F 0) (dryAt k₁ ρ.first m₁) a
  else if ch == 1 then
    realIn .shared F.shared.blocksInOrder G.shared 1 0 (earlierOf F 1) (dryAt k₂ ρ.shared m₂) a
  else
    realIn .own F.second.blocksInOrder G.second 2 F.lastChainFirstTreeNumber (earlierOf F 2) (dryAt k₃ ρ.second m₃) a

end ProofFile.Honest

#print axioms ProofFile.Honest.go_eq
#print axioms ProofFile.Honest.sim_is
#print axioms ProofFile.Honest.partShows
#print axioms ProofFile.Honest.RealAt
#print axioms ProofFile.Honest.zipLen
#print axioms ProofFile.Honest.Stretch.real
#print axioms ProofFile.Honest.Act.shows
#print axioms ProofFile.Honest.Act.tells
#print axioms ProofFile.Honest.Act.add
#print axioms ProofFile.Honest.Act.stage
#print axioms ProofFile.Honest.dryAt
#print axioms ProofFile.Honest.dryEnd
#print axioms ProofFile.Honest.realIn
#print axioms ProofFile.Honest.realAt
