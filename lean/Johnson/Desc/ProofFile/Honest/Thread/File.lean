-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/File.lean: the rule for a file, its first half. From the
hypotheses at every sub-protocol of the three chains' flat lists (Honest/Thread/Pays.lean), and the
conditions where the chains begin and meet: `runC` (Honest/Walk.lean) returns, outside the stops,
whatever the verifier's own steps decide. This is the lemma `file_runs`. A proof file has three
chains, run in this order: the first (number 0), the shared (1) and the second (2). The file also
has the definitions in which the rule for the description's acceptance is stated
(Honest/Thread/FileYes.lean, FileViews.lean).

What this is. Conditional lemmas on this folder's own definitions, pointwise: at one input, one
run's coins and one list of challenges. They are none of the library's goals and prove none of them,
and no goal follows from them without their hypotheses. Their hypotheses are proved here of no
description. They say nothing where an invariant cannot be entered: an invariant that is false
everywhere satisfies `Owes` and `Yes` vacuously; if it is the first or the shared chain's it fails
`Enters₁` or `Enters₂`, and if it is the second chain's, `DoorBehind` cannot be proved unless it
holds vacuously.

Five ways in which the rules over these definitions hold vacuously or trivially.
  * An invariant that cannot be entered: as said.
  * The parameters for the falls are free. With a fall that always fires, `Yes` holds vacuously, and
    "no fall fires" fails. Worse, with a fall that fires exactly where its sub-protocol's own step
    rejects, `Yes` holds trivially there, and "no fall fires" then is "that sub-protocol's own step
    accepts along the run": a hypothesis that contains part of the conclusion. At a sub-protocol
    without a round that is easily arranged: its step reads the state alone, as a fall's test does;
    and a description's sub-protocols without a round may have real tests.
  * A prover that stops at every list of challenges: `silentAt` is never `none`.
  * A book at which `ready` returns an error at every coin.
  * A prover with a part that reads the field `opened` and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`): `Owes` takes `Thr` alone, so it holds there only if the
    invariant before that part's sub-protocol is never met where it could play. In the rule for the
    acceptance the other hypotheses carry the invariant there: that rule says nothing at such a
    prover (the head of Honest/Thread/FileYes.lean). In `file_runs` no hypothesis says that a step
    accepts, but `Owes` is asked at every list of challenges, not at the run's alone: from
    `Enters₁`, `Enters₂` and `DoorBehind` it carries the invariant past every step that does accept.
    So at such a prover the hypotheses can all hold only if, at the run's input and coins, at every
    list of challenges that the rounds can draw the verifier rejects before that sub-protocol (for
    the second chain: in an earlier chain or at the chain's start too) or a part stops, in that
    sub-protocol at the latest. If at one list neither happens, the rule says nothing at any list,
    not even at one at which the verifier rejects early; and where the rule does speak, it speaks
    only of runs in which that part is never called. `runC_returns` (Honest/Law/RunsFile.lean) takes
    invariants that read the field.
What this costs is the share: a fall's stated share (`Fall.share`, Honest/Side.lean), which nothing
here compares with its test, and the stops' measure. Each fall's test is to name the verifier's own
Bools that it covers; whatever else its sub-protocol can reject at has to be proved in `Accepted`
(Honest/Thread/Pays.lean says the same of that hypothesis).

  1  `Sits`   the three `Thread`s are taken from the description and the prover
  2  `Owes`, `Yes`   the hypotheses at every sub-protocol: the four that say nothing of a fall; the
     acceptance
  3  `Enters₁`, `Enters₂`, `DoorBehind`, `DoorYes`, `FinYes`   the conditions where the chains begin
     and meet, at one run
  4  `lt_of_member`, `planOk_all`, `playsOn_of_owes`, `saysYes_of_yes`   from the hypotheses to
     `PlaysOn` and `SaysYes` (Honest/Law/ThreadC.lean)
  5  `file_runs`   the rule: the run returns

How. By calls alone: `playsOn_of_pays` (Honest/Thread/Ties.lean), `made_next`
(Honest/Thread/MadeLaw.lean), and the general rule `runC_returns` (Honest/Law/RunsFile.lean), at the
three families of conditions `Thr T₁`, `Thr T₂`, `Thr T₃`. `runC_returns` asks its conditions at the
chains' starts at the states as `ChainProgress.start` lays them, with the field `opened` set; `Enters₁`,
`Enters₂` and `DoorBehind` are stated at the states that `ready` gives. They serve there because
`Thr` does not read that field (by unfolding; Honest/Thread/ThrField.lean states it for `Mid.took`).

The rule for the acceptance, "and where no fall fires along that run, the description accepts its
views", follows from `Yes`, `DoorYes` and `FinYes`, by `saysYes_of_yes` (section 4). It is stated
and proved in Honest/Thread/FileYes.lean.

The conditions where the chains meet can be met only at invariants that tie the input to the run's
own. `DoorBehind`, `DoorYes` and `FinYes` fix the instance and the coins, and `DoorBehind` also what
`ready` has returned, and range over all verifier's states, states of the prover's run and tables at
which the invariants hold at their ends. An invariant reads the input of the state of the prover's
run, which nothing ties to the run's except its parameters `valid`, `rides`, `formP`. `DoorBehind`
asks for the second chain's invariant at the run's input and at the first chain's stored columns;
the last test reads the instance. So the three `Thread`s are to be a family in (what all requests
share, the stored tables' pads and encoding randomness, the instance), each with `valid` := "the
input is this one, and is one of which something is to be stated". That narrows no coin of the run's
and no challenge. Whoever proves `Owes` at a `Thread` with a general `valid` has proved it at one at
which `DoorBehind` cannot be proved. (The `Thread`s of Honest/Thread/FileRow.lean are such a
family.) The invariants cannot fix the challenges: so the last test's three states are independent
in what was heard, and a last test that compared two chains' ends at a challenge could not be proved
in this form.

Every hypothesis of `file_runs`, and what it is. `Sits`: equations and three executable tests on the
parameters. `F.planOk`, `sealPlain F`: executable tests on the description: evaluations at the
files. `ready … = .ok R`: the tests of Honest/Frame.lean on the book, the prover's sides, the range
and the trace. `ρ.due F`: the challenges are such as the description's rounds can draw; the first
chain's last challenge is the empty one. `silentAt … = none`: outside the stops. `PlanServes`
(Honest/Law/RunsFile.lean): each round declares as many oracle messages as its entry counts roots; a
round without a move declares no root and is under the part 0; a tree is declared no later than it
is opened, with the width at which it is opened; the first and the shared chain take over nothing;
what the second chain takes over is declared by the chain that it names, which is the first or the
shared one, with the width at which it is opened; and one condition that the plan does not state:
the prover's stored columns are available at every position below the depth, with the declared
width. `Owes`: four hypotheses at every sub-protocol. The three conditions where the chains begin
and meet.

Limits.
  * Nothing is said on how likely a stop is: no probability is in it.
  * Nothing is said on a verifier's acceptance.
  * `Owes` and `Yes` are made of the hypotheses of Honest/Thread/Pays.lean, which take `Thr` alone:
    they are asked at every value of the field `opened`: at `none`, and at lists of columns that no
    run opens, too (Honest/Thread/ThrField.lean, Limits).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Ties
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Law.RunsFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-! ## 1 Where the `Thread`s are taken from -/

/-- **The three `Thread`s are taken from the description and the prover.** It is a definition, meant
as a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
structure Sits (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop where
  one : T₁.φ = .own ∧ T₁.chain = 0 ∧ T₁.ft = 0 ∧ T₁.bs = F.first.blocksInOrder ∧ T₁.hs = H.first
  two : T₂.φ = .shared ∧ T₂.chain = 1 ∧ T₂.ft = 0 ∧ T₂.bs = F.shared.blocksInOrder ∧ T₂.hs = H.shared
  three : T₃.φ = .own ∧ T₃.chain = 2 ∧ T₃.ft = F.lastChainFirstTreeNumber ∧ T₃.bs = F.second.blocksInOrder ∧
    T₃.hs = H.second
  /-- executable tests on the parameters -/
  fits : T₁.fits F.first.blocksInOrder.length = true ∧ T₂.fits F.shared.blocksInOrder.length = true ∧
    T₃.fits F.second.blocksInOrder.length = true

/-! ## 2 The hypotheses at every sub-protocol -/

section
variable {S Cl V W Y Pb : Type} (T : Thread Bk S Cl V W Y Pb)

/-- **The hypotheses that say nothing of a fall**, at every sub-protocol. (`MadeNext` is proved:
`made_next`.) It is a definition, meant as a hypothesis. Nothing is claimed of it, and it is none of
the library's goals. -/
def Owes : Prop :=
  ∀ b, b < T.bs.length → Plays T b ∧ Behind T b ∧ Exchange T b ∧ RidesPast T b

/-- **The acceptance**, at every sub-protocol, outside the parameter `fl`. It is a definition, meant
as a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Yes (fl : Nat → S → List Fmt.Drawn → Option String) : Prop :=
  ∀ b, b < T.bs.length → Accepted T fl b

end

/-! ## 3 Where the chains begin and meet, at one run -/

section
variable (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X)

/-- The first chain's invariant holds at the start that `ready` gives. It is a definition, meant as
a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Enters₁ : Prop :=
  Thr T₁ 0 k (F.start₁ (F.pub x)) (R.start₁ H) (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])

/-- The shared chain's invariant holds at the start that `ready` gives. It is a definition, meant as
a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def Enters₂ : Prop :=
  Thr T₂ 0 k (F.start₂ (F.pub x)) (R.start₂ H) (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])

/-- **The second chain's start, after its acceptance**: from the two earlier invariants at their
last borders: wherever the second chain's start accepts, its invariant holds there. It is a
definition, meant as a hypothesis. Nothing is claimed of it, and it is none of the library's goals.
-/
def DoorBehind : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
    Thr T₃ 0 k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂)

/-- **The second chain's start accepts.** It is a definition, meant as a hypothesis. Nothing is
claimed of it, and it is none of the library's goals. -/
def DoorYes : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃

/-- **The last test accepts.** It is a definition, meant as a hypothesis. Nothing is claimed of it,
and it is none of the library's goals. -/
def FinYes : Prop :=
  ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → Thr T₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
    F.fin x e₁ e₂ e₃ = true

end

/-! ## 4 From the hypotheses to `PlaysOn` and `SaysYes` -/

/-- What the tests on the plan say of every sub-protocol of the three flat lists. -/
theorem planOk_all {F : FileDescription Xi} (h : F.planOk = true) :
    (∀ b ∈ F.first.blocksInOrder, b.planOk = true ∧ b.shaped = true) ∧
      (∀ b ∈ F.shared.blocksInOrder, b.planOk = true ∧ b.shaped = true) ∧
      ∀ b ∈ F.second.blocksInOrder, b.planOk = true ∧ b.shaped = true := by
  have h1 : blocksOk F.first.blocksInOrder = true := by
    cases hb : blocksOk F.first.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  have h2 : blocksOk F.shared.blocksInOrder = true := by
    cases hb : blocksOk F.shared.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  have h3 : blocksOk F.second.blocksInOrder = true := by
    cases hb : blocksOk F.second.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  unfold blocksOk at h1 h2 h3
  exact ⟨fun b hb => (Bool.and_eq_true _ _).mp (List.all_eq_true.1 h1 b hb),
    fun b hb => (Bool.and_eq_true _ _).mp (List.all_eq_true.1 h2 b hb),
    fun b hb => (Bool.and_eq_true _ _).mp (List.all_eq_true.1 h3 b hb)⟩

section
variable {S Cl V W Y Pb : Type} (T : Thread Bk S Cl V W Y Pb)

theorem lt_of_member {j : Nat} {b : Block S Cl} (hb : T.bs[j]? = some b) : j < T.bs.length :=
  Nat.lt_of_not_le fun h => by
    rw [List.getElem?_eq_none h] at hb
    cases hb

/-- `PlaysOn` at every sub-protocol, at the invariant. -/
theorem playsOn_of_owes (hfit : T.fits T.bs.length = true)
    (hsh : ∀ x ∈ T.bs, x.planOk = true ∧ x.shaped = true) (o : Owes T) :
    ∀ j b, T.bs[j]? = some b →
      PlaysOn T.φ Bk T.chain T.ft T.hs b (Thr T j) (Thr T (j + 1)) := by
  intro j b hb
  have hj := lt_of_member T hb
  obtain ⟨hP, hB, hX, hR⟩ := o j hj
  exact playsOn_of_pays T hfit hj hb hP hB hX hR (made_next T hfit hsh j)

/-- `SaysYes` at every sub-protocol, at the invariant. -/
theorem saysYes_of_yes {fl : Nat → S → List Fmt.Drawn → Option String} (y : Yes T fl) :
    ∀ j b, T.bs[j]? = some b → SaysYes T.φ Bk T.chain T.ft T.hs b (fl j) (Thr T j) := by
  intro j b hb
  exact saysYes_of_accepted T hb (y j (lt_of_member T hb))

end

/-! ## 5 The rule -/

/-- **The rule for a file: the run returns**, at the run's coins, whatever they are, outside the
stops, whatever the verifier's own steps decide. A conditional lemma on this folder's own
definitions. It is none of the library's goals and proves none of them. It holds vacuously in four
of the five ways that the head names: an invariant that cannot be entered; a prover that stops at
every list of challenges; a book at which `ready` returns an error at every coin; and the fifth, a
part that reads the field `opened`, unless no list of challenges reaches that part (the head). (The
free falls touch `Yes`, which is no hypothesis here.) -/
theorem file_runs {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true)
    (o₁ : Owes T₁) (o₂ : Owes T₂) (o₃ : Owes T₃)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hq : sealPlain F = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R) :
    ∃ r, runC F Bk H w₀ rc x k ρ = .ok r := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, ⟨p2, c2, f2, b2, h2⟩, ⟨p3, c3, f3, b3, h3⟩, t1, t2, t3⟩ := hS
  obtain ⟨s1, s2, s3⟩ := planOk_all hp
  have q₁ := playsOn_of_owes T₁ (by rw [b1]; exact t1) (by rw [b1]; exact s1) o₁
  have q₂ := playsOn_of_owes T₂ (by rw [b2]; exact t2) (by rw [b2]; exact s2) o₂
  have q₃ := playsOn_of_owes T₃ (by rw [b3]; exact t3) (by rw [b3]; exact s3) o₃
  rw [p1, c1, f1, b1, h1] at q₁
  rw [p2, c2, f2, b2, h2] at q₂
  rw [p3, c3, f3, b3, h3] at q₃
  exact runC_returns hR hq hρ hsil hP (Thr T₁) (Thr T₂) (Thr T₃) q₁ q₂ q₃ a₁ a₂
    fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ _ _ i₁ i₂ hs _ _ => a₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ i₁ i₂ hs

end ProofFile.Honest

#print axioms ProofFile.Honest.planOk_all
#print axioms ProofFile.Honest.lt_of_member
#print axioms ProofFile.Honest.playsOn_of_owes
#print axioms ProofFile.Honest.saysYes_of_yes
#print axioms ProofFile.Honest.file_runs
#print axioms ProofFile.Honest.Sits
#print axioms ProofFile.Honest.Owes
#print axioms ProofFile.Honest.Yes
#print axioms ProofFile.Honest.Enters₁
#print axioms ProofFile.Honest.Enters₂
#print axioms ProofFile.Honest.DoorBehind
#print axioms ProofFile.Honest.DoorYes
#print axioms ProofFile.Honest.FinYes
