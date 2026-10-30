-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FromThreads.lean: A VALUE OF `ThreadsC` FROM THREE THREADS.
`ThreadsC` (Honest/Law/ThreadStratC.lean) is a structure of hypotheses, at one input, one run's
coins and a letter `R` for what `ready` returns, from which, with thirteen further hypotheses,
`yes_at_stratC` concludes: three families of invariants, three lists of falls, `PlaysOn` and
`SaysYes` at every sub-protocol, the invariants at the starts, the last test. Here its sixteen
fields are laid from three threads, one for each chain, each with a letter for what is said (`ThrS`,
Honest/Thread/Said.lean). What the threads owe for that is gathered in ONE STRUCTURE OF NAMED
HYPOTHESES, `FromThreads`: seventeen fields. They are the hypotheses on threads of
`file_accepts_viewsD` (Honest/Thread/FileD.lean); that lemma's `ready … = .ok R` is not among them.
The steps are those of `file_acceptsD`'s own proof, cut off before the run, but for one: the turn
from the falls by the number to the falls by the place (`fallsBy_at`).

  `fallsBy_at`
  `playsS₁`, `playsS₂`, `playsS₃`, `saysS₁`, `saysS₂`, `saysS₃`: the two conditions at every
    sub-protocol, at the pairs, in the letters of the description and the prover
  `threadsC_ofS`: the value, from eighteen hypotheses one by one
  `FromThreads`: seventeen of them as one structure (the eighteenth is `FileDescription.planOk`)
  `FromThreads.threadsC`, `threadsC_of_threads`

WHOSE TEXT. `threadsC_ofS`, the six lemmas before it and the `variable` lines in front of them are
taken over, names, statements and proofs, from lean/E2E/DebtsOfPairs.lean (sha256,
lines 55 to 63 and 68 to 167), and `fallsBy_at` from lean/E2E/DebtsOfThreads.lean (sha256
, lines 90 to 95): two other files of this project.
What has changed: the namespace; the docstrings; some
line breaks; `Block` is written short, `ℕ` as `Nat`. Of the prose here, the second sentence of
`threadsC_ofS`'s docstring, "in the letters of the description and the prover", "the steps are those
of `file_acceptsD`'s own proof" and the limit on `enters₁` follow that file's. The structure and
what stands behind it are new.

WHAT THESE ARE. DEFINITIONS AND CONDITIONAL LEMMAS ON OUR OWN DEFINITIONS. NONE IS ONE OF THE
LIBRARY's GOALS; they bear no milestone's name. The value stands at one input and one run's coins;
of the seventeen fields SEVEN do (`enters₁`, `enters₂`, `said₁`, `said₂`, `door`, `doorYes`,
`finYes`); THE OTHER TEN (`sits`, `owes`, `next`, `yes`) READ NONE OF `w₀ rc x k R`: they are asked
at every run's coins and at every state that the pair allows. `FromThreads` is a structure of
hypotheses: nothing is claimed of it, and it is shown here of no description, no prover and no
thread. `ThreadsC` is a structure of hypotheses too: a value of it is no acceptance.

Limits.
  * No thread is made here, and no field of `FromThreads` is paid here.
  * ONE LETTER FOR A CHAIN SERVES SEVERAL FIELDS: the first chain's `S₁` stands in seven: `owes₁`,
    `next₁`, `yes₁`, `said₁`, `door`, `doorYes`, `finYes`. Laws that stand at different letters have
    to be carried to one: each debt of `owes` and `yes` passes to any stronger letter
    (Honest/Thread/SaidMono.lean; for `door`, `doorYes`, `finYes` no lemma lies there: `thrS_mono`
    does it where the letter stands in a premise), and `SaidNext` passes to a conjunction
    (`saidNext_and`, Honest/Thread/Said.lean): so the one letter is the conjunction of all that are
    spent, and it has to be met at the starts (`said₁`, `said₂`, `door`).
  * `enters₁` and `enters₂` name the states that `ready` gives, as they stand; `ThreadsC` asks its
    invariants at these states with the field `opened` set to `some []`. They serve there because
    `Thr` does not read that field (the head of Honest/Thread/FileD.lean); the letter, which may
    read it, is asked at the state with the field set.
  * The conditions where the chains meet can be met only at threads or letters that tie the state's
    input to the run's own (the head of Honest/Thread/File.lean says it of threads; here the three
    are asked from the pair, so a letter can bear the tie): so whoever pays the fields at every
    input lays a family of threads or of letters in the input.
  * With `S₁` or `T₁.valid` (`S₂`, `T₂.valid`) that holds of nothing `said₁` or `enters₁` (`said₂`,
    `enters₂`) cannot be met; with `S₃` or `T₃.valid` that holds of nothing `owes₃`, `next₃`,
    `yes₃`, `finYes` hold for nothing, and `door` only where no two ends meet.
  * MET FOR NOTHING in the ways that the heads of Honest/Law/ThreadStratC.lean,
    Honest/Thread/File.lean and Honest/Thread/FileD.lean name; nothing here excludes any.
  * The lists of falls are letters. How likely a fall or a stop is, is not said.
  * `R` is a letter: no field says `ready … = .ok R`; whoever uses the value brings that (`hR` of
    `yes_at_stratC`). At a request without a trace no `R` is `ready`'s, and the value serves no rule
    that asks `hR`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileD
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest
open VerifiableInference.Desc

/-- A chain's falls by the sub-protocol's number are those at the sub-protocol's place. -/
theorem fallsBy_at {S Cl : Type} (fs : List (Fall S)) (bs : List (Block S Cl)) {j : Nat}
    {b : Block S Cl} (hb : bs[j]? = some b) : fallsBy fs bs j = fallOf fs b.place := by
  unfold fallsBy
  rw [hb]

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-! ## 1 The two conditions at every sub-protocol, in the letters of description and prover -/

/-- `PlaysOn` at the first chain. -/
theorem playsS₁ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₁ S₁)
    (n : ∀ b, SaidNext T₁ S₁ b) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 0 0 H.first b (ThrS T₁ S₁ j) (ThrS T₁ S₁ (j + 1)) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, t, -, -⟩ := hS
  have q := playsOn_of_owesS T₁ S₁ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).1) o n
  rw [p, c, f, b, h] at q
  exact q

/-- `PlaysOn` at the shared chain. -/
theorem playsS₂ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₂ S₂)
    (n : ∀ b, SaidNext T₂ S₂ b) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (ThrS T₂ S₂ j) (ThrS T₂ S₂ (j + 1)) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -, t, -⟩ := hS
  have q := playsOn_of_owesS T₂ S₂ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.1) o n
  rw [p, c, f, b, h] at q
  exact q

/-- `PlaysOn` at the second chain. -/
theorem playsS₃ (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o : OwesS T₃ S₃)
    (n : ∀ b, SaidNext T₃ S₃ b) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (ThrS T₃ S₃ j) (ThrS T₃ S₃ (j + 1)) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -, -, t⟩ := hS
  have q := playsOn_of_owesS T₃ S₃ (by rw [b]; exact t) (by rw [b]; exact (planOk_all hp).2.2) o n
  rw [p, c, f, b, h] at q
  exact q

/-- `SaysYes` at the first chain, outside the falls at the sub-protocol's place. -/
theorem saysS₁ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder)) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYes .own Bk 0 0 H.first b (fallOf f₁ b.place) (ThrS T₁ S₁ j) := by
  obtain ⟨⟨p, c, f, b, h⟩, -, -, -⟩ := hS
  have z := saysYes_of_yesS T₁ S₁ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₁ F.first.blocksInOrder hm] at e
  exact e

/-- `SaysYes` at the shared chain. -/
theorem saysS₂ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder)) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYes .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (ThrS T₂ S₂ j) := by
  obtain ⟨-, ⟨p, c, f, b, h⟩, -, -⟩ := hS
  have z := saysYes_of_yesS T₂ S₂ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₂ F.shared.blocksInOrder hm] at e
  exact e

/-- `SaysYes` at the second chain. -/
theorem saysS₃ (hS : Sits F H T₁ T₂ T₃) (y : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder)) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (ThrS T₃ S₃ j) := by
  obtain ⟨-, -, ⟨p, c, f, b, h⟩, -⟩ := hS
  have z := saysYes_of_yesS T₃ S₃ y
  rw [p, c, f, b, h] at z
  intro j m hm
  have e := z j m hm
  rw [fallsBy_at f₃ F.second.blocksInOrder hm] at e
  exact e

/-! ## 2 The value -/

/-- **The value of `ThreadsC`, from the hypotheses on the pairs, one by one.** Its invariants are
the pairs of a thread's sentence and what is said; its lists of falls are the given ones. A
definition: it returns the value, so what its fields are holds by `rfl`. -/
def threadsC_ofS {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂)
    (o₃ : OwesS T₃ S₃) (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b)
    (n₃ : ∀ b, SaidNext T₃ S₃ b) (y₁ : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder))
    (y₂ : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder)) (y₃ : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder))
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (a₃ : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R) (door : DoorYesS F T₁ T₂ S₁ S₂ x k)
    (fin : FinYesS F T₁ T₂ T₃ S₁ S₂ S₃ x k) : ThreadsC F Bk H w₀ rc x k R where
  I₁ := ThrS T₁ S₁
  I₂ := ThrS T₂ S₂
  I₃ := ThrS T₃ S₃
  f₁ := f₁
  f₂ := f₂
  f₃ := f₃
  h₁ := playsS₁ hS hp o₁ n₁
  h₂ := playsS₂ hS hp o₂ n₂
  h₃ := playsS₃ hS hp o₃ n₃
  y₁ := saysS₁ hS y₁
  y₂ := saysS₂ hS y₂
  y₃ := saysS₃ hS y₃
  a₁ := ⟨a₁, e₁⟩
  a₂ := ⟨a₂, e₂⟩
  a₃ := fun v₁ m₁ E₁ v₂ m₂ E₂ c₁ c₂ u₁ u₂ g₁ g₂ => by
    obtain ⟨s₃, hs⟩ := door v₁ m₁ E₁ v₂ m₂ E₂ u₁ u₂
    exact ⟨s₃, hs, a₃ v₁ m₁ E₁ v₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hs g₁ g₂⟩
  fin := fin

/-! ## 3 The hypotheses as one structure -/

/-- **What three threads owe for a value of `ThreadsC`**, at one input (`w₀`, `rc`, `x`), one run's
coins (`k`) and a letter `R` for what `ready` returns (no field says that it does). `sits`, `owes`,
`next`, `yes` read none of these five letters: they are asked at every run's coins and at every
state that the pair allows. It is a structure of hypotheses. Nothing is claimed of it, and it is
none of the library's goals. -/
structure FromThreads (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Prop where
  /-- the threads' faces, numbers and lists are the description's and the prover's; three executable
  tests -/
  sits : Sits F H T₁ T₂ T₃
  /-- the four debts that say nothing of a fall, at every sub-protocol of the first chain -/
  owes₁ : OwesS T₁ S₁
  /-- the same at the shared chain -/
  owes₂ : OwesS T₂ S₂
  /-- the same at the second chain -/
  owes₃ : OwesS T₃ S₃
  /-- what is said is carried over every sub-protocol of the first chain -/
  next₁ : ∀ b, SaidNext T₁ S₁ b
  /-- the same at the shared chain -/
  next₂ : ∀ b, SaidNext T₂ S₂ b
  /-- the same at the second chain -/
  next₃ : ∀ b, SaidNext T₃ S₃ b
  /-- the acceptance at every sub-protocol of the first chain, outside the falls of `f₁` -/
  yes₁ : YesS T₁ S₁ (fallsBy f₁ F.first.blocksInOrder)
  /-- the same at the shared chain, outside the falls of `f₂` -/
  yes₂ : YesS T₂ S₂ (fallsBy f₂ F.shared.blocksInOrder)
  /-- the same at the second chain, outside the falls of `f₃` -/
  yes₃ : YesS T₃ S₃ (fallsBy f₃ F.second.blocksInOrder)
  /-- the first chain's invariant at the start that `ready` gives -/
  enters₁ : Enters₁ F H T₁ w₀ rc x k R
  /-- the shared chain's invariant at the start that `ready` gives -/
  enters₂ : Enters₂ F H T₂ w₀ rc x k R
  /-- what is said, at the first chain's start as `ChainProgress.start` lays it -/
  said₁ : S₁ 0 k { R.start₁ H with opened := some [] }
  /-- what is said, at the shared chain's start as `ChainProgress.start` lays it -/
  said₂ : S₂ 0 k { R.start₂ H with opened := some [] }
  /-- from the two ends to the second chain's start, behind its yes (`a₃` in `threadsC_ofS`, whose
  `door` is the field `doorYes` here) -/
  door : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R
  /-- the second chain's start says yes -/
  doorYes : DoorYesS F T₁ T₂ S₁ S₂ x k
  /-- the file's last test says yes -/
  finYes : FinYesS F T₁ T₂ T₃ S₁ S₂ S₃ x k

variable {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- The value, from the structure. -/
def FromThreads.threadsC (D : FromThreads F H T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ w₀ rc x k R)
    (hp : F.planOk = true) : ThreadsC F Bk H w₀ rc x k R :=
  threadsC_ofS D.sits hp D.owes₁ D.owes₂ D.owes₃ D.next₁ D.next₂ D.next₃ D.yes₁ D.yes₂ D.yes₃
    D.enters₁ D.enters₂ D.said₁ D.said₂ D.door D.doorYes D.finYes

/-- **A value of `ThreadsC` with the given lists of falls, from three threads.** A conditional lemma
on this folder's own definitions. It is none of the library's goals and proves none of them. Its end
says that the hypothesis `Thr` of `yes_at_stratC` can be laid with these lists; that lemma's
thirteen other hypotheses stay owed: no acceptance. -/
theorem threadsC_of_threads (hp : F.planOk = true)
    (D : FromThreads F H T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ w₀ rc x k R) :
    ∃ Thr : ThreadsC F Bk H w₀ rc x k R, Thr.f₁ = f₁ ∧ Thr.f₂ = f₂ ∧ Thr.f₃ = f₃ :=
  ⟨D.threadsC hp, rfl, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.fallsBy_at
#print axioms ProofFile.Honest.playsS₁
#print axioms ProofFile.Honest.playsS₂
#print axioms ProofFile.Honest.playsS₃
#print axioms ProofFile.Honest.saysS₁
#print axioms ProofFile.Honest.saysS₂
#print axioms ProofFile.Honest.saysS₃
#print axioms ProofFile.Honest.threadsC_ofS
#print axioms ProofFile.Honest.FromThreads
#print axioms ProofFile.Honest.FromThreads.threadsC
#print axioms ProofFile.Honest.threadsC_of_threads
