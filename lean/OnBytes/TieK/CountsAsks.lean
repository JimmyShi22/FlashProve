-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/CountsAsks.lean: how many strings the program's readers of a key file and of a proof
file ask of an oracle at most. For a key file the numbers are functions of the chains' parameters
alone. For a proof file they are functions of these and of the first chain's block, which a caller
makes of the request and the reply: that they are one number at all requests is not shown.

OnBytes/TieK/CountsTail.lean leaves one number a letter: a bound on the second chain's number at
every first chain as read. That number is secondAt at the number of roots that the first chain has
sent. OnBytes/TieK/CountsSent.lean shows, inside the count of calls: a chain that the strict reader
returns has sent as many roots as its description's rounds say (le_readChain_sent). Here that law is
carried through the readings. So the first chain's number of roots is a function of the rounds that
the first block's dry run states.

Main definitions: secondN p b s (the second chain's number at the first block b from the start s);
FirstBlockBelow cs table B N1 N3 (two numbers bound the first and the second chain's numbers at
every block of a family B); proofReadB cs N1 N3 (the bound on a proof file's reading from these).
Main theorems:
  le_readIn_roots, le_readNamed_roots, leR_readNamed_roots: the law carried through the reading
    within a session and the named reading.
  zip_describeWith: a description made of stated rounds R has R's rounds.
  leR_readKey1, leR_readProof1: the bounds of OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean, where the premise
    on the second chain is asked only at a first chain with itemsRoots of the dry run's rounds.
  readKey_asks1: a key file: no coin, and a bound on the strings at every file. No premise.
  secondN_key, tailN_key: its numbers do not hang on the table.
  readProof_asks1: a proof file: the like, AT ONE BLOCK: a lemma.
  readProof_asksB: THE FORM FOR A USER: under FirstBlockBelow, one bound at every block of the
    family, every table's content, request item, request file's bytes and file.

Limits. FirstBlockBelow IS A HYPOTHESIS: at the family of the blocks that the program makes of the
requests it is not shown here; it would follow if the first block's dry runs at any two requests
both failed, or both returned the same rounds, the same statement, the same book of trees and the
same four numbers (OnBytes/Flat/LinksDry.lean: FirstFree). That the numbers are the same at
parameter data with another digest of the public files is not shown. No number is evaluated here:
where a dry run fails its number is 0, and a bound then says little. Nothing says which strings are
asked. The bound doubles every chain's number, since a refused chain is gone over a second time.

-/
import OnBytes.TieK.CountsSent
import OnBytes.TieK.CountsTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.Counts

open OnBytes.Tie.CostX OnBytes.TwoPort OnBytes.TwoPort.M OnBytes.TwoPort.M.Asks
open OnBytes.Params (TableName KeyChains ProofChains)
open OnBytes.Proof (TailPublic FirstEnd)

/-- A description made of the stated rounds R has R's rounds. -/
theorem zip_describeWith {g : Params.Given} {label : Nat} {statement : ByteArray}
    {rand : Fmt.Rand} {R : Params.Rounds} {firstTree : Nat} {S : Fmt.SpecX}
    (e : Params.describeWith g label statement rand R firstTree = some S) :
    S.base.rounds.zip S.stored = R := by
  obtain ⟨h1, h2, -⟩ := describeWith_fields e
  have hz : ∀ l : Params.Rounds, (l.map (·.1)).zip (l.map (·.2)) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      show (a.1, a.2) :: (l.map (·.1)).zip (l.map (·.2)) = a :: l
      rw [ih]
  rw [h1, h2, hz]

section Cost
variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat) (h : HashM m)

/-- A chain as read has as many roots as what the strict reader returned has sent. -/
theorem roots_of_out (o : Fmt.ChainOut) (v : Fmt.View) (j : Nat) :
    (⟨o, v, j⟩ : ChainRead).roots.length = sent o.rounds := by
  unfold ChainRead.roots sent
  simp only [rootsT_eq]

variable
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)

include hk

/-- The law through the reading within a session. -/
theorem le_readIn_roots (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session) :
    c.le (M.readIn h S b i s).run (fileNX S * k) fun r => ∀ y, r = some y →
      y.1.roots.length = itemsRoots (S.base.rounds.zip S.stored) := by
  unfold M.readIn
  simp only [OptionT.run_mk]
  refine c.le_bind _ _ _ 0 _ _ (le_readChain_sent c k h hk S s.seen b i) fun r hr => ?_
  cases r with
  | none =>
    refine c.le_pure _ _ ?_
    intro y e
    cases e
  | some p =>
    obtain ⟨o, j⟩ := p
    refine c.le_pure _ _ ?_
    intro y e
    obtain rfl := Option.some.inj e
    show (⟨o, viewOf S o, j⟩ : ChainRead).roots.length =
      itemsRoots (S.base.rounds.zip S.stored)
    rw [roots_of_out]
    exact hr o j rfl

/-- The law through the named reading. -/
theorem le_readNamed_roots (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat)
    (s : Session) :
    c.le (M.Proof.readNamed h front S b i s).run (fileNX S * k + fileNX S * k) fun r =>
      ∀ a s', r = .ok (a, s') → a.roots.length = itemsRoots (S.base.rounds.zip S.stored) := by
  unfold M.Proof.readNamed
  simp only [ExceptT.run_mk]
  refine c.le_bind _ _ _ _ _ _ (le_readIn_roots c k h hk S b i s) fun r hr => ?_
  cases r with
  | some y =>
    refine Run.CostP.pureLe c _ _ _ ?_
    intro a s' e
    obtain rfl := Except.ok.inj e
    exact hr _ rfl
  | none =>
    refine c.le_bind _ _ _ 0 _ _ (RoadCost.le_readerName c k h hk _ _ _ _ _) fun _ _ => ?_
    refine c.le_pure _ _ ?_
    intro a s' e
    cases e

/-- The same in the form of the bounds on the readers. -/
theorem leR_readNamed_roots (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) {N : Nat}
    (hN : fileNX S ≤ N) :
    LeR c (M.Proof.readNamed h front S b i) (2 * N * k) fun first =>
      first.roots.length = itemsRoots (S.base.rounds.zip S.stored) :=
  fun s => c.le_mono _ _ _ _ _ (le_readNamed_roots c k h hk front S b i s)
    (by
      have e : fileNX S * k ≤ N * k := Nat.mul_le_mul_right k hN
      rw [Nat.mul_assoc, Nat.two_mul]
      exact Nat.add_le_add e e) fun _ q => q

/-- **The reading of a proof file**: the premise on the second chain is asked only at a first chain
with the roots that the dry run's rounds say. -/
theorem leR_readProof1 (cs : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) {N1 N2 N3 : Nat}
    (h1 : FirstBelow cs table copy request words block N1)
    (h2 : SharedBelow0 (OnBytes.Proof.tailPublic cs table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart cs.first) = some x →
      first.roots.length = itemsRoots x.1 →
      SecondBelow0 (OnBytes.Proof.tailPublic cs table) x.2 first N3) :
    LeR c (M.Proof.readProof h cs table copy request words block file)
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic cs table) N2 N3) * k) fun _ => True := by
  unfold M.Proof.readProof
  dsimp only
  refine leR_mono c (t := 0 + (0 + (0 + (2 * N1 * k +
    (tailN (OnBytes.Proof.tailPublic cs table) N2 N3 * k + 0))))) ?_
    (by simp only [Nat.add_mul]; omega) fun _ h => h
  split <;> refine leR_bind c (P := fun _ => True)
    (by first | exact leR_throw c _ _ | exact leR_pure c _ _ trivial) fun x _ => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine leR_guard c _ fun _ => ?_
    refine leR_guard c _ fun _ => ?_
    refine leR_bind c (leR_need c _ _) fun x hx => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine leR_bind c (leR_need c _ _) fun spec1 hs1 => ?_
    refine leR_bind c (leR_readNamed_roots c k h hk _ _ _ _ (h1 _ _ hx hs1)) fun first hf => ?_
    refine leR_bind c (leR_readTail0 c k h hk _ _ _ _ h2
      (h3 _ _ hx (hf.trans (congrArg itemsRoots (zip_describeWith hs1))))) fun r _ => ?_
    exact leR_guard c _ fun _ => leR_pure c _ _ trivial

/-- **The reading of a key file**, likewise. -/
theorem leR_readKey1 (ks : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    {N1 N2 N3 : Nat} (h1 : OneTimeBelow ks table N1)
    (h2 : SharedBelow0 (OnBytes.Key.tailPublic ks table) N2)
    (h3 : ∀ x first, (OnBytes.Key.oneTime ks.oneTime).dryRun (OnBytes.Key.startOf ks.oneTime) =
        some x → first.roots.length = itemsRoots x.1 →
      SecondBelow0 (OnBytes.Key.tailPublic ks table) x.2 first N3) :
    LeR c (M.Key.readKey h ks table file j)
      ((2 * N1 + tailN (OnBytes.Key.tailPublic ks table) N2 N3) * k) fun _ => True := by
  unfold M.Key.readKey
  dsimp only
  refine leR_mono c (t := 0 + (0 + (2 * N1 * k +
    (tailN (OnBytes.Key.tailPublic ks table) N2 N3 * k + 0)))) ?_
    (by simp only [Nat.add_mul]; omega) fun _ h => h
  refine leR_bind c (leR_need c _ _) fun x hx => ?_
  obtain ⟨rounds, dry⟩ := x
  refine leR_bind c (leR_need c _ _) fun spec hs => ?_
  refine leR_bind c (leR_readNamed_roots c k h hk _ _ _ _ (h1 _ _ hx hs)) fun first hf => ?_
  refine leR_bind c (leR_readTail0 c k h hk _ _ _ _ h2
    (h3 _ _ hx (hf.trans (congrArg itemsRoots (zip_describeWith hs))))) fun r _ => ?_
  exact leR_guard c _ fun _ => leR_pure c _ _ trivial

end Cost

/-! ## The second chain's number as a function of the first block -/

/-- The second chain's number at the first block b from the start s: secondAt at what the dry run
returns and at the roots that its rounds say; 0 if the dry run states nothing. -/
def secondN (p : TailPublic) (b : Blk FirstEnd) (s : Start) : Nat :=
  match b.dryRun s with
  | some x => secondAt p x.2 (itemsRoots x.1)
  | none => 0

/-- It bounds the second chain's number at every first chain with these roots. -/
theorem secondBelow0_secondN (p : TailPublic) (b : Blk FirstEnd) (s : Start)
    (x : Params.Rounds × FirstEnd) (first : ChainRead) (hx : b.dryRun s = some x)
    (hf : first.roots.length = itemsRoots x.1) : SecondBelow0 p x.2 first (secondN p b s) := by
  have e : secondN p b s = secondAt p x.2 first.roots.length := by
    unfold secondN
    rw [hx, hf]
  rw [e]
  exact secondBelow0_at p x.2 first

/-! ## The readings that ask the one oracle -/

open _root_.ZKCP _root_.Run

/-- **The reading of a key file that asks the one oracle: no coin, and a bound on its strings at
every file, in which every number is a function of the chains' parameters.** No premise. -/
theorem readKey_asks1 (ks : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    (s : Session) :
    (M.Key.readKey (Fmt.HM askB) ks table file j s).run.NoCoin ∧
      (M.Key.readKey (Fmt.HM askB) ks table file j s).run.QueryBound
        ((2 * dryN (OnBytes.Key.oneTime ks.oneTime) (OnBytes.Key.startOf ks.oneTime) +
          tailN (OnBytes.Key.tailPublic ks table) (sharedN (OnBytes.Key.tailPublic ks table))
            (secondN (OnBytes.Key.tailPublic ks table) (OnBytes.Key.oneTime ks.oneTime)
              (OnBytes.Key.startOf ks.oneTime))) * 2) :=
  have e := leR_readKey1 (qp 256) 2 (Fmt.HM askB) qp_HM ks table file j
    (oneTimeBelow ks table) (sharedBelow0 _)
    (fun x first hx hf => secondBelow0_secondN _ _ _ x first hx hf) s
  ⟨e.1, e.2.1⟩

/-- The same of a proof file, AT ONE BLOCK: the first and the third number are functions of the
first chain's block, which a caller makes of the request and the reply. A lemma: see
readProof_asksB. -/
theorem readProof_asks1 (cs : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (s : Session) :
    (M.Proof.readProof (Fmt.HM askB) cs table copy request words block file s).run.NoCoin ∧
      (M.Proof.readProof (Fmt.HM askB) cs table copy request words block file s).run.QueryBound
        ((2 * dryN block (OnBytes.Proof.firstStart cs.first) +
          tailN (OnBytes.Proof.tailPublic cs table)
            (sharedN (OnBytes.Proof.tailPublic cs table))
            (secondN (OnBytes.Proof.tailPublic cs table) block
              (OnBytes.Proof.firstStart cs.first))) * 2) :=
  have e := leR_readProof1 (qp 256) 2 (Fmt.HM askB) qp_HM cs table copy
    request words block file (firstBelow cs table copy request words block) (sharedBelow0 _)
    (fun x first hx hf => secondBelow0_secondN _ _ _ x first hx hf) s
  ⟨e.1, e.2.1⟩

/-- The key file's second number does not hang on the table. -/
theorem secondN_key (ks : KeyChains) (table table' : TableName) (b : Blk FirstEnd) (s : Start) :
    secondN (OnBytes.Key.tailPublic ks table) b s =
      secondN (OnBytes.Key.tailPublic ks table') b s := rfl

/-- Nor does the tail's number. -/
theorem tailN_key (ks : KeyChains) (table table' : TableName) (N2 N3 : Nat) :
    tailN (OnBytes.Key.tailPublic ks table) N2 N3 =
      tailN (OnBytes.Key.tailPublic ks table') N2 N3 := rfl

/-- The same of a proof file. -/
theorem secondN_proof (cs : ProofChains) (table table' : TableName) (b : Blk FirstEnd)
    (s : Start) :
    secondN (OnBytes.Proof.tailPublic cs table) b s =
      secondN (OnBytes.Proof.tailPublic cs table') b s := rfl

theorem tailN_proof (cs : ProofChains) (table table' : TableName) (N2 N3 : Nat) :
    tailN (OnBytes.Proof.tailPublic cs table) N2 N3 =
      tailN (OnBytes.Proof.tailPublic cs table') N2 N3 := rfl

/-- A table's name of no content: the numbers below read none. -/
def noTable : TableName := ⟨ByteArray.empty, []⟩

/-- The bound on the strings of the reading of a proof file, from bounds N1, N3 on the first and the
second chain's numbers. -/
def proofReadB (cs : ProofChains) (N1 N3 : Nat) : Nat :=
  (2 * N1 + tailN (OnBytes.Proof.tailPublic cs noTable)
    (sharedN (OnBytes.Proof.tailPublic cs noTable)) N3) * 2

/-- **Two numbers bound the first and the second chain's numbers at every block of a family.** A
hypothesis of readProof_asksB. -/
def FirstBlockBelow {ι : Type} (cs : ProofChains) (table : TableName) (B : ι → Blk FirstEnd)
    (N1 N3 : Nat) : Prop :=
  ∀ x, dryN (B x) (OnBytes.Proof.firstStart cs.first) ≤ N1 ∧
    secondN (OnBytes.Proof.tailPublic cs table) (B x) (OnBytes.Proof.firstStart cs.first) ≤ N3

/-- The tail's number grows with the second chain's. -/
theorem tailN_mono (p : TailPublic) (N2 : Nat) {N3 N3' : Nat} (h : N3 ≤ N3') :
    tailN p N2 N3 ≤ tailN p N2 N3' := by
  unfold tailN
  omega

/-- **The reading of a proof file that asks the one oracle: one bound at every block of a family**,
every request item, request file's bytes, number of a stored copy and file, under FirstBlockBelow.
-/
theorem readProof_asksB {ι : Type} (cs : ProofChains) (table : TableName) (B : ι → Blk FirstEnd)
    {N1 N3 : Nat} (hB : FirstBlockBelow cs table B N1 N3) (x : ι) (copy : Nat)
    (request words : ByteArray) (file : ByteArray) (s : Session) :
    (M.Proof.readProof (Fmt.HM askB) cs table copy request words (B x) file s).run.NoCoin ∧
      (M.Proof.readProof (Fmt.HM askB) cs table copy request words (B x) file s).run.QueryBound
        (proofReadB cs N1 N3) :=
  have e := leR_readProof1 (qp 256) 2 (Fmt.HM askB) qp_HM cs table copy request words (B x) file
    (N1 := N1) (N3 := N3)
    (fun y S hy hS => le_trans (firstBelow cs table copy request words (B x) y S hy hS) (hB x).1)
    (sharedBelow0 _)
    (fun y first hy hf key z shared r3 s1 s2 S a1 a2 a3 a4 a5 =>
      le_trans (secondBelow0_secondN _ _ _ y first hy hf key z shared r3 s1 s2 S a1 a2 a3 a4 a5)
        (hB x).2) s
  ⟨e.1, e.2.1⟩

end OnBytes.TieK.Counts
