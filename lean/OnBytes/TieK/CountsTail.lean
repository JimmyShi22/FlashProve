-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/CountsTail.lean: how many calls of the hash the reading of the shared and of the second
chain of a key file or a proof file makes at most; and the bound on the calls of the reading of a
tail from weaker premises than OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean has.

OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean bounds the strings that the readers ask under three premises. The
first is paid in OnBytes/TieK/CountsFirst.lean. The other two (SharedBelow, SecondBelow) speak of
every description of the shared and of the second chain that the reading can make. These are made of
rounds that dry runs state, and the dry runs start from what was read: the table's key; the first
and the shared chain.

The shared chain. By OnBytes/TypedOracleCompiler/Laws/LawDry.lean (shared_dryRun_eq) the dry run is the same at all
keys that fit the shape and name one item. The reading asks for the key of item 0. SharedBelow
speaks of keys of every item, so it is taken here with the clause "the key names item 0" more
(SharedBelow0), and the bound of Asks.lean on the reading of a tail is shown again from the weaker
premises.

The second chain. By second_rounds_alike there, the rounds at two readings of the first and the
shared chain are alike, and have one number, if the two first chains have as many roots. So the
number is a function of public data and of the number L of the first chain's roots (secondAt). It is
shown to be that function (second_number), and it reads of the first chain's dry end the statement,
the book of trees and four numbers alone (secondAt_dry).

Main definitions: SharedBelow0, SecondBelow0; sharedN, standIn, secondAt.
Main theorems: roundsNX_alike; sharedBelow0 (no premise); second_number, secondBelow0_at (no
premise); secondAt_dry; leR_readTail0; sharedN_key, sharedN_proof.

Limits. That secondAt does not hang on L is not shown. That the first chain as the readers return it
has the number of roots that its rounds say is not shown here: see OnBytes/TieK/CountsSent.lean and
CountsAsks.lean, where the bounds on the two readers stand. Where a dry run states no rounds the
numbers are 0 and the theorems say nothing. No number is evaluated here. Nothing says which strings
are asked.


-/
import OnBytes.TieK.CountsFirst
import OnBytes.TypedOracleCompiler.Laws.LawDry
import OnBytes.Iop.DrySizes
import OnBytes.Params.EntryRoundsRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.Counts

open OnBytes.Tie.CostX OnBytes.TwoPort OnBytes.TwoPort.M OnBytes.TwoPort.M.Asks OnBytes.TwoLaws
open OnBytes.Params (TableName KeyChains ProofChains)
open OnBytes.Proof (TailPublic FirstEnd SharedEnd sharedBlock sharedStart secondBlock secondStart
  secondFirstTree treesOf)

/-! ## Rounds that are alike have one number -/

section Alike
variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop}

theorem opensN_alike (L : Nat) {o o' : List (Fmt.Shape × Fmt.Src)}
    (h : LAlike (OpenAlike G) o o') : Run.opensN L o = Run.opensN L o' := by
  induction h with
  | nil => rfl
  | @cons a b l l' k _ ih =>
    obtain ⟨sa, xa⟩ := a
    obtain ⟨sb, xb⟩ := b
    have e : sa = sb := k.1
    subst e
    show (sa.a + 1) * L + Run.opensN L l = (sa.a + 1) * L + Run.opensN L l'
    rw [ih]

/-- Two lists of rounds that are alike round by round have one number. -/
theorem roundsNX_alike {l l' : Params.Rounds} (h : LAlike (RoundAlike G) l l') :
    roundsNX l = roundsNX l' := by
  induction h with
  | nil => rfl
  | @cons a b l l' k _ ih =>
    show roundNX a.1 a.2 + roundsNX l = roundNX b.1 b.2 + roundsNX l'
    unfold roundNX Run.roundN
    rw [ih, k.entry, k.kind, k.stored, opensN_alike _ k.opens]

end Alike

/-! ## Keys that fit -/

theorem lalike_of_map {α : Type} (f : α → Nat) :
    ∀ l l' : List α, l.map f = l'.map f → LAlike (fun a b => f a = f b) l l'
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l, b :: l', h => by
    rw [List.map_cons, List.map_cons] at h
    injection h with h1 h2
    exact .cons h1 (lalike_of_map f l l' h2)

/-- A key that fits the shape and names item 0 is alike to the key of zeros. -/
theorem keyAlike_zero {s : Params.IndexShape} {key : TableKey} (hf : key.fits s = true)
    (hi : key.item = 0) : KeyAlike key (Params.zeroKey s 0) := by
  have a := TableKey.alike_of_fits hf (Params.zeroKey_fits s 0) (hi.trans rfl)
  exact ⟨a.1, a.2.1, lalike_of_map (fun x : SampleSeed => x.z.length) _ _ a.2.2⟩

/-! ## The shared chain -/

/-- SharedBelow, of the keys that name item 0. -/
def SharedBelow0 (p : TailPublic) (N2 : Nat) : Prop :=
  ∀ key x root S, key.fits p.lin.fold.index = true → key.item = 0 →
    (sharedBlock p.lin key).dryRun (sharedStart p) = some x →
    p.shared.describe p.lab₂ p.table root x.1 = some S → fileNX S ≤ N2

/-- The shared chain's number: at the key of zeros. -/
def sharedN (p : TailPublic) : Nat :=
  dryN (sharedBlock p.lin (Params.zeroKey p.lin.fold.index 0)) (sharedStart p)

/-- **The shared chain**, at every tail: no premise. -/
theorem sharedBelow0 (p : TailPublic) : SharedBelow0 p (sharedN p) := by
  intro key x root S hf hi hx e
  rw [shared_dryRun_eq p (keyAlike_zero hf hi)] at hx
  exact le_of_eq (fileNX_dry hx e)

/-! ## The second chain -/

/-- SecondBelow, of the keys that name item 0. -/
def SecondBelow0 (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (N3 : Nat) : Prop :=
  ∀ key x shared rounds3 seal1 seal2 S, key.fits p.lin.fold.index = true → key.item = 0 →
    (sharedBlock p.lin key).dryRun (sharedStart p) = some x →
    (secondBlock p.lin dry.lin (x.2.goesOn shared)).rounds (secondStart p dry first) =
      some rounds3 →
    p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first) = some S → fileNX S ≤ N3

/-- A made-up chain as read that has sent L roots. -/
def standIn (L : Nat) : ChainRead where
  out :=
    { pd := .empty, run := none, rho0 := .empty, rho := .empty, seen := []
      rounds := #[{ msg := .empty, vals := List.replicate L (.root .empty), nonce := 0
                    drawn := ⟨[], [], [], none⟩, list := [], opens := [] }] }
  view := ⟨[], []⟩
  next := 0

theorem rootsT_replicate (d : ByteArray) : ∀ L, (rootsT (List.replicate L (.root d))).length = L
  | 0 => rfl
  | L + 1 => by
    show (d :: rootsT (List.replicate L (.root d))).length = L + 1
    rw [List.length_cons, rootsT_replicate d L]

theorem standIn_roots (L : Nat) : (standIn L).roots.length = L := by
  show (rootsT (List.replicate L (.root .empty)) ++ []).length = L
  rw [List.append_nil, rootsT_replicate]

/-- The second chain's number at a first chain with L roots: 3 and the number of the rounds that the
dry run states at made-up chains; 0 if a dry run states none. -/
def secondAt (p : TailPublic) (dry : FirstEnd) (L : Nat) : Nat :=
  match (sharedBlock p.lin (Params.zeroKey p.lin.fold.index 0)).dryRun (sharedStart p) with
  | none => 0
  | some x =>
    match (secondBlock p.lin dry.lin (x.2.goesOn (standIn 0))).rounds
        (secondStart p dry (standIn L)) with
    | none => 0
    | some R => 3 + roundsNX R

/-- A book of trees is alike to itself, whatever its given sources. -/
theorem bookAlike_self (B : TreeBook) : BookAlike AnyGiven B B :=
  ⟨fun i => by
    cases B.trees[i]? with
    | none => exact .none
    | some t =>
      refine .some ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
      cases t.src with
      | own n => exact .own n
      | given r s => exact .given trivial, rfl⟩

/-- The number of a description of the second chain that the reading can make, at a first chain as
read. -/
theorem second_number (p : TailPublic) (dry : FirstEnd) (first : ChainRead) {key : TableKey}
    {x : Params.Rounds × SharedEnd} {shared : ChainRead} {rounds3 : Params.Rounds}
    {seal1 seal2 : ByteArray} {S : Fmt.SpecX} (hf : key.fits p.lin.fold.index = true)
    (hi : key.item = 0) (hx : (sharedBlock p.lin key).dryRun (sharedStart p) = some x)
    (hr : (secondBlock p.lin dry.lin (x.2.goesOn shared)).rounds (secondStart p dry first) =
      some rounds3)
    (e : p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first) = some S) :
    fileNX S = secondAt p dry first.roots.length := by
  rw [shared_dryRun_eq p (keyAlike_zero hf hi)] at hx
  have k := second_rounds_alike (G := AnyGiven) p (dry := dry) (dry' := dry)
    ⟨rfl, bookAlike_self _, ⟨rfl, rfl, rfl, rfl⟩⟩ (end2 := x.2) (end2' := x.2)
    ⟨rfl, bookAlike_self _, rfl⟩ first (standIn first.roots.length) shared (standIn 0)
    (fun n => treesOf_any _ _ n) (fun n => treesOf_any _ _ n) (standIn_roots _).symm
  rw [hr] at k
  rw [fileNX_describeWith e]
  unfold secondAt
  rw [hx]
  dsimp only
  generalize (secondBlock p.lin dry.lin (x.2.goesOn (standIn 0))).rounds
    (secondStart p dry (standIn first.roots.length)) = y at k
  cases k with
  | some q => rw [roundsNX_alike q]

/-- **The second chain**, at every tail, every value of the first chain's dry run and every first
chain as read: the number at that chain's number of roots. No premise. -/
theorem secondBelow0_at (p : TailPublic) (dry : FirstEnd) (first : ChainRead) :
    SecondBelow0 p dry first (secondAt p dry first.roots.length) :=
  fun _ _ _ _ _ _ _ hf hi hx hr e => le_of_eq (second_number p dry first hf hi hx hr e)

/-- The second chain's number reads of the first chain's dry end the statement, the book of trees
and the four numbers alone. -/
theorem secondAt_dry (p : TailPublic) {dry dry' : FirstEnd} (hs : dry.st = dry'.st)
    (hb : dry.book = dry'.book) (hl : LinFirstAlike dry.lin dry'.lin) (L : Nat) :
    secondAt p dry L = secondAt p dry' L := by
  unfold secondAt
  cases (sharedBlock p.lin (Params.zeroKey p.lin.fold.index 0)).dryRun (sharedStart p) with
  | none => rfl
  | some x =>
    dsimp only
    have k := second_rounds_alike (G := AnyGiven) p (dry := dry) (dry' := dry')
      ⟨hs, hb ▸ bookAlike_self _, hl⟩ (end2 := x.2) (end2' := x.2) ⟨rfl, bookAlike_self _, rfl⟩
      (standIn L) (standIn L) (standIn 0) (standIn 0) (fun n => treesOf_any _ _ n)
      (fun n => treesOf_any _ _ n) rfl
    generalize (secondBlock p.lin dry.lin (x.2.goesOn (standIn 0))).rounds
      (secondStart p dry (standIn L)) = y at k
    generalize (secondBlock p.lin dry'.lin (x.2.goesOn (standIn 0))).rounds
      (secondStart p dry' (standIn L)) = y' at k
    cases k with
    | none => rfl
    | some q =>
      dsimp only
      rw [roundsNX_alike q]

/-! ## The bound of OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean on a tail, from the weaker premises -/

section Cost
variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat) (h : HashM m)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem leR_readTail0 (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    {N2 N3 : Nat} (h2 : SharedBelow0 p N2) (h3 : SecondBelow0 p dry first N3) :
    LeR c (M.Proof.readTail h p dry first b) (tailN p N2 N3 * k) fun _ => True := by
  unfold M.Proof.readTail
  dsimp only
  refine leR_mono c (t := 0 + ((1 + p.binding.logLeaves) * k + (RoadCost.keyN p.lin.fold.index * k +
    (0 + (0 + (2 * N2 * k + (0 + (0 + (0 + (2 * N3 * k + 0)))))))))) ?_
    (by simp only [tailN, Nat.add_mul]; omega) fun _ h => h
  refine leR_bind c (leR_need c _ _) fun seal1 _ => ?_
  refine leR_bind c (leR_needM c _ (le_readPlace c k h hk _ _ _ _ _)) fun place _ => ?_
  refine leR_bind c (leR_needM' c _ (le_tableKey_fits c k h hk _ _ _ _ _)) fun key hkey => ?_
  refine leR_bind c (leR_need c _ _) fun x hx => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine leR_bind c (leR_need c _ _) fun spec2 hs2 => ?_
  refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _ (h2 key _ _ _ hkey.1 hkey.2 hx hs2)) fun
      shared _ => ?_
  refine leR_bind c (leR_need c _ _) fun seal2 _ => ?_
  refine leR_bind c (leR_need c _ _) fun rounds3 hr3 => ?_
  refine leR_bind c (leR_need c _ _) fun spec3 hs3 => ?_
  refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _
    (h3 key _ shared _ _ _ _ hkey.1 hkey.2 hx hr3 hs3)) fun second _ => ?_
  exact leR_pure c _ _ trivial

end Cost

/-- The shared chain's number does not hang on the table. -/
theorem sharedN_key (ks : KeyChains) (table table' : TableName) :
    sharedN (OnBytes.Key.tailPublic ks table) = sharedN (OnBytes.Key.tailPublic ks table') := rfl

theorem sharedN_proof (cs : ProofChains) (table table' : TableName) :
    sharedN (OnBytes.Proof.tailPublic cs table) = sharedN (OnBytes.Proof.tailPublic cs table') :=
  rfl

end OnBytes.TieK.Counts
