-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyFiveFields.lean: the five facts on the committed table and the key that the linear claim's
laws take from a valid input (`ProofFile.Honest.K14.FiveFields`), at the key file's parameters.

Why. The committer in Lean shows these five at a value of `ProofFile.Pub`, at the parameters `p14Of` of
its chains (`Bind.ForProver.fiveFieldsK14_at`). By reading, that law reads of the value only its
chains, and `keyAsProof c` lays the key's numbers where `p14Of` reads them. So the five hold at the
key's own parameters `sharedPar c bp`, at a made-up value of `ProofFile.Pub` that carries those chains.

Main names.
  `p14Of_keyAsProof`: the two parameters are one, at every c and bp.
  `pubKey`, `pubKey_chains`, `linOf_pubKey`: a value of `ProofFile.Pub` with these chains laid in. IT IS
    MADE UP: no maker of the public part need return it, so no law that asks for the maker's value
    can be called at it.
  `five_key`: the five at the key's parameters, under the room test `rowsFit` and the bound on
    the code's positions, at the predicate `validAt`. The library's `rowsFit_of_ok` gives the room
    test at a shape that passes its own test, without the goals' scope.
  `rows_full`, `a_full`: those two tests at the written sizes of the key, by Lean's kernel.
  `five_in_scope`: under `KeySourced`, in the goals' scope, those two premises are gone.
  `five_along`: the five along a reader of the index and a reader of the coins.
  `madeIn`: the input whose key is the term that the committer makes of index, coins and seed.
  `five_made`: the five at the thread's own `valid` and `stored`, at such an input, through two
    readers.

What stays open.
  * That `encW` and `oodSh` at `pubKey` are those at the value that the maker returns: one table
    and one key for the key file and the proof file. The road: `stored_written`
    (E2E/KeyStoredRows.lean), `index_key` (Johnson/Goal/Numbers/K14BadAt.lean) against
    `shapeOf_inScope`; the index's answers and salt at the key are left.
  * Which table: the coins are read at the item 0, the first table. A copy's key file is not served.
  * That the table which a key file's rounds open is `encW` at these chains.
  * That a key file's input is such an input.
  * That any K meets `five_made`'s premises together, and the readers f, g at the object's types.
    Where `Vd` fails at the input, `five_made` says nothing.
  * `Z₀` is a letter: by reading, the five read nothing of it but the chains that are laid in.

NOT IN FRONT OF A LAW OVER COINS: `five_key`, `five_in_scope`, `five_along` and `five_made` bear
this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. This
file's ground. `five_key`, `five_in_scope`: the letter is w.key, under `validAt`, a premise of the first
kind; they call `fiveFieldsK14_at`. Their stored table is the term `storedW`. hfit, ha, hs and scope
speak of public values: of neither kind. What lifts the bar: the made term
`oodSh (shapeOf Z') Z' ⟨w₀, rc, sd⟩`; the lemma `validAt_oodSh`. `five_along`: valid and stored are
letters under F; f and g name no coin: none: the bar is flat. `five_made`: it calls
`fiveFields_of_imp`, which bears the label, and `five_along`. The key is the made term, and
`validAt` is shown at it by `validAt_oodSh`. `K.stored` is a letter under hS; hW, hR and hS name no
coin and tie nothing. `Vd` is a letter for a predicate that stands in front of each field: for `Vd`:
none: the bar is flat.

Nothing on soundness, completeness or hiding.

-/
import E2E.KeySharedThread
import Johnson.Bind.ForProver.FiveFieldsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyFiveFields
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedPar beforeSharedPoint keyAsProof)
open _root_.Desc.K14 (St)
open Bind.ForProver (shapeOf shapeOfIndex linOf rowsFit validAt validAt_oodSh storedW encW oodSh
  Seed fiveFields_of_imp)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey lettersKey randKey)
open Lk6.AtPlan (keyFull)

/-- **The proof file's parameters at `keyAsProof c` are the key's parameters at c.** -/
theorem p14Of_keyAsProof (c : OnBytes.Model.Verify.Chains) (bp : List (Nat × Nat)) :
    _root_.Desc.K14.p14Of (keyAsProof c) bp = sharedPar c bp := rfl

/-- A value of `ProofFile.Pub` with the chains `keyAsProof c` laid in. It is made up: no public files
need give it. -/
def pubKey (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains) : ProofFile.Pub :=
  { Z₀ with made := { Z₀.made with p := { Z₀.made.p with chains := keyAsProof c } } }

theorem pubKey_chains (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains) :
    (pubKey Z₀ c).p.chains = keyAsProof c := rfl

/-- What the committer reads of that value is the key's shape. -/
theorem linOf_pubKey (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains) :
    linOf (pubKey Z₀ c) = c.made.sized.key.once.shape := rfl

/-- **The five at the key's parameters.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem five_key (Z₀ : ProofFile.Pub) (c : OnBytes.Model.Verify.Chains) (bp : List (Nat × Nat))
    (hfit : rowsFit (shapeOf (pubKey Z₀ c)) (linOf (pubKey Z₀ c)).kLo
      (linOf (pubKey Z₀ c)).matrixRows = true)
    (ha : (shapeOf (pubKey Z₀ c)).a ≤ 32) :
    FiveFields (sharedPar c bp) (validAt (shapeOf (pubKey Z₀ c)) (pubKey Z₀ c))
      (fun w => storedW (pubKey Z₀ c) w.w₀ w.rc) id (fun rc => rc 0) :=
  Bind.ForProver.fiveFieldsK14_at (pubKey Z₀ c) bp hfit ha

/-- **The room test at the written sizes of the key.** By Lean's kernel. -/
theorem rows_full :
    rowsFit (shapeOfIndex keyFull.once.shape.fold.index) keyFull.once.shape.kLo
      keyFull.once.shape.matrixRows = true := by decide +kernel

/-- **The code's positions at the written sizes of the key.** By Lean's kernel. -/
theorem a_full : (shapeOfIndex keyFull.once.shape.fold.index).a ≤ 32 := by decide +kernel

/-- **The five at the key's parameters, under `KeySourced`, in the goals' scope.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem five_in_scope {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (Z₀ : ProofFile.Pub)
    (bp : List (Nat × Nat)) :
    FiveFields (sharedPar Xs.chains bp)
      (validAt (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains))
      (fun w => storedW (pubKey Z₀ Xs.chains) w.w₀ w.rc) id (fun rc => rc 0) := by
  have e := AtPublicFiles.AtFiles.sized_sourced hs scope
  refine five_key Z₀ Xs.chains bp ?_ ?_
  · show rowsFit (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index)
      Xs.chains.made.sized.key.once.shape.kLo Xs.chains.made.sized.key.once.shape.matrixRows = true
    rw [e]
    exact rows_full
  · show (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index).a ≤ 32
    rw [e]
    exact a_full

/-- **The five along a reader of the index and a reader of the coins.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem five_along {W₀ Rc W₁ R₁ : Type} {Q : _root_.Desc.K14.P14}
    {valid : Common W₀ Rc TableKey → Prop}
    {stored : Common W₀ Rc TableKey → ℕ → ℕ → Option (List UInt64)}
    {weights : W₀ → Weights} {rand : Rc → TableRand} (f : W₁ → W₀) (g : R₁ → Rc)
    (F : FiveFields Q valid stored weights rand) :
    FiveFields Q (fun v : Common W₁ R₁ TableKey => valid ⟨f v.w₀, g v.rc, v.key⟩)
      (fun v => stored ⟨f v.w₀, g v.rc, v.key⟩) (fun a => weights (f a)) (fun r => rand (g r)) where
  cols w hw := F.cols ⟨f w.w₀, g w.rc, w.key⟩ hw
  tab w hw := F.tab ⟨f w.w₀, g w.rc, w.key⟩ hw
  key w hw := F.key ⟨f w.w₀, g w.rc, w.key⟩ hw
  seeds w hw := F.seeds ⟨f w.w₀, g w.rc, w.key⟩ hw
  ans w hw := F.ans ⟨f w.w₀, g w.rc, w.key⟩ hw

/-- The input whose key is the term that the committer makes of index, coins and seed, through a
reader of the index and a reader of the coins. -/
abbrev madeIn {W₀ Rc : Type} (Z' : ProofFile.Pub) (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (w₀ : W₀)
    (rc : Rc) (sd : Seed (shapeOf Z') × ℕ) : Common W₀ Rc TableKey :=
  ⟨w₀, rc, oodSh (shapeOf Z') Z' ⟨f w₀, g rc, sd⟩⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand)

/-- **The five at the thread's own `valid` and `stored`**, at an input that the committer makes:
where the key prover reads the index by f, the coins by g at the item 0, and its stored table at
the item 0 is `encW` at these chains.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem five_made (Z₀ : ProofFile.Pub)
    (hfit : rowsFit (shapeOf (pubKey Z₀ Xs.chains)) (linOf (pubKey Z₀ Xs.chains)).kLo
      (linOf (pubKey Z₀ Xs.chains)).matrixRows = true)
    (ha : (shapeOf (pubKey Z₀ Xs.chains)).a ≤ 32)
    (hW : K.weights = f) (hR : K.rand = fun r => g r 0)
    (hS : ∀ a r x, K.stored a r 0 x = encW (pubKey Z₀ Xs.chains) (f a) (g r) 0 x)
    (w₀ : W₀) (rc : Rc) (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ) :
    FiveFields (parKey Xs Pl)
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd
        (madeIn (pubKey Z₀ Xs.chains) f g w₀ rc sd)).valid
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd
        (madeIn (pubKey Z₀ Xs.chains) f g w₀ rc sd)).stored
      K.weights (randKey K) := by
  have e : randKey K = fun r => g r 0 := by
    funext r
    unfold randKey
    rw [hR]
    rfl
  rw [hW, e]
  refine fiveFields_of_imp
    (five_along f g (five_key Z₀ Xs.chains (beforeSharedPoint Pl) hfit ha)) ?_ ?_
  · intro v hv
    obtain ⟨rfl, -⟩ := hv
    exact validAt_oodSh _ _ (f w₀) (g rc) sd
  · intro v _ x
    exact congrArg (Option.map (List.map OnBytes.Slice.ofF)) (hS v.w₀ v.rc x)

end

end AtPublicFiles.KeyFiveFields

#print axioms AtPublicFiles.KeyFiveFields.p14Of_keyAsProof
#print axioms AtPublicFiles.KeyFiveFields.pubKey_chains
#print axioms AtPublicFiles.KeyFiveFields.linOf_pubKey
#print axioms AtPublicFiles.KeyFiveFields.five_key
#print axioms AtPublicFiles.KeyFiveFields.rows_full
#print axioms AtPublicFiles.KeyFiveFields.a_full
#print axioms AtPublicFiles.KeyFiveFields.five_in_scope
#print axioms AtPublicFiles.KeyFiveFields.five_along
#print axioms AtPublicFiles.KeyFiveFields.five_made
