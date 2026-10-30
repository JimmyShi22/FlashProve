--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/LPFK9R/TreesRideK3.lean:
THE PUBLIC ITEM "ledger.treesAre" RIDES ACROSS AN ACCEPTING STEP OF THE
LOOKUP AS THE PROOF FILE's SEAT LAYS IT, IN THE LETTERS (`IM.Yes ft b s s'`,
`IM.LaidAlone`, `IM.k3At`, `IM.k3_of`).
Theorems.

  yes_alone_steps   a sub-protocol that is a lot's b', alone, under a name at an address: where b'
    decides in a relation R, an accepting step of it steps in R. General in R.
  k3_yes_trees   so at K3's sub-protocol at an address: `KeepsTrees`
    (Johnson/Desc/First/Link/Law/TreesRide.lean: `theStated_trees`).
  rides_treesAre_K3   **THE RIDE: under a fence Fk (not
    spent), a yes, no mark in front or behind: the composed public test at the item passes from
    (z, s) to (z, s').** At every segment's number m, at either of K3's two seats.
  behind_treesAre_K3   with the promise's public test in front and "the item is asked there"
    (TreesAsked.lean: `treesAre_behind`): the item holds behind.
  k3_calls_all   **AT ALL 25 SEGMENTS**: off `IM.k3_of`: the chain's sub-protocol at the lookup on
    the calls of segment l steps in `KeepsTrees`.
Limits. No `MadeOwed`, no `madeAtK`, no `footOf` is named: the strike from the debt's list is
in a file not in this library (`rides_of_rel` takes k3_yes_trees and pubAll_treesAre_keeps),
behind Johnson/IMR/MadeOwed.lean. Nothing on soundness.

-/
import Johnson.IMR.K3Seat
import Johnson.IMR.HandsDef
import Johnson.Desc.First.Link.Law.TreesAsked

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Pub PubData pubAll ePubAt)
open ProofFile (Cl)

/-- Alone under a name at an address: an accepting step steps where the lot's own decides. -/
theorem yes_alone_steps {R : S → S → Prop} {same : S → S → Bool} {b b' : Block S Cl}
    {name : String} {a : Place} (h : IM.LaidAlone same b b' name a) (hb : Keeps.Decides R b')
    {ft : Nat} {s s' : S} (hy : IM.Yes ft b s s') : R s s' := by
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' rs cols n e
  exact hb s rs' gs' s' ((IM.alone_underR h).2 s rs' gs' s' hd)

/-- K3's house's sub-protocol at an address, as the seat lays it. -/
theorem k3_yes_trees {X : Verify.Public} {Z : ProofFile.Pub} {a : Place} {b b' : Block S Cl}
    {name : String} (hb' : IM.k3At X Z a = some b')
    (h : IM.LaidAlone ProofFile.sameReply b b' name a) {ft : Nat} {s s' : S}
    (hy : IM.Yes ft b s s') : KeepsTrees s s' :=
  yes_alone_steps h (theStated_trees _ _ _ _ _ _ hb') hy

/-- **THE RIDE.** -/
theorem rides_treesAre_K3 {Q : Type} (Fk : Nat → S → Prop) (D : PubData)
    (base : Pub → Q × S → Bool) (z : Q) (ft k m : Nat) {X : Verify.Public} {Z : ProofFile.Pub}
    {a : Place} {b b' : Block S Cl} {name : String} (hb' : IM.k3At X Z a = some b')
    (h : IM.LaidAlone ProofFile.sameReply b b' name a) :
    ∀ s s', Fk k s → IM.Yes ft b s s' → s.failed = none → s'.failed = none →
      pubAll D base (taItem m) (z, s) = true → pubAll D base (taItem m) (z, s') = true :=
  fun _ _ _ hy _ _ ht => pubAll_treesAre_keeps D base z m (k3_yes_trees hb' h hy) ht

/-- With the promise's public test in front. -/
theorem behind_treesAre_K3 {Q : Type} (D : PubData) (base : Pub → Q × S → Bool)
    (links : List ModelPart) (ps : List Place) (z : Q) (ft k m : Nat) {X : Verify.Public}
    {Z : ProofFile.Pub} {a : Place} {b b' : Block S Cl} {name : String}
    (hb' : IM.k3At X Z a = some b') (h : IM.LaidAlone ProofFile.sameReply b b' name a)
    (hq : taItem m ∈ askedAt moreAll links ps k) :
    ∀ s s', IM.Yes ft b s s' → ePubAt (pubAll D base) moreAll links ps k (z, s) = true →
      pubAll D base (taItem m) (z, s') = true :=
  fun _ _ hy he => treesAre_behind D base links ps z k m (k3_yes_trees hb' h hy) hq he

/-- **AT ALL 25 SEGMENTS: THE LOOKUP ON THE CALLS.** -/
theorem k3_calls_all {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[l]? = some Lk ∧
      Lk.hear[IM.k3Ix l false]? = some b ∧ b.place = IM.k3Place l false ∧
      ∀ ft s s', IM.Yes ft b s s' → KeepsTrees s s' := by
  intro l hl
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl false
  exact ⟨Lk, b, h1, h2, IM.alone_place h4, fun _ _ _ hy => k3_yes_trees h3 h4 hy⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.yes_alone_steps
#print axioms VerifiableInference.Desc.LinkJoin.k3_yes_trees
#print axioms VerifiableInference.Desc.LinkJoin.rides_treesAre_K3
#print axioms VerifiableInference.Desc.LinkJoin.behind_treesAre_K3
#print axioms VerifiableInference.Desc.LinkJoin.k3_calls_all
