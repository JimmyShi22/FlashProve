-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SentAt.lean: K01_law, ROW N4, ONE TEST MORE ON THE PLAN's NUMBERS, WITH CODE, AND THE STATEMENTS ALONE (Props by def; no proof; no sorry).
WHY A NEW TEST. laterSeatsB N P m t nT (HeldAtLater.lean: «the tenants that the plan gives segment m at moment t are just the seats of this place's messages») FOLLOWS FROM NO TEST THAT LIES: numbersFit holds THE UNION of
all N.sent m t against the description's sampled tenants; groupsAreMembers · laysFenced · laysOpen go by groups: exchange N.sent 3 1 with N.sent 3 2: all of planSideOk's conjuncts, bookFit and fenceFit read the same; laterSeatsB turns false.
  sentAtB N told k m t   THE TEST: the sampled tenants of the trees that block number k tells, behind the trees told in front of it, are just N.sent m t. In bookFit's manner: the numbers against THE DESCRIPTION's OWN TELLING.
  DeclaredCounts         a declared list that is the layout (K1.Declares, Johnson/Desc/K1/Law/Declares.lean) has n tenants in all
  DeclaredSeats          and, where every message has a sample, its sampled tenants are just the layout's seats (tree i, part i), i < n
  LaterSeatsOfTold       N4: bookFit · sentAtB at k · block k tells a list that is P's layout · every message of P has a sample → laterSeatsB N P m t (N.treesAt ps[k]?) = true: THE USER's BINDER hP, TO THE LETTER
OBJECT. Plain data. USER. k01_digits_tied | k01_reads_tied's hP; msgs (by DeclaredCounts).
That K1's own text declares the layout: K1.oracles_declares (proved;
Johnson/Desc/K1/Law/Declares.lean). That every message of the fifty has a sample: later_sampled
(Johnson/Desc/K1/Law/FiftyAtFull.lean).
LETTERS. N; told. sentAtB HAS NOT RUN AT ANY PLAN: whether the numbers of record meet it at the fifty is owed (a sheet beside BookTests; or by the kernel at a written N).

(Where this and lean/THEOREM.md differ, the page holds.)
Where the proofs stand: Johnson/Desc/K1/Law/SentAtProofs.lean: «theorem declaredCounts :
DeclaredCounts» · «declaredSeats» · «laterSeatsOfTold».
-/
import Johnson.Desc.First.BookFit
import Johnson.Desc.K1.Law.Declares
import Johnson.Desc.K1.Law.HeldAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.First (Numbers bookFit treesTold tenantsOf sameMembers)

/-- **A TEST ON THE NUMBERS**: what block number k tells, against the plan's tenants of segment m at moment t. -/
def sentAtB (N : Numbers) (told : List (List Oracle)) (k m t : Nat) : Bool :=
  sameMembers ((tenantsOf (told[k]?.getD []) true).map fun x => (treesTold told k + x.1, x.2))
    (N.sent m t)

/-- A declared list that is the layout has n tenants in all. -/
def DeclaredCounts : Prop :=
  ∀ (decl : List Oracle) (lay : TreeLay) (n : Nat) (ten : Nat → SymbolComponent),
    Declares decl lay n ten → (decl.map fun o => o.tenants.length).sum = n

/-- Where every message has a sample, its sampled tenants are just the layout's seats. -/
def DeclaredSeats : Prop :=
  ∀ (decl : List Oracle) (lay : TreeLay) (n : Nat) (ten : Nat → SymbolComponent),
    Declares decl lay n ten → (∀ i, i < n → (ten i).sampled = true) →
      sameMembers (tenantsOf decl true)
        ((List.range n).map fun i => (lay.tree.getD i 0, lay.part.getD i 0)) = true

/-- **ROW N4.** -/
def LaterSeatsOfTold : Prop :=
  ∀ (N : Numbers) (ps : List Place) (told : List (List Oracle)) (k m t : Nat) (P : Par)
    (decl : List Oracle),
    bookFit N ps told = true → k ≤ ps.length → told[k]? = some decl →
    Declares decl (layOf P) P.sent.size (tenantOf P) →
    (∀ i, i < P.sent.size → (tenantOf P i).sampled = true) →
    sentAtB N told k m t = true → laterSeatsB N P m t (N.treesAt ps[k]?) = true

end VerifiableInference.Desc.K1
