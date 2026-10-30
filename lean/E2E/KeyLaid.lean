--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLaid.lean: THE KEY FILE's PROVER OF PARTS (`keyProver K`, E2E/KeyProver.lean) LAID INTO THE
LETTERS OF THE ACCEPT LAW (E2E/KeyAcceptLaid.lean): three tests with code. NOTHING IS CLAIMED OF
WHAT THE PARTS
SEND.

1. Bare rows. The accept law speaks of `G.prover H`: the prover whose halves are the rows G (parts
   with simulators and four letters; Johnson/Desc/ProofFile/Honest/Rule.lean). Of G it reads that
   prover and the three lists of falls alone.
  `noSim`, `bareRow`, `bareSides F Bk H f₁ f₂ f₃`: rows made of a prover's own halves, each part
    beside a simulator that tells nothing, with letters that say nothing; the three lists of falls
    as given.
  `bare_back`, **`bareSides_prover`**: their halves are the halves; their prover is H itself.
2. A half at every sub-protocol that sends (`halvedAll`,
Johnson/Desc/ProofFile/Honest/Law/Run.lean).
  `any_places`, `halved_of_rows`, `halved_sealed`: general: from a chain's rows (place, number of
    rounds): a sub-protocol without a round passes; one with rounds wants a half at its place; a
    sealed chain's last wants that its rounds state nothing but roots.
  `KeyParts.AtAll`: the letters bear the key file's sixteen places: the first chain's seven
    (`AtPlaces`), the shape splits, and the three further proximity tests' places.
  **`halvedAll_key`**: in scope, at `keyFileDescription X N P`: `halvedAll` holds of `keyProver K`.
3. Threads that sit.
  `seat₁`, `seat₂`, `seat₃`: any thread with its face, its chain's number, its first tree's number,
    its list of sub-protocols and its halves laid as `Sits` asks.
  **`sits_seated`**: such threads sit (`Sits`, Johnson/Desc/ProofFile/Honest/Thread/File.lean) where
    the tests with code on their other letters accept.

Limits.
- The bare rows' simulators are no simulators, and their letters ask nothing. With `On` and `bud`
  true and a simulator that yields nothing, the frame's sentence on a row's simulator (`Good.exact`,
  Honest/Side.lean) says there that the part shows nothing: false wherever a part plays, not idle.
  So `Good` is not to be had at these rows, and nothing on a simulator follows from them. They serve
  the accept law alone.
- `halvedAll` says that a half STANDS at a place: not that it has the place's number of rounds, nor
  what it sends.
- `AtAll` is a premise on letters. `atAll_value` (E2E/KeyValueHolds.lean) and `value_atAll`
  (E2E/OfflineSharedSixAtValue.lean) have it at `valueAt`, under their premises; the four proximity
  tests' halves are letters.
- `Thread.fits` stays a premise: it reads letters of the base threads that nothing fills here.

-/
import E2E.KeyProver
import E2E.KeyPlacesNamed
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLink
open VerifiableInference.Desc (FileDescription Block Chain Place)
open Johnson.RunOne.Sound (rowsOf)
open ProofFile.Honest

/-! ## 1. Bare rows -/

section Bare
variable {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts}

/-- A simulator that tells nothing. -/
def noSim : Sim Pb :=
  { addr := ⟨⟨0, none, 0, .frame⟩, 0⟩, takes := ⟨0, 0⟩, tell := fun _ _ _ _ _ => none }

/-- A half as a row: each part beside `noSim`; letters that say nothing. -/
def bareRow (h : Placed V W Y) : Lettered Bk S Cl V W Y Pb :=
  ⟨h.place, h.parts.map fun p => (p, noSim), fun _ _ _ _ => True, fun _ _ _ _ => True,
    fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- The halves of bare rows are the halves. -/
theorem bare_back : ∀ l : List (Placed V W Y),
    (l.map (bareRow (Bk := Bk) (S := S) (Cl := Cl) (Pb := Pb))).map
      (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) = l
  | [] => rfl
  | h :: t => by
    rw [List.map_cons, List.map_cons, bare_back t]
    have e : ((bareRow (Bk := Bk) (S := S) (Cl := Cl) (Pb := Pb) h).row.map (·.1)) = h.parts := by
      show (h.parts.map fun p => (p, (noSim : Sim Pb))).map (·.1) = h.parts
      rw [List.map_map]
      exact List.map_id _
    rw [e]
    rfl

end Bare

variable {W₀ Rc Xi Ky Tr X₀ X : Type}

/-- **Rows made of a prover's own halves**, with three lists of falls. -/
def bareSides (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) :
    Sides F Bk W₀ Rc Ky Tr X₀ X :=
  ⟨H.first.map bareRow, H.shared.map bareRow, H.second.map bareRow, f₁, f₂, f₃⟩

/-- **Their prover is the prover.** -/
theorem bareSides_prover (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) :
    (bareSides F Bk H f₁ f₂ f₃).prover H = H := by
  unfold Sides.prover bareSides
  simp only [bare_back]

/-! ## 2. A half at every sub-protocol that sends -/

section Halved
variable {S Cl V W Y : Type}

/-- Whether a half stands at a place, off the list of the halves' places. -/
theorem any_places (hs : List (Placed V W Y)) (p : Place) :
    (hs.any fun g => g.place == p) = ((hs.map (·.place)).any (· == p)) := by
  rw [List.any_map]
  rfl

/-- From the rows: a sub-protocol without a round passes; one with rounds wants a half. -/
theorem halved_of_rows (bs : List (Block S Cl)) (hs : List (Placed V W Y))
    (rows : List (Place × Nat)) (hr : rowsOf bs = rows)
    (hall : ∀ r ∈ rows, r.2 = 0 ∨ ((hs.map (·.place)).any (· == r.1)) = true) :
    halved bs hs = true := by
  unfold halved
  rw [List.all_eq_true]
  intro b hb
  have hm : (b.place, b.rounds.length) ∈ rows := by
    rw [← hr]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  rcases hall _ hm with h0 | h1
  · rw [List.eq_nil_of_length_eq_zero h0]
    exact Bool.or_true _
  · rw [any_places, h1]
    rfl

/-- The like for a chain whose last sub-protocol's rounds state nothing but roots. -/
theorem halved_sealed (c : Chain S Cl) (hs : List (Placed V W Y)) (rows : List (Place × Nat))
    (e : Place × Nat) (hr : rowsOf c.blocksInOrder = rows ++ [e])
    (hl : (c.last.rounds.all fun d => (d.items.filter (· != .root)).isEmpty) = true)
    (hall : ∀ r ∈ rows, r.2 = 0 ∨ ((hs.map (·.place)).any (· == r.1)) = true) :
    halved c.blocksInOrder hs = true := by
  obtain ⟨A, hA⟩ : ∃ A, c.blocksInOrder = A ++ [{ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }] :=
    ⟨_, rfl⟩
  rw [hA] at hr ⊢
  unfold rowsOf at hr
  rw [List.map_append] at hr
  have hA' : rowsOf A = rows := (List.append_inj' hr rfl).1
  have h1 := halved_of_rows A hs rows hA' hall
  unfold halved at h1 ⊢
  rw [List.all_append, h1, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true]
  have hl' : (({ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } : Block S Cl).rounds.all
      fun d => (d.items.filter (· != .root)).isEmpty) = true := hl
  rw [hl']
  exact Bool.or_true _

end Halved

/-! ## 3. Threads that sit -/

section Seats
variable {Bk : ProverCoinCounts} (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)

/-- A thread, seated at the first chain. -/
def seat₁ (U : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :
    Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { U with φ := .own, chain := 0, ft := 0, bs := F.first.blocksInOrder, hs := H.first }

/-- At the shared chain. -/
def seat₂ (U : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) :
    Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky :=
  { U with φ := .shared, chain := 1, ft := 0, bs := F.shared.blocksInOrder, hs := H.shared }

/-- At the second chain. -/
def seat₃ (U : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :
    Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { U with φ := .own, chain := 2, ft := F.lastChainFirstTreeNumber, bs := F.second.blocksInOrder, hs := H.second }

/-- **Seated threads sit**, where the tests with code on their other letters accept. -/
theorem sits_seated (U₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (U₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (U₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (h₁ : (seat₁ F H U₁).fits F.first.blocksInOrder.length = true)
    (h₂ : (seat₂ F H U₂).fits F.shared.blocksInOrder.length = true)
    (h₃ : (seat₃ F H U₃).fits F.second.blocksInOrder.length = true) :
    Sits F H (seat₁ F H U₁) (seat₂ F H U₂) (seat₃ F H U₃) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, h₁, h₂, h₃⟩

end Seats

end AtPublicFiles.KeyLink

namespace AtPublicFiles.KeyFile
open ProofFile.Honest AtPublicFiles.KeyLink AtPublicFiles.KeyBook
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

variable {W₀ Rc X₀ X Wk : Type}

/-- **The letters bear the key file's sixteen places.** -/
structure KeyParts.AtAll (K : KeyParts W₀ Rc X₀ X Wk) : Prop where
  first : K.AtPlaces
  splits : K.lin.S.sharedSplitNeeded = true
  onU : K.onU.place = foldedTestPlace
  onOmega : K.onOmega.place = omegaTestPlace
  own : K.own.place = ownTestPlace

/-- **In scope a half of `keyProver K` stands at every sub-protocol of the key file that sends.** -/
theorem halvedAll_key {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (scope : InScope Z = true)
    (h : KeyNamed Z Xs N P) (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) :
    halvedAll (keyFileDescription Xs N P) (keyProver K) = true := by
  obtain ⟨r1, r2, r3⟩ := places_named scope h
  have e1 : fullFirst = ([(idxPlace, 2), (msgPlace, 2)] ++ linkRows 0 9581 ++ linkRows 1 9220 ++
      [(rowsPlace, 0), (rngPlace, 23), (battPlace, 20), (wPlace, 2)]) ++ [(sealPlace, 1)] := by
    decide
  have e2 : fullShared = [(frontPlace, 0), (pointPlace, 1), (foldedPlace, 2), (gammaPlace, 0),
      (locPlace, 1), (omegaPlace, 2), (joinsPlace, 0), (zetaPlace, 1), (splitPlace, 1),
      (foldedTestPlace, 35), (omegaTestPlace, 24)] ++ [(sharedSealPlace, 1)] := by decide
  have a1 : halved (keyFileDescription Xs N P).first.blocksInOrder (keyProver K).first = true :=
    halved_sealed _ _ _ _ (r1.trans e1) rfl (by
      rw [first_places K hK.first]
      decide)
  have a2 : halved (keyFileDescription Xs N P).shared.blocksInOrder (keyProver K).shared = true :=
    halved_sealed _ _ _ _ (r2.trans e2) rfl (by
      rw [keyProver_shared K hK.splits, hK.onU, hK.onOmega]
      decide)
  have a3 : halved (keyFileDescription Xs N P).second.blocksInOrder (keyProver K).second = true :=
    halved_of_rows _ _ _ r3 (by
      show ∀ r ∈ fullSecond, r.2 = 0 ∨ (([K.own].map (·.place)).any (· == r.1)) = true
      rw [List.map_cons, List.map_nil, hK.own]
      decide)
  unfold halvedAll
  rw [a1, a2, a3]
  rfl

end AtPublicFiles.KeyFile

#print axioms AtPublicFiles.KeyLink.bare_back
#print axioms AtPublicFiles.KeyLink.bareSides_prover
#print axioms AtPublicFiles.KeyLink.any_places
#print axioms AtPublicFiles.KeyLink.halved_of_rows
#print axioms AtPublicFiles.KeyLink.halved_sealed
#print axioms AtPublicFiles.KeyLink.sits_seated
#print axioms AtPublicFiles.KeyFile.halvedAll_key
