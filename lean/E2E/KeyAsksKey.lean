-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyAsksKey.lean: the library's `K14Asks` (Johnson/Desc/ProofFile/Honest/K14/Asks.lean) at the key's
shared thread, from the five facts on the committed table and the key.

Why. From `K14Asks`, `k14_asks` gives each of the members 1 to 8 what it takes to go from one border to
the next. «No term of it is typed» says its head. This file types one at the key's own thread, at
halves that `keyProver` holds, and so keeps the field `hs` of the rule for a file.

Main names.
  `decl₂_front`: the chain's rounds begin with the eight's.
  `own_in`, `sends_in`: the kind's halves and the two sendings' are among `keyProver`'s.
  `asks_key`: `K14Asks`, in scope, at the tables `tbKey`.

Premises that stay. `F`: `FiveFields`; `five_made` (E2E/KeyFiveFields.lean) pays it at an input that the
committer makes. `hlin`, `hsend`: the letters `K.lin`, `K.send` are the plan's. `hap`: the two proximity
tests' places stand apart from the others. `hN`: no two messages have one tenant.

What stays open. `K14Asks` speaks under `Thr`: nothing here says that the thread stands.

NOT IN FRONT OF A LAW OVER COINS: `asks_key` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: `F` is over the letters `K.weights`, `randKey K`, `w`,
of the first kind where the input is made of a run's coins. `hs`, `scope` read public files. None of
these is the term that the committer makes. None: the bar is flat. The others name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyTreesKey
import E2E.KeySharedThread
import E2E.KeyBookSplit
import Johnson.Desc.ProofFile.Honest.K14.FiveFieldsAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyAsksKey
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedPar beforeSharedPoint sharedTests
  keyAsProof descriptionFromSource)
open _root_.Desc.K14 (P14 St blocksOr)
open AtPublicFiles.AtFiles (KeySourced flat₂ flat₂_cut)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared sharedChainProverSidesInOrder randK14)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey othersKey plan_key asked_key)
open AtPublicFiles.KeyThread (sentIn fixedOwn decl₂)
open AtPublicFiles.KeyTreesKey (declOf tbKey treesU_of treesO_of)

/-- The chain's rounds begin with the eight's. -/
theorem decl₂_front (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) :
    ∃ rest, decl₂ (descriptionFromSource Xs Nr Pl) = declOf (parKey Xs Pl) ++ rest := by
  refine ⟨(H2K.JointK.keyGu Pl :: ((Pl.O.toList.map H2K.JointK.keyOmega) ++
    [H2K.JointK.keySharedEnd Xs.chains Pl])).flatMap (·.rounds), ?_⟩
  show (flat₂ Xs.chains Pl).flatMap (·.rounds) = _
  rw [flat₂_cut, List.flatMap_append]
  congr 1
  unfold H2K.JointK.keySharedPre declOf
  simp only [List.flatMap_cons, List.flatMap_map]
  rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OnBytes.OracleNotice}
  {layO : OnBytes.TreeLay} {O : Others Bk W₀ Rc X₀ P₁ Wt} {weights : W₀ → Weights}
  {rand : Rc → TableRand}
  {tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}

/-- `treesU_of` at a value that is the written one. -/
theorem treesU_at (e : Q = QK) (hQ : Plan2 Q sentU layO) (Cl : Type) (rl : List Fmt.DeclaredRound)
    (hfx : ∀ j, O.fixed (.own j) = sentIn (declOf Q ++ rl) j)
    (htb : O.table = tbKey Q weights rand tk tt) :
    TreesLaid (letters2 Q sentU O Cl).thread 2 (jobU ⟨Q, 0⟩) (witOf Q weights rand) := by
  subst e
  exact treesU_of hQ Cl rl hfx htb

/-- `treesO_of` at a value that is the written one. -/
theorem treesO_at (e : Q = QK) (hQ : Plan2 Q sentU layO) (Cl : Type) (rl : List Fmt.DeclaredRound)
    (hfx : ∀ j, O.fixed (.own j) = sentIn (declOf Q ++ rl) j)
    (htb : O.table = tbKey Q weights rand tk tt) :
    TreesLaid (letters2 Q sentU O Cl).thread 5 (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) := by
  subst e
  exact treesO_of hQ Cl rl hfx htb

end

section
variable {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)

/-- The kind's own halves are among the key prover's. -/
theorem own_in (hsp : K.lin.S.sharedSplitNeeded = true) :
    ∀ h ∈ (K14.proverSidesOfSharedRounds K.lin K.weights : List (Placed Empty (Common W₀ Rc TableKey) X₀)),
      h ∈ (keyProver K).shared := by
  intro h hh
  rw [K14.halves_eq, hsp, if_pos rfl] at hh
  show h ∈ sharedChainProverSidesInOrder (K14.proverSidesOfSharedRounds K.lin K.weights)
    (K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++ [K.onU, K.onOmega]
  rw [K14.halves_eq, K14.sendHalves_eq, hsp, if_pos rfl]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, sharedChainProverSidesInOrder] at hh ⊢
  rcases hh with rfl | rfl | rfl | rfl <;> simp

/-- The two sendings' halves too. -/
theorem sends_in (hsp : K.lin.S.sharedSplitNeeded = true) :
    ∀ g ∈ (K14.proverSidesOfSharedSendings K.send K.weights (fun c => randK14 (K.rand c)) :
      List (Placed Empty (Common W₀ Rc TableKey) X₀)), g ∈ (keyProver K).shared := by
  intro g hg
  rw [K14.sendHalves_eq] at hg
  show g ∈ sharedChainProverSidesInOrder (K14.proverSidesOfSharedRounds K.lin K.weights)
    (K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++ [K.onU, K.onOmega]
  rw [K14.halves_eq, K14.sendHalves_eq, hsp, if_pos rfl]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, sharedChainProverSidesInOrder] at hg ⊢
  rcases hg with rfl | rfl <;> simp

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- The tables at the key. -/
abbrev tableKey : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn →
    Place × Table :=
  tbKey (parKey Xs Pl) K.weights (randKey K) tk tt

/-- **`K14Asks` at the key's shared thread.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem asks_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (F : FiveFields (parKey Xs Pl)
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w).valid
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w).stored
      K.weights (randKey K))
    (hlin : K.lin = planData (parKey Xs Pl)) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K.onU.place, K.onOmega.place].Nodup)
    (hN : Function.Injective Nm.tenant) :
    ∃ layO, K14Asks ℓ (lettersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w)
      (parKey Xs Pl) (sentKey Xs Pl) layO (keyAsProof Xs.chains) (sharedTests Pl)
      VerifiableInference.Desc.K12.Seat.last (planData (parKey Xs Pl)) K.weights (randKey K) := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  have e : parKey Xs Pl = QK := par_sourced hs scope
  have hsp : K.lin.S.sharedSplitNeeded = true := by
    rw [hlin]
    exact hQ.facts.two
  obtain ⟨rl, hr⟩ := decl₂_front Xs Nr Pl
  have hfx : ∀ j, (othersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w).fixed (.own j) =
      sentIn (declOf (parKey Xs Pl) ++ rl) j := by
    intro j
    show sentIn (decl₂ (descriptionFromSource Xs Nr Pl)) j = _
    rw [hr]
  have tU := treesU_at e hQ VerifiableInference.Desc.Key.Claim rl hfx
    (rfl : (othersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w).table = _)
  have tO := treesO_at e hQ VerifiableInference.Desc.Key.Claim rl hfx
    (rfl : (othersKey Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w).table = _)
  have sh : SendShapes QK := sendShapes_of QK (by decide +kernel)
  rw [← e] at sh
  have bk := AtPublicFiles.KeyBookSplit.book_field K₀ hK₀
  rw [← e] at bk
  refine ⟨layO, asks_of_five F (asked_key Xs Nr Pl K ℓ Nm Mg₀ (tableKey Xs Pl K₀ K tk tt) rest Kp Vd w) hQ sh
    rfl rfl ⟨rfl, ?_, ?_⟩ ?_ hN tU tO bk⟩
  · show ((keyProver K).shared.map (·.place)).Nodup
    rw [keyProver_shared K hsp]
    exact hap
  · intro h hh
    rw [← hlin] at hh
    exact own_in K hsp h hh
  · intro g hg
    have hg' : g ∈ (K14.proverSidesOfSharedSendings K.send K.weights (fun c => randK14 (K.rand c)) :
        List (Placed Empty (Common W₀ Rc TableKey) X₀)) := by
      rw [hsend]
      exact hg
    exact sends_in K hsp g hg'

end

end AtPublicFiles.KeyAsksKey

#print axioms AtPublicFiles.KeyAsksKey.decl₂_front
#print axioms AtPublicFiles.KeyAsksKey.own_in
#print axioms AtPublicFiles.KeyAsksKey.treesU_at
#print axioms AtPublicFiles.KeyAsksKey.treesO_at
#print axioms AtPublicFiles.KeyAsksKey.sends_in
#print axioms AtPublicFiles.KeyAsksKey.asks_key
