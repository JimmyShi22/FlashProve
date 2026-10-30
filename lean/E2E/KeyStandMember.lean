-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandMember.lean: the key's shared thread at border 3, at terms: the prover's table is the
encoded index, the key is the term that the committer makes.

Why. `pair_three` (E2E/KeyStandThree.lean) stands under premises. Here they are met, but for those on
`K'`, `hN`, `hPin`, and `hKp`, `hE`, `hV`, `hS`, `hSN` on the letters `Kp`, `Vd`, `Said`; `stand_full`
(E2E/KeyStandFull.lean) has a member of the first three.

Main names.
  `fitOf`, `draws_closed`: a written challenge for a round; it fits at each of the eight, at `QK`.
  `lists_fit`, `lists_key`: so some list of challenges fits at the members 1 and 2.
  `keyOf`: the prover's letters with `stored`, `weights`, `rand`, `lin`, `send` laid.
  `item_at_three`: at border 3 the state holds o_u's sample constraints, and they hold of the witness's
    words.
  `stand_three`: THE STATEMENT, at every letter `Said`, field `o` of the start, table letter `tt` and `Kp` with
    `hKp`, `hE`: where `Said` holds at the start and `SaidNext` at the first three members: at every run's coins, every index, coins of the
    committer and seed, and every list of challenges that fits, there are a state, a stand and tables
    at which the thread stands at border 3 with `Said`, it has heard that list, the item holds there,
    at least one sample row is there, and at the step of «send o_u» the first round that the step
    returned shows `treeTables` of `rowsU` (`PlayedSends`, `TieU`, E2E/KeyStandThree.lean).

What `Said` is worth. It is a letter: every sentence here is a conditional on it.

Premises that stay. `hS`, `hSN`: on the letter `Said`, at the start's field `o`. `hKp`, `hE`: on `Kp`. `hV`: on `Vd`.
`hx`: the instance is the committer's key. The letters of `K'`: the first chain's halves,
`onU`, `onOmega`, `rng`, `own`. `qr`, `qU`, `qO`, `qw` stand because `noStopAll_keyProver` asks them; no half at these
places is reached here. `pU`, `pO`: their places. `hN`: no two messages have one tenant. `hPin`: the item on the
stored table is left true: the thread of record's meaning is not this one, and this says nothing of
that item.

What stays open. It stands at pubKey, a made-up value. THE TREE: the item's words are `witL`'s honest
words. What ties the sample rows to them is the answers that the half sent and the verifier's fold
kept. `TieU` ties the tables that the first round returned to `rowsU`; no item does. The item read here is «the sample constraints that the state holds are true of
the words», the library's `Says` with a row as it lies, no more: that a row's summands lie within the
statement's tables is not shown. Thr at 3 also holds `omU`, `nearU`, `recRow`: they are not stated here. No
proximity test, nothing of the first chain, W, the door or the last chain: it fires none of the
statements behind `Thr` at the borders 12 or 19. «In scope» is one written value, the full size.

NOT IN FRONT OF A LAW OVER COINS: `item_at_three` and `stand_three` bear this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `Vd` under `hV` is a letter for a predicate, through
`inK w₀ rc x`, of the first kind. `Said` under `hS` is a letter for a predicate, of the first kind, through `k`,
and `o` is no coin; `hSN` is bound over all coins and by itself picks none; `tt` stands under no premise; `hKp`,
`hE` name no coin. The thread's clauses at `k`, of the first kind; `hx` ties `x` to the committer's coins at `f`, `g`, `sd`, of the first kind; `stored` is `encW` there: that
this is or is not the term of the rule's own reading is not this file's to say. None: the bar is
flat. `fitOf`, `draws_closed`, `lists_fit`, `keyOf` name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandThree
import E2E.KeyFiveFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyStandMember
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS Msg2 ItemS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open _root_.Desc.K14 (St blocks blocksOr)
open _root_.Desc.K14.Honest (SmpOwn)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace frontPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open Bind.ForProver (shapeOf shapeOfIndex linOf rowsFit encW oodSh Seed)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeySharedThread (parKey randKey threadKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (startAt inK envK)
open AtPublicFiles.KeyStandThree (pair_three)

/-- None of the eight places is the front's. -/
theorem front_apart : ∀ a ∈ [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5,
    K14.place 7, K14.place 8, foldedTestPlace, omegaTestPlace], (a == frontPlace) = false := by
  decide

/-- A written challenge for a round. -/
def fitOf (d : Fmt.DeclaredRound) : Fmt.Drawn :=
  { noChallenge with
    elems := List.replicate d.entry.drawE (1, 0, 0)
    poss := List.replicate d.entry.poss 0
    trits := List.replicate d.entry.trits 0 }

/-- **It fits at every round of the eight.** By Lean's kernel. -/
theorem draws_closed :
    (blocksOr QK).all (fun b => drawsFit b.rounds (b.rounds.map fitOf)) = true := by
  decide +kernel


/-- **Some list fits**: the written one, at the members 1 and 2, at any thread over the eight. -/
theorem lists_fit {Cl : Type} {T : List (VerifiableInference.Desc.Block St Cl)} {Q : _root_.Desc.K14.P14}
    (e : Q = QK)
    (hm : ∃ b1 b2 b3 b4 b5 b6 b7 b8 : VerifiableInference.Desc.Block St Unit,
      blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      ∀ i (c : VerifiableInference.Desc.Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some c →
        ∀ blk, T[1 + i]? = some blk → blk.rounds = c.rounds ∧ blk.oracles = c.oracles ∧
          blk.place = c.place) :
    ∃ ds₁ ds₂ : List Fmt.Drawn,
      (∀ blk, T[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
      (∀ blk, T[2]? = some blk → drawsFit blk.rounds ds₂ = true) := by
  subst e
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := hm
  have dc := draws_closed
  have eb : blocksOr QK = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hb]
    rfl
  rw [eb] at dc
  refine ⟨b1.rounds.map fitOf, b2.rounds.map fitOf, fun blk hblk => ?_, fun blk hblk => ?_⟩
  · rw [(hm 0 b1 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b1 (by simp)
  · rw [(hm 1 b2 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b2 (by simp)

section
variable {W₀ Rc X₀ X Wk : Type}

/-- **The prover's letters with its table, index, coins and the shared chain's own data laid.** -/
def keyOf (Zp : ProofFile.Pub) (Xs : Source) (Pl : LaterPlaces) (K' : KeyParts W₀ Rc X₀ X Wk)
    (f : W₀ → Weights) (g : Rc → ℕ → TableRand) : KeyParts W₀ Rc X₀ X Wk :=
  { K' with
    stored := fun a r i x => encW Zp (f a) (g r) i x
    weights := f
    rand := fun r => g r 0
    lin := planData (parKey Xs Pl)
    send := ⟨parKey Xs Pl, 0⟩ }

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The item at border 3.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem item_at_three {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 3 k s m E) (ds : List Fmt.Drawn) :
    SmpOwn (num .oU) s (ℓ.get ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).wit k m.st.input
      (m.st.heard ++ ds))) := by
  have hi : (ItemS.pin .oU) ∈ (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).opened 3 := by
    show (ItemS.pin .oU) ∈ fwdOpen SharedRows.start (SharedRows.rows true) 3
    decide
  exact u.2.2.2.1 ds _ hi .oU rfl

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (o : Option (List OpenedColumn))
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **Some list fits at this thread.** -/
theorem lists_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace) :
    ∃ ds₁ ds₂ : List Fmt.Drawn,
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true) := by
  subst hx
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  have hsp₀ : (planData (parKey Xs Pl)).S.sharedSplitNeeded = true := hQ.facts.two
  have hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place, (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place].Nodup := by
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K'.onU.place, K'.onOmega.place].Nodup
    rw [pU, pO]
    decide
  obtain ⟨B⟩ := hQ.eight
  have H := AtPublicFiles.KeyStandThree.halves_key Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ tk tt rest
    Kp Vd rfl hsp₀ hap
    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
  have E8 : AtEight (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
      (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
      (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)) 1 (parKey Xs Pl) (planData (parKey Xs Pl)) (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).weights :=
    atEight2 B (AtPublicFiles.KeySharedThread.sentKey Xs Pl) VerifiableInference.Desc.Key.Claim H
  exact lists_fit (AtPublicFiles.AtFiles.Full.par_sourced hs scope) E8.eight

/-- **The thread at border 3, at terms.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stand_three {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hV : Vd (inK w₀ rc x))
    (qr : AtPublicFiles.Stops.QuietHalf K'.rng) (qU : AtPublicFiles.Stops.QuietHalf K'.onU)
    (qO : AtPublicFiles.Stops.QuietHalf K'.onOmega) (qw : AtPublicFiles.Stops.QuietHalf K'.own)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true)
    (hS : Said 0 k (startAt (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) o (inK w₀ rc x)))
    (hSN : ∀ b, b < 3 → SaidNext (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)) Said b) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)) Said 3 k s m E ∧
      m.st.heard = ds₁ ++ ds₂ ∧
      SmpOwn (num .oU) s (ℓ.get ((threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).wit k m.st.input m.st.heard)) ∧
      (∃ y, s.st.oracles[num .oU]? = some y ∧ 0 < y.sampleRows.size) ∧
      AtPublicFiles.KeyStandThree.PlayedSends (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
                  (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
                  (inK w₀ rc x)) Said k ds₂ m E (fun ps =>
                  AtPublicFiles.KeyStandThree.TieU (parKey Xs Pl) (AtPublicFiles.KeySharedThread.sentKey Xs Pl) ℓ
                    (holds2 (parKey Xs Pl) (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).weights (randKey (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)) k (inK w₀ rc x))
                    (inK w₀ rc x).key (firstRv m.st.heard) ps
                    ((threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
                  (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
                  (inK w₀ rc x)).wit k m.st.input m.st.heard)) := by
  subst hx
  have es := AtPublicFiles.AtFiles.sized_sourced hs scope
  have hfit : rowsFit (shapeOf (pubKey Z₀ Xs.chains)) (linOf (pubKey Z₀ Xs.chains)).kLo
      (linOf (pubKey Z₀ Xs.chains)).matrixRows = true := by
    show rowsFit (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index)
      Xs.chains.made.sized.key.once.shape.kLo Xs.chains.made.sized.key.once.shape.matrixRows = true
    rw [es]
    exact AtPublicFiles.KeyFiveFields.rows_full
  have ha : (shapeOf (pubKey Z₀ Xs.chains)).a ≤ 32 := by
    show (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index).a ≤ 32
    rw [es]
    exact AtPublicFiles.KeyFiveFields.a_full
  have F := AtPublicFiles.KeyFiveFields.five_made Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd f g Z₀ hfit ha rfl rfl
    (fun _ _ _ => rfl) w₀ rc sd
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  have hsp₀ : (planData (parKey Xs Pl)).S.sharedSplitNeeded = true := hQ.facts.two
  have hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place, (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place].Nodup := by
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K'.onU.place, K'.onOmega.place].Nodup
    rw [pU, pO]
    decide
  have hO' := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
  obtain ⟨s, m, E, u, h, hy, hT⟩ := pair_three Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ tk tt rest Kp Vd Said o w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩ hs scope hK₀ F rfl rfl hap hN qr qU qO qw k hV
    (by
      intro ds i hi
      have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 0 := hi
      rw [AtPublicFiles.KeySharedQuiet.open_front] at hi'
      obtain rfl := List.mem_singleton.1 hi'
      exact hPin _ _ _ _)
    hKp hE (fun v s y _ u _ _ => hPin v s _ u)
    (by
      intro blk hblk
      rw [hO'.bs] at hblk
      have hb₀ : ∃ b₀, (descriptionFromSource Xs Nr Pl).shared.blocksInOrder[0]? = some b₀ ∧ b₀.place = frontPlace :=
        ⟨_, rfl, rfl⟩
      obtain ⟨b₀, e₀, hp⟩ := hb₀
      obtain rfl : b₀ = blk := Option.some.inj (e₀.symm.trans hblk)
      rw [List.find?_eq_none]
      intro g' hg
      have hmem : g'.place ∈ (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.map (·.place) := List.mem_map.2 ⟨g', hg, rfl⟩
      rw [keyProver_shared _ hsp₀] at hmem
      have hmem' : g'.place ∈ [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
          K14.place 8, foldedTestPlace, omegaTestPlace] := by
        have e1 : (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place = foldedTestPlace := pU
        have e2 : (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place = omegaTestPlace := pO
        rw [e1, e2] at hmem
        exact hmem
      rw [hp, front_apart _ hmem']
      exact Bool.false_ne_true)
    ds₁ ds₂ hd₁ hd₂ hS hSN
  refine ⟨s, m, E, u, h, ?_, hy, hT⟩
  have it := item_at_three Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ _ rest _ _ _ u.1 []
  rw [List.append_nil] at it
  exact it

end

end AtPublicFiles.KeyStandMember

#print axioms AtPublicFiles.KeyStandMember.front_apart
#print axioms AtPublicFiles.KeyStandMember.draws_closed
#print axioms AtPublicFiles.KeyStandMember.lists_fit
#print axioms AtPublicFiles.KeyStandMember.lists_key
#print axioms AtPublicFiles.KeyStandMember.item_at_three
#print axioms AtPublicFiles.KeyStandMember.stand_three
