-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtKeyBud.lean: THE FIELD bud₂ AT K14's SIX ROWS AT THE KEY FILE: at a sourced description, in scope, where the verifier's test on the files accepts: at each row with letters that
has the place, parts and bud of one of the six at the written parameters `QK`, the body of bud₂ of `BudDebts`: by the count of the key's written rounds (`keyOpens`, `same_key`), evaluated.

  `declOpens_key`, `count_key`, `first_chain_key`   what the description's rounds open is what the written rounds' data open; six trees in the first chain
  `tests_not_send`, `no_later_u_key`, `no_later_o_key`   no member behind the sending stands at its place
  `one_tree_key`   "send o_u" states one tree
  `tests_at_key`   **the test accepts at both sendings** (an evaluation)
  `key_sendings_trees`, `key_three_counts`, `key_four_rows`, `key_tests_bite`   its controls: the trees, the counts 97, 98, 146, the rows' r, and at a count greater by one it rejects
  `six_bud_key`    **the body of bud₂**
  `six_onFromS_key`   **`OnFromS` at the six**, at every frame's sentence over the list
  `KeySendersAtTheDescription`, `keyRows_mem_QK`   the two facts on a value of `KeyParts`, as named premises, and what they give

Limits. A RUN OF ONE REQUEST, AS ONLINE: a key file's proof is one. Positions that the frame lays at due challenges: the frame's rule is what says that a run's are these. No property of the protocol is claimed.
-/
import AtFullSide.K14.Sim.AtKey
import Johnson.Desc.ProofFile.Honest.K14.BudRows
import E2E.ReadsAtFiles
import E2E.TreeReadsAtWritten
import Johnson.Desc.Key.SharedChainIsChainOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedChain sharedPar beforeSharedPoint sharedTests keyAsProof
  sharedChain_flat_eq_chainOf_flat)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open Desc.K14 (St P14 blocks)
open Desc.K14.Law (flat_retype_all)
open Desc.K14.Honest (FlatOf)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced plan2_full)
open VerifierAndGoals (InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open OnBytes.SendSim.At (budAt)
open AtPublicFiles.TreeReads (declOpens treeNo opensOf opensOf_at opens_of_data keyOpens same_key)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- The proximity tests stand at neither sending's place. -/
theorem tests_not_send (M : LaterPlaces) :
    ∀ z ∈ sharedTests M, z.place ≠ sendPlace 2 ∧ z.place ≠ sendPlace 5 := by
  have k : ∀ (pl : Place) (x : H2U.PlaceNums),
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt pl x) : Block T12 Unit).place = pl := fun pl x =>
    (H2K.JointK.place_of_k12 _ _).trans (H2K.JointK.place_of_p12At _ _)
  intro z hz
  simp only [sharedTests, List.mem_append, List.mem_singleton, List.mem_map] at hz
  rcases hz with rfl | ⟨nO, -, rfl⟩
  · show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ M.U) : Block T12 Unit).place ≠ _ ∧
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ M.U) : Block T12 Unit).place ≠ _
    rw [k]
    simp [sendPlace]
  · show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).place ≠ _ ∧
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).place ≠ _
    rw [k]
    simp [sendPlace]

variable {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- No member of the key's shared list behind the third stands at "send o_u"'s place. -/
theorem no_later_u_key (c : OnBytes.Model.Verify.Chains) (M : LaterPlaces)
    (hb : blocks (sharedPar c (beforeSharedPoint M)) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ y ∈ ((sharedChain c M).retype (Cl' := Claim)).blocksInOrder.drop 3, y.place ≠ sendPlace 2 := by
  obtain ⟨-, p4, p7, p8⟩ := places4 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, p6⟩ := places2 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, pO⟩ := send_declares _ 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  intro y hy
  rw [sharedChain_flat_eq_chainOf_flat, flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb] at hy
  refine no_later_u_at [b3, b4, b5, b6, b7, b8]
    (VerifiableInference.Desc.K12.Seat.last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ sharedTests M))
    (sharedTests M) (fun z hz => ?_) (fun z hz => (tests_not_send M z hz).1)
    (by rw [H2K.JointK.last_place]; decide) y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [p3]; decide
  · rw [p4]; decide
  · rw [pO]; decide
  · rw [p6]; decide
  · rw [p7]; decide
  · rw [p8]; decide

/-- No member of the key's shared list behind the sixth stands at "send o_omega"'s place. -/
theorem no_later_o_key (c : OnBytes.Model.Verify.Chains) (M : LaterPlaces)
    (hb : blocks (sharedPar c (beforeSharedPoint M)) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ y ∈ ((sharedChain c M).retype (Cl' := Claim)).blocksInOrder.drop 6, y.place ≠ sendPlace 5 := by
  obtain ⟨-, -, p7, p8⟩ := places4 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, p6⟩ := places2 _ b1 b2 b3 b4 b5 b6 b7 b8 hb
  intro y hy
  rw [sharedChain_flat_eq_chainOf_flat, flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb] at hy
  exact no_later_at b6 b7 b8
    (VerifiableInference.Desc.K12.Seat.last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ sharedTests M))
    (sharedTests M) (by rw [p6]; decide) (by rw [p7]; decide) (by rw [p8]; decide)
    (fun z hz => (tests_not_send M z hz).2) (by rw [H2K.JointK.last_place]; decide) y hy

/-- "send o_u" states one tree, at the written parameters. -/
theorem one_tree_key (hb : blocks QK = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (os : List VerifiableInference.Desc.Oracle) (ho : b2.oracles = [os, []]) : os.length = 1 := by
  obtain ⟨sentU, hU, rfl, -⟩ := Desc.K14.Law.two_sendings QK b1 b2 b3 b4 b5 b6 b7 b8 hb
  have e : os = Desc.K14.oraclesOf QK.codes sentU [[0], []] := by
    have e1 := ((List.cons.inj ho).1).symm
    rwa [Desc.K14.Law.parK1_sent] at e1
  have hk : ((Desc.K14.withU QK.S).all fun s =>
      (Desc.K14.oraclesOf QK.codes s [[0], []]).length == 1) = true := by decide +kernel
  rw [hU] at hk
  rw [e]
  exact beq_iff_eq.1 hk

/-- **CONTROLS OF THE TEST AT THE KEY**, as the online file has them: each sending has two messages, each in a tree: o_u and the first mask in one; o_omega and o_sp in two. -/
theorem key_sendings_trees :
    (((VerifiableInference.Desc.Own.treesMade QK.codes ((Desc.K14.withU QK.S).getD #[])).getD {}).tree.toList,
      ((VerifiableInference.Desc.Own.treesMade QK.codes (Desc.K14.withOmega QK.S)).getD {}).tree.toList) =
      ([0, 0], [0, 1]) := by decide +kernel

/-- The counts in a batch of one request at the three trees' numbers. -/
theorem key_three_counts : (keyOpens.inBatch 1 6, keyOpens.inBatch 1 7, keyOpens.inBatch 1 8) =
    (97, 98, 146) := by decide +kernel

/-- The four messages' rows and codes: main rows, mask rows, the r of each. WITH `key_three_counts`: o_u's main rows: 97 of 97: FILLED · the first mask's row: 97 of 146 · o_omega's main rows: 98 of 98: FILLED · o_sp's mask row: 146 of 146: FILLED. -/
theorem key_four_rows :
    ((((Desc.K14.withU QK.S).getD #[]).toList.map fun x =>
        (x.shape.mainRows, x.shape.maskRows, (QK.codes.base.getD x.shape.code default).r,
          (QK.codes.mask.getD x.shape.maskCode default).r)),
      ((Desc.K14.withOmega QK.S).toList.map fun x =>
        (x.shape.mainRows, x.shape.maskRows, (QK.codes.base.getD x.shape.code default).r,
          (QK.codes.mask.getD x.shape.maskCode default).r))) =
      ([(107, 0, 97, 0), (0, 1, 0, 146)], [(12, 0, 98, 0), (0, 1, 0, 146)]) := by
  decide +kernel

/-- **IT CAN FAIL**: at a count that is greater by one the test rejects at both sendings. -/
theorem key_tests_bite :
    countsWithinB (fun j => keyOpens.inBatch 1 j + 1) 6 QK.codes
        ((Desc.K14.withU QK.S).getD #[]) = false ∧
      countsWithinB (fun j => keyOpens.inBatch 1 j + 1) 7 QK.codes
        (Desc.K14.withOmega QK.S) = false := by decide +kernel

/-- What the description's declared rounds open is what the written rounds' data open. -/
theorem declOpens_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    declOpens (keyFileDescription Xs N Pl) = opensOf Johnson.G.writtenKFull := by
  rw [← AtPublicFiles.Reads.key_data Z scope live, opensOf_at]
  exact (opens_of_data hs.named.data).symm

/-- So the count is that of the library's short lists. -/
theorem count_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (n : Nat) :
    (declOpens (keyFileDescription Xs N Pl)).inBatch n = keyOpens.inBatch n :=
  funext fun j => by rw [declOpens_key hs scope live, same_key.inBatch]

/-- The first chain sends six trees. -/
theorem first_chain_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : (keyFileDescription Xs N Pl).t₁ = 6 := by
  rw [← Desc.K14.Honest.opens_first_decl, declOpens_key hs scope live,
    Desc.K14.Honest.opens_first_data]
  exact same_key.e₁

/-- **The test accepts at both sendings.** -/
theorem tests_at_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (a : Nat) :
    countsWithinB ((declOpens (keyFileDescription Xs N Pl)).inBatch 1) (treeNo (keyFileDescription Xs N Pl) 1 0)
        (jobU ⟨QK, a⟩).Q.codes (jobU ⟨QK, a⟩).Q.sent = true ∧
      countsWithinB ((declOpens (keyFileDescription Xs N Pl)).inBatch 1) (treeNo (keyFileDescription Xs N Pl) 1 1)
        (jobOmega ⟨QK, a⟩).Q.codes (jobOmega ⟨QK, a⟩).Q.sent = true := by
  have eU : (jobU ⟨QK, a⟩).Q.sent = (Desc.K14.withU QK.S).getD #[] :=
    Desc.K14.Law.parK1_sent QK 2 _ _
  have eO : (jobOmega ⟨QK, a⟩).Q.sent = Desc.K14.withOmega QK.S :=
    Desc.K14.Law.parK1_sent QK 5 _ _
  have t0 : treeNo (keyFileDescription Xs N Pl) 1 0 = 6 := by
    show (keyFileDescription Xs N Pl).t₁ + 0 = 6
    rw [first_chain_key hs scope live]
  have t1 : treeNo (keyFileDescription Xs N Pl) 1 1 = 7 := by
    show (keyFileDescription Xs N Pl).t₁ + 1 = 7
    rw [first_chain_key hs scope live]
  rw [eU, eO, t0, t1, count_key hs scope live 1]
  show countsWithinB (keyOpens.inBatch 1) 6 QK.codes ((Desc.K14.withU QK.S).getD #[]) = true ∧
    countsWithinB (keyOpens.inBatch 1) 7 QK.codes (Desc.K14.withOmega QK.S) = true
  decide +kernel

variable {W₀ Rc X Pb : Type}

/-- **THE BODY OF bud₂ AT THE KEY FILE**, at every row with letters that has the place, parts and bud of one of the six at `QK`. -/
theorem six_bud_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (d : Data) (Bk : ProverCoinCounts)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X OnBytes.TableKey)
    (hr : r ∈ simRows d ⟨QK, 0⟩ weights rand)
    (L : Lettered Bk St Claim Empty (Common W₀ Rc OnBytes.TableKey) X OnBytes.TableKey)
    (c1 : L.place = r.place) (c2 : L.row = r.row) (c4 : L.bud = r.bud) :
    ∀ τ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
      ∀ (pre t : List (Block St Claim)) (n : Nat),
      (keyFileDescription Xs N Pl).shared.blocksInOrder = pre ++ τ.block :: t →
      n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (keyFileDescription Xs N Pl) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (keyFileDescription Xs N Pl) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  have e := par_sourced hs scope
  obtain ⟨layO, hP⟩ := plan2_full
  obtain ⟨B⟩ := hP.eight
  have hb : blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) =
      some [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
    rw [e]
    exact B.made
  have F : FlatOf (keyFileDescription Xs N Pl).shared.blocksInOrder Xs.chains B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 :=
    flatOf_key Xs.chains Pl hb
  rcases List.mem_append.1 hr with g | g
  · have eb : L.bud = k14Bud := by
      refine c4.trans ?_
      unfold ownRows at g
      rcases List.mem_append.1 g with g | g
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
        rcases g with rfl | rfl | rfl <;> rfl
      · split at g
        · obtain rfl := List.mem_singleton.1 g
          rfl
        · cases g
    intro τ _ u _ pre t n _ _ ρ _
    rw [eb]
    trivial
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    intro τ hτ u hu pre t n hx hn ρ hρ
    have hrow := (side_ok hτ).2.2
    have hpl := (side_ok hτ).2.1
    rcases g with rfl | rfl
    · rw [c2] at hrow
      rw [members_send τ _ _ hrow] at hu
      obtain rfl := List.mem_singleton.1 hu
      have h0 : n = (pre.flatMap (·.rounds)).length := hn
      have hz : (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take
          (pre.flatMap (·.rounds)).length).map (·.2.length)).sum = 0 :=
        none_before_u F hb (no_later_u_key Xs.chains Pl hb) pre t τ.block hx (hpl.trans c1)
      rw [h0, hz, c4]
      exact budAt_of_test hs.named.data 1 _ 0 (tests_at_key hs scope live 0).1 ρ hρ _
    · rw [c2] at hrow
      rw [members_send τ _ _ hrow] at hu
      obtain rfl := List.mem_singleton.1 hu
      have h0 : n = (pre.flatMap (·.rounds)).length := hn
      obtain ⟨os, ho, hsum⟩ := trees_before_omega F hb (no_later_o_key Xs.chains Pl hb) pre t
        τ.block hx (hpl.trans c1)
      have h1 := one_tree_key B.made os ho
      have hz : (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take
          (pre.flatMap (·.rounds)).length).map (·.2.length)).sum = 1 := hsum.trans h1
      rw [h0, hz, c4]
      exact budAt_of_test hs.named.data 1 _ 1 (tests_at_key hs scope live 0).2 ρ hρ _

/-- **`OnFromS` AT THE SIX ROWS, AT THE KEY FILE**, at every frame's sentence over the description's shared list: the form of RowDebts' field. -/
theorem six_onFromS_key (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (T₂ : Thread Bk St Claim Empty (Common W₀ Rc OnBytes.TableKey) X OnBytes.TableKey)
    (hbs : T₂.bs = (keyFileDescription Xs N Pl).shared.blocksInOrder)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X → Prop) (d : Data)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X OnBytes.TableKey)
    (hr : r ∈ simRows d ⟨QK, 0⟩ weights rand)
    (L : Lettered Bk St Claim Empty (Common W₀ Rc OnBytes.TableKey) X OnBytes.TableKey)
    (c1 : L.place = r.place) (c2 : L.row = r.row) (c3 : L.On = r.On) (b : Nat)
    (blk : Block St Claim) (hx : T₂.bs[b]? = some blk) (hp : blk.place = L.place)
    (len : Nat → Nat → Nat) : OnFromS T₂ S₂ L b len := by
  have e := par_sourced hs scope
  obtain ⟨layO, hP⟩ := plan2_full
  obtain ⟨B⟩ := hP.eight
  have hb : blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) =
      some [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
    rw [e]
    exact B.made
  have F : FlatOf T₂.bs Xs.chains B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 := by
    rw [hbs]
    exact flatOf_key Xs.chains Pl hb
  exact six_onFromS_flat T₂ F B.made S₂ d weights rand r hr L c1 c2 c3 b blk hx hp len

/-- **What the key prover's letters must be at the description.** Facts on a value of `KeyParts`, premises here. -/
structure KeySendersAtTheDescription {Wk X₀ : Type} (K : AtPublicFiles.KeyFile.KeyParts W₀ Rc X₀ X Wk) : Prop where
  send : K.send = ⟨QK, 0⟩
  lin : K.lin.S = QK.S

/-- So the key prover's six rows are the six rows at `QK`. -/
theorem keyRows_mem_QK {Wk X₀ : Type} (K : AtPublicFiles.KeyFile.KeyParts W₀ Rc X₀ X Wk)
    (hK : KeySendersAtTheDescription K)
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey) (hr : r ∈ keyRows K) :
    r ∈ simRows K.lin ⟨QK, 0⟩ K.weights fun c => AtPublicFiles.KeyFile.randK14 (K.rand c) := by
  have := keyRows_mem K r hr
  rwa [hK.send] at this

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.six_onFromS_key
#print axioms ProofFile.Honest.K14.keyRows_mem_QK
#print axioms ProofFile.Honest.K14.key_sendings_trees
#print axioms ProofFile.Honest.K14.key_three_counts
#print axioms ProofFile.Honest.K14.key_four_rows
#print axioms ProofFile.Honest.K14.key_tests_bite
#print axioms ProofFile.Honest.K14.tests_not_send
#print axioms ProofFile.Honest.K14.no_later_u_key
#print axioms ProofFile.Honest.K14.no_later_o_key
#print axioms ProofFile.Honest.K14.one_tree_key
#print axioms ProofFile.Honest.K14.declOpens_key
#print axioms ProofFile.Honest.K14.first_chain_key
#print axioms ProofFile.Honest.K14.tests_at_key
#print axioms ProofFile.Honest.K14.six_bud_key
