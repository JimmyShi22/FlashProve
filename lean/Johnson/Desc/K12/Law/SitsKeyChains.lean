-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsChains
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.Chains23
/-
Johnson/Desc/K12/Law/SitsKeyChains.lean: THE KEY FILE's THREE CHAINS' FLAT LISTS CUT AT THE
PROXIMITY TEST's FOUR PLACES: ⟨1, none, 5, .K12⟩ (the ranges' test) · ⟨2, none, 9 | 10, .K12⟩ · ⟨3,
none, 2, .K12⟩; AND THAT THE ENTRY THERE SITS. Of the chains' own makers: Key.firstChain
(Johnson/Desc/Key/Chain1.lean) · Key.sharedChain | thirdChain (Johnson/Desc/Key/Chains23.lean). Over
Johnson/Desc/K12/Law/Sits.lean | SitsChains.lean. NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  Alike · alike_andThen | _stages | _dress | _k12 · Sits.onto     the kind's block does not hang on
      the type
      of claims (the key file's first chain seats it at Claim, the law speaks of it at Unit): one
      list of rounds, one decision, one test on the plan.
  rngEntry one N · rngEntry_sits · keyFirstPre | keyFirstPost · keyFirst_cut     the first chain:
      the ranges' test's block as Chain.blocksInOrder lays it; it sits on proximityTestKind guardedProximityTestParts (rangesParams N)
      behind the door enterAndAsk (enterRanges one) (rangesParams N) | leaveRanges; the flat list
      written out.
  enterAndAsk_asks     that door itself asks: where it lets in, asksOnRecord has said yes at the
      very record.
  keyGu P · keyOmega nO · keySharedPre | keySharedEnd · keyShared_cut(_omega)     the shared chain,
      behind Chain.retype. (keyGu is guEntry's text at another record of places' numbers: a twin by
      type alone.)
  pOwnK P · keySecond_cut     the last chain (thirdChain = lastChainWithOwnTest): by second_cut.
LIMITS. keyFirstPre | keyFirstPost are written THROUGH THE CHAIN's OWN FIELDS (first · front · links
· back.drop 2 · last): what keyFirst_cut pins is «back = layRows :: rangesTest :: …». alike_k12
follows the SHAPE of the kind's block's text (Johnson/Desc/K12/Frame.lean: proximityTestKind: three joins, the
stages, one dress) and writes no name of a block out: a turn of a name there leaves it green; a turn
of the shape does not. That the key file's description's chains are these:
Johnson/Desc/K12/Law/SitsKey.lean. That no other entry bears the kind K12 is not typed. NO RUN.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

/-! ### the kind's block at two types of claims -/

/-- Two blocks at one record, over two types of claims, with one list of rounds, one decision and
one test on the plan. -/
def Alike {T Cl Cl' : Type} (a : Block T Cl) (b : Block T Cl') : Prop :=
  a.rounds = b.rounds ∧ a.decide = b.decide ∧ a.planOk = b.planOk

theorem alike_andThen {T Cl Cl' : Type} (n : String) {a c : Block T Cl} {b d : Block T Cl'}
    (h1 : Alike a b) (h2 : Alike c d) : Alike (a.andThen n c) (b.andThen n d) := by
  obtain ⟨r1, d1, p1⟩ := h1
  obtain ⟨r2, d2, p2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · show a.rounds ++ c.rounds = b.rounds ++ d.rounds
    rw [r1, r2]
  · funext s rs gs
    show (a.decide s (rs.take a.rounds.length) (gs.take a.openings)).bind (fun s' =>
        c.decide s' (rs.drop a.rounds.length) (gs.drop a.openings)) =
      (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind fun s' =>
        d.decide s' (rs.drop b.rounds.length) (gs.drop b.openings)
    have ho : a.openings = b.openings := by unfold Block.openings; rw [r1]
    rw [r1, d1, d2, ho]
  · show (a.planOk && c.planOk) = (b.planOk && d.planOk)
    rw [p1, p2]

theorem alike_stages {T : Type} (Cl Cl' : Type) (X : Parts T) (p : P12) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (l : Laid),
      Alike (stagesFrom X p j cur rest l : Block T Cl)
        (stagesFrom X p j cur rest l : Block T Cl') := by
  intro rest
  induction rest with
  | nil => intro j cur l; exact ⟨rfl, rfl, rfl⟩
  | cons next rest ih =>
    intro j cur l
    unfold stagesFrom
    exact alike_andThen _ (alike_andThen _ (alike_andThen _ (alike_andThen _ ⟨rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl⟩) ⟨rfl, rfl, rfl⟩) ⟨rfl, rfl, rfl⟩) (ih _ _ _)

/-- A block in another dress (name · place · before; one test more on the plan) is alike. -/
theorem alike_dress {T Cl Cl' : Type} {b : Block T Cl} {b' : Block T Cl'} (h : Alike b b')
    (n : String) (pl : Place) (bf : List (Nat × Nat)) (q : Bool) :
    Alike { b with name := n, place := pl, before := bf, planOk := q && b.planOk }
      { b' with name := n, place := pl, before := bf, planOk := q && b'.planOk } :=
  ⟨h.1, h.2.1, congrArg (q && ·) h.2.2⟩

/-- The kind's block does not hang on the type of claims. (No name of a block is written out
here: the names are read off the kind's own text.) -/
theorem alike_k12 {T : Type} (Cl Cl' : Type) (X : Parts T) (p : P12) :
    Alike (proximityTestKind X p : Block T Cl) (proximityTestKind X p : Block T Cl') := by
  unfold proximityTestKind
  split
  · refine alike_dress ?_ _ _ _ _
    exact alike_andThen _ (alike_andThen _ (alike_andThen _ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)
      ⟨rfl, rfl, rfl⟩) (alike_stages Cl Cl' X p _ _ _ _)
  · exact ⟨rfl, rfl, rfl⟩

/-- A seat on a block is a seat on every block alike. -/
theorem Sits.onto {S T Cl Cl' Cl'' : Type} {B : Block S Cl} {K : Block T Cl'} {K' : Block T Cl''}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (hk : Alike K K') : Sits B K' enter leave where
  rounds := h.rounds.trans hk.1
  plan := fun a => hk.2.2 ▸ h.plan a
  step := fun ft s s' rs cols k a => by
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft s s' rs cols k a
    exact ⟨t, t', e1, step_same2 K K' hk.1 hk.2.1 ft t rs cols ▸ e2, e3⟩

/-! ### the first chain -/

/-- The ranges' test's block as Chain.blocksInOrder lays it. -/
def rngEntry (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums) : Block Key.FirstState Key.Claim :=
  (Key.rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim).asBare

theorem rngEntry_sits (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums) :
    Sits (rngEntry one N) (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Blk')
      (Key.enterAndAsk (Key.enterRanges one) (Key.rangesParams N)) Key.leaveRanges :=
  (((sits_inside _ (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Block T12 Key.Claim) _).same
    (Key.rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim)
    rfl rfl
    (fun a => by
      simp only [Key.rangesTest, Bool.and_eq_true] at a
      exact a.1)).asBare).onto (alike_k12 Key.Claim Unit guardedProximityTestParts _)

/-- What stands in front of the ranges' test: the chain's first block, its front, the lookups'
links, the laying of the lookups' rows. -/
def keyFirstPre (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) : List (Block Key.FirstState Key.Claim) :=
  (Key.firstChain one D told set N).first.asBare ::
    (Key.firstChain one D told set N).front.map Block.asBare ++
    (Key.firstChain one D told set N).links.flatMap Link.blocksInOrder ++ [(Key.layRows one).asBare]

/-- What stands behind it: the rest of the chain's back, and its end. -/
def keyFirstPost (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) : List (Block Key.FirstState Key.Claim) :=
  ((Key.firstChain one D told set N).back.drop 2).map Block.asBare ++
    [(Key.firstChain one D told set N).last.asBare]

/-- The key file's first chain's flat list is cut at the ranges' test. -/
theorem keyFirst_cut (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) :
    (Key.firstChain one D told set N).blocksInOrder =
      keyFirstPre one D told set N ++ rngEntry one N :: keyFirstPost one D told set N := by
  rw [Chain.flat_eq]
  have hb : (Key.firstChain one D told set N).back =
      Key.layRows one :: Key.rangesTest (Key.enterRanges one) Key.leaveRanges N ::
        (Key.firstChain one D told set N).back.drop 2 := rfl
  rw [hb]
  simp only [keyFirstPre, keyFirstPost, rngEntry, List.map_cons, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The door of the ranges' test itself asks: where it lets in, what the seat asks of the record has
passed. -/
theorem enterAndAsk_asks {σ : Type} (laid : σ → Except String Key.RangesLaid) (p : P12) (s : σ)
    (t : T12) (h : Key.enterAndAsk laid p s = .ok t) :
    Key.rangesRecord laid s = .ok t ∧ ∃ u, Key.asksOnRecord p t = .ok u := by
  unfold Key.enterAndAsk at h
  cases h1 : Key.rangesRecord laid s with
  | error e => rw [h1] at h; cases h
  | ok t' =>
    rw [h1] at h
    cases h2 : Key.asksOnRecord p t' with
    | error e =>
      simp only [Except.bind, h2, Except.map] at h
      cases h
    | ok u =>
      simp only [Except.bind, h2, Except.map] at h
      cases h
      exact ⟨rfl, u, h2⟩

/-! ### the two later chains -/

def keyGu (P : Key.LaterPlaces) : Block _root_.Desc.K14.St Key.Claim :=
  ((onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk')).retype (Cl' := Key.Claim)).asBare

def keyOmega (nO : H2U.PlaceNums) : Block _root_.Desc.K14.St Key.Claim := omegaEntry Key.Claim nO

theorem keyGu_sits (P : Key.LaterPlaces) :
    Sits (keyGu P) (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk')
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave :=
  (sits_inside _ _ _).retype.asBare

/-- What stands in front of the test on G_u in the key file's shared chain. -/
def keySharedPre (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    List (Block _root_.Desc.K14.St Key.Claim) :=
  ((Key.sharedChain c P).retype (Cl' := Key.Claim)).first.asBare ::
    (_root_.Desc.K14.blocksOr (Key.sharedPar c (Key.beforeSharedPoint P))).map
      fun b => (b.retype (Cl' := Key.Claim)).asBare

def keySharedEnd (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    Block _root_.Desc.K14.St Key.Claim :=
  ((Key.sharedChain c P).last.retype (Cl' := Key.Claim)).asBare

/-- The key file's shared chain's flat list. -/
theorem keyShared_cut (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    ((Key.sharedChain c P).retype (Cl' := Key.Claim)).blocksInOrder =
      keySharedPre c P ++ keyGu P :: ((P.O.toList.map keyOmega) ++ [keySharedEnd c P]) := by
  rw [Chain.flat_eq]
  simp [Chain.retype, Key.sharedChain, Key.sharedTests, keyGu, keyOmega, omegaEntry, pGomega,
    keySharedPre, keySharedEnd, List.map_append, List.map_map, Function.comp_def]

theorem keyShared_cut_omega (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ((Key.sharedChain c P).retype (Cl' := Key.Claim)).blocksInOrder =
      (keySharedPre c P ++ [keyGu P]) ++ keyOmega nO :: [keySharedEnd c P] := by
  rw [keyShared_cut, hO]
  simp

/-- The own test's numbers in the key file. -/
def pOwnK (P : Key.LaterPlaces) : P12 := H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W

/-- The key file's last chain's flat list. -/
theorem keySecond_cut (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    ((Key.thirdChain c P).retype (Cl' := Key.Claim)).blocksInOrder =
      secondPre Key.Claim (Key.thirdPar c) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ++
        ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ::
          [secondEnd Key.Claim (Key.thirdPar c) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')] :=
  second_cut Key.Claim _ _

end H2K.JointK

#print axioms H2K.JointK.alike_k12
#print axioms H2K.JointK.Sits.onto
#print axioms H2K.JointK.rngEntry_sits
#print axioms H2K.JointK.keyFirst_cut
#print axioms H2K.JointK.enterAndAsk_asks
#print axioms H2K.JointK.keyGu_sits
#print axioms H2K.JointK.keyShared_cut
#print axioms H2K.JointK.keyShared_cut_omega
#print axioms H2K.JointK.keySecond_cut
