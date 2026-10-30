-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
RE-BASED over Block.lean's ninth and State.lean's tenth issue, and over the seats that go with
them (Stored/HeadSeatAt.lean, Stored/ReplySeatAt.lean). WHAT TURNED: joinAtTruth_of_front: K6On
has six clauses now (Law/RowPins.lean's head): its sixth is its last: one projection turns. The
statements are as they were.
Johnson/Desc/Kinds/Law/JoinFromFront.lean: **THE ONE HOLE OF Law/K06HonestStep.lean (JoinAtTruth) IS MOVED OUT OF K6's BLOCK: IT FOLLOWS FROM ONE SENTENCE AT THE BORDER IN FRONT, IN THE LOOKUP's OWN LETTERS: KeysTrueInFront.** No round of K6 stands in that sentence.
  KeysTrueInFront W s c mask   for what the lookup has heard at s (gk): mean1's KeysWorth at s (Law/RowJoin.lean): the formula of «join» (the sum over the calls of e_c (alpha - c theta - key_c), the public term for the empty trees, less the lookup's last claim cEnd), FED WITH THE EXTENSIONS OF THE SIX CALLS' KEY TABLES OF
                   THE CELLS c AT THE LOOKUP's KEY POINTS, is worth 0 in the world of the ledger in front: THAT IS: WHAT LIES HIDDEN UNDER THE LOOKUP's LAST CLAIM IS WHAT THE CELLS' KEYS MAKE IT.
  keys_back        mean1's keys_front the other way: the sentence rides to a LATER record (same letters, same points, a later ledger, cEnd's numbers filled in front: K6On's sixth clause).
  join_of_keys     mean1's keys_worth the other way: where the block's conclusion Closed holds, the sentence gives JoinOpened (both are one equation between two values of the formula).
  joinAtTruth_of_front   K6On · K6MoreB · KeysTrueInFront ⇒ JoinAtTruth. HERE K6On's SIXTH CLAUSE IS SPENT.
  K06HonestStepFrontStatement | k06HonestStepFront   Law/K06HonestStep.lean's top with KeysTrueInFront in JoinAtTruth's place.
EVERY LETTER UNDER "THERE IS" AND "FOR ALL" IN THE TOP: as in Law/K06HonestStep.lean's head: s': the step's own return, with the count 0 · H: heard s' = some H · rs: NO EQUATION (HeardAre; ShapedAs): the sender is a "there is" · cols · firstTree: idle · l: blockOf alone. In KeysTrueInFront: gk: pinned by s.lookHeard? = some gk.
NOTE: WHAT IT IS NOT, FIRST. (1) **KeysTrueInFront IS SHOWN UNDER PREMISES** (Johnson/Desc/Kinds/Law/KeysRoadBack.lean; Johnson/Desc/ProofFile/Honest/K6/Law/KeysAtThread.lean, ScriptFields.lean): THAT AN HONEST LOOKUP's HEARING LEAVES IT is not shown here: THE TOP MAY BE EMPTY AT EVERY LOOKUP THAT HAS HEARD ANYTHING.
(2) NOTE: IT IS THE THIRD CLAUSE OF rowStep's OWN CONCLUSION K6In: so in this top that clause is handed through; K6In's first two clauses (FrontIdn, FrontRider) are what the law gives. That is as it must be at a truth: a member of a soundness law stands where its conclusion is true. (3) not a member of k6Own. (4) all
fourteen fences of Law/K06Honest.lean | K06HonestWhole.lean. Nothing on soundness.
IMPORTED, NOT MINE: mean1's KeysWorth | JoinOpened | joinForm_congr | joinForm_worlds | vW_later | decide_frames | trueKeys_getD | rd_trueKey | calls_keys; the two turned proofs follow mean1's own, line for line.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06HonestStep
import Johnson.Desc.Kinds.Law.RowFront
import Johnson.Desc.Kinds.Law.RowAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World Reading)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

/-- mean1's keys_front, the other way: the keys' sentence rides from a record to a LATER one. -/
theorem keys_back (p : Par) (L : Seat S) (s s' : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (hG : given p L s' = given p L s)
    (hZ : L.lookup s' = L.lookup s) (hL : Later (L.ledger s) (L.ledger s'))
    (hf : CEndFilled gk (L.ledger s)) (h : KeysWorth p L s c mask gk) :
    KeysWorth p L s' c mask gk := by
  obtain ⟨g, z, hg, hz, hv⟩ := h
  refine ⟨g, z, hG.trans hg, hZ.trans hz, ?_⟩
  rw [← hv]
  refine Came.joinForm_worlds Reading.gl _ _ gk _ (fun call hc => ?_)
    (Came.vW_later mask noEnt gk.cEnd hL hf)
  have hc6 : call < 6 := by simpa [trueKeys] using hc
  rw [Came.trueKeys_getD g z.2 c call hc6, Aff.value_ofConst, Aff.value_ofConst]

/-- mean1's keys_worth, the other way: where the block's conclusion holds, the keys' sentence gives "join" worth 0. -/
theorem join_of_keys (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (hC : Closed p L s c mask)
    (hK : KeysWorth p L s c mask gk) : JoinOpened p L s c mask gk := by
  obtain ⟨g, H, z, hg, hH, hz, hcl⟩ := hC
  obtain ⟨g', z', hg', hz', hj⟩ := hK
  rw [hg] at hg'
  obtain rfl : g = g' := Except.ok.inj hg'
  rw [hz] at hz'
  obtain rfl : z = z' := Option.some.inj hz'
  refine ⟨g, H, hg, hH, ?_⟩
  rw [← hj]
  have hlen : g.calls.length = 6 := by
    obtain ⟨_, _, _, _, _, rfl⟩ := Came.given_ok p L s g hg
    rfl
  have hk : ∀ call, call < 6 → (g.calls.getD call (0, [])).2 = callKeys call := by
    obtain ⟨z', y, _, _, _, rfl⟩ := Came.given_ok p L s g hg
    intro call hc
    exact @Came.calls_keys p.sizes p.floor z'.1 z'.2 call hc
  have hkeys := hcl.2.1
  refine (Came.joinForm_congr Reading.gl _ gk _ _ ?_ fun call hc => ?_).symm
  · simp [trueKeys, keysAt, hlen]
  · have hc6 : call < 6 := by simpa [trueKeys] using hc
    rw [Came.trueKeys_getD g z.2 c call hc6, Aff.value_ofConst]
    have e2 := hkeys call hc6
    rw [rd_atWorld] at e2
    unfold keysAt
    rw [Came.getD_map_toArray _ _ call (by rw [hlen]; exact hc6) _ (0, [])]
    rw [hk call hc6]
    exact (Came.rd_trueKey c z.2 call).trans e2.symm

/-- **THE HOLE, AT THE BORDER IN FRONT OF K6's BLOCK, IN THE LOOKUP's OWN LETTERS**: mean1's KeysWorth at the record in front: the formula of "join", fed with the extensions of the six calls' key tables OF THE CELLS at the lookup's key points, is worth 0 in the
world of the ledger in front: that is: what lies hidden under the lookup's last claim is what the cells' keys make it. No round of K6 is in it. -/
def KeysTrueInFront (W : OnBytes.Model.Verify.Public) (s : S) (c : NCells) (mask : Nat → E) : Prop :=
  ∀ gk, s.lookHeard? = some gk →
    KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask gk

/-- **JoinAtTruth FROM THE KEYS' SENTENCE IN FRONT.** -/
theorem joinAtTruth_of_front (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s : S) (c : NCells) (mask : Nat → E) (hOn : K6On W s)
    (hMore : K6MoreB s = true) (hK : KeysTrueInFront W s c mask) : JoinAtTruth W b s c mask := by
  intro rs s' gk RK hd hlk
  obtain ⟨s'', gs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := k06Honest W l b hb s c mask rs hOn hMore RK
  have hcl := Came.rowRides W l b hb s c mask s'' rs gs h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  have h1' : (blockAt W.hS iU3 (workOf W) l).decide s rs [] = .ok s'' := h1
  have hs : s'' = s' := Except.ok.inj (h1'.symm.trans hd)
  subst hs
  have hlk0 : s.lookHeard? = some gk :=
    (Came.lookHeard_leaves W.hS iU3 (workOf W) l s rs [] s'' hd).symm.trans hlk
  have hkd : (kind (fun _ => ()) (seatAt W.hS (readsOf W)) l 4 (parOf W.hS (workOf W))).decide s rs []
      = .ok s'' := by
    rw [hr]
    exact hd
  obtain ⟨fG, fZ, fL⟩ := Came.decide_frames (fun _ => ()) (seatAt W.hS (readsOf W)) l 4
    (parOf W.hS (workOf W)) hkd
    ((Came.seatBack_iff _ _ _).2 (seatBack_at W.hS (readsOf W) (workOf W) s)) h2 h7
  exact join_of_keys _ _ s'' c mask gk hcl.2
    (keys_back _ _ s s'' c mask gk fG fZ fL (hOn.2.2.2.2.2 gk hlk0) (hK gk hlk0))

/-- **rowStep's FIVE PREMISES ARE MET TOGETHER, UNDER THE KEYS' SENTENCE IN FRONT.** -/
def K06HonestStepFrontStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (firstTree : Nat) (s : S) (c : NCells) (mask : Nat → E), K6On W s → K6MoreB s = true →
    K6RoomB W s = true →
    (∀ g : Given, given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g →
      (dataOf c).Holds ∧ HonestHead c.toCells) →
    KeysTrueInFront W s c mask →
    ∀ (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E),
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     DrawsOk pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) →
    ∀ (cols : List OpenedColumn), ∃ (rs : List Fmt.RoundView) (s' : S) (H : HeardAll),
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     HeardAre pts gam om rsS rsP rsN rsL H) ∧
    ShapedAs (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs
      (@rounds (parOf W.hS (workOf W)).sizes) ∧
    K6On W s ∧ Sound.NoBad (ruleStep W s (c, mask)) rs ∧ Canonical rs ∧
    b.step firstTree s rs cols = .ok (s', 0) ∧ K6Out W s' (c, mask) ∧
    K6In W s (c, mask)

theorem k06HonestStepFront : K06HonestStepFrontStatement :=
  fun W l b hb firstTree s c mask hOn hMore hRoom hc hK =>
    k06HonestStep W l b hb firstTree s c mask hOn hMore hRoom hc
      (joinAtTruth_of_front W l b hb s c mask hOn hMore hK)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keys_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_of_keys
#print axioms VerifiableInference.Desc.Kinds.Head.Law.joinAtTruth_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06HonestStepFront
