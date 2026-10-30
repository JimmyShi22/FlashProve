-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/StandAtNine.lean: A STAND OF Thr AT
9 at the filled thread at the real halves (TableFilled.lean's TR), and Moved and the trees there.


  thr_carry      Thr at 9 carries to another table that agrees at the own numbers in front, to any Mg₀ from
                 idlePin Mg₀, to any Kp, to any two halves at the tests, and to any Vd of the input
  pinT_shut      the item on the stored table is not open at 9
  quiet_plain    a test's plain half is quiet
  K1, K2         the parts, and the parts with the two halves
  TS, StandFacts the thread of the stand, and what the stand says beside Thr
  stand_at_TR    the thread at the filled table stands at 9, at every list that fits, at every Mg₀, Kp, Vd
                 of the input; with the heard and the rows' counts; NO TIE of the state to the parts' play
  moved_at_TR    at a stand, at every list that fits at 9: the real half returns, and the four new trees are
                 testTbl's: Plays' two conclusions
  enters_at_TR   at a stand the seat's way in IS the job's state on entry: no fall-back: enters_nine, called
  moved_idle     the same at idle letters, every premise paid, KeySourced kept: at the written key

WHAT IS IDLE. Thr at 9 reads no field of Mg₀ that a filling lays: mgWords writes over pin, nearU, recRow, omU,
row, and pinT is shut at member 1. So the stand is carried here to every Mg₀. WHAT STAYS OWED: the road to it:
Thr at 0 and 1, Enters₂, Exchange at LIN point were walked with pinT told true (stand_nine's hPin): a filling's
thread must still enter with its own pinT, at borders 0 and 1. That debt is not K12's. The stand is
stand_nine in other letters, carried: no new fact on a run. It bears on the placed table by the trees in
moved_at_TR alone: without them its statement holds word for word at tbKey, where Plays at 9 is false.

MOVED IS A FACT ON SHAPES: every message fits its declared shape and every column read is at hand. rec₀ is total
with a silent fall-back, so Moved would return off a fall-back state. That the half plays off the verifier's
state s, or that what it shows is right, is not in it.

A YES WOULD NOT SHOW: a stand at 10 · Accepted · hop for any letter · the columns · that a filling's thread
reaches 9 · a run of the frame: first chain idle, field none · anything at the maker's own ProofFile.Pub · anything
over coins, and nothing on hiding.

NOT IN FRONT OF A LAW OVER COINS: stand_at_TR and moved_at_TR bear this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: stand_nine's.

WHAT IT FIRES: plays_real and enters_nine are called here, at the stand. With StandFacts' rows and enters_at_TR:
real rows, and no fall-back at the stand. Other laws from Thr at 9 are not called here.

WHAT A PASS WOULD MAKE IDLE: with the letter laid in tableKey, thr_carry's table; with the halves laid in keyOf, K2.

Limits. moved_idle takes one written list at each of the seven members; stand_at_TR and moved_at_TR take every
list that fits. Nothing on completeness, soundness or hiding.
-/
import E2E.TableFilled
import E2E.PlaysAtLetters
import E2E.KeyNoStop

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.StandAtNine
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey randKey plan_key)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf fitOf)
open AtPublicFiles.KeyStandNineAt (stand_nine lists_nine)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyDoorNine (seat_nine)
open AtPublicFiles.KeyPlaysAt (place_on fit_gu memsOf members_closed fresh_closed stages_two)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyDepthsAt (lays_U_at)
open AtPublicFiles.KeyTblTrial (sendings_count)
open AtPublicFiles.KeyTreesKey (tbKey treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key)
open AtPublicFiles.KeyLay (onUOf onOmegaOf withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO place_omega onU_is_job onOmega_is_job find_U place_gu JO)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.TableFilled (TR plays_real)
open AtPublicFiles.PlaysAtNine (quiet_job)
open AtPublicFiles.Stops (QuietHalf)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleTk idleRest idleNm_tenant)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open Bind.ForProver (shapeOf oodSh Seed)
open H2K.Member (piKUFull)

/-- A test's plain half is quiet. -/
theorem quiet_plain {V W X : Type} (J : TestJob W X) : QuietHalf (proverSideOfProximityTest J : Placed V W X) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact first_quiet J
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact rest_quiet J
    · cases hp

/-- The item on the stored table is shut behind member 1: it is not open at 9. -/
theorem pinT_shut : VerifiableInference.Desc.Shared.ItemS.pinT ∉
    fwdOpen SharedRows.start (SharedRows.rows true) 9 := by
  decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb tb' : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp Kp' : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (a b : Placed Empty (Common W₀ Rc TableKey) X₀)

/-- Mg₀ with the item on the stored table told true. -/
abbrev idlePin (v : Common W₀ Rc TableKey) : MeaningS St P₁ Wt :=
  { Mg₀ v with pinT := fun _ _ _ => True }

/-- **Thr at 9 carries**: to another table that agrees at the own numbers in front, to any Mg₀ of which
idlePin Mg₀ was the thread's, to any Kp, to any two halves at the tests, and to any Vd that holds of the
input. So Thr at 9 reads a table at what is at hand, no field of Mg₀ (the one that its rewriting leaves, pinT,
is shut), no Kp and no half. -/
theorem thr_carry
    (hag : ∀ n, n < treesTo (threadKey Xs Nr PF K ℓ Nm (idlePin Mg₀) tb rest Kp (fun _ => True) w).bs 9 →
      tb (.own n) = tb' (.own n)) (hVd : Vd w)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (h : Thr (threadKey Xs Nr PF K ℓ Nm (idlePin Mg₀) tb rest Kp (fun _ => True) w) 9 k s m E) :
    Thr (threadKey Xs Nr PF { K with onU := a, onOmega := b } ℓ Nm Mg₀ tb' rest Kp' Vd w) 9 k s m E := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨⟨h1, ?_⟩, h3, h4, ?_, h6, h7, ?_⟩
  · intro σ hσ
    have hσ' : σ ∈ [] ++ (List.range (treesTo
        (threadKey Xs Nr PF K ℓ Nm (idlePin Mg₀) tb rest Kp (fun _ => True) w).bs 9)).map
        Fmt.TreeSource.own := hσ
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 (List.mem_append.1 hσ' |>.resolve_left (by simp))
    have hn' := List.mem_range.1 hn
    have e := h2 (.own n) hσ
    unfold Thread.handAt Thread.tableAt at e ⊢
    show (E.tree (.own n)).any (fun u =>
      u.1 == (tb' (.own n) k m.st.input (m.st.heard.take
        ((threadKey Xs Nr PF K ℓ Nm (idlePin Mg₀) tb rest Kp (fun _ => True) w).fixed (.own n)))).1 &&
      u.2.same (tb' (.own n) k m.st.input (m.st.heard.take
        ((threadKey Xs Nr PF K ℓ Nm (idlePin Mg₀) tb rest Kp (fun _ => True) w).fixed (.own n)))).2) = true
    rw [← hag n hn']
    exact e
  · intro ds i hi
    have e := h5 ds i hi
    have hne : i ≠ VerifiableInference.Desc.Shared.ItemS.pinT := by
      rintro rfl
      exact pinT_shut hi
    cases i <;> first | exact absurd rfl hne | exact e
  · obtain ⟨e1, -⟩ := h8
    exact ⟨e1, e1 ▸ hVd⟩

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- The parts with the table, index, coins and the shared chain's own data laid. -/
abbrev K1 : KeyParts W₀ Rc X₀ X Wk := keyOf (pubKey Z₀ Xs.chains) Xs PF K' f g

/-- The letters under them, with the two halves in. -/
abbrev K2 : KeyParts W₀ Rc X₀ X Wk :=
  { K' with onU := onUOf (K1 Xs K' f g Z₀) pU, onOmega := onOmegaOf (K1 Xs K' f g Z₀) pU pO }

/-- The thread of the stand. -/
abbrev TS := TR K₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀

/-- What a stand says beside Thr: what has been heard, and the rows of its state. -/
def StandFacts (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn) (s : St)
    (m : Mid (Common W₀ Rc TableKey) X₀) : Prop :=
  m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ∧
    AtPublicFiles.KeyStandNine.HasRow (num .oU) s ∧
    AtPublicFiles.KeyStandNine.HasRow (num .oOmega) s ∧
    AtPublicFiles.KeyStandNine.HasRow (num .oSp) s ∧
    (_root_.Desc.K14.Law.rowsOn s s.loc.gU).length = (parKey Xs PF).par.S.fold.index.answers +
      (parKey Xs PF).par.S.fold.columns + 1 ∧
    (_root_.Desc.K14.Law.rowsOn s s.loc.gOmega).length = 1 ∧
    0 < (parKey Xs PF).par.S.fold.index.answers ∧ 0 < (parKey Xs PF).par.S.fold.columns

/-- **The filled thread stands at 9, at every list of challenges that fits at the six members, at every Mg₀,
Kp and Vd that holds of the input.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stand_at_TR {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hVd : Vd (inK w₀ rc x))
    (qr : QuietHalf K'.rng) (qw : QuietHalf K'.own)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[1]? = some blk →
      drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[2]? = some blk →
      drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[4]? = some blk →
      drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[5]? = some blk →
      drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[7]? = some blk →
      drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[8]? = some blk →
      drawsFit blk.rounds ds₈ = true) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      Thr (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) 9 k s m E ∧
      StandFacts Xs K₀ k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ s m := by
  have e : parKey Xs PF = QK := par_sourced hs scope
  have hsend : (K1 Xs K' f g Z₀).send = ⟨parKey Xs PF, 0⟩ := rfl
  have qU : QuietHalf (K2 Xs K' f g Z₀).onU := by
    show QuietHalf (onUOf (K1 Xs K' f g Z₀) pU)
    rw [onU_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_plain _
  have qO : QuietHalf (K2 Xs K' f g Z₀).onOmega := by
    show QuietHalf (onOmegaOf (K1 Xs K' f g Z₀) pU pO)
    rw [onOmega_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_job _
  have pa : (K2 Xs K' f g Z₀).onU.place = foldedTestPlace := place_on
  have pb : (K2 Xs K' f g Z₀).onOmega.place = omegaTestPlace := place_omega
  obtain ⟨s, m, E, u, h9, -, r1, r2, r3, r4, r5, r6, r7⟩ := stand_nine Xs Nr PF K₀ (K2 Xs K' f g Z₀) ℓ Nm
    (idlePin Mg₀) tk (AtPublicFiles.TableFilled.ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀) rest (fun _ s s' => s' = s)
    (fun _ => True) (fun _ _ _ => True) none f g Z₀ w₀ rc x hs scope hK₀ sd hx hN
    (fun _ _ _ _ => trivial) (fun _ _ _ => rfl) (fun _ _ h => h) trivial qr qU qO qw pa pb
    k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ hd₁ hd₂ hd₄ hd₅ hd₇ hd₈ trivial
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  have hT := thr_carry Xs Nr (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g) ℓ Nm Mg₀
    (tableKey Xs PF K₀ (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g) tk
      (AtPublicFiles.TableFilled.ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀))
    (tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights (randKey (K1 Xs K' f g Z₀)) tk
      (AtPublicFiles.TableFilled.ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest (fun _ s s' => s' = s) Kp Vd (inK w₀ rc x)
    (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g).onU
    (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g).onOmega (fun _ _ => rfl) hVd u.1
  exact ⟨s, m, E, hT, h9, r1, r2, r3, r4, r5, r6, r7⟩

/-- **At a stand the play of the real half returns, and the four new trees are testTbl's**, at every list
that fits at member 9: Plays' two conclusions, kept.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem moved_at_TR {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (qr : QuietHalf K'.rng) (qw : QuietHalf K'.own)
    (k : Coins (keyBook K₀)) (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env)
    (u : Thr (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) 9 k s m E)
    (ds : List Fmt.Drawn) (hd : drawsFit (H2K.JointK.keyGu PF).rounds ds = true) :
    ∃ (y : List Played × Mid (Common W₀ Rc TableKey) X₀) (cols : List VerifiableInference.Desc.OpenedColumn),
      (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).Moved (H2K.JointK.keyGu PF) k m E ds
        y cols ∧
      (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).Trees
        ((TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).fresh 9) k y.2 (E.add y.1) := by
  have e : parKey Xs PF = QK := par_sourced hs scope
  have hsend : (K1 Xs K' f g Z₀).send = ⟨parKey Xs PF, 0⟩ := rfl
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  have hsp : (K1 Xs K' f g Z₀).lin.S.sharedSplitNeeded = true := hQ.facts.two
  have hplays := plays_real K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀ e
    hsend hsp
  have hblk := (seat_nine Xs Nr PF (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights (randKey (K1 Xs K' f g Z₀)) tk
      (AtPublicFiles.TableFilled.ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest Kp Vd (inK w₀ rc x) B).1
  have hseat := (seat_nine Xs Nr PF (K1 Xs K' f g Z₀) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) (K1 Xs K' f g Z₀).weights (randKey (K1 Xs K' f g Z₀)) tk
      (AtPublicFiles.TableFilled.ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀)) rest Kp Vd (inK w₀ rc x) B).2
  have hp : (JN Xs (K1 Xs K' f g Z₀) B).p = piKUFull := place_full
  have hmU : (JN Xs (K1 Xs K' f g Z₀) B).members = AtPublicFiles.KeyTest.jobFolded.members := by
    show memsOf (parKey Xs PF) = _
    rw [e]
    exact members_closed
  have hlays := lays_U_at K₀ hK₀ (JN Xs (K1 Xs K' f g Z₀) B) hp hmU fresh_closed.symm
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, (JN Xs (K1 Xs K' f g Z₀) B).p.nums.stages = a :: b :: r := by
    have h2 : 2 ≤ (JN Xs (K1 Xs K' f g Z₀) B).p.nums.stages.length := by
      rw [hp]
      exact stages_two
    cases hh : (JN Xs (K1 Xs K' f g Z₀) B).p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a t =>
      cases t with
      | nil =>
        rw [hh] at h2
        simp only [List.length_cons, List.length_nil] at h2
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hfind := find_U Xs (K1 Xs K' f g Z₀) B hsend hsp
  have hfind' : ((keyProver (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO)).shared.find? fun q =>
      q.place == (JN Xs (K1 Xs K' f g Z₀) B).p.place) = some (proverSideOfProximityTest (JN Xs (K1 Xs K' f g Z₀) B)) := by
    rw [← hseat.place]
    exact hfind
  obtain ⟨c, -, hsteps⟩ := lays_of_B (keyBook K₀) 1 (Or.inr rfl) (JN Xs (K1 Xs K' f g Z₀) B) st0 st1 st2
    hst hlays (H2K.JointK.keyGu PF) (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave hseat _ hfind' k
    ((TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).φ.sees m.st.input)
  have qU : QuietHalf (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO).onU := by
    show QuietHalf (onUOf (K1 Xs K' f g Z₀) pU)
    rw [AtPublicFiles.HalvesAreJobs.onU_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_plain _
  have qO : QuietHalf (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO).onOmega := by
    show QuietHalf (onOmegaOf (K1 Xs K' f g Z₀) pU pO)
    rw [onOmega_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_job _
  have hno := (AtPublicFiles.KeyFile.noStopAll_keyProver (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO) qr qU qO qw).2.1
  exact hplays _ hblk k s m E ds _ u hd (AtPublicFiles.Stops.chainStopAt_none _ hno [_] _ _) hsteps

/-- **At a stand the job's state on entry is the seat's way in: no fall-back.** enters_nine, called. -/
theorem enters_at_TR {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (k : Coins (keyBook K₀)) (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env)
    (u : Thr (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) 9 k s m E) :
    VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) s =
      .ok ((JN Xs (K1 Xs K' f g Z₀) B).rec₀ m.st.input (ProofFile.Honest.K12.frontOf m)) := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  exact AtPublicFiles.KeyDoorNine.enters_nine Xs Nr PF (withTestsOnUAndOmega (K1 Xs K' f g Z₀) pU pO) ℓ Nm Mg₀ _ rest Kp Vd _
    hQ B u

end

/-- **Every premise paid, at idle letters**: at the written key, at every index, committer's coins and seed,
at these letters the thread stands at 9, the real half plays there, and the four new trees are testTbl's.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem moved_idle (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub), KeySourced VerifierAndGoals.storedPublicFiles Xs Nr PF ∧
      fullPub = some K₀ ∧ ∃ B : Eight (parKey Xs PF),
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ) (k : Coins (keyBook K₀)),
        ∃ (s : St) (m : Mid (Common Weights (ℕ → TableRand) TableKey) Unit)
          (E : Env) (ds : List Fmt.Drawn)
          (y : List Played × Mid (Common Weights (ℕ → TableRand) TableKey) Unit)
          (cols : List VerifiableInference.Desc.OpenedColumn),
          Thr (TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
              (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ s s' => s' = s)
            (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()) 9 k s m E ∧
          (TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
              (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ s s' => s' = s)
            (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()).Moved
            (H2K.JointK.keyGu PF) k m E ds y cols ∧
          (TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
              (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ s s' => s' = s)
            (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()).Trees
            ((TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
              (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest (fun _ s s' => s' = s)
            (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()).fresh 9)
            k y.2 (E.add y.1) := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := full_made
  have hPl : Pl = PF := later_sourced hs VerifierAndGoals.inScope_full
  subst hPl
  obtain ⟨layO, hQ⟩ := plan_key hs VerifierAndGoals.inScope_full
  obtain ⟨B⟩ := hQ.eight
  refine ⟨Xs, Nr, K₀, hs, hK₀, B, fun fc w₀ rc sd k => ?_⟩
  obtain ⟨qr, -, -, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
    (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
  have pa : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
      (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onU.place = foldedTestPlace := place_on
  have pb : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
      (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onOmega.place = omegaTestPlace :=
    place_omega
  obtain ⟨ds₁, ds₂, ds₄, ds₅, ds₇, ds₈, h₁, h₂, h₄, h₅, h₇, h₈⟩ := lists_nine Xs Nr PF K₀
    (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc
      idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀) WitLens.words idleNm (fun _ => idleMg) idleTk _ idleRest
    (fun _ s s' => s' = s) (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl pa pb
  obtain ⟨s, m, E, u, -⟩ := stand_at_TR Xs Nr K₀
    (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm (fun _ => idleMg) idleTk idleRest
    (fun _ s s' => s' = s) (fun _ => True) id id Z₀ w₀ rc _ B () hs VerifierAndGoals.inScope_full hK₀ sd rfl
    idleNm_tenant trivial qr qw k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ h₁ h₂ h₄ h₅ h₇ h₈
  obtain ⟨y, cols, h1, h2⟩ := moved_at_TR Xs Nr K₀
    (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm (fun _ => idleMg) idleTk idleRest
    (fun _ s s' => s' = s) (fun _ => True) id id Z₀ w₀ rc _ B () hs VerifierAndGoals.inScope_full hK₀ qr qw k s m E
    u _ fit_gu
  exact ⟨s, m, E, _, y, cols, u, h1, h2⟩

end AtPublicFiles.StandAtNine

end

#print axioms AtPublicFiles.StandAtNine.quiet_plain
#print axioms AtPublicFiles.StandAtNine.pinT_shut
#print axioms AtPublicFiles.StandAtNine.idlePin
#print axioms AtPublicFiles.StandAtNine.thr_carry
#print axioms AtPublicFiles.StandAtNine.K1
#print axioms AtPublicFiles.StandAtNine.K2
#print axioms AtPublicFiles.StandAtNine.TS
#print axioms AtPublicFiles.StandAtNine.StandFacts
#print axioms AtPublicFiles.StandAtNine.stand_at_TR
#print axioms AtPublicFiles.StandAtNine.moved_at_TR
#print axioms AtPublicFiles.StandAtNine.enters_at_TR
#print axioms AtPublicFiles.StandAtNine.moved_idle
