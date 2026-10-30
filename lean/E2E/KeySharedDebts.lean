-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySharedDebts.lean: what the accept law owes at the key's shared thread, at every member, from the two proximity
tests' debts at members 9 and 10.

Why. `MembersS` asks `OwesS` and `YesS` at every member of each chain. At the shared chain ten members of twelve are had:
0, 1 to 8 and 11; 9 and 10 are the two proximity tests.

Main names.
  `sharedOwes`: `OwesS` at the thread.
  `sharedYes`: `YesS` at the thread.
  `shared_at_start`: the thread and the letter at the frame's start, as the accept law asks at a run.
  `keepsAtEnds`: a value of the letter `Kp`, with its three laws.
  `walked_unique_shared`: one state at a border of the walk, at one input and list of challenges.
  `sits_chosen`: `Sits` at the first thread `laid₁`, the shared thread here and a last thread with its own facts.

What stays open. As premises: `owes₉`, `owes₁₀`, `yes₉`, `yes₁₀`: members 9 and 10. `hC`: `CellsAlone` at the meaning.
`hFits`: the key fits the index. `hn`: no half at the chain's end. The letters `Kp` with `hKp`, `hE`, `hEnd`.

No law over coins. Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandWalked
import E2E.KeyElevenFive
import E2E.KeyMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeySharedDebts
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyStandWalked (threadAt eight_at_letters front_at_letters)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyAsksKey (tableKey)
open Bind.ForProver (shapeOf oodSh Seed)

variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (fall : Nat → (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₂ → List Fmt.Drawn → Option String)

/-- The thread has twelve members. -/
theorem thread_length {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).bs.length = 12 := by
  rw [(AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
    (inK w₀ rc x)).bs]
  exact (AtPublicFiles.KeyThread.lengths scope hs.named).2.1

/-- **The four debts at every member**, from members 9 and 10. -/
theorem sharedOwes {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (hFits : keyFits x.key QK.par.S.fold.index = true)
    (hn : ((keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.find? fun h =>
      h.place == (keyFileDescription Xs Nr Pl).shared.last.place) = none)
    (owes₉ : PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 9 ∧
      BehindS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 9 ∧
      ExchangeS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 9 ∧
      RidesPastS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 9)
    (owes₁₀ : PlaysS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 10 ∧
      BehindS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 10 ∧
      ExchangeS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 10 ∧
      RidesPastS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said 10) :
    OwesS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said := by
  intro b hb
  rw [thread_length Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope] at hb
  by_cases h0 : b = 0
  · subst h0
    obtain ⟨p, q, e, r, -⟩ := front_at_letters Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x
      hs scope hKp hE hC Said (fun _ _ _ => none)
    exact ⟨p, q, e, r⟩
  by_cases h8 : b ≤ 8
  · obtain ⟨p, q, e, r, -⟩ := eight_at_letters Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x
      hs scope hK₀ sd hx hN pU pO Said (fun _ _ _ => none) b (by omega) h8
    exact ⟨p, q, e, r⟩
  by_cases h9 : b = 9
  · subst h9
    exact owes₉
  by_cases h10 : b = 10
  · subst h10
    exact owes₁₀
  have h11 : b = 11 := by omega
  subst h11
  obtain ⟨p, q, e, r, -⟩ := AtPublicFiles.KeyElevenFive.eleven_five Xs Nr Pl
    (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd w₀ rc x hs scope
    hFits hn hKp hEnd Said (fun _ _ _ => none)
  exact ⟨p, q, e, r⟩

/-- **The acceptance at every member**, from members 9 and 10. -/
theorem sharedYes {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK₀ : fullPub = some K₀)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (hFits : keyFits x.key QK.par.S.fold.index = true)
    (hn : ((keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.find? fun h =>
      h.place == (keyFileDescription Xs Nr Pl).shared.last.place) = none)
    (yes₉ : AcceptedS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said fall 9)
    (yes₁₀ : AcceptedS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said fall 10) :
    YesS (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) Said fall := by
  intro b hb
  rw [thread_length Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope] at hb
  by_cases h0 : b = 0
  · subst h0
    exact (front_at_letters Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope hKp hE hC
      Said fall).2.2.2.2
  by_cases h8 : b ≤ 8
  · exact (eight_at_letters Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x hs scope hK₀ sd hx
      hN pU pO Said fall b (by omega) h8).2.2.2.2
  by_cases h9 : b = 9
  · subst h9
    exact yes₉
  by_cases h10 : b = 10
  · subst h10
    exact yes₁₀
  have h11 : b = 11 := by omega
  subst h11
  exact (AtPublicFiles.KeyElevenFive.eleven_five Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd w₀ rc x hs scope
    hFits hn hKp hEnd Said fall).2.2.2.2

/-- **The thread and the letter at the frame's start.** -/
theorem shared_at_start {k : Coins (keyBook K₀)}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ X}
    (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl) (keyBook K₀)
      (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)) w₀ rc x k = .ok R)
    (hV : Vd (inK w₀ rc x)) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u) :
    Enters₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl)
        (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g))
        (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) w₀ rc x k R ∧
      AtPublicFiles.KeyStandWalked.walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x 0 k
        { R.start₂ (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)) with opened := some [] } := by
  have hw : R.common = inK w₀ rc x := common_of_ready hR
  refine ⟨AtPublicFiles.KeySharedQuiet.enters_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x) hR
    hw rfl hV ?_, .begun ?_⟩
  · intro ds i hi
    have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 0 := hi
    rw [AtPublicFiles.KeySharedQuiet.open_front] at hi'
    obtain rfl := List.mem_singleton.1 hi'
    exact hPin _ _ _ _
  · show { startShared (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)) R.common with
        opened := some [] } = _
    rw [hw]

/-- **The three threads sit**: the first at the prover's own halves, any table, the shared at these letters, the last at
its own tests. -/
theorem sits_chosen {Z : VerifierAndGoals.PublicFiles} {Cells M Smp Rec : Type} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (L : AtPublicFiles.KeyThread.KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec)
    (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
    (U₃ : Thread (keyBook K₀) (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).S₃
      (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X Xi)
    (h₃ : U₃.φ = .own ∧ U₃.chain = 2 ∧ U₃.ft = (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber ∧
      U₃.bs = (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).second.blocksInOrder ∧
      U₃.hs = (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).second)
    (hf₃ : U₃.fits (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).second.blocksInOrder.length = true) :
    Sits (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl) (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g))
      (AtPublicFiles.KeyThread.laid₁ Xs Nr Pl L w₀ rc x
        (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).first tb₁)
      (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) U₃ :=
  AtPublicFiles.KeyThread.sits_laid scope hs.named L w₀ rc x _ tb₁ _
    (AtPublicFiles.KeySharedThread.sits_two Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
      (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x))
    (by
      rw [(AtPublicFiles.KeyThread.lengths scope hs.named).2.1]
      exact AtPublicFiles.KeySharedQuiet.fits_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd (inK w₀ rc x)
        hs.named.plan)
    U₃ h₃ hf₃

/-- **A value of the letter `Kp`**: at the chain's front and end the state stays; elsewhere nothing is said. -/
def keepsAtEnds : Nat → St → St → Prop := fun b s s' => (b = 0 ∨ b = 11) → s' = s

theorem keepsAtEnds_self : ∀ b ∈ [0, 11], ∀ s, keepsAtEnds b s s := fun _ _ _ _ => rfl

theorem keepsAtEnds_front : ∀ s s', keepsAtEnds 0 s s' → s' = s := fun _ _ h => h (Or.inl rfl)

theorem keepsAtEnds_end : ∀ s s', keepsAtEnds 11 s s' → s' = s := fun _ _ h => h (Or.inr rfl)

/-- **One state at a border**: two states of the walk at one input and one list of challenges are one, where every source
that a round opens is at hand with its depth. What the members 9 and 10 spend of a stand. -/
theorem walked_unique_shared (hTaken : ∀ j, Fmt.TreeSource.own j ∉
      (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).taken)
    (hO : ∀ b, b < 12 →
      (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x).opensAvailable (b + 1) = true)
    (hD : ∀ b, b < 12 → ∀ k m,
      DepthsAt (threadAt Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x) (b + 1) k m)
    {b : Nat} {k : Coins (keyBook K₀)} {m m' : Mid (Common W₀ Rc TableKey) X₀} (hb : b ≤ 12)
    (h : AtPublicFiles.KeyStandWalked.walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x b k m)
    (h' : AtPublicFiles.KeyStandWalked.walkedLetter Xs Nr Pl K₀ K' ℓ Nm Mg₀ tk tt rest Kp Vd f g Z₀ w₀ rc x b k m')
    (hi : m.st.input = m'.st.input) (hh : m.st.heard = m'.st.heard) : m = m' :=
  walked_unique (fun _ _ _ e e' _ _ => e.trans e'.symm) (oneColumns_of hTaken hO hD) hb h h' hi hh

end AtPublicFiles.KeySharedDebts

#print axioms AtPublicFiles.KeySharedDebts.thread_length
#print axioms AtPublicFiles.KeySharedDebts.sharedOwes
#print axioms AtPublicFiles.KeySharedDebts.sharedYes
#print axioms AtPublicFiles.KeySharedDebts.shared_at_start
#print axioms AtPublicFiles.KeySharedDebts.keepsAtEnds_self
#print axioms AtPublicFiles.KeySharedDebts.sits_chosen
#print axioms AtPublicFiles.KeySharedDebts.walked_unique_shared
