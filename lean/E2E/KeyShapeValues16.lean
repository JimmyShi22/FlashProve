-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeValues16.lean: THE KEY FILE's FIRST CHAIN: THE NAMED TEST ON VALUES AT "batt.1.batt" IS
PAID BY THE VERIFIER's OWN ACCEPTS. Where a `Thread` stands at the border in front of that
sub-protocol, in the goals' scope, the test on the claims on the keys accepts, at all values. So of
the named tests on values of E2E/KeyShapeFirstAll.lean's letters ONE is left: the ranges' proximity
test's last clause. Statements and proofs. NOTHING IS SHOWN OF ANY PROVER.

  **`keysSum_of`**: where the lists of claims on keys are the lookups' own text's (`KeysAt`,
    E2E/KeyKeysKeeps.lean), the mark on their form holds and the verifier's tests on public values
    accept: each claim's weights add up as `keysSumB` asks. By `passes_keysOf` (E2E/KeyPasses.lean),
    which calls the library's `Wf.Proved.pendOkKeys`, and `keyClaims_at` (E2E/KeyPileAccepts.lean):
    CALLED.
  `pub_keys_six`: these tests on public values, under E2E/KeyShapeFullTies.lean's six equations. By
    Lean's kernel.
  `run16_six`, `shape16_of_thr`: at the border 16 the state's shape is `T16` (as
    E2E/KeyRangesShape15.lean does at 15).
  `keysOk16`: the mark on the claims' form is set in `T16`. By Lean's kernel.
  `keys_of_thr`: at the border 16: `KeysAt`.
  **`values16`**: so the letters' named test at number 16 accepts there.
  **`values_but15`**: at every border but 15 the named test accepts at the state that stands there.

Limits.
- The ranges' proximity test's named test stays (E2E/KeyShapeValues15.lean: from `valsK12` alone):
  the algebra there is all owed.
- That a `Thread` stands at a border is a premise.
- "The weights add up" is a fact on the verifier's two ways of saying which places are covered;
  nothing on what a claim holds of.


-/
import E2E.KeyKeysKeeps
import E2E.KeyShapeValues15

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open H2K.Member (nKRFull)
open H2K.JointK (keyFirstPre rngEntry keyFirst_cut)
open VerifiableInference.Desc (foldBlocks)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces lookupPlace lookupsOf)

/-- **Claims that the lookups' own text makes pass the test on values.** -/
theorem keysSum_of {one : OneTime} {n : Nat} {s : FirstState} (fBits : Nat)
    (hA : KeysAt one n s)
    (hk : keysB (Wf.matrixOf one.lin) one.ranges.lookups s.base.keys = true)
    (hm : (Wf.matrixOf one.lin).ok = true)
    (hl : ∀ l ∈ one.ranges.lookups, Wf.lookupOk fBits l = true ∧
      Wf.fitsMatrix (Wf.matrixOf one.lin) l = true) :
    keysSumB (Wf.matrixOf one.lin) one.ranges.lookups s.base.keys = true := by
  unfold keysSumB
  unfold keysB at hk
  rw [List.all_eq_true] at hk ⊢
  intro x hx
  have hkx := hk x hx
  rw [Bool.and_eq_true, List.all_eq_true] at hkx
  rw [List.all_eq_true]
  intro y hy
  have hky := hkx.2 y hy
  rw [Bool.and_eq_true, beq_iff_eq] at hky
  rw [zipT_eq] at hx hy
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨j1, j2⟩ := List.getElem?_zip_eq_some.1 hj
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hy
  obtain ⟨i1, i2⟩ := List.getElem?_zip_eq_some.1 hi
  obtain ⟨X, F, home, g, hX, hc⟩ := hA.2 j x.2 j2
  have hX' : X = Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) x.1 := by
    have q : (one.ranges.lookups.map
        (Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin)))[j]? = some X := hX
    rw [List.getElem?_map, j1] at q
    exact (Option.some.inj q).symm
  subst hX'
  obtain ⟨hlen, hat⟩ := AtPublicFiles.Key.keyClaims_at _ F home g x.2 hc
  have hig : i < g.keys.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.1 i2).1
  obtain ⟨w, hw⟩ := hat i g.keys[i] (List.getElem?_eq_getElem hig)
  rw [i2] at hw
  have e : y.2 = _ := Option.some.inj hw
  have hmem : x.1 ∈ one.ranges.lookups := List.mem_of_getElem? j1
  rw [e] at hky
  have hp := passes_keysOf fBits one.ranges.messageId (Wf.matrixOf one.lin) x.1 i y.1 g.theta
    g.alpha ⟨(g.keys[i]).1.toList.reverse, w.1, w.2⟩ (hl x.1 hmem).1 hm (hl x.1 hmem).2 i1 hky.1
  unfold Passes at hp
  rw [Bool.and_eq_true] at hp
  rw [e]
  exact hp.2

/-- The verifier's tests on public values, under the six equations. -/
theorem pub_keys_six {Q : Pub1} (h : Six Q) : (Wf.matrixOf Q.one.lin).ok = true ∧
    ∀ l ∈ Q.one.ranges.lookups, Wf.lookupOk 64 l = true ∧
      Wf.fitsMatrix (Wf.matrixOf Q.one.lin) l = true := by
  rw [h.lin, h.ranges]
  decide +kernel

/-- Under the six equations the guards' run over the first sixteen returns the term `T16`. -/
theorem run16_six {Q : Pub1} (h : Six Q) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    (Z₁W Q CF D told nKRFull v).run 16 T0 = .ok T16 := by
  unfold Z₁W
  rw [gAll₁_six h]
  rw [run_take (sh₁B Q CF) gsF v T0 16 (by decide)]
  have e : gsF.take 16 = gsF.take 15 ++ [gRng QF nKRFull] := rfl
  rw [e, runL_append _ _ _ _ (run15_full h0 h1), runL_cons _ _ _ _ step15]
  rfl

/-- The mark on the form of the claims on the keys is set in the term in front of "batt.1.batt". -/
theorem keysOk16 : T16.2.look.keysOk = true := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Where a `Thread` stands at the border 16 the state's shape is `T16`**, in scope. -/
theorem shape16_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 16 k e m E) :
    sh₁B (pubOf X) CF e = T16 := by
  obtain ⟨hN, -, -, hlen, hsh0, -, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have h16 := shape_at T₁ (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (a₀ := T0)
    (n := 19) (b := 16) (le_of_eq (by rw [hbs, hlen])) (by decide) hyes
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
      exact (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0)
    (fun j => by
      rw [hbs]
      exact carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N T₁.ft _ bw hw he ha j) h
  subst hN
  have q0 := entries_six X nKRFull P hs.named.plan h6 0 (by decide)
  have q1 := entries_six X nKRFull P hs.named.plan h6 1 (by decide)
  exact Except.ok.inj (h16.symm.trans (run16_six h6 _ _ _ q0 q1))

/-- Where a `Thread` stands at the border 16 the claims on the keys are the lookups' own text's. -/
theorem keys_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 16 k e m E) :
    KeysAt X.Y.k.oneTime (lookupsOf X.Y.k.oneTime).length e := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, hb0, -, hf⟩, -, hval⟩ := h
  obtain ⟨x, rfl⟩ := hbeg _ _ _ _ hval hb0
  have hl16 : (keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N ++
      [rngEntry X.Y.k.oneTime N]).length = 16 := by
    rw [List.length_append, pre_len hs scope]
    rfl
  have e16 : (keyFileDescription X N P).first.blocksInOrder.take 16 =
      keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N ++ [rngEntry X.Y.k.oneTime N] :=
    (congrArg (List.take 16) ((keyFirst_cut _ _ _ _ _).trans
      (List.append_cons _ _ _))).trans (List.take_left' hl16)
  rw [hbs, e16] at hf
  exact keys_of_front _ _ _ _ _ T₁.ft hf rfl ⟨rfl, fun _ _ hj => by cases hj⟩

/-- Under the six equations the letters' named test at number 16 is the one on the claims on the
keys. -/
theorem vals16_is {Q : Pub1} (h : Six Q) (cs : Codes) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) : (Z₁A Q cs D told N).vals 16 = vKeys Q := by
  show vOf ((gvAll₁ Q cs D told N (vRng N)).map (·.2)) 16 = vKeys Q
  rw [snd_six h]
  rfl

/-- **At a `Thread` at the border 16, in scope: the named test on values accepts.** -/
theorem values16 {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 16 k e m E)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).vals 16 e rs gs = true := by
  have h6 := six_sourced hs scope
  have e16 := shape16_of_thr hs scope T₁ hbs hbeg h
  have hk : (sh₁B (pubOf X) CF e).2.look.keysOk = true := by
    rw [e16]
    exact keysOk16
  obtain ⟨hm, hl⟩ := pub_keys_six h6
  rw [vals16_is h6]
  exact keysSum_of (one := (pubOf X).one) 64 (keys_of_thr hs scope T₁ hbs hbeg h) hk hm hl

/-- **AT EVERY BORDER BUT 15 THE NAMED TEST ON VALUES ACCEPTS AT THE STATE THAT STANDS THERE.** -/
theorem values_but15 {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {j : Nat} (hj : j ≠ 15) {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env}
    (h : Thr T₁ j k e m E) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).vals j e rs gs = true := by
  by_cases c : j = 16
  · subst c
    exact values16 hs scope T₁ hbs hbeg h rs gs
  · exact vals_sourced hs scope CF j hj c e rs gs

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.keysSum_of
#print axioms AtPublicFiles.AtFiles.Full.pub_keys_six
#print axioms AtPublicFiles.AtFiles.Full.run16_six
#print axioms AtPublicFiles.AtFiles.Full.keysOk16
#print axioms AtPublicFiles.AtFiles.Full.shape16_of_thr
#print axioms AtPublicFiles.AtFiles.Full.keys_of_thr
#print axioms AtPublicFiles.AtFiles.Full.vals16_is
#print axioms AtPublicFiles.AtFiles.Full.values16
#print axioms AtPublicFiles.AtFiles.Full.values_but15
