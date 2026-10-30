-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastExchangeOwn.lean: `ExchangeS` at member 0 of the key file's last thread, with the letter `mlKey`: paid from the written shape
but for two premises, each about what the thread's items say.

  `shape_zero`: at a stand at border 0 the state has the shape `A0`.
  `exchange_own`: the exchange.

Left as premises: `hrows` (the rows in front hold of the chain's words: `rows_front` pays it from the item (Eval)), `hdot` ((Dot) in the
last chain's form: `dotSem_key` pays it from the item (Dot)).
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastAll
import E2E.KeyLastAtDot
import E2E.KeyLastRowsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey Part)
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (DotSem RowsHold)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Z₃Own sh₃ SF CF carries_all_in_scope)
open AtPublicFiles.AtFiles.Full (A0 first_of_sourced six_sourced)

/-- **At a stand at border 0 the state has the written shape.** -/
theorem shape_zero {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts} {V W Y Pb : Type}
    {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl V W Y Pb}
    {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hZ : ThirdShaped T₃ v A0) {k : Coins Bk} {s : S₃}
    {m : Mid W Y} {E : Env} (hT : Thr T₃ 0 k s m E) : sh₃ SF s = A0 := by
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have hS : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (six_sourced hs scope).lin
  have hr := shape_at T₃ (Z₃Own Xs Pl v) (n := 4) (b := 0) (a₀ := A0)
    (by rw [hbs]; exact Nat.le_of_eq (AtPublicFiles.KeyThread.lengths scope hs.named).2.2.symm) (by decide) hZ.yes hZ.first
    (fun j => by rw [hbs]; exact carries_all_in_scope hs scope v T₃.ft j) hT
  have hr₁ : (Except.ok A0 : Except String AtPublicFiles.AtFiles.Sh₃) =
      .ok (sh₃ Xs.chains.made.sized.key.once.shape s) := hr
  have e : sh₃ Xs.chains.made.sized.key.once.shape s = A0 := (Except.ok.inj hr₁).symm
  rw [hS] at e
  exact e

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (val₁ : Wit Cells Unit M → Nat → Part → Nat → GE)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **The exchange at member 0.** -/
theorem exchange_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hZ : ThirdShaped (X := Xs) (N := Nr) (P := Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (fun _ _ _ => true) A0)
    (hp : (thirdPar Xs.chains).S = SF)
    (hrows : ∀ k s m E ds, ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) 0 k s m E →
      RowsHold rdE s (wordsKey val₁ s ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds))))
    (hdot : ∀ k s m E ds, ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) 0 k s m E →
      DotSem rdE (thirdPar Xs.chains) (omK (thirdPar Xs.chains).S CF)
        (wvK val₁ (thirdPar Xs.chains).S CF A0.2.w) s
        ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds))) :
    ExchangeS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) 0 := by
  refine exchangeS_firstW rdE _ (thirdPar Xs.chains) (OkKey CF A0.2.w) (wordsKey val₁)
    (omK (thirdPar Xs.chains).S CF) (wvK val₁ (thirdPar Xs.chains).S CF A0.2.w) _
    (fun blk h => by
      have h' : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[0]? = some blk := h
      obtain rfl := Option.some.inj h'
      exact ⟨rfl, rfl⟩) (fun _ _ => Iff.rfl)
    (reads_key val₁ _ CF A0.2.w) (fun _ _ _ _ _ hT _ => ok_of_shape (shape_zero hs scope rfl hZ hT.1))
    (fun _ _ _ _ hT => at_of_shape hp (shape_zero hs scope rfl hZ hT.1)) hrows hdot

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.shape_zero
#print axioms AtPublicFiles.KeyLastChain.exchange_own
