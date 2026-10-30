-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastEvOwn.lean: the premise `hrows` of `exchange_own`, from the item (Eval) that the thread says at border 0: the first chain's
claim 1 "Eval" speaks of the own group's row number 0, and at the written shape that group has just one open row.

  `val₁Key`: the first half's reader: the library's `valOf`, read.
  `claim_eval`: what the claim says.
  `rows_of_claim`, `rows_stand`: the rows in front hold of the chain's words, at the start's state, at a stand at border 0.

What stays open. `hsame`: the letter for sameness is "the two read as one element". `ThirdShaped` (`third_shaped`).
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastExchangeOwn
import E2E.KeyLastDotOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey Part)
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE readE)
open VerifiableInference.Desc (Place Wit OpenedColumn Strs)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (RowsHold)
open VerifiableInference.Desc.Last (ItemL startLast)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar valOf RowHolds)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyLastThread (start_key handOf)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Sh₃ sh₃ SF)
open AtPublicFiles.AtFiles.Full (A0)
open Johnson.RunOne.KeyRows1 (meaning₁At plan₁ readers₁)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)

/-- **The first half's reader.** -/
def val₁Key : Wit Cells Unit M → Nat → Part → Nat → GE := fun w o pt i =>
  readE (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R w o pt i)

/-- **What the claim (Eval) says, at the library's filling.** -/
theorem claim_meaning {P S Cl₁ Ms : Type} (Kp : VerifiableInference.Desc.Key.KPlan)
    (R : VerifiableInference.Desc.Key.KRead Cl₁ Ms) (Xr : VerifiableInference.Desc.Key.KReaders S)
    (near : Nat → P × S → Strs → Prop)
    (forms worth other : Nat → String → P × S → Strs → Wit Cl₁ Unit Ms → Prop) (a : P × S) (y : Strs)
    (u : Wit Cl₁ Unit Ms)
    (h : (VerifiableInference.Desc.Key.meaning₁ Kp R Xr near forms worth other).claim 1 "Eval" a y u) :
    ∃ r, Xr.eval a.2 = some r ∧ RowHolds R.same (Xr.st a.2) (valOf Kp R u) r := by
  unfold VerifiableInference.Desc.Key.meaning₁ at h
  simp only [eq_self_iff_true, and_self, if_true] at h
  exact h

/-- **What the first chain's claim (Eval) says.** -/
theorem claim_eval {p : Xi × FirstState} {y : Strs} {u : Wit Cells Unit M}
    (h : (meaning₁At (AtPublicFiles.KeyThread.one₀ Xs) L.R).claim 1 "Eval" p y u) :
    ∃ r, (readers₁ (AtPublicFiles.KeyThread.one₀ Xs)).eval p.2 = some r ∧
      RowHolds L.R.same ((readers₁ (AtPublicFiles.KeyThread.one₀ Xs)).st p.2)
        (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R u) r :=
  claim_meaning _ _ _ _ _ _ _ _ _ _ h

/-- **The rows in front hold, at the state that the start returns**, from the claim (Eval) at the first chain's end. -/
theorem rows_of_claim {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {x : Xi} {f : FirstState} {e : St} {s₀ : S₃}
    {Wt₂ : Type} (val₁ : Wt₂ → Nat → Part → Nat → GE) (u : Wt₂ × Words GE) (val : Nat → Part → Nat → OnBytes.E)
    (hv : ∀ o pt i, val₁ u.1 o pt i = readE (val o pt i))
    (hst : (descriptionFromSource Xs Nr Pl).start₃ x f e = .ok s₀) (hsh : sh₃ SF s₀ = A0) (r : OnBytes.Row)
    (he : (f.lin.bind fun L => (f.d.st.groups[L.own]?).bind fun G => G.rows[0]?) = some r)
    (hh : RowHolds (fun a b => readE a = readE b) f.d.st val r) : RowsHold rdE s₀ (wordsKey val₁ s₀ u) := by
  obtain ⟨h, o, hh₁, -, hs'⟩ := (start_key Xs Nr Pl x f e s₀).1 hst
  have hh₂ : f.lin.map (handOf f) = some h := hh₁
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hh₂
  obtain ⟨-, -, -, -, est, -, -, eown, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o s₀ hs'
  rw [hl] at he
  have he' : (f.d.st.groups[l.own]?).bind (fun G => G.rows[0]?) = some r := he
  obtain ⟨G, hG, hr⟩ := Option.bind_eq_some_iff.1 he'
  have e₀ : f.d.st = s₀.st := est.symm
  have hG' : s₀.st.groups[s₀.loc.own]? = some G := by
    rw [eown]
    show s₀.st.groups[l.own]? = _
    rw [← e₀]
    exact hG
  rw [e₀] at hh
  have ht : stTidyB s₀.st = true := (congrArg (fun a : Sh₃ => a.2.tidy) hsh).trans tidy_A0
  exact rows_front val₁ s₀ u val hv G hG' (one_row_of_shape hsh hG') r hr
    ((tidy_of ht).inOrder.rows _ G hG' r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hr))) hh
    (ok_of_shape (s' := s₀) hsh).2.2.2

variable
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
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

set_option maxHeartbeats 1000000 in
/-- **The rows in front hold**, at a stand at border 0. -/
theorem rows_stand (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hZ : ThirdShaped (X := Xs) (N := Nr) (P := Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (fun _ _ _ => true) A0)
    (hsame : L.R.same = fun a b => readE a = readE b)
    {k : Coins Bk} {s : S₃} {m : Mid (Local W₀ Rc Xi Unit) X} {E : Env} (ds : List Fmt.Drawn)
    (hT : Thr (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 0 k s m E) :
    RowsHold rdE s (wordsKey (val₁Key Xs L) s ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds))) := by
  have hsh := shape_zero hs scope rfl hZ hT
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  have hs₀ : s₀ = s := by
    have q : (Except.ok (s₀, _, cols) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (s, [], []) := hf
    exact (Prod.mk.inj (Except.ok.inj q)).1
  subst hs₀
  have hi : ItemL.ev ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).opened 0 := by
    show ItemL.ev ∈ startLast
    decide
  have hit := hT.2.2.2.1 ds ItemL.ev hi
  have hit' : (meaning₁At (AtPublicFiles.KeyThread.one₀ Xs) L.R).claim 1 "Eval" ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m s₀).1.1
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).strs E)
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)).1 := hit
  obtain ⟨r, he, hh⟩ := claim_eval Xs L hit'
  rw [hsame] at hh
  exact rows_of_claim (val₁Key Xs L) _ (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R _) (fun _ _ _ => rfl) hbeg hsh r he hh

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.claim_eval
#print axioms AtPublicFiles.KeyLastChain.rows_stand
