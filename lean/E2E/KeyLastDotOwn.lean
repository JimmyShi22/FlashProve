-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastDotOwn.lean: the premise `hdot` of `exchange_own`, from the item (Dot) that the thread says at border 0, at a meaning whose
(Dot) is the library's `dotI`.

  `gKey`: the row weights of the first chain's claim, read.
  `border_key`: what the start lays as the border, against the shared chain's last state.
  `dot_stand`: (Dot) in the last chain's form at a stand at border 0.

What stays open. `hDt`: the letter Dt's (Dot) is `dotI` at `gKey` and W's reader. `hend`: at the handed shared state Omega's number is 2 and
the codes are the written ones (`end_at_key`, `codes_at_key` give these wherever the shared thread stands).
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastExchangeOwn
import Johnson.Desc.Third.Law.Row0DotOm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey Part)
open OnBytes.Means (Words)
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc (Place Wit OpenedColumn foldBlocks)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (DotSem BorderIs borderIs_of_start ended_shared dotI)
open VerifiableInference.Desc.Last (ItemL startLast)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar rowOfLinClaim)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyLastThread (start_key handOf endKey)
open AtPublicFiles.AtFiles (KeySourced CF)
open AtPublicFiles.AtFiles.Full (A0)

/-- The row weights of the first chain's claim, read. -/
def gKey (q : Xi × FirstState) : Nat → GE := fun y =>
  ((((q.2.lin.map fun l => (rowOfLinClaim l.claim).g)).getD []).map fun t =>
    OnBytes.Model.Reading.gl.val (t.entry y)).sum

/-- **What the start lays, against the shared chain's last state.** -/
theorem border_key {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {x : Xi} {e₁ : FirstState} {d : St} {s₀ : S₃}
    (hst : (descriptionFromSource Xs Nr Pl).start₃ x e₁ d = .ok s₀) : BorderIs (gKey (x, e₁)) d s₀ := by
  obtain ⟨h, o, hh, ho, hs⟩ := (start_key Xs Nr Pl x e₁ d s₀).1 hst
  have hh' : e₁.lin.map (handOf e₁) = some h := hh
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hh'
  have ho' : (_root_.Desc.K14.ended d).map VerifiableInference.Desc.Third.sharedOfEnd = some o := ho
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 ho'
  have hp : (handOf e₁ l).pending = [rowOfLinClaim l.claim] := by
    show (match e₁.lin with
      | some l => [rowOfLinClaim l.claim]
      | none => e₁.pile) = _
    rw [hl]
  rw [hp] at hs
  have r := borderIs_of_start _ _ _ _ _ _ _ _ _ _ s₀ hs d (ended_shared d e he).1
  have eg : gKey (x, e₁) = fun y =>
      ((rowOfLinClaim l.claim).g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum := by
    funext y
    unfold gKey
    simp only [hl, Option.map_some, Option.getD_some]
  rw [eg]
  exact r

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type}
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

/-- **(Dot) at a stand at border 0.** -/
theorem dot_stand
    (hDt : ∀ v, (Dt v).dot = dotI (thirdPar Xs.chains).S gKey (fun _ u => u.2)
      (fun _ => wvK val₁ (thirdPar Xs.chains).S CF A0.2.w))
    (hend : ∀ k s m E, ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) 0 k s m E →
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).seat k m s).1.2.loc.oOmega = 2 ∧ ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).seat k m s).1.2.st.codes = CF)
    {k : Coins Bk} {s : S₃} {m : Mid (Local W₀ Rc Xi Unit) X} {E : Env} (ds : List Fmt.Drawn)
    (hT' : ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM) 0 k s m E) :
    DotSem rdE (thirdPar Xs.chains) (omK (thirdPar Xs.chains).S CF)
      (wvK val₁ (thirdPar Xs.chains).S CF A0.2.w) s
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)) := by
  have hT := hT'.1
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  have hs₀ : s₀ = s := by
    have q : (Except.ok (s₀, _, cols) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (s, [], []) := hf
    exact (Prod.mk.inj (Except.ok.inj q)).1
  subst hs₀
  have hB := border_key hbeg
  have hi : ItemL.dot ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).opened 0 := by
    show ItemL.dot ∈ startLast
    decide
  have hit := hT.2.2.2.1 ds ItemL.dot hi
  have hit' : (Dt m.st.input).dot ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).seat k m s₀).1.1 ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).seat k m s₀).1.2
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).strs E) ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey val₁) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)) := hit
  rw [hDt] at hit'
  obtain ⟨e2, ec⟩ := hend k s₀ m E hT'
  obtain ⟨g', hg⟩ : ∃ b, s₀.loc.border = some b := by
    have hst := hbeg
    obtain ⟨h, o, -, -, hs'⟩ := (AtPublicFiles.KeyLastThread.start_key Xs Nr Pl _ _ _ s₀).1 hst
    obtain ⟨⟨g, hb⟩, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o s₀ hs'
    exact ⟨_, hb⟩
  exact dotSem_key val₁ (thirdPar Xs.chains) CF A0.2.w _ _ s₀ g' hg hB _ hit' e2 ec

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.border_key
#print axioms AtPublicFiles.KeyLastChain.dot_stand
