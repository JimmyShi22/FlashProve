-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastDoor.lean: the door between the key file's chains and the file's end, at the threads that the honest prover
of parts uses: `laid₁`, `threadKey`, and at the last chain `lastT` with the letter `saidLast`.

Main names.
  `doorYesS_key`: the third chain's start returns, wherever the two threads stand at their last borders. In scope.
  `finYesS_key`: the file's last test says yes, wherever the three stand at theirs. In scope.
  `door_join`: the door at the letter, from the door at no letter and the letter at the start.
  `last_front`: the last thread's count of rounds in front is what the two earlier threads heard.
  `form_door`: the last thread's clause on the state at its first border: by `form_start_key`.
  `door_behind_key`: `DoorBehindS` at the three threads, at the letter `saidLast`.

What is a conditional. Each statement speaks of where the threads stand: that they stand at any run is not said here.
`door_behind_key` keeps as premises: `OneState` at both earlier threads; the field clauses at their last borders (`L₁`,
`L₂`); the item (Dot) `hdot`; that the key fits (`hfit`); the tie of the stored tables `hst`; the tie of the trees that
are taken over `htrees`; the riders `hr`; the input `hv`. `form_door` stands on the closed line `door_form_full`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyDoorForm
import E2E.KeyLastSaid
import E2E.KeyDoorPairs
import E2E.KeyDoorShaped
import E2E.KeyEndAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit OpenedColumn FileDescription)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource ownTest)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St first)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey sits_two parKey)
open AtPublicFiles.KeyThread (KeyFill laid₁ lengths)
open AtPublicFiles.KeyDoorItems (commonOf lastT)
open AtPublicFiles.KeyDoorPairs (endsKey ends_are begun_pairs door_pairs_key)
open AtPublicFiles.KeyEndAtKey (codes_at_key)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (shape19_of_thr shape12_of_thr QK)

section yes
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X₀ X Wk P₁ Wt : Type} {Z : VerifierAndGoals.PublicFiles}
  {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)

/-- **The door says yes at the two threads**: in scope, at all letters. -/
theorem doorYesS_key (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (y : Xi) (k : Coins Bk) :
    DoorYesS (descriptionFromSource Xs Nr Pl) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) S₁ S₂ y k :=
  AtPublicFiles.AtFiles.doorYesS_of_two Xs Nr Pl (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
    (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) S₁ S₂ y k hs.named.plan
    (sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1 (lengths scope hs.named).2.1
    (fun e₁ m₁ E₁ u => by
      rw [(lengths scope hs.named).1] at u
      exact AtPublicFiles.AtFiles.Full.last₁_of_thr hs scope (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) rfl
        (fun _ _ _ _ _ hb => ⟨_, hb⟩) u.1)
    fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ => by
      rw [(lengths scope hs.named).2.1] at u₂
      exact codes_at_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w ⟨m₂.st.input.key⟩ rfl u₂.1

/-- **The last test says yes at the three threads**: in scope, at all letters, at every thread over the last chain. -/
theorem finYesS_key (scope : VerifierAndGoals.InScope Z = true) (h : AtPublicFiles.AtFiles.KeyNamed Z Xs Nr Pl)
    (U₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X Xi)
    (hbs₃ : U₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder)
    (S₃' : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop) (y : Xi) (k : Coins Bk) :
    FinYesS (descriptionFromSource Xs Nr Pl) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) U₃ S₁ S₂ S₃' y k :=
  AtPublicFiles.AtFiles.finYesS_of_first Xs Nr Pl (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
    (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) U₃ S₁ S₂ S₃' y k hbs₃ (lengths scope h).2.2
    fun e₁ m₁ E₁ u => by
      rw [(lengths scope h).1] at u
      exact u.1.2.2.1.1

end yes

section general
variable {Xi' W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi'} {H : Prover W₀ Rc Xi' Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi' Tr) (Local W₀ Rc Xi' Tr) X Xi'}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi' Tr) (Local W₀ Rc Xi' Tr) X Xi'}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi' Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃' : Nat → Coins Bk → Mid (Local W₀ Rc Xi' Tr) X → Prop} {x : Xi'} {k : Coins Bk}
  {R : Ready W₀ Rc Xi' Ky Tr X₀ X}

/-- **The door at a letter**: from the door at no letter, and the letter at the state that the door lays, from the
pairs in hand. -/
theorem door_join (hT : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ (fun _ _ _ => True) x k R)
    (hS : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃' 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) }) :
    DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃' x k R :=
  fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs j₁ j₂ =>
    ⟨(hT e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs j₁ j₂).1, hS e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs j₁ j₂⟩

/-- **What the last thread has in front is what the two earlier threads heard.** -/
theorem last_front {n₁ n₂ : Nat} (hah₁ : T₁.ahead = []) (hah₂ : T₂.ahead = [])
    (hah : T₃.ahead = declsTo T₁.bs n₁ ++ declsTo T₂.bs n₂) {e₁ : F.S₁}
    {m₁ : Mid (Local W₀ Rc Xi' Tr) X} {E₁ : Env} {e₂ : F.S₂} {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env}
    (u₁ : Thr T₁ n₁ k e₁ m₁ E₁) (u₂ : Thr T₂ n₂ k e₂ m₂ E₂) :
    T₃.front = (m₁.st.heard ++ m₂.st.heard).length := by
  have f₁ : drawsFit (T₁.ahead ++ declsTo T₁.bs n₁) m₁.st.heard = true := u₁.2.1
  have f₂ : drawsFit (T₂.ahead ++ declsTo T₂.bs n₂) m₂.st.heard = true := u₂.2.1
  rw [hah₁, List.nil_append] at f₁
  rw [hah₂, List.nil_append] at f₂
  have l₁ := drawsFit_length _ _ f₁
  have l₂ := drawsFit_length _ _ f₂
  unfold Thread.front
  rw [hah, List.length_append, List.length_append, l₁, l₂]

end general

section door
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
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- The last thread at the term for `ends`. -/
abbrev T₃K : Thread Bk S₃ VerifiableInference.Desc.Key.Claim (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X Xi :=
  lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML
    (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂ Vd Rd Kp w

/-- The rounds in front of the last thread are the two earlier threads'. -/
theorem ahead_last :
    (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w).ahead =
      declsTo (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
        declsTo (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).bs (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length := by
  rw [(sits_two Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).2.2.2.1]
  rfl

/-- **The last thread's clause on the state at its first border, at the state that the door lays**, from the pairs and
`OneState`, in scope. hfit: the key fits the shape's index, at whatever the shared thread's input is. -/
theorem form_door (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
    (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env) (s₃ : S₃) (c : Option (List OpenedColumn))
    (u₁ : ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂
      (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂)
    (hst : (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃) (H : Prover W₀ Rc Xi TableKey Unit X₀ X) :
    (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w).Form
      0 k s₃ { R.start₃ H m₁ m₂ with opened := c } := by
  have hl := lengths scope hs.named
  have fr := last_front (T₃ := T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML
      table n₁ n₂ Vd Rd Kp w) rfl rfl
    (ahead_last Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w)
    u₁.1 u₂.1
  rw [hl.1] at u₁
  rw [hl.2.1] at u₂
  have i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := u₁.1.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) :=
    (u₂.1.2.2.2.2.2.2.1).trans hw₂
  have he := ends_are Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d o₁ o₂ k u₁ u₂ i₁ i₂
  have h1 := shape19_of_thr hs scope (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) rfl
    (fun _ _ _ _ _ hb => ⟨_, hb⟩) u₁.1
  have h2 := shape12_of_thr hs scope (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
    (sits_two Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).2.2.2.1
    (fun _ v _ s₀ hv hb => ⟨⟨v.key⟩, by
      have h : s₀ = first (parKey Xs Pl).codes v.key := hb
      rw [h]
      rfl, hfit v hv⟩) u₂.1
  have hf := form_start_key hs scope (ownTest Pl).rounds x e₁ e₂ s₃ h1 h2 hst
  have fr' : (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w).front = (m₁.st.heard ++ m₂.st.heard).length := fr
  have hseat : (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w).seat k { R.start₃ H m₁ m₂ with opened := c } s₃ = (((x, e₁), e₂), s₃) := by
    unfold Thread.seat
    show (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k R.own
      ((m₁.st.heard ++ m₂.st.heard).take _), s₃) = _
    rw [hown, fr', List.take_length, he]
  refine ⟨?_, ?_⟩
  · show Thread.form _ 0 (Thread.seat _ k _ s₃) = true
    rw [hseat]
    exact (Bool.and_eq_true _ _).mpr ⟨hf.1, rfl⟩
  · show Thread.formP _ 0 (Thread.seat _ k _ s₃)
    rw [hseat]
    exact hf.2

/-- **The door at the three threads, at the letter `saidLast`.** A conditional. -/
theorem door_behind_key (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (AtPublicFiles.KeyDoorItems.wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds))))
    (hst : ∀ v, (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).valid v → ∀ i p,
      (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).stored v i p =
        (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w).stored R.own i p)
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂,
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂
        E₂ →
      (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
        Kp w).Trees
        (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w).taken k { R.start₃ (keyProver K) m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂
        E₂ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃ → Rd 0 R.own s₃)
    (hv : (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
      Kp w).valid R.own)
    (L₁ : ∀ e m E, ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e m E →
      (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).Field [] (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length m E)
    (L₂ : ∀ e m E, ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂
        (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e m E →
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).Field [] (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length m E) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
      (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
      (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w)
      Said₁ Said₂
      (saidLast (descriptionFromSource Xs Nr Pl)
        (T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w)) x k R := by
  have hl := lengths scope hs.named
  refine door_join ?_ ?_
  · exact door_pairs_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂
      Vd Rd Kp w (fun _ _ _ => True) rfl rfl rfl o₁ o₂ hl.1 hl.2.1 hw₂ k R hown hdot rfl rfl rfl
      (ahead_last Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
        Kp w)
      rfl hst htrees
      (fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hh =>
        form_door Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd
          Kp w hs scope o₁ o₂ hfit hw₂ k R hown e₁ m₁ E₁ e₂ m₂ E₂ s₃ (some (c₁ ++ c₂)) u₁ u₂ hh (keyProver K))
      hr hv (fun _ _ _ _ _ _ _ _ => trivial)
  · intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ c₁ c₂ u₁ u₂ hh j₁ j₂
    have fr := last_front (T₃ := T₃K Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML
        table n₁ n₂ Vd Rd Kp w) rfl rfl
      (ahead_last Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂ Vd Rd Kp w)
      u₁.1 u₂.1
    have f₁ := L₁ _ _ _ u₁
    have f₂ := L₂ _ _ _ u₂
    have v₁ := u₁
    have v₂ := u₂
    rw [hl.1] at v₁
    rw [hl.2.1] at v₂
    have i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := v₁.1.2.2.2.2.2.2.1
    have i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) :=
      (v₂.1.2.2.2.2.2.2.1).trans hw₂
    have hx : R.own.x = x := by rw [hown]
    refine said_door _ _ _ (keyProver K) R k rfl rfl rfl
      (sits_two Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).2.2.2.1 rfl rfl u₁.1 u₂.1 f₁ f₂
      (fun t h => ?_) (fun t h => ?_) (by rw [hx]; exact hh) j₁ j₂ ?_ fr
    · have h' : t = (descriptionFromSource Xs Nr Pl).start₁ ((descriptionFromSource Xs Nr Pl).pub m₁.st.input.x) := h
      rw [h', i₁, hx]
    · have h' : t = first (parKey Xs Pl).codes m₂.st.input.key := h
      rw [h', i₂, hx]
      rfl
    · rw [hown]
      exact begun_pairs Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂
        Vd Rd Kp w o₁ o₂ k v₁ v₂ i₁ i₂ hh

end door

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.doorYesS_key
#print axioms AtPublicFiles.KeyLastChain.finYesS_key
#print axioms AtPublicFiles.KeyLastChain.door_join
#print axioms AtPublicFiles.KeyLastChain.last_front
#print axioms AtPublicFiles.KeyLastChain.form_door
#print axioms AtPublicFiles.KeyLastChain.door_behind_key
