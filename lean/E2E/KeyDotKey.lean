-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDotKey.lean: the premise `hdot` of `door_items` (E2E/KeyDoorPairs.lean), at the filling `dotFill`
(E2E/KeyDotItem.lean), behind the two threads, from the half on W and, named, `hs`, `scope`, `hO`, `l₁`,
`hw₂`. `door_dot` (E2E/KeyDoorDot.lean) pays `hO` and `l₁`.

Why. `dot_item` asks four things of the shared chain's last state and the words at number 2.
`end_at_key` and `codes_at_key` (E2E/KeyEndAtKey.lean) give the first three, `words_at_two` the words.

Main names.
  `two_key`: number 2 is of `Ours`, in scope. By Lean's kernel at the written value.
  `hdot_key`: the item (Dot) at the last witness, wherever the two threads stand, from the half on W.

What stays open. `hV`, the half on W, at the letters `g` and `wv`: which weights and which reader of the
witness are meant is not laid here; `vis_of_wIs` (E2E/KeyDotMeets.lean) shows what `VIs` follows from. At
idle letters `hV` holds by unfolding, and the item says nothing of the witness: so over letters this
cannot fail; what bites is who reads `g` and `wv`, at members 0 and 2. That the last chain's first
member stands at this file's shape is not said. «In scope» is one written value: the full size. No
thread is shown to stand.

NOT IN FRONT OF A LAW OVER COINS: `hdot_key` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it stands behind `Thr` of two threads, whose
clauses tie their letters to a run's coins, of the first kind; `hw₂` ties `w₂` to `rc`, of the first
kind; `hV` reads the hidden matrix through `holds2`, of the second kind, and names `k` and `rc`, so it
ties `g` and `wv`, of the first kind too. It calls `dot_item`,
`end_at_key` and `codes_at_key`, which bear the label, and keeps their letters. `holds2` here is the
made term at `K.weights` and `randKey K`, and `K` stays a letter, so it is no term that the committer
makes. None: the bar is flat. `hs`, `scope`, `hO` read public files. `two_key` names no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyDotItem
import E2E.KeyEndAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyDotKey
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open _root_.Desc.K14 (St first drawn)
open _root_.Desc.K14.Law (VIs)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey threadKey plan_key)
open AtPublicFiles.KeyThread (KeyFill laid₁ decl₁)
open AtPublicFiles.KeyDoorItems (commonOf wit₃)
open AtPublicFiles.KeyDotItem (dotFill dot_item words_at_two)
open AtPublicFiles.KeyEndAtKey (end_at_key codes_at_key)

/-- Number 2 is of `Ours`, in scope. -/
theorem two_key {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    Ours (parKey Xs Pl) (sentKey Xs Pl) 2 := by
  have h : 0 < (_root_.Desc.K14.withOmega QK.S).size := by decide +kernel
  refine Or.inr ⟨Nat.le_refl _, ?_⟩
  have e : parKey Xs Pl = QK := par_sourced hs scope
  rw [e]
  omega

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (g : Xi × FirstState → Nat → GE)
  (wv : Xi × FirstState → Wit Cells Unit M × Words GE → Nat → GE)
  (D : MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words GE))

/-- **The item (Dot) at the last witness, wherever the two threads stand**, from the half on W.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem hdot_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (nO : H2U.PlaceNums) (hO : Pl.O = some nO) (l₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    {e₁ : FirstState} {m₁ : Mid (Local W₀ Rc Xi Unit) X} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) 19 k e₁ m₁ E₁)
    (u₂ : Thr (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) 12 k e₂ m₂ E₂)
    (y : Strs) (ds : List Fmt.Drawn)
    (hV : VIs (parKey Xs Pl).par.S (g (x, e₁))
      (holds2 (parKey Xs Pl) K.weights (AtPublicFiles.KeySharedThread.randKey K) k w₂).Rw
      (wv (x, e₁) (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))))) :
    (dotFill (parKey Xs Pl).par.S g wv D).dot (x, e₁) e₂ y
      (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))) := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  obtain ⟨d, hd, hp, hl, ho⟩ :=
    end_at_key Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ hs scope nO hO u₂
  have hv₂ : m₂.st.input = w₂ := u₂.2.2.2.2.2.2.1
  have hc := codes_at_key Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ x
    (by rw [hv₂, hw₂]; rfl) u₂
  have hl₁ : m₁.st.heard.length = (decl₁ (descriptionFromSource Xs Nr Pl)).length := by
    have e := (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).heard_length u₁.2.1
    rw [e]
    show 0 + (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 19).length = _
    rw [Nat.zero_add, ← l₁]
    unfold declsTo
    rw [List.take_length]
  have hhead : (m₂.st.heard ++ ds).headD noChallenge = d := by
    cases hh : m₂.st.heard with
    | nil => rw [hh] at hd; cases hd
    | cons a t =>
      rw [hh] at hd
      obtain rfl : a = d := Option.some.inj hd
      rfl
  have hpsi : e₂.loc.psiSh = drawn (firstRv (m₂.st.heard ++ ds)) := by
    rw [hp]
    show _ = drawn (rvOf ((m₂.st.heard ++ ds).headD noChallenge))
    rw [hhead]
    rfl
  refine dot_item hQ.facts w₂.key e₂ (firstRv (m₂.st.heard ++ ds)) _ ?_ g wv D _ y _ hV ho hc hpsi ?_
  · rw [← hpsi]
    exact hl
  · intro part i
    show ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k
      (commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit))
      ((m₁.st.heard ++ (m₂.st.heard ++ ds)).drop (decl₁ (descriptionFromSource Xs Nr Pl)).length)) 2 part i = _
    rw [← hl₁, List.drop_left, ← hw₂]
    exact words_at_two ℓ₂ (parKey Xs Pl) (sentKey Xs Pl) (AtPublicFiles.KeyDotKey.two_key hs scope) _ _ k w₂ _ part i

end

end AtPublicFiles.KeyDotKey

#print axioms AtPublicFiles.KeyDotKey.two_key
#print axioms AtPublicFiles.KeyDotKey.hdot_key
