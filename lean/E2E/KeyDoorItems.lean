-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorItems.lean: the five items that the key file's last thread has open at its start, at a
pair of states at which the first thread and the shared thread stand at their last borders: the body
of the premise `hItems` of the door (`doorBehind_of`, Johnson/Desc/ProofFile/Honest/Thread/Door.lean).

Why. Four of the five items were said by an earlier chain, and they are carried over by construction
once the last thread's witness is made of the earlier threads' witnesses, `m₁` is `firstSays` and the
row (Eval) is `evFirst`: they cannot fail here, and what they say is spent at the members 0 and 2. The
fifth, (Dot), is new.

Main names.
  `commonOf`: the shared chain's input, out of the last chain's.
  `firstSays`: what the first chain's items say, read at the first half of the last witness.
  `evFirst`: a meaning whose row (Eval) is the first chain's.
  `wit₃`: THE LAST CHAIN's WITNESS: a pair: the first thread's witness at the first chain's
    challenges, and the words of the shared thread's witness at the shared chain's.
  `lastT`: the last thread at these letters.
  `items_pair`: the items, at a pair of states where the two threads stand and that `ends` returns.

Premises that stay, all named in the statement.
  `hin`, `hheard`, `hw₂`: the run's input is the one of which the letters speak; its challenges are
    the two chains'.
  `hends`: the letter `ends` returns this pair.
  `hdot`: the item (Dot), at the letter `Dt`, at the last witness.
  `l₁`, `l₂`: the numbers of sub-protocols of the two chains: `lengths` (E2E/KeyThreadFits.lean) pays
    them in scope.

What stays open. The words of the pair's second half are tied to its first by nothing here. The
meaning `Dt` is a letter but for its row (Eval). Whether the two threads stand at any run is not said:
this is an implication. The first thread here is `laid₁`, the thread over the key's own table of
joints, in the script of `L`; the shared and the last thread are in that of `K`: that the two agree
(`hst`, `Sits`) is not said here. Nothing here is a law on any prover.

NOT IN FRONT OF A LAW OVER COINS: `items_pair` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground. It stands behind `Thr` of two threads, whose
clauses tie those threads' letters to the run's coins and the input, of the first kind. `hw₂` ties `w₂`
to `rc`, `hin` ties `m₃` to it, of the first kind. `hends` and `hdot` stand on the letters `ends`, `Dt`
under those clauses, of the first kind. None of these is the term that the committer makes. None: the
bar is flat. `commonOf`, `firstSays`, `evFirst`, `wit₃`, `lastT` are definitions; `end_has` and
`start_cases` are closed.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeySharedQuiet
import E2E.KeyLastQuiet
import E2E.KeyDoorMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyDoorItems
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (ItemL MeaningL startLast)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces descriptionFromSource)
open Johnson.RunOne.KeyRows1 (meaning₁At)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill holdsH laid₁ one₀ decl₁)
open Johnson.RunOne.KeyRows23 (atSix)
open AtPublicFiles.KeyLastThread (lettersLastKey pinSays)

/-- The five items that the first chain leaves open and this file reads. -/
theorem end_has : KItem.pin 0 ∈ VerifiableInference.Desc.Key.end₁ ++ [KItem.claim 1 "Eval"] ∧
    KItem.srow 0 ∈ VerifiableInference.Desc.Key.end₁ ++ [KItem.claim 1 "Eval"] ∧
    KItem.pin 2 ∈ VerifiableInference.Desc.Key.end₁ ++ [KItem.claim 1 "Eval"] ∧
    KItem.srow 2 ∈ VerifiableInference.Desc.Key.end₁ ++ [KItem.claim 1 "Eval"] ∧
    KItem.claim 1 "Eval" ∈ VerifiableInference.Desc.Key.end₁ ++ [KItem.claim 1 "Eval"] := by
  decide

/-- What is open at the last chain's start. -/
theorem start_cases (j : ItemL) (h : j ∈ startLast) :
    j = .pinI ∨ j = .pinV ∨ j = .ev ∨ j = .dot ∨ j = .pinO := by
  simpa [startLast] using h

/-- The shared chain's input, out of the last chain's. -/
def commonOf {W₀ Rc : Type} (v : Local W₀ Rc Xi Unit) : Common W₀ Rc TableKey :=
  ⟨v.w₀, v.rc, v.x.key⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)

/-- **What the first chain's items say**, of the first half of the last witness. -/
def firstSays (_ : Local W₀ Rc Xi Unit) (i : KItem) (p : Xi × FirstState) (y : Strs)
    (u : Wit Cells Unit M × Words Cb.Gl.E) : Prop :=
  holdsH (descriptionFromSource Xs Nr Pl) L.base.h₁ atSix L.meetsT (meaning₁At (one₀ Xs) L.R) i p y u.1

/-- A meaning whose row (Eval) is what the first chain's item says. -/
def evFirst {Wt : Type} (m : KItem → Xi × FirstState → Strs → Wt → Prop)
    (D : MeaningS St (Xi × FirstState) Wt) : MeaningS St (Xi × FirstState) Wt :=
  { D with ev := fun p y u => m (.claim 1 "Eval") p y u }

variable (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey)

/-- **The last chain's witness**: of the challenges heard, the first chain's go to the first thread's
witness, and the others to the shared thread's. -/
def wit₃ (k : Coins Bk) (v : Local W₀ Rc Xi Unit) (h : List Fmt.Drawn) :
    Wit Cells Unit M × Words Cb.Gl.E :=
  (L.wit k v.w₀ v.rc (h.take (decl₁ (descriptionFromSource Xs Nr Pl)).length) [],
    ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k (commonOf v)
      (h.drop (decl₁ (descriptionFromSource Xs Nr Pl)).length)))

variable (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Dt : Local W₀ Rc Xi Unit →
    MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (ends : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → (Xi × FirstState) × St)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- The last chain's thread at these letters: the key's, with the witness `wit₃`, the first chain's
items as `firstSays`, and the row (Eval) as `evFirst`. -/
abbrev lastT :
    Thread Bk S₃ VerifiableInference.Desc.Key.Claim (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X Xi :=
  (lettersLastKey Xs Nr Pl K (WitLens.snd (Wit Cells Unit M)) Nm
    (fun v => evFirst (firstSays Xs Nr Pl L v) (Dt v))
    (firstSays Xs Nr Pl L) ML ends (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) table n₁ n₂ Vd Rd
    Kp w).thread

/-- **The items at the last thread's start**, at a pair of states at which the two earlier threads
stand and that `ends` returns. At any run state of the last chain whose input is the letters' and
whose challenges are the two chains'.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem items_pair (l₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19)
    (l₂ : (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = 12)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    {e₁ : FirstState} {m₁ : Mid (Local W₀ Rc Xi Unit) X} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env} (u₁ : Thr (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) 19 k e₁ m₁ E₁)
    (u₂ : Thr (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) 12 k e₂ m₂ E₂)
    (hends : ends k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) = ((x, e₁), e₂))
    (hdot : ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
      (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))))
    (s₃ : S₃) (m₃ : Mid (Local W₀ Rc Xi Unit) X) (E₃ : Env)
    (hin : m₃.st.input = ⟨w₀, rc, x, ()⟩) (hheard : m₃.st.heard = m₁.st.heard ++ m₂.st.heard) :
    (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).Items ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).opened 0) k s₃ m₃ E₃ := by
  have hv₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := u₁.2.2.2.2.2.2.1
  have hv₂ : m₂.st.input = w₂ := u₂.2.2.2.2.2.2.1
  have hl₁ : m₁.st.heard.length = (decl₁ (descriptionFromSource Xs Nr Pl)).length := by
    have e := (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).heard_length u₁.2.1
    rw [e]
    show 0 + (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder 19).length = _
    rw [Nat.zero_add, ← l₁]
    unfold declsTo
    rw [List.take_length]
  have hl₂ : m₂.st.heard.length = (AtPublicFiles.KeyThread.decl₂ (descriptionFromSource Xs Nr Pl)).length := by
    have e := (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).heard_length u₂.2.1
    rw [e]
    have hbs := (AtPublicFiles.KeySharedThread.sits_two Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).2.2.2.1
    rw [hbs]
    show 0 + (declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder 12).length = _
    rw [Nat.zero_add, ← l₂]
    unfold declsTo
    rw [List.take_length]
  have hseat : ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).seat k m₃ s₃).1 = ((x, e₁), e₂) := by
    have hf : (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).front = (m₁.st.heard ++ m₂.st.heard).length := by
      show (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
        declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length).length = _
      rw [List.length_append, List.length_append, hl₁, hl₂]
      unfold declsTo
      rw [List.take_length, List.take_length]
    show ends k m₃.st.input (m₃.st.heard.take (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).front) = _
    rw [hin, hheard, hf, List.take_length, hends]
  intro ds i hi
  have hw : (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).wit k m₃.st.input (m₃.st.heard ++ ds) =
      wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds)) := by
    show wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k m₃.st.input (m₃.st.heard ++ ds) = _
    rw [hin, hheard, List.append_assoc]
  have hu₁ : (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
      (m₁.st.heard ++ (m₂.st.heard ++ ds))).1 = L.wit k w₀ rc m₁.st.heard [] := by
    show L.wit k w₀ rc ((m₁.st.heard ++ (m₂.st.heard ++ ds)).take
      (decl₁ (descriptionFromSource Xs Nr Pl)).length) [] = _
    rw [← hl₁, List.take_left]
  have hu₂ : (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
      (m₁.st.heard ++ (m₂.st.heard ++ ds))).2 =
      ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k m₂.st.input (m₂.st.heard ++ ds)) := by
    show ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k (commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit))
      ((m₁.st.heard ++ (m₂.st.heard ++ ds)).drop (decl₁ (descriptionFromSource Xs Nr Pl)).length)) = _
    rw [← hl₁, List.drop_left, hv₂, hw₂]
  have hop : (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).opened 19 = VerifiableInference.Desc.Key.end₁ ++ [.claim 1 "Eval"] :=
    AtPublicFiles.KeyThread.ends_table.1
  have hfirst : ∀ j ∈ (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).opened 19, holdsH (descriptionFromSource Xs Nr Pl) L.base.h₁ atSix L.meetsT
      (meaning₁At (one₀ Xs) L.R) j (x, e₁) ((laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).strs E₁)
      ((wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))).1) := by
    intro j hj
    have h : holdsH (descriptionFromSource Xs Nr Pl) L.base.h₁ atSix L.meetsT (meaning₁At (one₀ Xs) L.R) j
        (m₁.st.input.x, e₁) ((laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).strs E₁)
        (L.wit k m₁.st.input.w₀ m₁.st.input.rc (m₁.st.heard ++ []) []) :=
      u₁.2.2.2.1 [] j hj
    rw [hv₁, List.append_nil] at h
    rw [hu₁]
    exact h
  have hO : (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).opened 0 = startLast := rfl
  rw [hO] at hi
  have hfin : ∀ (j : ItemL), j ∈ startLast → ∀ y, ItemL.holds Nm
      (((lettersLastKey Xs Nr Pl K (WitLens.snd (Wit Cells Unit M)) Nm
        (fun v => evFirst (firstSays Xs Nr Pl L v) (Dt v))
        (firstSays Xs Nr Pl L) ML ends (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) table
        n₁ n₂ Vd Rd Kp w).Mg) ⟨w₀, rc, x, ()⟩) ML j (x, e₁) e₂ s₃ y
      (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
        (m₁.st.heard ++ (m₂.st.heard ++ ds))) := by
    intro j hj y
    have p0 := hfirst (.pin 0) (by rw [hop]; exact end_has.1)
    have r0 := hfirst (.srow 0) (by rw [hop]; exact end_has.2.1)
    have p2 := hfirst (.pin 2) (by rw [hop]; exact end_has.2.2.1)
    have r2 := hfirst (.srow 2) (by rw [hop]; exact end_has.2.2.2.1)
    have he := hfirst (.claim 1 "Eval") (by rw [hop]; exact end_has.2.2.2.2)
    rcases start_cases j hj with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => ⟨p0, r0⟩, fun _ => ⟨p2, r2⟩⟩
    · exact ⟨fun _ => ⟨p0, r0⟩, fun _ => ⟨p2, r2⟩⟩
    · have he' : (meaning₁At (one₀ Xs) L.R).claim 1 "Eval" (x, e₁) ((laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁).strs E₁)
          (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds))).1 := he
      show (meaning₁At (one₀ Xs) L.R).claim 1 "Eval" (x, e₁) y
        (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
          (m₁.st.heard ++ (m₂.st.heard ++ ds))).1
      exact AtPublicFiles.KeyDoorMaps.eval_map _ _ _ _ _ _ _ _ _ y _ _ rfl he'
    · exact hdot y ds
    · have hm : ItemS.pin .oOmega ∈ fwdOpen SharedRows.start (SharedRows.rows true) 12 := by
        decide
      have h := u₂.2.2.2.1 ds _ hm
      intro m' hm'
      have h' : _root_.Desc.K14.Honest.SmpOwn (num m') e₂
          (ℓ₂.get ((threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).wit k m₂.st.input (m₂.st.heard ++ ds))) := h m' hm'
      show _root_.Desc.K14.Honest.SmpOwn (num m') e₂ (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂
        w₂ k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ (m₂.st.heard ++ ds))).2
      rw [hu₂]
      exact h'
  show ItemL.holds Nm _ ML i ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).seat k m₃ s₃).1.1 ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).seat k m₃ s₃).1.2 s₃ ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).strs E₃)
    ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML ends table n₁ n₂ Vd Rd Kp w).wit k m₃.st.input (m₃.st.heard ++ ds))
  rw [hseat, hw, hin]
  exact hfin i hi _

end

end AtPublicFiles.KeyDoorItems

#print axioms AtPublicFiles.KeyDoorItems.end_has
#print axioms AtPublicFiles.KeyDoorItems.start_cases
#print axioms AtPublicFiles.KeyDoorItems.items_pair
