-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyLastThread.lean: the last chain's thread at a key file, as the proof file's last chain has
it: the thread `Letters.thread` (Johnson/Desc/ProofFile/Honest/Thread/Last.lean) at the key file's
description, the twin of `lettersLast` (Honest/Thread/LastHead.lean).

Why. One type of thread at both files lets the laws of the last chain's members be stated once.
The key file's own last thread (`keyBase₃`, E2E/KeyThreadBase.lean) has items of its own; this one
has the proof file's: a pin of W, of the index masks' message and of Omega, (Eval), (Dot), and
the rows of the own group.

Main names.
  `handOf`, `handKey`: the seven values of the first chain's last state that the description's
    start hands on. `endKey`: what it takes of the shared chain's last state.
  `pinSays`, `pinFirst`: a pin of the first chain, as that chain's items say it: the pin of the
    message and its sample rows, at W and at the index masks' message.
  `lettersLastKey`, `threadLastKey`: the letters and the thread. The form is the library's test
    `fillAt`: border 2 of it is where the sample rows, the seats and the trees' numbers of the
    three members cross from the states handed on to the own test's state.
  `sits_three`: the thread stands where the rule for a file asks the last chain's thread.
  `ahead_key`: two equations that the law at the chain's start asks. By unfolding.
  `start_key`: the description's start says yes just where the start that `fillAt` reads says yes.
  `pinO_says`, `pinV_is`, `pinI_is`: what the three pins say here. The first gives Omega's sample
    rows. The other two restate the definition.
  `second_formKeeps_at`, `inOrder_of_fill`: the library's `second_formKeeps`, `inOrder_of_form` at
    `fillAt`, general in how the two states are read. The library's ask the form `fillZ`, which
    reads a proof file's first state, so they cannot be called here: these are their twins, proof
    for proof.
  `like_key`, `second_key`: the form behind the first member, and what that member keeps.

What stays a letter. How a witness is read (`ℓ`), the table's numbers, the meaning of the fields
that are not laid here, (Eval) and (Dot) among them, what the first chain's items say (`m₁`), the
rows' item (`ML`), the two states handed on (`ends`), the witness, the trees' tables, the numbers of
trees of the two earlier chains, the riders (`Rd`), what a member keeps outside the first member,
and which inputs are meant.

What stays open.
  * The form has never been evaluated at a key file's states. Owed before the key file's files on
    the last chain are turned to this thread: the evaluation of `firstDoorB` and `sharedDoorB` at
    the two chain ends of the honest key file.
  * The state's side that `keyBase₃` has in its form, `Side₃`, reads the border, and this thread's
    `order` cannot: it can stand in `Rd` alone. The law for it at the chain's start goes through the
    shared chain's side at that chain's last border, and at the shared thread's present letters
    (form and riders true) nothing holds that side.
  * Nothing ties `ℓ`, `Nm` or the witness to the two earlier threads', so no open item is paid at
    the chain's start. That `K.own` stands at the own test's place is not said.
  * The numbers of trees are letters: the library types 6 and 11, the full size's.

Not claimed. That this thread holds at any run. That the letters can be met together. That the
form can be met: `second_key` holds vacuously wherever it fails. `second_key` tests the form's type
and the first member, and holds at any reader of the states; `start_key` alone tests `handKey`.
Nothing on soundness, completeness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `second_formKeeps_at` and `second_key` bear this label; the rule
is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. This file's ground.
`FormKeeps` stands behind the thread at the border. There, of the first kind: `w` and `Vd` under
the thread's clause on the input, which fixes the input, with its index and the committer's coins;
`K.stored`
under its clause on the stored table; `table` under its clause on the trees; `ends` under the form
and the clause on how the state began; `wit`, `Mg₀`, `m₁` and `ML` under its clause on the items;
`Rd` under its clause on the riders. In `second_formKeeps_at` these are the fields of `L`. None of
them is the term that the committer makes: none: the bar is flat. `pinV_is`, `pinI_is`: no premise.
`pinO_says`: its premise reads the shared state and the witness, and names no coin.

-/
import E2E.KeyProver
import E2E.KeyThreadBase
import Johnson.Desc.Key.Desc
import Johnson.Desc.Third.Border
import Johnson.Desc.ProofFile.Honest.K14.SecondBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.KeyLastThread
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ P₁₄ FirstEnd₃ SharedOut sharedOfEnd start₃E batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (laid_k14Second)
open VerifiableInference.Desc.Last (ItemL MeaningL fillAt shapeAt_of_fill fill_of_shapeAt step_zero
  behindOk_of_one lastPlaces)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces Claim descriptionFromSource sharedPar
  beforeSharedPoint thirdPar ownTest)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (SmpOwn)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyThread (takenIn fixedLast decl₃)

/-! ## 1 The form, general in how the two states are read -/

section general
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ix Tr X P₁ Wt : Type}
  (L : LastThread.Letters Bk St S₃ Cl W₀ Rc Ix Tr X P₁ Wt) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (hand : P₁ → Option FirstEnd₃) (ended : St → Option SharedOut)

/-- **The form behind the first member, and what it keeps**, at the form `fillAt`, under the four
premises of the library's `second_formKeeps`.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem second_formKeeps_at (hPL : L.PL = fillAt p R hand ended)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hK : ∀ s s', SecondLaid p s s' → L.keeps 0 s s')
    (hO : ∀ x e s', (fillAt p R hand ended).shape 1 x e s' = true → L.order s') :
    FormKeeps L.thread 0 := by
  intro blk hb k s m E ds y cols s' hA hds hS
  obtain ⟨-, -, ⟨hF, -⟩, -, -, -, -⟩ := hA
  obtain ⟨hM, hst⟩ := hS
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [(hblk blk hb).decide] at hd
  have hL : SecondLaid p s s' := laid_k14Second p s s' _ gs hd
  -- the member has no round: no challenge comes: what was handed on is read as in front
  rw [(hblk blk hb).rounds] at hds
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hds
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have ei := (play_mid _ _ _ _ _ hy).1
  have eh := play_heard _ _ _ _ _ hy
  rw [List.append_nil] at eh
  have es : L.thread.seat k y.2 s' = ((L.thread.seat k m s).1, s') := by
    unfold Thread.seat
    rw [ei, eh]
  have hF' : (L.PL.shape 0 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
      (!decide (lastPlaces.length ≤ 0) || L.PL.nothingLeft s)) = true := hF
  rw [Bool.and_eq_true] at hF'
  have h0 := hF'.1
  rw [hPL] at h0
  obtain ⟨f, o, hf, ho, hs0⟩ := shapeAt_of_fill p R _ _ h0
  have h1 := fill_of_shapeAt p R _ _ hf ho (step_zero (Cl := Cl) hs0 _ gs hd)
  refine ⟨⟨?_, ?_⟩, hK s s' hL⟩
  · rw [es]
    show (L.PL.shape 1 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s' &&
        (!decide (lastPlaces.length ≤ 1) || L.PL.nothingLeft s')) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, rfl⟩
    rw [hPL]
    exact h1
  · rw [es]
    exact hO _ _ s' h1

/-- The form at border 1 gives that the statement is in order: it asks that the statement is
tidy. -/
theorem inOrder_of_fill (x : P₁) (e : St) (s' : S₃)
    (h : (fillAt p R hand ended).shape 1 x e s' = true) : OnBytes.Means.InOrder s'.st := by
  obtain ⟨f, o, -, -, hs⟩ := shapeAt_of_fill p R _ _ h
  obtain ⟨_, B⟩ := behindOk_of_one hs
  exact B.tidy.inOrder

end general

/-! ## 2 What the last chain reads of the two earlier chains' last states -/

/-- The seven values of the first chain's last state that the description's start hands on, at the
linear claim's first part l. -/
def handOf (s : FirstState) (l : OnBytes.LinFirst) : FirstEnd₃ :=
  { st := (VerifiableInference.Desc.Key.firstOf s).1
    book := (VerifiableInference.Desc.Key.firstOf s).2.1
    roots := (VerifiableInference.Desc.Key.firstOf s).2.2.1
    w := l.w, own := l.own, mask := l.mask
    pending := (VerifiableInference.Desc.Key.firstOf s).2.2.2 }

/-- What the form reads of what is handed on: nothing where the state names no linear claim. -/
def handKey (a : Xi × FirstState) : Option FirstEnd₃ := a.2.lin.map (handOf a.2)

/-- What the form reads of the shared chain's last state: nothing where it has not ended. -/
def endKey (d : St) : Option SharedOut := (_root_.Desc.K14.ended d).map sharedOfEnd

/-- **The description's start says yes just where the start that the form reads says yes.** -/
theorem start_key (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (x : Xi) (s : FirstState)
    (e : St) (s₀ : S₃) :
    (descriptionFromSource Xs Nr Pl).start₃ x s e = .ok s₀ ↔
      ∃ h o, handKey (x, s) = some h ∧ endKey e = some o ∧
        start₃E (thirdPar Xs.chains).codes (thirdPar Xs.chains).S h.st h.book h.roots h.w h.own
          h.mask h.pending o = .ok s₀ := by
  have key : (descriptionFromSource Xs Nr Pl).start₃ x s e =
      Except.bind (VerifiableInference.Desc.named "the first chain's end names no W" s.lin)
        fun l => Except.bind
          (VerifiableInference.Desc.named "the shared chain's end: something is untested"
            (_root_.Desc.K14.ended e))
          fun e₂ => start₃E (thirdPar Xs.chains).codes (thirdPar Xs.chains).S (handOf s l).st
            (handOf s l).book (handOf s l).roots (handOf s l).w (handOf s l).own (handOf s l).mask
            (handOf s l).pending (sharedOfEnd e₂) := rfl
  constructor
  · intro h
    rw [key] at h
    cases hl : s.lin with
    | none =>
      rw [hl] at h
      simp [VerifiableInference.Desc.named, Except.bind] at h
    | some l =>
      cases he : _root_.Desc.K14.ended e with
      | none =>
        rw [hl, he] at h
        simp [VerifiableInference.Desc.named, Except.bind] at h
      | some e₂ =>
        rw [hl, he] at h
        refine ⟨handOf s l, sharedOfEnd e₂, ?_, ?_, h⟩
        · show s.lin.map (handOf s) = _
          rw [hl]
          rfl
        · show (_root_.Desc.K14.ended e).map sharedOfEnd = _
          rw [he]
          rfl
  · rintro ⟨h, o, hh, ho, hs⟩
    have hh' : s.lin.map (handOf s) = some h := hh
    have ho' : (_root_.Desc.K14.ended e).map sharedOfEnd = some o := ho
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hh'
    obtain ⟨e₂, he, rfl⟩ := Option.map_eq_some_iff.1 ho'
    rw [key, hl, he]
    exact hs

/-! ## 3 A pin of the first chain -/

section pins
variable {P₁ Wt : Type}

/-- **What a pin of the first chain says**, of what the first chain's items say (m): at the tenant
of the index masks' message, that message's pin and sample rows; at W's, W's. As in `mgWords`: it
is true at a pair that is nobody's, and asks both where two share one. -/
def pinSays (N : NumbersS) (m : KItem → P₁ → Strs → Wt → Prop) (j t : Nat) (p : P₁) (y : Strs)
    (u : Wt) : Prop :=
  ((j, t) = N.index → m (.pin 0) p y u ∧ m (.srow 0) p y u) ∧
    ((j, t) = N.w → m (.pin 2) p y u ∧ m (.srow 2) p y u)

/-- The meaning with that sentence as the first chain's pin. -/
def pinFirst (N : NumbersS) (m : KItem → P₁ → Strs → Wt → Prop) (Mg₀ : MeaningS St P₁ Wt) :
    MeaningS St P₁ Wt :=
  { Mg₀ with pin₁ := pinSays N m }

end pins

/-! ## 4 The letters -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) Wt)
  (m₁ : Local W₀ Rc Xi Unit → KItem → Xi × FirstState → Strs → Wt → Prop)
  (ML : MeaningL S₃ Wt)
  (ends : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → (Xi × FirstState) × St)
  (wit : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- **The last chain's letters at the key.** -/
def lettersLastKey :
    LastThread.Letters Bk St S₃ Claim W₀ Rc Xi Unit X (Xi × FirstState) Wt :=
  { N := Nm
    Mg := fun v => mgWords ℓ (sharedPar Xs.chains (beforeSharedPoint Pl)) Nm
      (pinFirst Nm (m₁ v) (Mg₀ v))
    ML := ML
    PL := fillAt (thirdPar Xs.chains) (ownTest Pl).rounds handKey endKey
    order := fun s => OnBytes.Means.InOrder s.st
    ft := (descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber
    bs := (descriptionFromSource Xs Nr Pl).second.blocksInOrder
    hs := (keyProver K).second
    ahead := declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
      declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length
    near := (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length).length
    taken := takenIn (decl₃ (descriptionFromSource Xs Nr Pl))
    ends := ends
    first := fun a s₀ => (descriptionFromSource Xs Nr Pl).start₃ a.1.1 a.1.2 a.2 = .ok s₀
    wit := wit
    table := table
    fixed := fixedLast (descriptionFromSource Xs Nr Pl)
    stored := fun v => (keyProver K).storedWords v.w₀ v.rc
    item := (sharedPar Xs.chains (beforeSharedPoint Pl)).item
    n₁ := n₁
    n₂ := n₂
    valid := fun v => v = w ∧ Vd v
    rides := Rd
    keeps := fun b s s' => ∀ q, lastPlaces[b]? = some q → kpSecond (thirdPar Xs.chains) Kp q s s' }

/-- **The last chain's thread at the key**, at the types of the description. -/
def threadLastKey :
    Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X
      Xi :=
  (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread

/-- **The thread stands where the rule for a file asks the last chain's thread to stand**: the
field `three` of `Sits`, at the key's description and the key's prover. The field `fits` is not
said here. -/
theorem sits_three :
    (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).φ = .own ∧
      (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).chain = 2 ∧
      (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).ft =
        (descriptionFromSource Xs Nr Pl).lastChainFirstTreeNumber ∧
      (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).bs =
        (descriptionFromSource Xs Nr Pl).second.blocksInOrder ∧
      (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).hs =
        (keyProver K).second :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The two equations that the law at the chain's start asks of the rounds in front. -/
theorem ahead_key :
    (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).ahead =
        declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
          declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length ∧
      (threadLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).near =
        (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length).length :=
  ⟨rfl, rfl⟩

/-- **Omega's pin gives its sample rows**, at the shared chain's last state. -/
theorem pinO_says (v : Local W₀ Rc Xi Unit) (p : Xi × FirstState) (e : St) (s : S₃) (y : Strs)
    (u : Wt)
    (h : ItemL.holds Nm
      ((lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).Mg v)
      ML .pinO p e s y u) :
    SmpOwn 2 e (ℓ.get u) := by
  have h' : ∀ m, Nm.tenant m = Nm.tenant .oOmega → SmpOwn (num m) e (ℓ.get u) := h
  exact h' .oOmega rfl

/-- What W's pin says here. -/
theorem pinV_is (v : Local W₀ Rc Xi Unit) (p : Xi × FirstState) (e : St) (s : S₃) (y : Strs)
    (u : Wt) :
    ItemL.holds Nm
        ((lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).Mg v)
        ML .pinV p e s y u ↔
      pinSays Nm (m₁ v) Nm.w.1 Nm.w.2 p y u :=
  Iff.rfl

/-- What the index masks' pin says here. -/
theorem pinI_is (v : Local W₀ Rc Xi Unit) (p : Xi × FirstState) (e : St) (s : S₃) (y : Strs)
    (u : Wt) :
    ItemL.holds Nm
        ((lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).Mg v)
        ML .pinI p e s y u ↔
      pinSays Nm (m₁ v) Nm.index.1 Nm.index.2 p y u :=
  Iff.rfl

/-- The first member of the key's last chain is K14's second part, at the chain's parameters. -/
theorem like_key (blk : Block S₃ Claim) (hb : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[0]? = some blk) :
    LikeSecond blk (thirdPar Xs.chains) := by
  obtain rfl := Option.some.inj hb
  exact ⟨rfl, rfl⟩

/-- **The form behind the first member, and what it keeps, at the key.** It holds vacuously wherever
the form at border 0 is false.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem second_key :
    FormKeeps
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 0 := by
  refine second_formKeeps_at
    (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w)
    (thirdPar Xs.chains) (ownTest Pl).rounds handKey endKey rfl
    (fun blk hb => like_key Xs Nr Pl blk hb) ?_
    (fun x e s' h => inOrder_of_fill _ _ _ _ x e s' h)
  intro s s' hL q hq
  obtain rfl : (⟨3, none, 0, .K14⟩ : Place) = q := Option.some.inj hq
  show (if (⟨3, none, 0, .K14⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
  rw [if_pos rfl]
  exact hL

end

end AtPublicFiles.KeyLastThread

#print axioms AtPublicFiles.KeyLastThread.second_formKeeps_at
#print axioms AtPublicFiles.KeyLastThread.inOrder_of_fill
#print axioms AtPublicFiles.KeyLastThread.start_key
#print axioms AtPublicFiles.KeyLastThread.sits_three
#print axioms AtPublicFiles.KeyLastThread.ahead_key
#print axioms AtPublicFiles.KeyLastThread.pinO_says
#print axioms AtPublicFiles.KeyLastThread.pinV_is
#print axioms AtPublicFiles.KeyLastThread.pinI_is
#print axioms AtPublicFiles.KeyLastThread.like_key
#print axioms AtPublicFiles.KeyLastThread.second_key
