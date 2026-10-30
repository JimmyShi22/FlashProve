-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EqMg.lean: THE SEVEN RIDERS ON THE TABLE's MEANING (`MgRides`,
QuietRides.lean) AT THE COMPOSED MEANING OVER THE CLOSED BASE (`mgAll 𝔇 mgBase`), AT THE ONE
EQUATION's SUB-PROTOCOL (our files call a sub-protocol a block); AND SO THE LINK LAW's PREMISE hon3
(«an accepting transcript hands the condition on» over the one equation's piece) AT THAT MEANING.
Definitions, theorems, evaluations.

What is said.
  `keepsE`: the three readers of the verifier's state that this sub-protocol leaves: what goes on to
    the later chains, the frame between segments, «can the pending claim on the weights be made».
    `stepE A A'`: a Bool on two lists: each public item that is asked behind is asked in front, and
    is «the index masks' message is there» or reads `keepsE` alone. `pubHeld_stepE`: under its yes
    the public items hold behind, where the base's tests answer alike at the two states. `pubAtE`,
    `pubFitE M links ps`: the Bool along the written list, at the places of a one equation, with
    «none of the two items that say something beside their Bool is open behind, and each that is
    open behind is «hasRow» or one to which the table `First.saysNone` gives «no sentence is meant»»
    (`notLeft`, PubFitK9.lean); `fitE_at`; `pubFitE_full`: the kernel's yes at the composed filling
    and the full list; `pubAsksE_full`: 25 numbers; `pubFitE_bent`: a negative test: with the places
    of the second segment's one equation and of the frame's sub-protocol in front of it changed
    over: no. `EqAsks`: what is asked of the parameters and of the frame's numbering. `mgRides_eq`:
    **`MgRides Nm (mgAll 𝔇 mgBase) links pl z k p a b` over the one equation's piece.** `hon3_mg`:
    **hon3 at the composed meaning.**

Limits. PREMISES THAT STAY, in `EqAsks`: `OracleAsks` (a fence on the plan's numbers; the committed
table's decoder and the OOD samples' reader answer alike at the two states): by nobody; «no message
of the link's own is the index masks' message»: by nobody. In hon3_mg beside: the table's own test
on the plan's numbers (`rowsAtFit`); the plan's two counts; hg («the group that the link's context
names is the plan's group of the segment»): NOTHING HERE MAKES IT: it is asked of the promise in
front, which does not give it; other files have the fact along the fold; the bridge from there to
this premise is GroupBridge.lean's. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.MgRidesAt
import Johnson.Desc.First.Link.Law.DoorBlind
import Johnson.Desc.First.Link.Law.OpensRides
import Johnson.Desc.First.Link.Law.EqNumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where messageNow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub PubData More Meaning Numbers Rdr SameOn footOf
  pubAll pubAll_same pubAll_indexThere pubHeld pubOfItems flatPlacesOf start openSets stepOpen rowOf
  pubSets pubStep pubRowM rowsAtFit)
open _root_.Run.PQ (CK)

/-- The three readers that the one equation's sub-protocol leaves. -/
def keepsE : List Rdr := [.out, .frame, .row]

/-- Is the item «the index masks' message is there»? -/
def isThere : Pub → Bool
  | .indexThere => true
  | _ => false

/-- **A Bool on two lists**: A: what is asked in front; A': behind. -/
def stepE (A A' : List Pub) : Bool :=
  A'.all fun q => A.contains q && (isThere q || (foot0 q).any fun R => R.all keepsE.contains)

/-- **THE PUBLIC ITEMS HOLD BEHIND.** -/
theorem pubHeld_stepE {P W : Type} (Mg : Meaning P W) (D : PubData) (base : Pub → P × S → Bool)
    (hpub : Mg.pub = pubAll D base) (O O' : List Item) (Q Q' : List Pub) (z : P) (s s' : S)
    (hB : stepE (Q ++ pubOfItems O) (Q' ++ pubOfItems O') = true) (hs : SameOn D keepsE s s')
    (hb : ∀ q, base q (z, s') = base q (z, s))
    (ht : ∀ j : ℕ, (s'.st.oracles[j]?).isSome = (s.st.oracles[j]?).isSome)
    (h : pubHeld Mg O Q (z, s) = true) : pubHeld Mg O' Q' (z, s') = true := by
  unfold pubHeld at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro q hq
  obtain ⟨hin, h3⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 hB q hq)
  have hfront := h q (by simpa using hin)
  rw [hpub] at hfront ⊢
  rcases Bool.or_eq_true_iff.1 h3 with hth | hfoot
  · cases q with
    | indexThere =>
      rw [pubAll_indexThere] at hfront ⊢
      have ho : s'.out = s.out := hs .out (by simp [keepsE])
      show (s'.st.oracles[s'.out.indexMasks]?).isSome = true
      rw [ho, ht]
      exact hfront
    | _ => simp [isThere] at hth
  · have e0 := foot_at D keepsE (by decide) q hfoot
    cases hf : foot0 q with
    | none => simp [hf] at hfoot
    | some R =>
      rw [hf] at hfoot e0
      have h4 : R.all keepsE.contains = true := hfoot
      rw [pubAll_same D base q R e0 z s s' (fun r hr => hs r (by
        have := List.all_eq_true.1 h4 r hr
        simpa using this)) (hb q)]
      exact hfront

/-- **The test at number k of the list.** -/
def pubAtE (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 3 then
        stepE
          ((pubSets M links ps)[k]?.getD [] ++
            pubOfItems ((openSets links ps (start links))[k]?.getD []))
          (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) ++
            pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p)))
          && (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p)).all notLeft
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def pubFitE (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (pubAtE M links ps)

/-- **THE FACT AT A PLACE.** -/
theorem fitE_at (M : More) (links : List ModelPart) (ps : List Place) (h : pubFitE M links ps = true)
    (k m : ℕ) (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3) :
    stepE
      ((pubSets M links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []))
      (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) ++
        pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))) =
      true ∧
    (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p)).all notLeft = true := by
  unfold pubFitE at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold pubAtE at h0
  rw [hp] at h0
  simpa [hl, hpc] using h0

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE COMPOSED FILLING AND THE FULL LIST.** -/
theorem pubFitE_full : pubFitE moreAll fullList (flatPlacesOf fullList true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE TEST ASKS SOMETHING AT 25 NUMBERS OF THE FULL LIST.** -/
theorem pubAsksE_full : ((List.range (flatPlacesOf fullList true).length).filter
    (listAsks fullList (flatPlacesOf fullList true))).length = 25 := listAsks_full

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: THE SECOND SEGMENT's ONE EQUATION AND THE FRAME's SUB-PROTOCOL IN FRONT OF IT
CHANGED OVER.** -/
theorem pubFitE_bent :
    pubFitE moreAll fullList (swapAt (flatPlacesOf fullList true) 24) = false := by
  decide +kernel

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- **What is asked of the parameters and of the frame's numbering.** -/
structure EqAsks (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k base : ℕ)
    (s s' : S) : Prop where
  oracle : OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k base s s'
  /-- no message of the link's own is the index masks' message -/
  own : ∀ a, atS.get? s = some a → ∀ m o,
    messageNow a.L.check.frame a.L.check.frame.link m = some o → o ≠ s.out.indexMasks

/-- **MgRides OVER THE ONE EQUATION's PIECE.** -/
theorem mgRides_eq (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p : Place) (hfit : pubFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C pe.ds)) (hout : pe.ior.red.out a τ = some b)
    (A : EqAsks 𝔇 Nm links pl z k pe.base a.1 b.1) :
    MgRides Nm (mgAll 𝔇 mgBase) links pl z k p a b := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  have hb := out_strs hout
  have hmore : (mgAll 𝔇 mgBase).more = moreAll := mgAll_more_base 𝔇
  obtain ⟨hB, hnl⟩ := fitE_at moreAll links pl hfit k m p hp hl hpc
  obtain ⟨a0, out, _, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ j (hb₃ _ _ _ _ _ hstep)
  have hsame : SameOn 𝔇.pubD keepsE a.1 b.1 := by
    intro r hr
    simp only [keepsE, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · show b.1.out = a.1.out
      rw [hs']
      exact out_set a.1 _
    · show b.1.check.frame = a.1.check.frame
      rw [hs']
      exact congrArg (·.frame) (check_set a.1 _)
    · exact fun lay n lin => eq_hasRow pw b₃ hb₃ _ _ _ _ _ j hstep A.own lay n lin
  refine ⟨fun h => ?_, fun h => h, ?_, ?_, fun x _ h => ?_, fun x hx h => ?_, fun x hx h => ?_⟩
  · rw [mgAll_decodes] at h ⊢
    rw [hb]
    exact dec_rides 𝔇.decT z a.1 b.1 pe.base pe.ds a.2 τ A.oracle.dec h
  · rw [hmore]
    exact pubHeld_stepE (mgAll 𝔇 mgBase) 𝔇.pubD _ (mgAll_pub 𝔇 mgBase) _ _ _ _ z a.1 b.1 hB hsame
      (fun _ => rfl) (eq_there pw b₃ hb₃ _ _ _ _ _ j hstep)
  · rw [hmore]
    intro _ q hq
    have h1 := List.all_eq_true.1 hnl q hq
    cases q with
    | left _ => simp [notLeft] at h1
    | leftOn _ => simp [notLeft] at h1
    | hasRow _ => trivial
    | _ => exact mgAll_pubP_said 𝔇 _ _ h1
  · rw [mgAll_held] at h ⊢
    show smpHeld b.1.st b.1.book x.1 x.2 = true
    rw [eq_held pw b₃ hb₃ _ _ _ _ _ j hstep]
    exact h
  · rw [mgAll_shown] at h ⊢
    rw [hb]
    exact shown_rides 𝔇.cs 𝔇.G 𝔇.ms x.1 x.2 pe.base (A.oracle.fence x hx) pe.ds a.2 τ h
  · rw [mgAll_noColl] at h ⊢
    rw [hb]
    exact noColl_rides 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms z a.1 b.1 x.1 x.2 pe.base (A.oracle.fence x hx) pe.ds
      a.2 τ A.oracle.smp h

/-- **hon3 AT THE COMPOSED MEANING.** -/
theorem hon3_mg (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k m : ℕ)
    (p p' : Place) (hfit : linkFit links pl = true) (hlf : listFit links pl = true)
    (hpf : pubFitE moreAll links pl = true) (hN : rowsAtFit Nm links.length = true)
    (hml : m < links.length) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃)
    (hg : ∀ a : S × F.E.Str, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      ∀ x, atS.get? a.1 = some x → Nm.groupAt m = x.L.check.group)
    (A : ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pe.ior.red.out a τ = some b → EqAsks 𝔇 Nm links pl z k pe.base a.1 b.1) :
    ∀ a τ b, onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) k a →
      pe.ior.red.out a τ = some b →
      onT Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) (k + 1) b := by
  obtain ⟨⟨n1, n2⟩, hins, houts, fresh, seg⟩ := fit_eq links pl hfit k m p p' hp hp' hl hpc
  obtain ⟨hat, inj⟩ := numbers_of_fit Nm links pl hN hlf k m p hp hl hpc hml
  exact hon3_at Nm (mgAll 𝔇 mgBase) links pl z k m p p' hp hp' ⟨n1, n2⟩ hins houts fresh seg hat
    inj ht hm pw b₃ hb₃ pe hpe hg fun a τ b ha hout =>
      mgRides_eq 𝔇 Nm links pl z k m p hpf hp hl hpc pw b₃ hb₃ pe hpe a b τ hout (A a τ b ha hout)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pubHeld_stepE
#print axioms VerifiableInference.Desc.LinkJoin.pubFitE_full
#print axioms VerifiableInference.Desc.LinkJoin.pubFitE_bent
#print axioms VerifiableInference.Desc.LinkJoin.mgRides_eq
#print axioms VerifiableInference.Desc.LinkJoin.hon3_mg
