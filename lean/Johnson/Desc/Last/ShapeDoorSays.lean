-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorSays.lean: SH₃ (the premise on `PL.shape 0` of the joint between the
shared and the last chain) AT THE SEATED DESCRIPTION'S OWN START, FROM WHAT THE FIRST TABLE'S
MEANING SAYS AT FIVE NAMES AND OF THE OUT-OF-DOMAIN (OOD) SAMPLES. One small definition, one
structure of premises, statements and proofs. IT OVERTAKES THE ROAD BY THE ONE ITEM "K13.doorFirst"
(Johnson/Desc/First/FillDoor.lean; `sh₃_at_texts` to `sh₃_at_pub_X`): what that item's six tests ask
rides under names of its own.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`DoorSays N₁ Mg₁ links ps Pw V`**: THE DOOR'S PREMISES OVER A LETTER Mg₁, GATHERED. WHAT IS
    SAID: tidy: `Mg₁.inOrder a = true` gives `Means.tidy4B a.2.st` · fits, weights, laid, sits:
    `Mg₁.pub` at "K12.bookFits", "K13.weightsOk", the table's own `evalLaid`, "K13.ownSits" is
    `bookFitsB a.2.book`, `First.weightsB a.2`, `K13.Law.evalLaidB Pw a.2`, `ownSitsB V a.2` · held:
    `Mg₁.held j t a` is `smpHeld a.2.st a.2.book j t`. WHAT IS OPEN AT THE FIRST CHAIN'S LAST
    BORDER: fitsOpen, weightsOpen, laidOpen, sitsOpen: the four public items · indexIn, wIn: the
    plan's two places `V.index`, `V.w` are among the sampled tenants of the open items. ON THE PLAN:
    oneIndex, oneW: the plan's two shapes count one answer. `nFitsName`: the first of the names, as
    a sister layer spells it.
  `ocEnd_inOrder`: at a verifier's state without a mark the first chain's last promise holds "in
    order". `two_of_ownTwoB`: what `ownTwoB` says where something is handed.
    **`doorFirstB_of_says`**: under `DoorSays`, inside `ocEnd`, at a state without a mark:
    `doorFirstB` (by `doorFirstB_of_items`, Johnson/Desc/Last/ShapeDoorItems.lean;
    `ownTwoB_of_sits`, Johnson/Desc/Last/ShapeTwoOfSits.lean; `ocEnd_held`,
    Johnson/Desc/Last/ShapeDoorHeld.lean).
  `sh₃_of_first`: SH₃'s line at PLm := `fillZ …` from the two texts, wherever they come from: Oc a
    letter. **`sh₃_says_X`**: at the seated start (`ProofFile.seatedAt o Z Np c`), p := `ProofFile.pAt Z`, Pm :=
    `besideP Pm₀ fun k d => doorX p K k d && (k != K || X d)`, Oc := `ocEnd g N₁ Mg₁ links ps`:
    `PLm.shape 0 … = true` and `X b.1.2 = true`. ITS PREMISES: hZ (Z is the computed public part) ·
    hg (the reader's second half is the state) · H : `DoorSays`. **`pub_at_door`**: THE SLOT FOR
    FURTHER FACTS ON THE FIRST CHAIN'S LAST STATE: at the seated start's yes every public item that
    is open at that chain's last border holds of its last state.

Every "there is": none in a conclusion.
WHO COULD PAY `DoorSays`, FIELD BY FIELD (others' words; nothing of it is held here). tidy: by the
make where "in order" is laid as a layer in other files lays it. fits, weights, sits: by the make at
the three layers (the sister layers' lemmas; `fillWeights_weights`). laid, held: by the make at the
layers of kind K13's files and of the table's files. The four "open":
`First.pubSets_last_of_start`, `pubSets_last_of_made` (Johnson/Desc/First/BordersKept.lean), where
no row of the merged filling drops the names; for `evalLaid` the like in kind K13's files. indexIn,
wIn: where `pinI` and `pinV` are open at the last border and V's places are the table's numbers
`N₁.index`, `N₁.w`: an evaluation of the table. oneIndex, oneW: facts on the plan.
Limits. (1) WHAT THE NAMES SAY MUST BE EARNED AND KEPT ALONG THE FIRST CHAIN: that is each name's
own debt; "K13.ownSits" is earned by nobody yet. (2) `nFitsName` is tied to the sister layer's name
by no term: a misspelling fails shut (fits and fitsOpen cannot both be paid). (3) N, Pm₀, Mg₁, N₁,
links, ps, Pw, V, split, T, R, g, X are letters. (4) NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorWithX
import Johnson.Desc.Last.ShapeDoorItems
import Johnson.Desc.First.FillOwnSits
import Johnson.Desc.Last.ShapeTwoOfSits
import Johnson.Desc.Last.ShapeDoorHeld
import Johnson.Desc.First.FillWeights
import Johnson.Desc.K13.Law.Bools

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open OnBytes

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub MoreName moreItem nSits nWeights
  pubSets weightsB openSets sampledIn)
open _root_.Desc.K14 (St)

/-- The name under which "the first chain's book fits" rides (a sister layer's item). -/
def nFitsName : MoreName := (none, "K12.bookFits")

/-- **WHAT THE DOOR ASKS OF THE FIRST TABLE's MEANING AND TABLE, AND OF THE PLAN**, gathered: what
six things say; what is open at the chain's last border; one answer at the plan's two shapes. -/
structure DoorSays {P₀ W₁ : Type} (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart)
    (ps : List Place) (Pw : K13.Where) (V : OwnSeats) : Prop where
  tidy : ∀ a, Mg₁.inOrder a = true → Means.tidy4B a.2.st = true
  fits : ∀ a, Mg₁.pub (moreItem nFitsName) a = bookFitsB a.2.book
  weights : ∀ a, Mg₁.pub (moreItem nWeights) a = weightsB a.2
  laid : ∀ a, Mg₁.pub .evalLaid a = K13.Law.evalLaidB Pw a.2
  sits : ∀ a, Mg₁.pub (moreItem nSits) a = ownSitsB V a.2
  held : ∀ j t a, Mg₁.held j t a = smpHeld a.2.st a.2.book j t
  fitsOpen : moreItem nFitsName ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []
  weightsOpen : moreItem nWeights ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []
  laidOpen : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []
  sitsOpen : moreItem nSits ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []
  indexIn : V.index ∈ sampledIn N₁ ((openSets links ps (First.start links))[ps.length]?.getD [])
  wIn : V.w ∈ sampledIn N₁ ((openSets links ps (First.start links))[ps.length]?.getD [])
  oneIndex : V.indexShape.answers = 1
  oneW : V.wShape.answers = 1

/-- At a state without a mark the first chain's last promise holds "in order". -/
theorem ocEnd_inOrder {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) : Mg₁.inOrder (get p) = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h'.1).1).1).2

/-- What `ownTwoB` says where something is handed, in the shape of `doorFirstB_of_items`' h2. -/
theorem two_of_ownTwoB {s : First.S} (h : ownTwoB s = true) (hsome : (firstOfS s).isSome = true) :
    ∀ l G, K13.Law.linAt s = some l → s.st.groups[l.own]? = some G →
      G.members.size = 2 ∧ ∀ i ∈ G.members.toList, ∃ x, s.st.oracles[i]? = some x ∧
        x.sampleRows.size = 1 := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨l₀, hl₀, e1, -, e3⟩ := firstOfS_at hf
  intro l G hl hG
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  unfold ownTwoB at h
  rw [hf] at h
  have h' : (match f.st.groups[f.own]? with
    | some G => G.members.size == 2 && G.members.toList.all fun i =>
        match f.st.oracles[i]? with
        | some x => x.sampleRows.size == 1
        | none => false
    | none => false) = true := h
  rw [e1, e3, hG] at h'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h'
  refine ⟨h'.1, fun i hi => ?_⟩
  have h2 := h'.2 i hi
  cases hx : s.st.oracles[i]? with
  | none =>
    rw [hx] at h2
    cases h2
  | some x =>
    rw [hx] at h2
    exact ⟨x, rfl, by simpa using h2⟩

/-- **THE FIRST CHAIN's TEXT AT THE DOOR, OUT OF THAT CHAIN's LAST PROMISE.** -/
theorem doorFirstB_of_says {A P₀ W₁ : Type} (get : A → P₀ × First.S) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where) (V : OwnSeats)
    (H : DoorSays N₁ Mg₁ links ps Pw V) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) : doorFirstB (get p).2 = true := by
  have pb := fun q hq => ocEnd_pub get N₁ Mg₁ links ps p y h hm q hq
  have t1 := H.tidy _ (ocEnd_inOrder get N₁ Mg₁ links ps p y h hm)
  have t2 := pb _ H.fitsOpen
  have t3 := pb _ H.weightsOpen
  have t4 := pb _ H.laidOpen
  have t5 := pb _ H.sitsOpen
  have t6 := ocEnd_held get N₁ Mg₁ links ps p y h hm _ H.indexIn
  have t7 := ocEnd_held get N₁ Mg₁ links ps p y h hm _ H.wIn
  rw [H.fits] at t2
  rw [H.weights] at t3
  rw [H.laid] at t4
  rw [H.sits] at t5
  rw [H.held] at t6 t7
  have t8 := ownTwoB_of_sits t5 t2 t6 t7 H.oneIndex H.oneW
  cases hs : (firstOfS (get p).2).isSome with
  | false =>
    unfold doorFirstB
    rw [Option.isSome_eq_false_iff.1 hs |> Option.isNone_iff_eq_none.1]
  | true =>
    exact doorFirstB_of_items t1 t2 t3 ((K13.Law.evalLaidB_iff Pw _).1 t4) (two_of_ownTwoB t8 hs)

/-- **SH₃ FROM THE TWO TEXTS, WHEREVER THEY COME FROM**: Oc is a letter; hfirst: inside it, at a
state without a mark, the first chain's text holds. -/
theorem sh₃_of_first {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ P₀ X₁ X₂ Cl Wt : Type}
    (p : P₁₄) (R : List Fmt.DeclaredRound) (get : P × S₁ → P₀ × First.S)
    (start₃ : P → S₁ → St → Option S₃)
    (T : Three C D all Y (P × S₁) ((P × S₁) × St) ((P × S₁ × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm : PromMeaning St) (Oc : P × S₁ → Strs → Prop) (split : Bool)
    (hPm : ∀ d, Pm.shape (1 + T.l₂.length) d = true → doorSharedB p d = true)
    (hfirst : ∀ q y, Oc q y → (get q).2.failed = none → doorFirstB (get q).2 = true)
    (hmark : ∀ q s₁ d s, start₃ q s₁ d = some s → (get (q, s₁)).2.failed = none)
    (hstart : ∀ q s₁ d s, start₃ q s₁ d = some s →
      ∃ e, _root_.Desc.K14.ended d = some e ∧ startAtEnds p q (get (q, s₁)).2 e = .ok s)
    (ahead : p.S.masksAhead = true)
    (b : ((P × S₁) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : start₃ b.1.1.1 b.1.1.2 b.1.2 = some s) :
    (fillZ p R fun q => (get q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true := by
  refine door_fillZ_less (On₂ := onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length))
    (start₃ := start₃) ⟨?_, ?_, hstart, ahead⟩ b s hb hs
  · intro b s hb hs f hf
    exact firstSix_of_text (hfirst b.1.1 _ hb.2 (hmark b.1.1.1 b.1.1.2 b.1.2 s hs)) hf
  · intro b s hb _ e he
    have hmem : PromS.shape (1 + T.l₂.length) ∈ promsAt split (1 + T.l₂.length) := by
      unfold promsAt
      simp
    exact sharedDoor_of_text (hPm _ (hb.1 _ hmem)) he

/-- **SH₃'s CONCLUSION AND X, AT THE SEATED START AND A COMPUTED PUBLIC PART, FROM WHAT THE FIRST
TABLE's MEANING SAYS AT FIVE NAMES.** -/
theorem sh₃_says_X {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where)
    (V : OwnSeats) (H : DoorSays N₁ Mg₁ links ps Pw V) (X : St → Bool)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ fun k d => doorX (ProofFile.pAt Z) (1 + T.l₂.length) k d &&
        (k != 1 + T.l₂.length || X d))
      (ocEnd g N₁ Mg₁ links ps) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true ∧
      X b.1.2 = true := by
  refine ⟨?_, x_at_last N Pm₀ _ split T.p₂ T.l₂ (ProofFile.pAt Z) (1 + T.l₂.length) X b hb⟩
  refine sh₃_of_first (ProofFile.pAt Z) R g
    (fun q a d => ((ProofFile.seatedAt o Z Np c).start₃ q a d).toOption) T N _ _ split (fun d hd => ?_)
    (fun q y hq hm => doorFirstB_of_says g N₁ Mg₁ links ps Pw V H q y hq hm)
    (ProofFile.hmark_at o Z Np c g hg) (ProofFile.hstart_at o Z Np c g hg) (ahead_at_seat hZ) b s hb hs
  have h' : (Pm₀.shape (1 + T.l₂.length) d && (doorX (ProofFile.pAt Z) (1 + T.l₂.length)
      (1 + T.l₂.length) d && (1 + T.l₂.length != 1 + T.l₂.length || X d))) = true := hd
  have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').2).1
  rw [doorX_at] at h2
  exact h2

/-- **THE DOOR's SLOT FOR FURTHER FACTS ON THE FIRST CHAIN's LAST STATE**: at the seated start's
yes, inside the shared chain's promise, every public item that is open at the first chain's last
border holds of that chain's last state. (For facts on the shared chain's last state: X,
above.) -/
theorem pub_at_door {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Pub) (hq : q ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N Pm (ocEnd g N₁ Mg₁ links ps) split T.p₂ T.l₂ k b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    Mg₁.pub q (g b.1.1) = true :=
  ocEnd_pub g N₁ Mg₁ links ps b.1.1 _ hb.2
    (ProofFile.hmark_at o Z Np c g hg b.1.1.1 b.1.1.2 b.1.2 s hs) q hq

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.pub_at_door
#print axioms VerifiableInference.Desc.Last.sh₃_of_first
#print axioms VerifiableInference.Desc.Last.sh₃_says_X
#print axioms VerifiableInference.Desc.Last.ocEnd_inOrder
#print axioms VerifiableInference.Desc.Last.two_of_ownTwoB
#print axioms VerifiableInference.Desc.Last.doorFirstB_of_says
