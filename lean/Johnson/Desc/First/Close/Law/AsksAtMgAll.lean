-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AsksAtMgAll.lean (kind K10): WHAT K10's SECOND TIE ASKS OF A MEANING
(`K10AsksR`, AsksOfMgR.lean, beside this file) HOLDS AT THE COMPOSED MEANING OVER THE CLOSED BASE
(`mgAll Dm mgBase`), UNDER THE FENCE "the index masks' message is a member of no group"; AND
"decodes" RIDES THERE AT EVERY STATE. Definitions, statements and proofs. After the proof of
`mgRides_eq` (Johnson/Desc/First/Link/Law/EqMg.lean), which does the like at the one equation.

  `closeLedgers_map`, `behind_tri`: the statement behind a closing gives, at every message, the same
    shape, the same mark "sampled" and the same sample rows (`tri`,
    Johnson/Desc/First/Link/Law/DoorBlind.lean): a closing turns ledgers and the mark "spent as a
    mask" alone.
  `k10_held`: along `K10Step s s'`: "the state holds the OOD sample" (`smpHeld`) is as it was.
  `OutF s`: the fence: the index masks' message is a member of no group of s.st.
  `saidFitK M links ps`: a test with code on the table's lists: at every place of the kind K10 every
    public item that the rows hold open behind is one without a sentence of its own, or "the pending
    claim on the weights can be made" (`notLeft`, PubFitK9.lean). `saidK_at`: what its yes gives at
    a place.
  `k10_dec_mg`: where the decoder of the committed table reads nothing of the verifier's state (hd):
    (mgAll Dm Mg).decodes rides from (z, s) to (z, s') at ALL s, s', along `Behind F base`. It is
    `K10CondAt`'s field dec (KindK10.lean).
  `k10_asksR_mg`: `pubFitK`'s and `saidFitK`'s yes at `moreAll`; pl[k]? = some p of the kind K10;
    hO: at every fenced step what the four riders on oracles take (`OracleAsks`, OracleRides.lean:
    every sampled tenant sits in a tree below base; the decoder and the reader of the OOD samples
    answer alike at the two states): THEN `K10AsksR OutF Nm (mgAll Dm mgBase)` at the k-th and (k +
    1)-th open sets and public sets, at `Behind F base`: `K10CondAt`'s field asks.
Limits. hd AND hO ARE PREMISES on the structure of parameters Dm (other files pay their
like at the closed constant). The two tests' yes are premises here. The fence is owed at reached
states. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AsksOfMgR
import Johnson.Desc.First.Close.Law.EPubAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (tri smpHeld_same notLeft OracleAsks dec_rides shown_rides
  noColl_rides)
open VerifiableInference.Desc.First (ModelPart Pub More Numbers start pubSets openSets sampledIn)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- Closing ledgers turns nothing that does not read a ledger. -/
theorem closeLedgers_map {β : Type} (f : OnBytes.Oracle → β)
    (hf : ∀ (x : OnBytes.Oracle) l, f { x with ledger := l } = f x) :
    ∀ (l : List ℕ) (T : Statement) (o : ℕ),
      ((closeLedgers T l).oracles[o]?).map f = (T.oracles[o]?).map f
  | [], _, _ => rfl
  | i :: l, T, o => by
    show ((closeLedgers { T with oracles := T.oracles.modify i fun x =>
      { x with ledger := x.ledger.map fun l => { l with closed := true } } } l).oracles[o]?).map
        f = _
    rw [closeLedgers_map f hf l]
    exact map_modify f _ i o _ fun x => hf x _

/-- Behind a closing: each message with its shape, its mark "sampled" and its sample rows. -/
theorem behind_tri (T : Statement) (g : ℕ) (G : Group) (id o : ℕ) :
    ((spent (begun T g G) id).oracles[o]?).map tri = (T.oracles[o]?).map tri := by
  show (((closeLedgers T G.members.toList).oracles.modify id _)[o]?).map _ = _
  exact (map_modify tri _ id o (fun x : OnBytes.Oracle => { x with spentAsMask := true })
    fun _ => rfl).trans (closeLedgers_map tri (fun _ _ => rfl) _ T o)

/-- **"The state holds the OOD sample" is as it was.** -/
theorem k10_held {s s' : VerifiableInference.Desc.First.S} (hs : K10Step s s') (j t : ℕ) :
    smpHeld s'.st s'.book j t = smpHeld s.st s.book j t := by
  obtain ⟨es, rs, x, hx, rfl⟩ := hs
  obtain ⟨G, id, -, -, e⟩ := closeFrame_st hx
  rw [(putRec_keeps s ⟨none, x.1, x.2⟩).1]
  show smpHeld x.2 s.book j t = _
  rw [e]
  exact smpHeld_same _ _ _ ⟨behind_codes _ _ G id, fun o => behind_tri _ _ G id o⟩ j t

/-- The fence. -/
def OutF (s : VerifiableInference.Desc.First.S) : Prop :=
  ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members

/-- **The test along the list**: what the rows hold open behind K10 has no sentence to ride. -/
def saidFitK (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k => (ps[k]?).all fun p => p.kind != KindName.K10 ||
    ((pubSets M links ps)[k + 1]?.getD []).all notLeft

/-- The fact at a place. -/
theorem saidK_at (M : More) (links : List ModelPart) (ps : List Place) (h : saidFitK M links ps = true)
    (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∀ q ∈ (pubSets M links ps)[k + 1]?.getD [], notLeft q = true := by
  unfold saidFitK at h
  have h0 := List.all_eq_true.1 h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  rw [hp] at h0
  simp only [Option.all_some, hK, bne_self_eq_false, Bool.false_or] at h0
  exact fun q hq => List.all_eq_true.1 h0 q hq

section
variable {F : Frame} {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)

/-- **"decodes" rides at every state**, where the decoder reads nothing of the state. -/
theorem k10_dec_mg (Mg : VerifiableInference.Desc.First.Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (base : ℕ) (hd : ∀ c z (s s' : VerifiableInference.Desc.First.S),
      Dm.decT c (z, s') = Dm.decT c (z, s)) :
    ∀ z (s s' : VerifiableInference.Desc.First.S) y y', Behind F base y y' →
      (mgAll Dm Mg).decodes (z, s) y → (mgAll Dm Mg).decodes (z, s') y' := by
  rintro z s s' _ _ ⟨ds, u, τ, rfl, rfl⟩ h
  rw [mgAll_decodes] at h ⊢
  exact dec_rides Dm.decT z s s' base ds u τ (fun c => hd c z s s') h

/-- **WHAT K10's SECOND TIE ASKS, AT THE COMPOSED MEANING OVER THE CLOSED BASE.** -/
theorem k10_asksR_mg (Nm : Numbers) (links : List ModelPart) (pl : List Place) (k base : ℕ)
    (p : Place) (hfit : pubFitK moreAll links pl = true)
    (hsaid : saidFitK moreAll links pl = true) (hp : pl[k]? = some p)
    (hK : p.kind = KindName.K10)
    (hO : ∀ z s s', OutF s → K10Step s s' →
      OracleAsks Dm.cs Dm.decT Dm.smp Nm links pl z k base s s') :
    K10AsksR OutF Nm (mgAll Dm mgBase) ((openSets links pl (start links))[k]?.getD [])
      ((openSets links pl (start links))[k + 1]?.getD [])
      ((pubSets (mgAll Dm mgBase).more links pl)[k]?.getD [])
      ((pubSets (mgAll Dm mgBase).more links pl)[k + 1]?.getD []) (Behind F base) := by
  have hmore : (mgAll Dm mgBase).more = moreAll := mgAll_more_base Dm
  rw [hmore]
  refine ⟨?_, fun _ _ _ _ _ _ h => h, ?_, ?_, ?_, ?_⟩
  · rintro z s s' _ _ hf hs ⟨ds, u, τ, rfl, rfl⟩ h
    rw [mgAll_decodes] at h ⊢
    exact dec_rides Dm.decT z s s' base ds u τ (hO z s s' hf hs).dec h
  · intro z s s' hf hs _ h
    exact e_k10 Dm.pubD mgBase.pub links pl z (fun _ _ _ => rfl) k p hfit hp hK s s' hs hf h
  · intro z s s' _ _ _ _ q hq
    have h1 := saidK_at moreAll links pl hsaid k p hp hK q hq
    cases q with
    | left _ => simp [notLeft] at h1
    | leftOn _ => simp [notLeft] at h1
    | hasRow _ => trivial
    | _ => exact mgAll_pubP_said Dm _ _ h1
  · intro z s s' _ hs _ x _ h
    rw [mgAll_held] at h ⊢
    show smpHeld s'.st s'.book x.1 x.2 = true
    rw [k10_held hs]
    exact h
  · rintro z s s' _ _ hf hs ⟨ds, u, τ, rfl, rfl⟩ _ x hx ⟨h1, h2⟩
    have A := hO z s s' hf hs
    rw [mgAll_shown] at h1 ⊢
    rw [mgAll_noColl] at h2 ⊢
    exact ⟨shown_rides Dm.cs Dm.G Dm.ms x.1 x.2 base (A.fence x hx) ds u τ h1,
      noColl_rides Dm.cs Dm.G Dm.smp Dm.ms z s s' x.1 x.2 base (A.fence x hx) ds u τ A.smp h2⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.behind_tri
#print axioms VerifiableInference.Desc.First.Close.k10_held
#print axioms VerifiableInference.Desc.First.Close.k10_dec_mg
#print axioms VerifiableInference.Desc.First.Close.k10_asksR_mg
