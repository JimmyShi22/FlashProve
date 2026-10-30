-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/StartsSized.lean: WHO STARTS "WITH ITS SIZES": PAID AT THE LINK's FRAME's OWN
TEXT: behind "opened", at each of the three sorts of opening that the frame has (an attention link;
a layers' link behind link 0; link 0), the carried record holds the ledger `startFork X ns`, AND
THAT LEDGER HAS ITS SIZES; nothing is heard yet by the lookup on the calls. Theorems with their
proofs. OVER State.lean AND THE FRAME's TEXTS;
BY THESE TEXTS ALONE: it leans on no law file of another kind's.

THE TEXTS:
Johnson/Desc/First/Walk/Frame.lean · FrameZero.lean · FirstQuiet.lean
· LinkZero.lean · Quiet.lean; Johnson/Desc/First/State.lean.

Why. `RanAtOfLink` | `RanAtToSettling` (Johnson/Desc/Sound/FoldSteps.lean) and the roads behind them
KEEP "with its sizes" from the record behind a hearing place's decision on; they do not start it.
The kind "lookup"'s own tie gives the sizes behind its decision from the sizes in front. In front
stands the place that opens the ledger: its share is what this file shows.

  `startFork_sized`: `Sized (startFork X ns)`: at every public record X and number ns.
    `startFork_next`: its next free slot is the planned ledger's.
  `attQuietF`, `layQuietF`, `layQuietZeroF`: what the three quiet steps lay as the ledger is
    `startFork X ns`: by their texts.
  `openAtt_is`, `openLay_is`, `openLayZero_is`: where "opened" goes on, to t: t's ledger is
    `startFork P.X P.ns`, and `t.lookHeard? = none`.
  `OpensSized f`: that, with the sizes, as a property of a function on the record; `sizedBehind`: A
    BLOCK THAT ENDS IN SUCH A FUNCTION (two blocks at one place by `Block.andThen`, the second the
    frame's `openedBlock`) leaves a ledger with its sizes wherever its decision goes on.
  `foldStartsSized`: OF THE FOLD ALONE: where the fold over laid :: [p.andThen name (openedBlock …
    f)] goes on, to t: t holds a ledger with its sizes, and nothing is heard there.
  `tracedStartsSized`: JOINED WITH A TRACE (`Traced`).

Limits. A frame's law: no error; nothing on soundness. The head's link is opened otherwise
(`S.openHead`; its ledger is laid by other steps): NOT HERE. That the first place of a real link IS
‹the first call's block›.andThen … (openedBlock …) is not shown here. No
yes of "opened" is shown by evaluation here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Walk.FrameZero
import Johnson.Desc.First.LedgerAtFo
import Johnson.Desc.Sound.StepsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock Link Traced foldBlocks OpenedColumn bindOk foldConsOk stepOk)
open VerifiableInference.Desc.First (S)
open OnBytes.PscRun (Sized)

/-- **The ledger from which a sub-proof starts has its sizes.** -/
theorem startFork_sized (X : LinkPub) (ns : Nat) : Sized (startFork X ns) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [startFork, emptySlots]

theorem startFork_next (X : LinkPub) (ns : Nat) : (startFork X ns).next = X.Fp.next := rfl

/-! ## What the three quiet steps lay as the ledger: by their own texts -/

theorem attQuietF {X : LinkPub} {l ns : Nat} {tl₀ : HTailF2} {check : ChainCheck}
    {out : Proof.LinksResult} {a : AttStart} (h : attFirstQuiet X l ns tl₀ check out = .ok a) :
    a.F = startFork X ns := by
  unfold attFirstQuiet at h
  repeat' split at h
  all_goals first | rw [← Except.ok.inj h] | exact nomatch h

theorem layQuietF {X : LinkPub} {l : Nat} {p4 : Bool} {g : Nat} {Tp : Tail2} {Fp : Fork} {ns : Nat}
    {check : ChainCheck} {out : Proof.LinksResult} {a : LayStart}
    (h : layFirstQuiet X l p4 g Tp Fp ns check out = .ok a) : a.F = startFork X ns := by
  unfold layFirstQuiet at h
  repeat' split at h
  all_goals first | rw [← Except.ok.inj h] | exact nomatch h

theorem layQuietZeroF {X : LinkPub} {p4 : Bool} {g : Nat} {Tp : Tail2} {Fp : Fork} {ns room : Nat}
    {check : ChainCheck} {out : Proof.LinksResult} {os : Array Oracle} {a : LayStart}
    (h : layFirstQuietZero X p4 g Tp Fp ns room check out os = .ok a) : a.F = startFork X ns := by
  unfold layFirstQuietZero at h
  repeat' split at h
  all_goals first | rw [← Except.ok.inj h] | exact nomatch h

/-! ## The record's two entries -/

theorem unmarkedOk {s t : S} (h : s.unmarked = .ok t) : t = s := by
  unfold S.unmarked at h
  split at h
  · exact (Except.ok.inj h).symm
  · exact nomatch h

theorem needTrue {name : String} {b : Bool} {u : Unit}
    (h : VerifiableInference.Desc.need name b = .ok u) : b = true := by
  unfold VerifiableInference.Desc.need at h
  split at h
  · assumption
  · exact nomatch h

theorem enterLay_fork (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) (hB : s.atBetween = true) :
    (S.enterLay s L F tl).fork? = some F ∧ (S.enterLay s L F tl).lookHeard? = none := by
  simp [S.enterLay, hB, S.fork?, S.lookHeard?]

theorem enterAtt_fork (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) (hB : s.atBetween = true) :
    (S.enterAtt s L F tl).fork? = some F ∧ (S.enterAtt s L F tl).lookHeard? = none := by
  simp [S.enterAtt, hB, S.fork?, S.lookHeard?]

/-! ## "opened" -/

theorem openAtt_is {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    t.fork? = some (startFork P.X P.ns) ∧ t.lookHeard? = none := by
  obtain ⟨_, hB, h⟩ := bindOk (x := VerifiableInference.Desc.need "B: a link is open in the record"
    s.atBetween) h
  obtain ⟨_, _, h⟩ := bindOk (x := VerifiableInference.Desc.need
    "A: the link's first call has not run" (firstRun s.check)) h
  obtain ⟨a, ha, h⟩ := bindOk (x := attFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out) h
  rw [unmarkedOk h, ← attQuietF ha]
  exact enterAtt_fork _ _ _ _ (needTrue hB)

theorem openLay_is {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    t.fork? = some (startFork P.X P.ns) ∧ t.lookHeard? = none := by
  obtain ⟨_, hB, h⟩ := bindOk (x := VerifiableInference.Desc.need "B: a link is open in the record"
    s.atBetween) h
  obtain ⟨_, _, h⟩ := bindOk (x := VerifiableInference.Desc.need
    "A: the link's first call has not run" (firstRun s.check)) h
  obtain ⟨a, ha, h⟩ := bindOk (x := layFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out) h
  rw [unmarkedOk h, ← layQuietF ha]
  exact enterLay_fork _ _ _ _ (needTrue hB)

theorem openLayZero_is {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    t.fork? = some (startFork P.X P.ns) ∧ t.lookHeard? = none := by
  obtain ⟨_, hB, h⟩ := bindOk (x := VerifiableInference.Desc.need "B: a link is open in the record"
    s.atBetween) h
  obtain ⟨_, _, h⟩ := bindOk (x := VerifiableInference.Desc.need
    "A: the link's first call has not run" (firstRun s.check)) h
  obtain ⟨a, ha, h⟩ := bindOk (x := layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol)
    s.check s.out s.st.oracles) h
  rw [unmarkedOk h, ← layQuietZeroF ha]
  exact enterLay_fork _ _ _ _ (needTrue hB)

/-! ## As a property of a function, of a block, and in a trace -/

/-- Where f goes on, the record behind holds a ledger with its sizes, and the lookup on the calls
has heard nothing. -/
def OpensSized (f : S → Except String S) : Prop :=
  ∀ s t, f s = .ok t → (∃ F, t.fork? = some F ∧ Sized F) ∧ t.lookHeard? = none

theorem opensAtt (P : AttPar) : OpensSized (openAtt P) :=
  fun _ _ h => ⟨⟨_, (openAtt_is h).1, startFork_sized _ _⟩, (openAtt_is h).2⟩

theorem opensLay (P : LayPar) : OpensSized (openLay P) :=
  fun _ _ h => ⟨⟨_, (openLay_is h).1, startFork_sized _ _⟩, (openLay_is h).2⟩

theorem opensLayZero (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    OpensSized (openLayZero P fvs kCol) :=
  fun _ _ h => ⟨⟨_, (openLayZero_is h).1, startFork_sized _ _⟩, (openLayZero_is h).2⟩

/-- **A block that ends in "opened" leaves a ledger with its sizes.** -/
theorem sizedBehind {Cl : Type} (p : Block S Cl) (name on : String) (l piece : Nat) (plan : Bool)
    (f : S → Except String S) (hf : OpensSized f) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (p.andThen name (openedBlock on l piece plan f)).decide s rs gs = .ok t) :
    (∃ F, t.fork? = some F ∧ Sized F) ∧ t.lookHeard? = none := by
  obtain ⟨m, _, h⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) h
  exact hf m t h

/-- **Of the fold alone**: where the fold over the link's first block and a place that ends in
"opened" goes on, to t: t holds a ledger with its sizes, and nothing is heard there.
(No whole trace is asked.) -/
theorem foldStartsSized {Cl : Type} {L : Link S Cl} (p : Block S Cl) (name on : String)
    (l piece : Nat) (plan : Bool) (f : S → Except String S) (hf : OpensSized f) {ft : Nat} {s t : S}
    {rs r : List Fmt.RoundView} {cols c : List Col}
    (hc : foldBlocks ft (L.laid :: [p.andThen name (openedBlock on l piece plan f)]) s rs cols =
      .ok (t, r, c)) :
    (∃ F, t.fork? = some F ∧ Sized F) ∧ t.lookHeard? = none := by
  obtain ⟨s₁, k₁, _, H₁⟩ := foldConsOk hc
  obtain ⟨s₂, k₂, hst, H₂⟩ := foldConsOk H₁
  obtain ⟨gs, hd⟩ := stepOk hst
  have e₂ : s₂ = t := congrArg Prod.fst (Except.ok.inj H₂)
  exact e₂ ▸ sizedBehind p name on l piece plan f hf _ _ _ _ hd

/-- **Joined with a trace**: the one place in front of b ends in "opened": then the record t in
front of b's decision holds a ledger with its sizes, and nothing is heard there. -/
theorem tracedStartsSized {Cl : Type} {R : S → S → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop} {L : Link S Cl} {b : Block S Cl}
    (p : Block S Cl) (name on : String) (l piece : Nat) (plan : Bool) (f : S → Except String S)
    (hf : OpensSized f) {ft : Nat} {s : S} {rs : List Fmt.RoundView} {cols : List Col}
    {t t₁ u₀ z u e : S} {cls : List Cl}
    (hT : Traced R Q L [p.andThen name (openedBlock on l piece plan f)] b ft s rs cols t t₁ u₀ z u e
      cls) :
    (∃ F, t.fork? = some F ∧ Sized F) ∧ t.lookHeard? = none := by
  obtain ⟨c, hc⟩ := hT.front
  exact foldStartsSized p name on l piece plan f hf hc

end Johnson.Desc.First.Walk

#print axioms Johnson.Desc.First.Walk.startFork_sized
#print axioms Johnson.Desc.First.Walk.opensAtt
#print axioms Johnson.Desc.First.Walk.opensLay
#print axioms Johnson.Desc.First.Walk.opensLayZero
#print axioms Johnson.Desc.First.Walk.sizedBehind
#print axioms Johnson.Desc.First.Walk.foldStartsSized
#print axioms Johnson.Desc.First.Walk.tracedStartsSized
