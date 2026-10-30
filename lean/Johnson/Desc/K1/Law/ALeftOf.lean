-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ALeftOf.lean: THE ARM aLeft OF k01_law: WHAT THE PUBLIC
ITEMS "left m" AND "leftOn m" SAY BESIDE THEIR BOOLS (Meaning.pubP) HOLDS BEHIND A YES OF EACH OF
THE FIFTY LATER BLOCKS OF KIND K1 (blkL: a link's digits, its reads), inside the promise in front.

  ledgerB_at_later   the Bool on the open ledger's sizes goes over a yes of commitAtS.
  k1Quiet_look       the reads' quiet block leaves the four readers of the state (LookSame).
  leftOn_blkL        the sentence of "leftOn m" over a yes of blkL Z G l d X arrs.
  inAt_pubP, inAt_pubQ   what the promise in front, unmarked, holds at an open public item.
  aLeftOn_of         the arm at q := leftOn m.
  aLeft_of           **the arm**, with its test on q as a letter isL.
HOW. leftOn_at_later, leftOn_quiet (Johnson/Desc/K1/Law/LeftOnAtLater.lean) · lookSame_layers,
_head, _att (Johnson/Desc/K1/Law/QuietLook.lean) through k1Quiet_decides
(Johnson/Desc/K1/Law/PileAtLater.lean) · the lookups' layer's pubP at "leftOn m" by rfl.
PREMISES THAT STAY, BY NAME.
  hP     Mg.pubP = (fillK3 X3 D3 Mg0).pubP · hMg  Mg.pub = pubAll D base (FillsK1's two fields).
  hled   ON THE TABLE: some "ledger m₀" is open in front of the place: its Bool is ledgerB, which
         leftOn_at_later asks of the state in front.
  hnl    ON THE TABLE: no "left m" is open in front of the place. (Of "left m" nothing is proved
         here: where one is open there, the arm is owed at it.)
  hisL   isL says yes at "left m" and "leftOn m" alone: at the top's isL := isLeft
         (Johnson/Desc/K1/Law/CallsB.lean) by cases.
         isLeft ITSELF IS NOT NAMED HERE: its file stands over
         Johnson/Desc/K1/Law/MgK1.lean, which this file does not import.
What is not claimed. hled, hnl at the table. That a block says yes. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LeftOnAtLater
import Johnson.Desc.K1.Law.QuietLook
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.First.PubAll
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.KeepAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers PubData pubAll ledgerB flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads k1Quiet)

/-- The Bool on the open ledger's sizes goes over a yes of a segment's later moment. -/
theorem ledgerB_at_later {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s')
    (hz : ledgerB s = true) : ledgerB s' = true := by
  obtain ⟨F, F', a, b, hs⟩ := commitAtS_forkSlots P link moment arrays s s' rs gs h
  obtain ⟨-, hz'⟩ := later_of_slots hs (sized_of_ledgerB a hz)
  unfold ledgerB
  rw [b]
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩

/-- The reads' quiet block leaves the four readers of the state. -/
theorem k1Quiet_look (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => LookSame s s') (k1Quiet G l X) :=
  k1Quiet_decides _ (fun _ _ _ _ _ h => lookSame_layers h) (fun _ _ _ _ _ h => lookSame_head h)
    (fun _ _ _ h => lookSame_att h) G l X

/-- **The sentence of "leftOn m" over a yes of each of the fifty later blocks.** -/
theorem leftOn_blkL (X3 : Verify.Public) (m : Nat) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ)
    (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (blkL Z G l d X arrs).decide s rs gs = .ok s')
    (hz : ledgerB s = true) (h0 : k3LeftOnItemAt X3 m s) : k3LeftOnItemAt X3 m s' := by
  cases d with
  | true =>
    exact leftOn_at_later (Cl := Unit) X3 m (parLater G.first (gpOf Z) l (k1Ix l true + 1) 2) l 2
      arrs s s' rs gs h hz h0
  | false =>
    have h' : ((laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs :
          Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs :
          Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs :
            Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs :
            Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    have a1 := leftOn_at_later (Cl := Unit) X3 m (parLater G.first (gpOf Z) l (k1Ix l false + 1) 1)
      l 1 arrs s s₁ _ _ h1 hz h0
    have z1 := ledgerB_at_later (Cl := Unit) (parLater G.first (gpOf Z) l (k1Ix l false + 1) 1) l 1
      arrs s s₁ _ _ h1 hz
    exact leftOn_quiet X3 m (k1Quiet_look G l X _ _ _ _ h2) z1 a1

section
variable {Pp W : Type}

/-- The promise in front, unmarked, holds what each open public item says beside its Bool. -/
theorem inAt_pubP {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {x : Pp × S} {y : Strs} (h : InAt N Mg links ps k x y) (q : Pub)
    (hq : q ∈ (First.pubSets Mg.more links ps)[k]?.getD []) : Mg.pubP q x := by
  obtain ⟨⟨_, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨_, _, _, h4⟩
  · exact absurd hm hx
  · exact h4 q hq

/-- And its Bool. -/
theorem inAt_pubQ {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {x : Pp × S} {y : Strs} (h : InAt N Mg links ps k x y) (q : Pub)
    (hq : q ∈ (First.pubSets Mg.more links ps)[k]?.getD []) : Mg.pub q x = true := by
  obtain ⟨⟨_, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨_, c5⟩, _⟩ := h1
    unfold First.pubHeld at c5
    exact List.all_eq_true.1 c5 q (List.mem_append_left _ hq)

variable (D : PubData) (base : Pub → Pp × S → Bool) (X3 : Verify.Public) (D3 : First.Look.Sent)
  (Mg0 Mg : Meaning Pp W) (hP : Mg.pubP = (First.Look.fillK3 X3 D3 Mg0).pubP)
  (hMg : Mg.pub = pubAll D base) (N : Numbers) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool)
  (X : LinkH) (arrs : Option (List ℕ)) (m₀ : ℕ)
  (hled : Pub.ledger m₀ ∈
    (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
include hP hMg hled

/-- The arm at "leftOn m". -/
theorem aLeftOn_of (x x' : Pp × S) (y : Strs) (m : ℕ) (hy : YesOf (blkL Z G l d X arrs) x x')
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y)
    (hq : Pub.leftOn m ∈
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD []) :
    Mg.pubP (.leftOn m) x' := by
  have h0 := inAt_pubP hIn _ hq
  have hz := inAt_pubQ hIn _ hled
  rw [hMg] at hz
  rw [hP] at h0 ⊢
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  exact leftOn_blkL X3 m Z G l d X arrs x.2 x'.2 _ gs hd hz h0

/-- **The arm aLeft.** -/
theorem aLeft_of (isL : Pub → Bool)
    (hisL : ∀ q, isL q = true → (∃ m, q = .left m) ∨ ∃ m, q = .leftOn m)
    (hnl : ∀ m, Pub.left m ∉
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD []) :
    ∀ (x x' : Pp × S) y q, YesOf (blkL Z G l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → isL q = true →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] →
      Mg.pubP q x' := by
  intro x x' y q hy hIn hL hq
  rcases hisL q hL with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact absurd hq (hnl m)
  · exact aLeftOn_of D base X3 D3 Mg0 Mg hP hMg N Z G l d X arrs m₀ hled x x' y m hy hIn hq

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.ledgerB_at_later
#print axioms VerifiableInference.Desc.K1.k1Quiet_look
#print axioms VerifiableInference.Desc.K1.leftOn_blkL
#print axioms VerifiableInference.Desc.K1.aLeftOn_of
#print axioms VerifiableInference.Desc.K1.aLeft_of
