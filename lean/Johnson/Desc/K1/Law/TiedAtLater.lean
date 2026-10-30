-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/TiedAtLater.lean: A LATER MOMENT's SENDING OF KIND K1 AT ITS ROW OF THE TABLE OF JOINTS: THE FIVE TIES (TiedAt, Johnson/Desc/Sound/ChainOfPromises.lean), by the sending's general rule
(K1.send_tied, Johnson/Desc/K1/Law/AtTable.lean) with its premise hkeep taken from Johnson/Desc/K1/Law/KeepAtLater.lean's keep_later. The twin, for the fifty later places, of Johnson/Desc/K13/Law/AtTableW.lean's
w_tied | w_tied_seat.
  later_tied     the five ties, of ANY block b with IsSend, at any reader get of the chain's state
  block_tied     **the five ties AT ANY BLOCK c OVER THE CHAIN's STATE THAT IS UNDER THE LOT's OWN BLOCK** (c.UnderR B.retype; get := (z, ·)): at c := B.retype THE FORM THAT THE RULE seatLaws_of_tied (Johnson/Desc/Sound/SeatLawsOfTied.lean) TAKES; at
                 c := below e, e the block that the description seats, THE FORM THAT THE KIND-FREE ROAD tiedAt_of_seatTie (Johnson/Desc/AtSeats/Road.lean) TAKES
OF send_tied's SIX PREMISES, IN block_tied: hkeep: four clauses PROVED (keep_later), the rest BROUGHT DOWN TO FillL | hseal | hshown | hpub | hpubP · hMark: PAID (hmark: a fact on the block) · hDec: BROUGHT DOWN TO
FillL.decodes · hride: BROUGHT DOWN TO hgo (a riding item's sentence goes back over the block's own yes, from inside the promise in front) · hseal · hback: PREMISES STILL.
WHAT block_tied ASKS OF THE BLOCK B (facts on its text): two declared rounds · IsSend · a yes leaves the mark · a yes is a step StepL at the state's frame's group.
What is not claimed. NO MEMBER OF RowL | FillL | hgo | hg | hbase | hseal | hshown | hpub | hpubP | hback IS SHOWN HERE. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.K1.Law.AtTable
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Run OnBytes.Flat OnBytes.Maker
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter)
open VerifiableInference.Desc.K13.Law (openAt piece_step)

variable {A Pp Cl W : Type} {F : Frame}

/-- **THE FIVE TIES AT A LATER MOMENT's SENDING.** -/
theorem later_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k m t : ℕ) (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (b : Block A Cl) (hS : IsSend P (fun a => (get a).2.st) b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (St : Pp × S → Pp × S → Prop) (T : List Pub)
    (hT : RowL N Mg.more links ps k m t (layOf P).shapes.size P.sent.size T)
    (hF : FillL St (InAt N Mg links ps k) N Mg (openAt links ps k)
      ((First.pubSets Mg.more links ps)[k]?.getD []) (openAt links ps (k + 1))
      ((First.pubSets Mg.more links ps)[k + 1]?.getD []))
    (hP : laterSeatsB N P m t (N.treesAt ps[k]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt links ps k), u.1 < base)
    (hyes : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      St (get a.1) (get x.1) ∧ StepL P (N.groupAt m) (get a.1) (get x.1))
    (hseal : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt P j →
        Sealed P.codes (shapeAt P j) (rad j.val) (fOf x.2 j) (get x.1).2.st
          ((get x.1).2.st.oracles.size - (shapesOf P).length + j.val)) →
      ∀ u ∈ N.sent m t, Mg.held u.1 u.2 (get x.1) = true ∧
        Mg.noColl u.1 u.2 (get x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      ∀ u ∈ N.sent m t, Mg.shown u.1 u.2 (strsOf F x.2))
    (hpub : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ T, Mg.pub q (get x.1) = true)
    (hpubP : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ T, q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] → Mg.pubP q (get x.1))
    (hback : ∀ a τ x w, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      relAt (meansQ N Mg get) (outsQ links ps k) x w →
      relAt (meansQ N Mg get) (insQ links ps k) a w)
    (hride : ∀ a τ x w i, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      onQ N Mg links ps get (k + 1) x → relQ N Mg links ps get (k + 1) x w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
      ¬ insQ links ps k i → meansQ N Mg get i a w)
    (hMark : ∀ a τ x,
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      (get a.1).2.failed ≠ none → (get x.1).2.failed ≠ none)
    (hDec : ∀ a τ x,
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      Mg.decodes (get a.1) (strsOf F a.2) → Mg.decodes (get x.1) (strsOf F x.2)) :
    TiedAt N Mg links ps get k (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e) :=
  send_tied N Mg links ps get k P rad hC b hS base d₁ d₂ he₁ hk₁ e he fOf fIn hf
    (fun x => ∀ u ∈ N.sent m t, Mg.held u.1 u.2 (get x.1) = true ∧
      Mg.noColl u.1 u.2 (get x.1) (strsOf F x.2))
    hseal
    (fun a τ x ha hm hx hn =>
      keep_later N Mg links ps get k m t P St base T hT hF hP hbase a x ha hm
        (hyes a τ x ha hm hx).1 (hyes a τ x ha hm hx).2 (keptBelow_out _ hx)
        (fun u hu => ⟨(hn u hu).1, hshown a τ x ha hm hx u hu, (hn u hu).2⟩)
        (hpub a τ x ha hm hx) (hpubP a τ x ha hm hx))
    hback hride hMark hDec

/-- Where a step of a block with two declared rounds says yes, its decision has said yes on two rounds. -/
theorem yes_of_step {T : Type} (b : Block T Cl) (hl : b.rounds.length = 2) (ft : Nat) (s s' : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) (h : b.step ft s rs cols = .ok (s', n)) :
    ∃ r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ _ _ rs cols n h
  have hl' : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hfit, hl]
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, rs.map noDigest = [r₁, r₂] := by
    match rs.map noDigest, hl' with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [e] at hd
  exact ⟨r₁, r₂, gs, hd⟩

/-- **THE FIVE TIES AT A BLOCK OVER THE CHAIN's STATE.** B: the lot's own block. c: ANY BLOCK THAT HAS B's DECLARED ROUNDS AND SAYS YES ONLY WHERE B DOES, TO THE SAME STATE (c.UnderR B.retype): B.retype itself; the block
that the description seats; `below` of it. -/
theorem block_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp)
    (k m t : ℕ) (P : Par) (B : Block S Unit) (c : Block S Cl)
    (hc : c.UnderR (B.retype : Block S Cl)) (hl : B.rounds.length = 2)
    (hS : IsSend P (fun s : S => s.st) B)
    (hmark : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' → s'.failed = s.failed)
    (hstep : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' → ∀ g,
      (∀ L, s.link? = some L → L.check.frame.group = g) → StepL P g (z, s) (z, s'))
    (rad : Nat → Nat) (hC : condPort P rad = true) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) c base d₁ d₂
      P.coordinates e).ior.imp y τ) = fIn y τ.1)
    (T : List Pub)
    (hT : RowL N Mg.more links ps k m t (layOf P).shapes.size P.sent.size T)
    (hF : FillL (YesOf B) (InAt N Mg links ps k) N Mg (openAt links ps k)
      ((First.pubSets Mg.more links ps)[k]?.getD []) (openAt links ps (k + 1))
      ((First.pubSets Mg.more links ps)[k + 1]?.getD []))
    (hgo : ∀ (x x' : Pp × S) y y' w i, YesOf B x x' → InAt N Mg links ps k x y →
      KeptBelow base y y' →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
      ¬ insQ links ps k i → i.holds N Mg x' y' w → i.holds N Mg x y w)
    (hP : laterSeatsB N P m t (N.treesAt ps[k]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt links ps k), u.1 < base)
    (hg : ∀ (s : S) y, InAt N Mg links ps k (z, s) y →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt m)
    (hseal : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt P j →
        Sealed P.codes (shapeAt P j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf P).length + j.val)) →
      ∀ u ∈ N.sent m t, Mg.held u.1 u.2 (z, x.1) = true ∧ Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      ∀ u ∈ N.sent m t, Mg.shown u.1 u.2 (strsOf F x.2))
    (hpub : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ T, Mg.pub q (z, x.1) = true)
    (hpubP : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ T, q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] → Mg.pubP q (z, x.1))
    (hback : ∀ a τ x w, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      relAt (meansQ N Mg fun s : S => (z, s)) (outsQ links ps k) x w →
      relAt (meansQ N Mg fun s : S => (z, s)) (insQ links ps k) a w) :
    TiedAt N Mg links ps (fun s : S => (z, s)) k
      (sendPiece (W := W) (F := F) c base d₁ d₂ P.coordinates e) := by
  have hdec : ∀ a τ x,
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x →
      ∃ r₁ r₂ gs, B.decide a.1 [r₁, r₂] gs = .ok x.1 := by
    intro a τ x hx
    obtain ⟨rs, cols, n, hst⟩ := piece_step _ hx
    obtain ⟨r₁, r₂, gs, hd⟩ := yes_of_step c (by rw [hc.1]; exact hl) _ _ _ rs cols n hst
    exact ⟨r₁, r₂, gs, hc.2 _ _ _ _ hd⟩
  have hfit : ∀ a τ x,
      (sendPiece (W := W) (F := F) c base d₁ d₂
        P.coordinates e).ior.red.out a τ = some x → YesOf B (z, a.1) (z, x.1) := by
    intro a τ x hx
    obtain ⟨rs, cols, n, hst⟩ := piece_step _ hx
    obtain ⟨h1, gs, h2⟩ := step_ok F.ft c _ _ rs cols n hst
    exact ⟨rfl, rs, gs, by rw [hc.1] at h1; exact h1, hc.2 _ _ _ _ h2⟩
  refine later_tied N Mg links ps _ k m t P rad hC _
    (fun s s' r₁ r₂ gs hy => hS s s' r₁ r₂ gs (hc.2 _ _ _ _ hy)) base d₁ d₂ he₁ hk₁ e he fOf fIn hf (YesOf B) T hT
    hF hP hbase ?_ hseal hshown hpub hpubP hback ?_ ?_ ?_
  · intro a τ x ha hm hx
    obtain ⟨r₁, r₂, gs, hd⟩ := hdec a τ x hx
    exact ⟨hfit a τ x hx, hstep _ _ r₁ r₂ gs hd _ (hg a.1 _ ⟨ha, hm⟩)⟩
  · intro a τ x w i ha hm hx _ hall hi hin
    exact hgo (z, a.1) (z, x.1) _ _ w i (hfit a τ x hx) ⟨ha, hm⟩ (keptBelow_out _ hx) hi hin
      (hall i (Or.inl ⟨hi, hin⟩))
  · intro a τ x hx hm
    obtain ⟨r₁, r₂, gs, hd⟩ := hdec a τ x hx
    show x.1.failed ≠ none
    rw [hmark _ _ r₁ r₂ gs hd]
    exact hm
  · intro a τ x hx hd0
    exact hF.decodes (z, a.1) (z, x.1) _ _ (hfit a τ x hx) (keptBelow_out _ hx).1 hd0

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.later_tied
#print axioms VerifiableInference.Desc.K1.yes_of_step
#print axioms VerifiableInference.Desc.K1.block_tied
