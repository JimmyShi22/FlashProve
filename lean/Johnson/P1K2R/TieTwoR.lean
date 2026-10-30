-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieTwoR.lean: code switching (the kind K2): THE SECOND TIE AT A PLACE, WITH
«REACHED», BROUGHT FURTHER DOWN: the promise of the table of joints behind an accept, in the
letters of the structure of ties (TiesAtR.t2; P1K2.t2R_of_handsR, Johnson/P1K2R/TieTwoAt.lean),
with two of that theorem's three premises on the strings and the samples taken apart. NO BLOCK
IMPORTS THIS FILE.
  front_of_on   what the promise in front says at a tenant whose pin is open there: «shown», «no
                collision»
  k02_t2R       t2R_of_handsR's end, FROM: H · hF · dec (as there) · hsam | hidx (closed facts on
                the table: behind the switch the sampled tenants are N.index :: N.sent m 0; in
                front N.index is among them: P1K2.sampled_behind | sampled_front) · the meaning's
                three fields by unfolding (shown · noColl · held) · K2.MembersLike · SmpBySeat ·
                ho' (the promise behind is the law's own: lawPb at fbMade) · hI (the index masks'
                tree lies in front of the piece's base) · AT EVERY ACCEPT: hSI (the reader's
                sample at the index masks' members stays) · hσ (K2.SmpLike) · hshN (every leaf of
                each new member is shown) · hHeldS (THE STATE BEHIND HOLDS THE OOD SAMPLE OF EACH
                OF THESE TENANTS: smpHeld: at the kind's own decision: K2.held_behind,
                Tw/K2C/HeldAtYes.lean; the ways in and out are not joined here) · hPP (as there:
                pubP_behind)
BY: K2.sn_behind (Tw/K2C/StringsBehind.lean) · K2Caller.k2_sn_new
(Tw/K2C/StringsNew.lean).
LIMITS. A JOINING; t2 IS NOT PAID. No soundness is claimed.
-/
import Johnson.P1K2R.TieTwoAt
import Johnson.Top.H0.Tw.K2C.StringsNew
import Johnson.Top.H0.Tw.K2C.StringsBehind
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning onAt sampledIn)
open IM (openAt)

variable {P W : Type}

theorem front_of_on {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {k : ℕ} {s : S} {y : Strs}
    (ha : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, s) y)
    (hu : s.failed = none) {x : ℕ × ℕ} (hx : x ∈ sampledIn N (openAt links ps k)) :
    Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 (z, s) y := by
  rcases ha.2 with hm | ⟨_, _, h3, _⟩
  · exact absurd hu hm
  · exact h3 x hx

end P1K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription Strs smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers Meaning onAt samplesHeld sampledIn)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike sn_behind)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt t2R_of_handsR front_of_on)

variable {P W : Type} {C : CK} {F : Frame}

set_option maxHeartbeats 1000000 in
theorem k02_t2R {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List
          VerifiableInference.Desc.Place}
    {Rch : ℕ → (P × Rec) × F.E.Str → Prop} {k m : ℕ} {q : Piece C F (P × Rec) Cl W} {B : Block Rec
        Cl}
    {ext : P → Rec × F.E.Str → Iop.Tr (uLT C q.ds) → W → W} {err : Err (uLT C q.ds)}
    {o' : P → Rec × F.E.Str → Prop} {Fk : P → Nat → Rec → Prop}
    (H : ∀ z, HandsR (Fk z) N links ps (EQ Mg links ps z) F.ft k B)
    (hF : ∀ z (a : Rec × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1)
    (dec : ∀ z a τ b, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      Mg.decodes (z, a.1) (strsOf F a.2) → Mg.decodes (z, b.1) (strsOf F b.2))
    (hsam : sampledIn N (openAt links ps (k + 1)) = N.index :: N.sent m 0)
    (hidx : N.index ∈ sampledIn N (openAt links ps k))
    {r : SwRow} {Hr : r.OK}
    (iJ : ((rowsAt r Hr (Letters.plain r Hr).t₀ (Letters.plain r Hr).oM
      (Letters.plain r Hr).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r Hr (Letters.plain r Hr).t₀ (Letters.plain r Hr).oM
      (Letters.plain r Hr).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    {Xi : Type} (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ)
    (b₀ : TB (Letters.plain r Hr) iJ iQ)
    (smp : P × Rec → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    {ms : List Mem}
    (hshown : ∀ j t y, Mg.shown j t y ↔ shownJT r.cs G ms j t y)
    (hnc : ∀ j t a y, Mg.noColl j t a y ↔ noCollJT r.cs G smp ms j t a y)
    (hheld : ∀ j t (a : P × Rec), Mg.held j t a = smpHeld a.2.st a.2.book j t)
    (M : MembersLike ms ⟨r.l, seatN⟩ (N.sent m 0)) (hBy : SmpBySeat r.cs smp)
    (ho' : ∀ z b, o' z b → lawPb (Letters.plain r Hr) iJ iQ (fbMade iJ iQ G seatN n0 b₀ b))
    (hI : ∀ z, N.index.1 < (ownPiece q B (ext z) err).base)
    (hSI : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ x ∈ ms, SitsAt x N.index.1 N.index.2 → smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2)
    (hσ : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      SmpLike r.cs smp (z, b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o))
    (hshN : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ i, ShownAt G r.cs r.l seatN (strsOf F b.2) i)
    (hHeldS : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      b.1.failed = none → ∀ x ∈ N.index :: N.sent m 0, smpHeld b.1.st b.1.book x.1 x.2 = true)
    (hPP : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      b.1.failed = none → ∀ x ∈ pubAt Mg links ps (k + 1), Mg.pubP x (z, b.1)) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b := by
  refine t2R_of_handsR H hF dec ?_ ?_ hPP
  · intro z a τ b ha hr hm hb _ hu'
    unfold samplesHeld
    rw [hsam]
    apply List.all_eq_true.2
    intro x hx
    rw [hheld]
    exact hHeldS z a τ b ha hr hm hb hu' x hx
  · intro z a τ b ha hr hm hb ho _ x hx
    rw [hsam] at hx
    have hu : a.1.failed = none := Classical.byContradiction hm
    have ha' : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, a.1)
        (strsOf F a.2) := ha
    have hf := front_of_on ha' hu hidx
    have hall := sn_behind r.cs G smp ms N m (ownPiece q B (ext z) err) z a b τ hb (hI z)
      (hSI z a τ b ha hr hm hb) ⟨(hshown _ _ _).1 hf.1, (hnc _ _ _ _).1 hf.2⟩
      (k2_sn_new iJ iQ G seatN n0 b₀ smp M hBy (z, b.1) b (hσ z a τ b ha hr hm hb)
        (hshN z a τ b ha hr hm hb) (ho' z b ho)) x hx
    exact ⟨(hshown _ _ _).2 hall.1, (hnc _ _ _ _).2 hall.2⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms P1K2.front_of_on
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t2R
