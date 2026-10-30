-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieTwoS.lean: code switching (the kind K2): THE SECOND TIE AT A PLACE, WITH
«REACHED»: k02_t2R (Johnson/P1K2R/TieTwoR.lean) WITH ITS PREMISE ON «held» PAID THROUGH THE
PLACE's DOOR. NO BLOCK IMPORTS THIS FILE.
  held_of_on   what the promise in front says at a tenant whose pin is open there: the meaning's
               «held»
  k02_t2S      k02_t2R's end, with hHeldS gone; IN ITS PLACE: hS (B sits over the kind's own
               sub-protocol behind a door) · hin | hout (the way in and the way out each give Left,
               Johnson/Top/H0/K2Ties/Left.lean) · hbk (the way in leaves the book) · hSR
               (K2.SeedReads: a named premise of Tw/K2C/HeldAtYes.lean) · AT EVERY ACCEPT: hBF |
               hBF' (BookFits, Johnson/Desc/Book/BookFits.lean, at the book in front and behind) ·
               hnew (at the state that the way in lets in: the front, the lay of the trees, the
               field «sent», «each of the first n notices counts an answer and has a row»)
BY: K2.held_at_place (Tw/K2C/HeldAtPlace.lean) · P1K2.yes_of_out (Johnson/P1K2R/TieTwoAt.lean).
LIMITS. A JOINING; t2 IS NOT PAID. No soundness is claimed.
-/
import Johnson.P1K2R.TieTwoR
import Johnson.Top.H0.Tw.K2C.HeldAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning onAt sampledIn samplesHeld)
open IM (openAt)

variable {P W : Type}

theorem held_of_on {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {k : ℕ} {s : S} {y : Strs}
    (ha : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, s) y)
    (hu : s.failed = none) {x : ℕ × ℕ} (hx : x ∈ sampledIn N (openAt links ps k)) :
    Mg.held x.1 x.2 (z, s) = true := by
  rcases ha.2 with hm | ⟨_, h2, _, _⟩
  · exact absurd hu hm
  · unfold samplesHeld at h2
    exact List.all_eq_true.1 h2 x hx

end P1K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open _root_.Run.PQ (CK)
open _root_.Tw.K2 (switchNotices)
open VerifiableInference.Desc (Block FileDescription Strs smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers Meaning onAt samplesHeld sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike held_at_place SeedReads)
open VerifiableInference.Desc.First.K2Ties (Left)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt yes_of_out held_of_on)

variable {P W : Type} {C : CK} {F : Frame}

set_option maxHeartbeats 1000000 in
theorem k02_t2S {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List
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
    {p : K2.P2} {enter : Rec → Except String Rec} {leave : Rec → Rec → Except String Rec}
    (hS : Sits B (K2.codeSwitchKind p : Block Rec Unit) enter leave)
    (hin : ∀ s t, enter s = .ok t → Left s t) (hout : ∀ s t s', leave s t = .ok s' → Left t s')
    (hbk : ∀ s t, enter s = .ok t → t.book = s.book) (hSR : SeedReads)
    (hBF : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      BookFits a.1.book ∧ BookFits b.1.book)
    (hnew : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows)
    (hPP : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      b.1.failed = none → ∀ x ∈ pubAt Mg links ps (k + 1), Mg.pubP x (z, b.1)) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b :=
  k02_t2R H hF dec hsam hidx iJ iQ G seatN n0 b₀ smp hshown hnc hheld M hBy ho' hI hSI hσ hshN
    (fun z a τ b ha hr hm hb _ => by
      have hu : a.1.failed = none := Classical.byContradiction hm
      have ha' : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, a.1)
          (strsOf F a.2) := ha
      obtain ⟨rs, cols, n₁, hy⟩ := yes_of_out hb
      have hI0 := held_of_on ha' hu hidx
      rw [hheld] at hI0
      exact held_at_place hS hin hout hbk hy (hBF z a τ b ha hr hm hb).1
        (hBF z a τ b ha hr hm hb).2 hSR (hnew z a τ b ha hr hm hb) hI0)
    hPP

end VerifiableInference.Desc.First.K2Caller

#print axioms P1K2.held_of_on
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t2S
