-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/PieceYesBare.lean: A PIECE WITH NO ROUNDS BEHIND IT (`p.back = []`) WHOSE
STRETCH OPENS AND STORES NOTHING SAYS YES AT SOME TRANSCRIPT, WHEREVER ITS BLOCK's STEP SAYS YES AT
ROUNDS THAT FIT THE STRETCH's DATA, WITH NO COLUMNS: the transcript's written oracles are the fixed
symbol; the piece opens none of them. General in the piece.
ALMOST ALL OF IT IS CALLED: `plain_onto` | `drawn_of_blocks` | `step_congr`
(Johnson/Desc/K12/Law/TrOnto.lean | DrawnOnto.lean) · `wantsOf_bare` | `opened_nil`
(Johnson/Road/K4/PieceTiled.lean) · `Piece.out_iff` through `piece_out_of_step`
(PieceOutOfStep.lean).
Main names.
  `RoundIsT d r`: a round as a view shows it fits a round's data with a list of trees: `RoundIs`
    (Johnson/Desc/K12/Law/TrOnto.lean), at `RDT`.
  `trT_onto`: `tr_onto` (the same file), at `RDT` | `uLT` | `rvT` | `passT`: for rounds that fit
    there is a typed transcript whose rounds are these, but for the digests, and whose tests of work
    pass. The written oracles are the fixed symbol.
  `fullOf_bare` · `sTests_bare`: at a stretch that opens and stores nothing the tests in front of a
    run pass wherever the tests of work pass. `fullOf_bare` HAS TWO TWINS (`First.Att.P.full_none`,
    Johnson/Desc/First/Att/K05SeamBack.lean · `First.MergeLaw.fullOf_quiet`,
    Johnson/Top/H0/MergeLaw/PieceOut.lean): this file keeps its own proof.
  `piece_yes_bare`: THE THEOREM.
OBJECT: `Piece.ior` · USER: Johnson/LPFFrame/Proofs.lean · LETTERS: all.
Limits. THE BITS OF WORK ARE LAID AS ZEROS, SO THE TESTS OF WORK PASS: A YES AT SUCH A TRANSCRIPT
SAYS NOTHING OF A SEARCH, nor that the challenges are a hash function's answers. It serves
non-emptiness alone: that a law's piece says yes at a statement. At the challenges as hash blocks
(`ckP .two`). Nothing on soundness.

-/
import Johnson.Top.Fire.Code.PieceOutOfStep
import Johnson.Desc.K12.Law.TrOnto
import Johnson.Road.K4.PieceTiled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open _root_.Iop (GPlain GChal)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open H2K.Onto (DrawnIs plain_onto drawn_of_blocks gplain_old gchal_old gchal_pass step_congr)

/-- A round as a view shows it fits a round's data. -/
structure RoundIsT (d : RDT) (r : _root_.Fmt.RoundView) : Prop where
  items : r.vals.map itemOf = d.items.filter (· != .root)
  logN : d.entry.logN ≤ 64
  drawn : DrawnIs d.entry d.kind r.drawn

/-- **A typed transcript for given rounds.** -/
theorem trT_onto : ∀ (ds : List RDT) (rs : List _root_.Fmt.RoundView), List.Forall₂ RoundIsT ds rs →
    ∃ τ : Iop.Tr (uLT (ckP .two) ds),
      (rvT (ckP .two) ds τ).map noDigest = rs.map noDigest ∧ passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true
  | [], [], _ => ⟨(), rfl, rfl⟩
  | d :: ds, r :: rs, h => by
    cases h with
    | cons hr hrs =>
      obtain ⟨τ, a, b⟩ := trT_onto ds rs hrs
      obtain ⟨x, hx⟩ := plain_onto d.items r.vals hr.items
      obtain ⟨u, hu⟩ := drawn_of_blocks d.entry d.kind r.drawn hr.logN hr.drawn
      refine ⟨((zeroT d.trees, GPlain.mk d.entry.work x (default : ℕ)), GChal.zero d.entry.work u, τ), ?_, ?_⟩
      · show noDigest ⟨_root_.Run.PQ.PlainOf.gots d.items (GPlain.old (GPlain.mk d.entry.work x (default : ℕ))),
          (ckP .two).dr d.entry d.kind (GChal.old (GChal.zero d.entry.work u))⟩ ::
            (rvT (ckP .two) ds τ).map noDigest = noDigest r :: rs.map noDigest
        rw [gplain_old, gchal_old, a, hx]
        congr 1
        show (⟨r.vals, { (ckP .two).dr d.entry d.kind u with digest := none }⟩ : _root_.Fmt.RoundView) =
          ⟨r.vals, { r.drawn with digest := none }⟩
        rw [hu]
      · show (GChal.pass (GChal.zero d.entry.work u) && passT (ckP .two) ds (rhoT (ckP .two) ds τ)) = true
        rw [gchal_pass, b]
        rfl

theorem fullOf_bare : ∀ (ds : List RDT) (Rs : List _root_.Fmt.Drawn), (∀ d ∈ ds, d.stored = []) → fullOf ds Rs = true
  | [], _, _ => by simp [fullOf]
  | _ :: _, [], _ => by simp [fullOf]
  | d :: ds, R :: Rs, h => by
    simp only [fullOf, h d List.mem_cons_self, List.all_nil, Bool.true_and]
    exact fullOf_bare ds Rs fun e he => h e (List.mem_cons_of_mem _ he)

/-- At a stretch that opens and stores nothing the tests in front of a run pass wherever the tests
of work pass. -/
theorem sTests_bare (C : CK) (S : StageD) (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (h : ∀ d ∈ S.ds, d.opens = [] ∧ d.stored = [])
    (hp : passT C S.ds (rhoT C S.ds τ) = true) : sTests C S y τ = true := by
  have w : sWants C S (rhoT C S.ds τ) = [] := OnBytes.Road.K4.wantsOf_bare _ _ _ _ h
  unfold sTests
  rw [hp, fullOf_bare _ _ fun d hd => (h d hd).2, w]
  rfl

variable {S Cl W : Type} {Fr : Frame}

/-- **A PIECE WITH NO ROUNDS BEHIND IT WHOSE STRETCH OPENS AND STORES NOTHING SAYS YES AT SOME
TRANSCRIPT, WHEREVER ITS BLOCK's STEP SAYS YES AT ROUNDS THAT FIT, WITH NO COLUMNS**: the
transcript's written oracles are the fixed symbol. -/
theorem piece_yes_bare (p : Piece (ckP .two) Fr S Cl W) (hback : p.back = []) (hb : ∀ d ∈ p.ds, d.opens = [] ∧ d.stored = [])
    (a : S × Fr.E.Str) (rs : List _root_.Fmt.RoundView) (hR : List.Forall₂ RoundIsT p.ds rs) (s' : S) (n : ℕ)
    (hs : p.b.step Fr.ft a.1 rs [] = .ok (s', n)) :
    ∃ τ : Iop.Tr (uLT (ckP .two) p.ds), p.ior.red.out a τ = some (s', p.ior.imp a.2 τ) := by
  obtain ⟨τ, hr, hp⟩ := trT_onto p.ds rs hR
  have ho : (sView (ckP .two) p.stage a.2 τ).opened = [] := OnBytes.Road.K4.opened_nil _ p.stage a.2 τ hb
  refine ⟨τ, piece_out_of_step p a τ s' n (sTests_bare _ p.stage a.2 τ hb hp) ?_ (by rw [ho]; exact List.drop_nil)⟩
  rw [ho, hback, List.append_nil]
  rw [step_congr Fr.ft p.b a.1 (sView (ckP .two) p.stage a.2 τ).rounds rs [] hr]
  exact hs

end LPFD

#print axioms LPFD.trT_onto
#print axioms LPFD.fullOf_bare
#print axioms LPFD.sTests_bare
#print axioms LPFD.piece_yes_bare
