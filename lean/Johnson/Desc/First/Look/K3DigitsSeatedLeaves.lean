-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsSeatedLeaves.lean: the lookup on the digits of a link's smallness
test: WHAT ELSE A YES OF THE SEATED BLOCK LEAVES, ACROSS THE STEP WITHOUT A ROUND BEHIND ITS ROUNDS:
the ledger behind is a later one and sized; what the link's other lookup heard is not turned; that
lookup's promise behind (k3OnOut) rides; every slot from the ledger's next on stays free. Facts on
the text: no premise on a filling, no letter of the table of joints. Statements and proofs. A tie:
no error term.

Why. The promise behind the digits' block asks more than
the lookup's own item: lookOut of the other lookup, leftOn (what that lookup left, at a later
ledger), freeAbove. Each hangs on one of the facts here.

Main names.
  (freeAboveB s: the kind's one Bool for freeAbove: Johnson/Desc/First/Look/K3CallsKeeps.lean: not
    typed anew here.)
  freeAbove_hearing: it rides over a hearing (by PadExact.next and .marks).
  putFork_look: laying a ledger where one is open leaves what the lookup on the calls heard.
  quietAt_ledger: a yes of K3.quietAt's step at the digits leaves the ledger but for its count of
    planned claims, and what the lookup on the calls heard.
  DigLeft s t: the five facts as one definition.
  k3_digits_seated_leaves: THE END: DigLeft u.1 v.1, at a piece that holds «below B'», B' any block
    that narrows K3.theStated's value at the digits' address.
OBJECT. Desc.K3.theStated claim readers X codes shape a, at a.link = some i and a.piece = K3.pieceAt
X i true; K3.quietAt X i true's steps.
USER. k3_digits_row_seated_cut (K3DigitsSeatedCut.lean) hands it to its premise «behind». Meant: the
clauses lookOut m (2 + o), leftOn m and freeAbove m of the table's promise behind the digits' block
(inside that premise); leftOn's keeping lemma asks just the first three facts.
LETTERS. Those of k3_digits_seated_turns; pc: any place with digits = false: NOTHING TIES IT TO THE
LINK.
IS IT EMPTY? Its premises are those of k3_digits_seated_turns (the object's equations, hOk, hN, the
piece's two) and a yes of the piece. NOT TRIED AT A REAL PLACE.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. Nothing where the piece says no. freeAboveB does not say that there is room at all (a ledger
with ns = next has it).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Desc.First.Look.K3DigitsOtherRides
import Johnson.Desc.First.Look.K3CallsKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- "Free above" rides over a hearing, at the raw form of the Bool freeAboveB. THREE SISTERS OF THIS
LEMMA LIE ELSEWHERE (on the library's Prop FreeAbove; on a Bool of a ledger; inside the proof of
k3_calls_freeAbove): when this file goes to a door, the one that is home is to be called and this
one struck. -/
theorem freeAbove_hearing {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (E : _root_.Fo.Tp.PadExact h F F' g) (hns : F'.ns = F.ns) (hz : OnBytes.PscRun.Sized F')
    (hfree : ((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) = true) :
    ((List.range (F'.ns - F'.next)).all fun j => !F'.gotF.getD (F'.next + j) true) = true := by
  rw [List.all_eq_true] at hfree ⊢
  intro j hj
  have hj2 : j < F.ns - (F.next + Forest.elems h) := by
    have hj' := List.mem_range.1 hj
    rw [E.next, hns] at hj'
    exact hj'
  have hq := hfree (Forest.elems h + j) (List.mem_range.2 (by omega))
  simp only [Bool.not_eq_true'] at hq ⊢
  have e : F'.next + j = F.next + (Forest.elems h + j) := by
    rw [E.next]
    omega
  rw [e]
  have hin : F.next + (Forest.elems h + j) < F'.gotF.size := by
    rw [hz.2.2, hns]
    omega
  refine getD_out _ _ hin ?_
  have hF : ¬ OnBytes.PscRun.Filled F (F.next + (Forest.elems h + j)) := by
    intro hc
    have q' := getD_in _ _ hq
    unfold OnBytes.PscRun.Filled at hc
    rw [q'] at hc
    cases hc
  have hF' : ¬ OnBytes.PscRun.Filled F' (F.next + (Forest.elems h + j)) := by
    intro hc
    rcases (E.marks _).1 hc with h1 | ⟨-, h2, -⟩
    · exact hF h1
    · omega
  unfold OnBytes.PscRun.Filled at hF'
  cases hv : F'.gotF.getD (F.next + (Forest.elems h + j)) false with
  | false => rfl
  | true => exact absurd hv hF'

/-- Laying a ledger where one is open leaves what the lookup on the calls heard. -/
theorem putFork_look (s : Desc.First.S) (F Gk : Fork) (hF : s.fork? = some F) :
    (s.putFork Gk).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a => simp [Desc.First.S.putFork, Desc.First.S.lookHeard?, hh]
  | att a => simp [Desc.First.S.putFork, Desc.First.S.lookHeard?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true => simp [Desc.First.S.putFork, Desc.First.S.lookHeard?, hh, ho]

/-- **What a yes of the step behind the digits' rounds leaves.** -/
theorem quietAt_ledger (X : Verify.Public) (i : ℕ) (f : Desc.First.S → Except String Desc.First.S)
    (hf : Desc.K3.quietAt X i true = some f) (s t : Desc.First.S) (h : f s = .ok t) :
    ∃ F c, s.fork? = some F ∧ t.fork? = some { F with planClaimsF := c } ∧
      t.lookHeard? = s.lookHeard? := by
  unfold Desc.K3.quietAt at hf
  simp only [if_true] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    obtain ⟨ah, c, ha, ho, e⟩ := Desc.K3.quietHead_ok X s t h
    have hFs : s.fork? = some ah.F := by simp [Desc.First.S.fork?, ha, ho]
    have e1 : t.fork? = s.fork? := by
      rw [e]
      simp [Desc.First.S.fork?, ha]
    have e2 : t.lookHeard? = s.lookHeard? := by
      rw [e]
      simp [Desc.First.S.lookHeard?, ha]
    exact ⟨ah.F, ah.F.planClaimsF, hFs, e1.trans hFs, e2⟩
  · split at hf <;> split at hf <;>
      (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       obtain ⟨F, hF, -, e⟩ := Desc.K3.quietDigits_ok _ _ s t h
       obtain ⟨F₂, hF₂, hG₂⟩ := Desc.K3.quietDigits_fork _ _ s t h
       obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
       exact ⟨F, _, hF, hG₂, by rw [e]; exact putFork_look s F _ hF⟩)

/-- **What else the digits' lookup leaves**, from the record s in front to the record t behind: both
hold a ledger; what the link's other lookup heard is not turned; where the ledger in front has its
sizes, the one behind is a later one, has its sizes, and "free above" rides; the other lookup's
promise behind rides. -/
def DigLeft (s t : Desc.First.S) : Prop :=
  ∃ F Gk, s.fork? = some F ∧ t.fork? = some Gk ∧ t.lookHeard? = s.lookHeard? ∧
    (OnBytes.PscRun.Sized F → _root_.Fo.Later F Gk ∧ OnBytes.PscRun.Sized Gk ∧
      (freeAboveB s = true → freeAboveB t = true)) ∧
    ∀ pc : Desc.First.Look.P, pc.digits = false → Desc.K3.k3OnOut pc s = true →
      Desc.K3.k3OnOut pc t = true

section
variable {Cl : Type} {Fr : Frame}

/-- **WHAT ELSE A YES OF THE SEATED DIGITS' PIECE LEAVES.** -/
theorem k3_digits_seated_leaves {W : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (q : Piece (ckP .two) Fr Desc.First.S Cl W) (hq : q.b = below B') (hback : q.back = [])
    (u v : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out u τ = some v) : DigLeft u.1 v.1 := by
  unfold DigLeft
  obtain ⟨-, -, -, cols, hd⟩ := piece_hears_below q B' hq hback u τ v hout
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc u.1 v.1 _ cols
      (hN.2 _ _ _ _ hd)
  obtain ⟨F, y, hF, hn, e, hE⟩ :=
    decide_exact (Desc.K3.seatDigits claim) a.piece laid sent P' [] u.1 s' _ gs' hyes
  have hF0 : u.1.fork? = some F := hF
  have hsome : ((Desc.K3.seatDigits claim).fork u.1).isSome = true := by
    rw [hF]
    rfl
  have hF' : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have hL : s'.lookHeard? = u.1.lookHeard? := by
    rw [e]
    exact putDigits_look claim u.1 y.1 F y.2 hF
  have hO : ∀ pc : Desc.First.Look.P, pc.digits = false → Desc.K3.k3OnOut pc u.1 = true →
      Desc.K3.k3OnOut pc s' = true :=
    fun pc hdc hIn => k3OnOut_other_rides claim a.piece laid sent P' [] pc hdc u.1 s' _ gs' hyes hIn
  have hZ : OnBytes.PscRun.Sized F → _root_.Fo.Later F y.2 ∧ OnBytes.PscRun.Sized y.2 ∧
      (((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) = true →
        ((List.range (y.2.ns - y.2.next)).all fun j => !y.2.gotF.getD (y.2.next + j) true) =
          true) := by
    intro hz
    obtain ⟨E, hLat⟩ := hE hz
    exact ⟨⟨hLat.next, hLat.ns, hLat.keep⟩, hLat.sized hz,
      freeAbove_hearing E hLat.ns (hLat.sized hz)⟩
  rcases hstep with e' | ⟨f, hf, hfs⟩
  · rw [e']
    refine ⟨F, y.2, hF0, hF', hL, fun hz => ⟨(hZ hz).1, (hZ hz).2.1, fun hfr => ?_⟩, hO⟩
    unfold freeAboveB at hfr ⊢
    rw [hF0] at hfr
    rw [hF']
    exact (hZ hz).2.2 hfr
  · obtain ⟨F₂, c, hF₂, hG₂, hL₂⟩ := quietAt_ledger X i f hf s' v.1 hfs
    obtain rfl : y.2 = F₂ := Option.some.inj (hF'.symm.trans hF₂)
    refine ⟨F, _, hF0, hG₂, hL₂.trans hL, fun hz => ⟨?_, ?_, fun hfr => ?_⟩, fun pc hdc hIn => ?_⟩
    · exact (hZ hz).1.trans (later_planClaims y.2 c)
    · exact (hZ hz).2.1
    · unfold freeAboveB at hfr ⊢
      rw [hF0] at hfr
      rw [hG₂]
      exact (hZ hz).2.2 hfr
    · refine k3OnOut_planClaims pc s' v.1 y.2 c hF' hG₂ ?_ (hO pc hdc hIn)
      rw [hdc]
      exact hL₂

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.freeAbove_hearing
#print axioms VerifiableInference.OnPublicFiles.putFork_look
#print axioms VerifiableInference.OnPublicFiles.quietAt_ledger
#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated_leaves
