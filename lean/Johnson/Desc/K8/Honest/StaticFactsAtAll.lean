-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/StaticFactsAtAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE
FACTS OF THE BUNDLE `FourFactsAt` (FourFactsAt.lean) THAT READ NO HEARD VALUE, IN FRONT OF EACH OF
THE 25 BATCHINGS, AT THE STATE's DATA OF THE TEST WITH THE FOURTEEN WRITTEN FIELDS SET TO u's
(TailClaims.Law.blank u tl) AND AT THE STATE's OWN LEDGER: IN THE GOALS' SCOPE, THE FILES READ,
UNDER AN OPENING OF THE DESCRIPTION, AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH THERE.
THAT ANY SUCH STATE IS REACHED IS NOT SHOWN. A definition and lemmas; none of the library's goals.

  `sixFields tl`, `planned_six`, `six_blank` the data with all but f9, ix, mz, tau, z1, z2 at their
                   defaults; a reading of planned fields (LinkJoin.Planned); it reads none of the
                   fourteen written fields
  `tailTest_six`, `pieceTest_six`, `apartTest_six`, `callsTest_six`, `zOf_six`, `allPieces_six` four
                   public tests and two readings read these six fields alone: each by rfl
  `static_of_six` ON PLAIN DATA: Fo.ZTests X X Fc (OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean)
                   · sixFields t = sixFields X ⊢ TailOK t ∧ 2 ^ t.f9.cK = t.f9.NC ∧ 5 ≤ t.f9.kT +
                   t.f9.cK ∧ (∀ c < 2, c < t.f9.NC ∧ the shape's call c says the number of t's own
                   call c) ∧ (∀ c < 2, that number ≤ 63) ∧ PieceOK at every piece ∧ the pieces apart
                   ∧ every piece's rows lie inside its tree at Fc
  **`staticFacts_at_all`** the scope · the files read · the opening · l < 25 · the built segment Xl
                   · Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 l + (if l = 24 then 11 else 9)) (z, s) ·
                   s.tl? = some tl · s.fork? = some G · u ⊢ these eight at blank u tl (the three on
                   f9 at tl.f9) and at G, and Fo.CoefOK (blank u tl) G
By: P1K8.tests_at_built (Johnson/P1K8R/StaticAtBuilt.lean): the ten public tests hold at the built
segment's data and ledger · `planned_at_all` (SameDigAtReach.lean) at `planned_six` · the library's
tailOK_of_test, Fo.pieceOK_of_test, Fo.apart_of_test · the ledger: P1K8.looks_at_batch with
LinkJoin.looks_array and frame_of_looks · CoefOK: P1K8.static_at_built, static_at_batch,
three_of_static (Johnson/P1K8R/StaticAtBatch.lean), carried to blank u tl by LinkJoin.coefOK_congr
at g9_blank (Johnson/Desc/First/Link/Law/OkJoin.lean).
KIN IN THE LIBRARY, NOT CALLED: `DigStatic` (Johnson/Desc/First/Link/Law/RestStatic.lean) is five of
these with `SameDig`; digStatic_of_tests (Johnson/P5T/DigFiveAtMg.lean) makes it from Fo.ZTests at
ONE data. The step on callsTest is tail_zk_size's (OnBytes/Tie/Pv/Lookup/Ends/FoTailSizes.lean),
WRITTEN A FURTHER TIME.
WHAT IT DOES NOT HAND: the sizes of what was heard (g.zk): it hands the calls' numbers, to which
`K3Left`'s field zkLen ties them.
No option is raised and no instance is taken away. TACTICS THAT SEARCH: a bare `simp` on two lines,
each on the membership of 0 or 1 in the list [0, 1] · `omega` on one line.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED: where none is, the last is idle. IN SCOPE ALONE: the
full size; the first chain; at OnBytes.secondHashFunction. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.SameDigAtReach
import Johnson.P1K8R.StaticAtBuilt
import Johnson.P1K8R.StaticAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.DgP
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The data with all but six fields at their defaults. -/
def sixFields (tl : HTailF2) : HTailF2 :=
  { f9 := tl.f9, ix := tl.ix, mz := tl.mz, tau := tl.tau, z1 := tl.z1, z2 := tl.z2 }

/-- A reading of planned fields. -/
theorem planned_six : LinkJoin.Planned sixFields :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- It reads none of the fourteen written fields. -/
theorem six_blank (u tl : HTailF2) :
    sixFields (TailClaims.Law.blank u tl) = sixFields tl := rfl

theorem tailTest_six (tl : HTailF2) : tailTest tl = tailTest (sixFields tl) := rfl
theorem pieceTest_six (tl : HTailF2) (q : ℕ) :
    _root_.Fo.pieceTest tl q = _root_.Fo.pieceTest (sixFields tl) q := rfl
theorem apartTest_six (tl : HTailF2) (q : ℕ) :
    _root_.Fo.apartTest tl q = _root_.Fo.apartTest (sixFields tl) q := rfl
theorem callsTest_six (tl : HTailF2) :
    _root_.Fo.callsTest tl = _root_.Fo.callsTest (sixFields tl) := rfl
theorem zOf_six (tl : HTailF2) (q : ℕ) : tl.zOf q = (sixFields tl).zOf q := rfl
theorem allPieces_six (tl : HTailF2) :
    _root_.Fo.allPieces tl = _root_.Fo.allPieces (sixFields tl) := rfl

/-- **On plain data: what the public tests at X give at any data with X's six fields.** -/
theorem static_of_six {X t : HTailF2} {Fc : Fork} (T : _root_.Fo.ZTests X X Fc)
    (e : sixFields t = sixFields X) :
    TailOK t ∧ 2 ^ t.f9.cK = t.f9.NC ∧ 5 ≤ t.f9.kT + t.f9.cK ∧
    (∀ c < 2, c < t.f9.NC ∧ ((t.f9.calls[c]?).map (·.n)).getD 0 = (t.zOf c).call.n) ∧
    (∀ c < 2, (t.zOf c).call.n ≤ 63) ∧
    (∀ c < 2, ∀ p ∈ piecesL t c, _root_.Fo.PieceOK t c (t.zOf c).call.n p) ∧
    (∀ c < 2, (piecesL t c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off) ∧
    ∀ a ∈ _root_.Fo.allPieces t, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R := by
  have e9 : t.f9 = X.f9 := congrArg (·.f9) e
  have hz : ∀ q, t.zOf q = X.zOf q := fun q =>
    (zOf_six t q).trans ((congrArg (·.zOf q) e).trans (zOf_six X q).symm)
  have h1 : tailTest t = true :=
    ((tailTest_six t).trans ((congrArg tailTest e).trans (tailTest_six X).symm)).trans T.t1
  have h2 : ∀ q < 2, _root_.Fo.pieceTest t q = true := fun q hq =>
    ((pieceTest_six t q).trans ((congrArg (_root_.Fo.pieceTest · q) e).trans
      (pieceTest_six X q).symm)).trans (T.t2 q hq)
  have h3 : ∀ q < 2, _root_.Fo.apartTest t q = true := fun q hq =>
    ((apartTest_six t q).trans ((congrArg (_root_.Fo.apartTest · q) e).trans
      (apartTest_six X q).symm)).trans (T.t3 q hq)
  have h4 : _root_.Fo.callsTest t = true :=
    ((callsTest_six t).trans ((congrArg _root_.Fo.callsTest e).trans
      (callsTest_six X).symm)).trans T.t4
  have hA : _root_.Fo.allPieces t = _root_.Fo.allPieces X :=
    (allPieces_six t).trans ((congrArg _root_.Fo.allPieces e).trans (allPieces_six X).symm)
  have K := tailOK_of_test h1
  refine ⟨K, ?_, ?_, fun c hc => ⟨?_, ?_⟩, fun c hc => ?_,
    fun c hc => _root_.Fo.pieceOK_of_test (h2 c hc),
    fun c hc => _root_.Fo.apart_of_test (h3 c hc), fun a ha => T.t10 a (hA ▸ ha)⟩
  · rw [e9]
    exact T.t6
  · rw [e9]
    exact T.t7
  · rw [K.nc]
    exact hc
  · have h5 : (((t.f9.calls[c]?).map (·.n)).getD 0 == (t.zOf c).call.n) = true :=
      List.all_eq_true.1 h4 c (by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
        · obtain rfl : c = 0 := by omega
          simp
        · subst h
          simp)
    exact beq_iff_eq.1 h5
  · rw [hz c]
    exact T.t8 c hc

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF EACH OF THE 25 BATCHINGS: THE FACTS THAT READ NO HEARD VALUE, AT THE STATE's DATA
WITH THE FOURTEEN WRITTEN FIELDS SET TO u's, AND AT THE STATE's OWN LEDGER.** -/
theorem staticFacts_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) (u : HTailF2) :
    TailOK (TailClaims.Law.blank u tl) ∧ 2 ^ tl.f9.cK = tl.f9.NC ∧
    5 ≤ tl.f9.kT + tl.f9.cK ∧
    (∀ c < 2, c < tl.f9.NC ∧
      ((tl.f9.calls[c]?).map (·.n)).getD 0 =
        ((TailClaims.Law.blank u tl).zOf c).call.n) ∧
    (∀ c < 2, ((TailClaims.Law.blank u tl).zOf c).call.n ≤ 63) ∧
    (∀ c < 2, ∀ p ∈ piecesL (TailClaims.Law.blank u tl) c,
      _root_.Fo.PieceOK (TailClaims.Law.blank u tl) c
        ((TailClaims.Law.blank u tl).zOf c).call.n p) ∧
    (∀ c < 2, (piecesL (TailClaims.Law.blank u tl) c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off) ∧
    _root_.Fo.CoefOK (TailClaims.Law.blank u tl) G ∧
    ∀ a ∈ _root_.Fo.allPieces (TailClaims.Law.blank u tl),
      a.2.r0 + a.2.Rp ≤ (G.trees.getD a.2.tree {}).R := by
  have v : sixFields tl = sixFields Xl.tl := planned_at_all planned_six hS hR O hl e3 h ht
  have e : sixFields (TailClaims.Law.blank u tl) = sixFields Xl.tl :=
    (six_blank u tl).trans v
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    static_of_six (_root_.P1K8.tests_at_built hS O hl e3) e
  have fr : _root_.Fo.Frame Xl.Fp G := LinkJoin.frame_of_looks
    (LinkJoin.looks_array (_root_.P1K8.looks_at_batch hS hR O hl e3 h hG))
  have co : _root_.Fo.CoefOK tl G := (_root_.P1K8.three_of_static
    (_root_.P1K8.static_at_batch hS hR O hl e3 h ht hG
      (_root_.P1K8.static_at_built hS O hl e3))).2.1
  refine ⟨a1, a2, a3, a4, a5, a6, a7, LinkJoin.coefOK_congr (LinkJoin.g9_blank u tl) co,
    fun a ha => ?_⟩
  rw [(fr.2 _).1]
  exact a8 a ha

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planned_six
#print axioms VerifiableInference.Desc.First.K8.Honest.six_blank
#print axioms VerifiableInference.Desc.First.K8.Honest.tailTest_six
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceTest_six
#print axioms VerifiableInference.Desc.First.K8.Honest.apartTest_six
#print axioms VerifiableInference.Desc.First.K8.Honest.callsTest_six
#print axioms VerifiableInference.Desc.First.K8.Honest.zOf_six
#print axioms VerifiableInference.Desc.First.K8.Honest.allPieces_six
#print axioms VerifiableInference.Desc.First.K8.Honest.static_of_six
#print axioms VerifiableInference.Desc.First.K8.Honest.staticFacts_at_all
#print axioms VerifiableInference.Desc.First.K8.Honest.sixFields
