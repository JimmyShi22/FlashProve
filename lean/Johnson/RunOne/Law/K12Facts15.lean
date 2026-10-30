-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE FOUR FACTS (marked), (smp), (shape) AND (free) OF fwd_of_facts' hdec (Johnson/RunOne/Law/K12FwdFacts.lean) FROM THE DESCRIPTION's OWN TEST ON THE PLAN AND TWO PREMISES ON THE TABLES' FILES' LETTERS. Statements with proofs; each proof is a joining of calls.
OBJECT. The four conjuncts of fwd_of_facts' hdec, at every yes of the held block. USER. Whoever fills hdec.
LETTERS. The tables' own. PREMISES: hpl : (descriptionFromSource X N P).planOk = true · hft : N.nums.firstTree = 0 (for (shape)) · for (free): hcoll (a collision is read off the cells alone: what CellOnly coll gives) · for (smp): three on the tables' files' letters: B.SmOnly · B.orc₁ = (plan₁ one).orc (their AtFk.orc) · ArrOk B.h₁ at_ [0, 1, 2] (it stands in free₁ too).
PREMISES OF Johnson/RunOne/Law/K12Join15.lean's shape_fact | free_fact THAT ARE PAID HERE, BY WHAT:
  hf     the test on the file: a field of FileDescription.PlanOk (Johnson/Desc/RunLaws.lean).
  hp     the block's own test on the plan: the block stands, bared, in the first chain's flat list (fk_rng_at, Johnson/RunOne/Sound/KeyMapAtFK.lean), whose every block has passed its test.
  hl     two lookups: the ties at border 15 say it themselves (shape₁'s ties do not read the number of lookups that shape₁ is handed).
  hS     the sampled messages stay: Johnson/RunOne/Law/K12Keeps.lean's ranges_keeps at the base's groundKeeps_smpStay | beginRun_smpStay: ONE CALL (ranges_smpStay says the same under the plan's test; it calls ranges_keeps itself).
  hone   each switch's message lays one tree: oneTree_all (Johnson/RunOne/Law/K12OneTree.lean): for all codes, no premise.
THE TABLES' TIES ASK THAT «THE BOOK IS IN ORDER»: the ties' clause on the book is carried by k12_bookStep (Johnson/Desc/K12/Coin/BookThrough.lean): ONE PUBLIC PREMISE: hft : N.nums.firstTree = 0 (no test of the description asks it; the maker of the place's numbers lays 0).
  rng_plan · two_of_shape · marked_15 · shape_15 · free_15.
  hrec   the reading's recOf: B.h₁.recOf a := B.recOf a.1 by the tables' files' own text: the held block hands a.1 on: rec_15.
Limits. A block that says no to all meets every statement. (smp) and (free) stand UNDER THE BOOK-KEEPING IN FRONT. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Join15
import Johnson.RunOne.Law.K12Keeps
import Johnson.RunOne.Law.K12OneTree
import Johnson.RunOne.Sound.KeyMapAtFK
import Johnson.Desc.RunLaws
import Johnson.RunOne.KeySmStay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay beginRun_smpStay)
open Johnson.RunOne.KeyRows23 (BaseSt Fk oneAt)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ open₁ free₁ plan₁ readers₁ book₁ slots₁ ties₁ tiesA)
open Johnson.RunOne.Law.K12Join15 (shape_fact' free_fact)
open Johnson.RunOne.Law.K12Keeps (ranges_keeps)
open Johnson.RunOne.Law.K12OneTree (oneTree_all)
open Johnson.RunOne.Law.K12Shape15 (core15_eq sentB_iff)

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The description's test on the plan holds the ranges' test's own. -/
theorem rng_plan (hpl : (descriptionFromSource X N P).planOk = true) :
    (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true := by
  have Q := ((descriptionFromSource X N P).planOk_ok).1 hpl
  have hat : (descriptionFromSource X N P).first.blocksInOrder[2 + 6 * (lookupsOf X.Y.k.oneTime).length + 1]? =
      some (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N)) := Johnson.RunOne.Sound.fk_rng_at X N P
  have h1 := (Q.blocks₁ _ (List.mem_of_getElem? hat)).1
  have h2 : ((rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk &&
      (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).hasNoClaimsAndNothingAfter) = true := h1
  exact (Bool.and_eq_true_iff.1 h2).1

/-- The book-keeping's yes at any border says that the plan has two lookups, whatever number it is handed. -/
theorem two_of_shape (one : OneTime) (n k : Nat) (s : FirstState)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) n (slots₁ one) k s = true) : (lookupsOf one).length = 2 := by
  have ht : ties₁ one k s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA at ht
  simp only [Bool.and_eq_true] at ht
  exact beq_iff_eq.1 ht.1.1.1.1.1.1

/-- The fact (marked): at these readers nothing is marked. -/
theorem marked_15 (a b : Xi × FirstState) : (readers₁ (oneAt X)).marked a.2 = (readers₁ (oneAt X)).marked b.2 := rfl

/-- **The fact (shape)**, in the letter of fwd_of_facts' hdec, from the description's test on the plan and hft. -/
theorem shape_15 (hpl : (descriptionFromSource X N P).planOk = true) (hft : N.nums.firstTree = 0) (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b) :
    shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16 b.2 = true := fun h15 =>
  shape_fact' X N P (((descriptionFromSource X N P).planOk_ok).1 hpl).fileOk (two_of_shape _ _ _ _ h15) hft (rng_plan X N P hpl)
    (fun s rs gs s' h => ranges_keeps groundKeeps_smpStay (fun d d' g run hb => beginRun_smpStay d d' g run hb) _ N s s' rs gs h)
    (fun nx last lay h => oneTree_all _ nx last lay h) a b rs gs hd h15

variable {Cells M Smp Rec : Type} (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- The tables' one reading reads the stored table's record off the instance, which the held block hands on. -/
theorem rec_15 : ∀ a rs gs b, (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b →
    B.h₁.recOf b = B.h₁.recOf a := by
  intro a rs gs b hd
  show B.recOf b.1 = B.recOf a.1
  rw [(held_decide _ a rs gs b hd).1]

/-- At two lookups one pin is open at border 16: the index masks'. -/
theorem pin16 : ∀ k ∈ pinned (open₁ 2 16), k = 0 := by decide

/-- **The fact (smp)**, under the book-keeping in front: at each pin still open behind the reading's sample is the same in front and behind. hSm | horc | hArr: on the tables' files' letters. -/
theorem smp_15 (hSm : B.SmOnly) (horc : B.orc₁ = (plan₁ (oneAt X)).orc) (hArr : ArrOk B.h₁ at_ [0, 1, 2])
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b)
    (h15 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true) :
    ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 16), B.h₁.smp a (at_ k).1 (at_ k).2 = B.h₁.smp b (at_ k).1 (at_ k).2 := by
  have hn : n₁ (oneAt X) = 2 := two_of_shape _ _ _ _ h15
  rw [hn] at h15 ⊢
  intro k hk
  obtain rfl := pin16 k hk
  have hy := (held_decide _ a rs gs b hd).2
  have hS : SmpStay a.2.d.st b.2.d.st :=
    ranges_keeps groundKeeps_smpStay (fun d d' g run hb => beginRun_smpStay d d' g run hb) _ N a.2 b.2 rs gs hy
  refine (Johnson.RunOne.KeyRows23.smp₁_of_smpStay B hSm a b _ _ hS fun o ho => ?_).symm
  have e0 : B.arr (at_ 0).1 (at_ 0).2 = 0 := hArr 0 (by simp)
  rw [e0, horc] at ho
  obtain rfl : 0 = o := Option.some.inj ho
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 h15).2
  rw [core15_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨x, hx, x1, _⟩ := (sentB_iff a.2 (k := 0) (o := 0) rfl).1 hc.1.1.1.1.1
  exact ⟨x, hx, x1⟩

/-- **The fact (free)**, under the book-keeping in front. -/
theorem free_15 (hpl : (descriptionFromSource X N P).planOk = true)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b)
    (h15 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true) :
    ∀ y y', StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) y y' → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y →
      free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 b y' :=
  free_fact X N P B at_ R coll (((descriptionFromSource X N P).planOk_ok).1 hpl).fileOk (two_of_shape _ _ _ _ h15) (rng_plan X N P hpl) (rec_15 X N B) hcoll a b rs gs hd h15

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.rng_plan
#print axioms Johnson.RunOne.Law.K12Facts15.two_of_shape
#print axioms Johnson.RunOne.Law.K12Facts15.marked_15
#print axioms Johnson.RunOne.Law.K12Facts15.shape_15
#print axioms Johnson.RunOne.Law.K12Facts15.free_15
#print axioms Johnson.RunOne.Law.K12Facts15.rec_15
#print axioms Johnson.RunOne.Law.K12Facts15.smp_15
