-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/HeadDigitsAtBatch.lean: AT THE HEAD's SEGMENT, IN FRONT OF THE BATCHING: THE LOOKUP ON
THE DIGITS HAS HEARD SOMETHING, AND ITS cEnd, ITS leaves.start AND ITS ROWS NAME NO ENTRY. AT STATES
THAT THE FIRST CHAIN's OWN BLOCKS REACH, WHERE THE LEDGER IS OPEN WITH ITS SIZES; UNDER THE SCOPE,
THE FILES READ, IM.Open AND THE DESCRIPTION's TEST ON ITS PLAN. Lemmas; none of the library's goals.
No prover stands in them; nothing on completeness, soundness or hiding. Why. At the 24 segments in
front of the head's the ledger's sizes are had from the front (OnPublicFiles.sized_upTo,
Johnson/Desc/First/Look/K03RowsBare.lean); at the head's the library has them at the border 340
(K1.sized_340, Johnson/Desc/AtSeats/RowsBareWalk.lean), not at the lookup on the digits; here they
are taken behind it, as a premise, and the library pulls them back.

  `stated_digits_all`   behind a yes of the seated lookup on the digits, from a ledger with its
      sizes: `stated_digits_named` (Johnson/P1K8R/NamedAtBatch.lean) and OnPublicFiles.stated_rowsBare
      (K03RowsBare.lean)
  **`digitsHeard_head`**   two blocks back from 347. The merge: LinkJoin.back_k11_of
      (Johnson/Desc/First/Link/Law/StretchParts.lean), k11_sizesS (SizesStretch.lean),
      merge_leaves_tl (FourAtBatch.lean). The lookup: LinkJoin.back_of (StretchBack.lean),
      sizes_behind_digits (SizesDigits.lean); the sizes come back by SizesS.pulls
      (SizesStretch.lean). The proof's three lines that find the block are those of
      `digitsLeft_at_batch` (NamedAtBatch.lean). It gives the fields cEnd and leaves of `StillFront`
      at the head's segment, and the field digits of `StillHead` (Johnson/P1K8R/BehindAtReach.lean)
Limits. That the ledger is open with its sizes in front of the head's batching is a premise here:
the library's own (hB of LinkJoin.laterSized_head, SizesDigits.lean). `head_at_rch`
(Johnson/P1K8R/BehindAtRch.lean) shows it at the states that the wrapped blocks reach. Nothing on
whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.NamedAtBatch
import Johnson.Desc.First.Link.Law.FourAtBatch
import Johnson.Desc.First.Link.Law.SizesDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **Behind a yes of the seated lookup on the digits, from a ledger with its sizes: it has heard
something, and its cEnd, its leaves.start and its rows name no entry**: `stated_digits_named`
(Johnson/P1K8R/NamedAtBatch.lean) and OnPublicFiles.stated_rowsBare
(Johnson/Desc/First/Look/K03RowsBare.lean) of one value. -/
theorem stated_digits_all {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) {F : Fork}
    (hF : s.fork? = some F) (hz : PscRun.Sized F) :
    ∃ g, c.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] ∧
      ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨g, hg, h1, h2⟩ :=
    stated_digits_named claim readers X codes shape a B h hOk i hi hpc s c rs gs hd hF hz
  obtain ⟨g', hg', h3⟩ :=
    OnPublicFiles.stated_rowsBare claim readers X codes shape a B h hOk i true hi hpc s c rs gs hd hF hz
  have hg2 : c.tl?.bind (·.heard) = some g' := hg'
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg2)
  exact ⟨g, hg, h1, h2, h3⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF THE HEAD's BATCHING, WHERE THE LEDGER IS OPEN WITH ITS SIZES: THE LOOKUP ON THE
DIGITS HAS HEARD SOMETHING, AND THE THREE NAME NO ENTRY.** Two blocks back: the merge leaves the
data and the ledger's sizes; the lookup leaves the sizes, so the ledger in front of it had them. -/
theorem digitsHeard_head {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 347 (z, s))
    (hB : ∃ G, s.fork? = some G ∧ PscRun.Sized G) :
    ∃ g, s.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] ∧
      ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨s6, r6, q6, k6⟩ := LinkJoin.back_k11_of
    (R := fun u t => LinkJoin.SizesS u t ∧ ∀ G, u.fork? = some G → t.tl? = u.tl?)
    (fun M u rs gs t hd => ⟨LinkJoin.k11_sizesS M u rs gs t hd,
      fun G hG => (LinkJoin.merge_leaves_tl (P := M) (rs := rs) hd hG).1⟩) hS hR O h
  obtain ⟨G6, hG6, hz6⟩ := q6.pulls hB
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O 24 (by omega) true
  obtain ⟨b'', e3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk 24 (by omega) true
  obtain rfl : b' = b'' := Option.some.inj (e3.symm.trans e3')
  have hpc := (K3Lot.k03_place _ _ _ _ _ 24 true b' e3).1
  obtain ⟨s5, -, q5, k5⟩ := LinkJoin.back_of
    (R := fun u t => LinkJoin.SizesS u t ∧ ∀ G, u.fork? = some G → PscRun.Sized G →
      ∃ g, t.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] ∧
        ∀ f ∈ g.rows.toList, f.ents = #[])
    hS hR O (l := 24) (i := IM.k3Ix 24 true) (by omega) e1 e2 e4 (fun q => nomatch q)
    (fun u rs gs t hd => ⟨LinkJoin.sizes_behind_digits _ _ _ _ _ _ b' 24 e3 hk rfl hpc u rs gs t hd,
      fun G hG hz => stated_digits_all _ _ _ _ _ _ b' e3 hk 24 rfl hpc u t rs gs hd hG hz⟩) r6
  obtain ⟨G5, hG5, hz5⟩ := q5.pulls ⟨G6, hG6, hz6⟩
  rw [k6 G6 hG6]
  exact k5 G5 hG5 hz5

end

end P1K8

#print axioms P1K8.stated_digits_all
#print axioms P1K8.digitsHeard_head
