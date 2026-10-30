-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeSite.lean: the honest side of the kind "lookup"
(K3): AT A LOOKUP OF A PUBLIC PART, WHERE THE SUB-PROTOCOL HAS ACCEPTED: the three items of the
library's row out AT THE STATE THAT THE SUB-PROTOCOL LEAVES. Theorems with proofs; no definition.

`LeftAt` (Honest/K3/Law/Thread/LeftThr.lean) says what stands behind the acceptance in the thread's
own letters: the coins lent, the ledger in front, the hearing's return, how the state left is tied
to what was heard, and `Left` at the site's data. Honest/K3/Law/Thread/ExchangeOut.lean gives the
items from `Left` and premises on a ledger and a reading. Here the ledger's premises are paid at the
state left, and the dictionary is asked of the course that `LeftAt` binds.

  `plan_later`, `plan_sized`, `plan_owed`, `plan_unpaid`   a ledger with the plan's number of
                   claims laid anew is later, has its sizes, owes the same slots, has the same
                   debts unmarked
  `worth_site`     CONDITIONAL ON `LeftAt`; the ledger in front as the lookup's laws ask it; public
                   tests; and, OF THE WITNESS'S READING nu w AND KEY VECTORS Kv w: 0 at the place
                   "zero"; the site's data's bits are its readings; the site's data's keys are the
                   joint vector; THE DICTIONARY, AT COINS BY STAGE THAT ARE THOSE WHICH THE BOOK
                   LENT THE ROW: at the state st' left: `K3Objects`, `K3WorthPlanes`, `K3WorthKeys`

The dictionary's premise has the form of the statement `DictAt`
(Honest/K3/Law/Thread/DictAt.lean): from the lending and "the coins by stage are the row's" to
`Dict`. It is not asked at all coins: two courses with other coins ask other mask rows of one
reading.

Limits. The items are in the inner form of Johnson/Top/H/K3Worth.lean, at letters nu and Kv: that
the table of joints' own filling has these forms at the site's place, at which nu and Kv, is the
library's equations': not called here. No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOut
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftThr
import Johnson.Desc.ProofFile.Honest.K3.Law.BehindHands
import Johnson.Desc.ProofFile.Honest.K3.Law.DigitsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Reading)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Later Filled)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV faceOf hearV unpaid)
open VerifiableInference.Desc.First.Look (planesOk)
open VerifiableInference.OnPublicFiles (K3Objects K3WorthPlanes K3WorthKeys)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The plan's number of claims -/

theorem plan_later (G : Fork) (c : Nat) : Later G { G with planClaimsF := c } :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem plan_sized {G : Fork} (h : Sized G) (c : Nat) : Sized { G with planClaimsF := c } := h

theorem plan_owed {G : Fork} {a n : Nat} (h : OnBytes.PscRun.SlotsOwed G a n) (c : Nat) :
    OnBytes.PscRun.SlotsOwed { G with planClaimsF := c } a n := h

theorem plan_unpaid {G : Fork} {i : Nat} (h : unpaid G i = true) (c : Nat) :
    unpaid { G with planClaimsF := c } i = true := h

/-! ## 2 At a site -/

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Wt : Type}

/-- **CONDITIONAL, as the file's head lists: where the sub-protocol at a lookup of a public part has
accepted, at the state that it leaves: the three items of the library's row out.** No instance of
these hypotheses is exhibited in this file. -/
theorem worth_site (chain : Nat) (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt chain k blk Z s J wit st st' m ds y cols)
    (hf : s.at_.face = faceOf s.shape)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hok : FoNums.ok s.shape = true) (hpo : planesOk s.shape s.p.lm = true)
    (nu : Wt → _root_.Fo.Pl → GE) (Kv : Wt → Nat → Nat → GE) (w : Wt)
    (h0 : nu w .zero = 0)
    (hbit : ∀ u j, u < 2 ^ (siteData s (wit m.st.input) m.st.heard ds).N.d →
      j < 2 ^ (siteData s (wit m.st.input) m.st.heard ds).N.w →
      (siteData s (wit m.st.input) m.st.heard ds).bits u j =
        nu w ((siteData s (wit m.st.input) m.st.heard ds).N.bAt u j))
    (hkey : ∀ x, x < 2 ^ s.shape.v → (siteData s (wit m.st.input) m.st.heard ds).key x =
      OnBytes.Ends.jointKey s.shape (Kv w)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x)
    (hD : ∀ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit
        s.at_).parts) (c' : (t : Stage) → StageCoins s.at_ t),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) blk.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
          .ok c →
      CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
        (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) →
      Dict (courseAt s.at_ J s.p.first wit m ds c') (nu w)) :
    K3Objects (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard s.shape
        s.p.lm s.p.first nu st' w ∧
      K3WorthPlanes (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu st' w ∧
      K3WorthKeys (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu Kv st' w := by
  obtain ⟨_, _, c, F, g, G, c', hlend, hFk, hh, hQ, hc, hHd, hP, _, hLeft⟩ := hA
  obtain ⟨g', cn, hg, hheard, hfork, _⟩ := oneQ_hands K3Lot.ofForm hQ
  have L := hLed F hFk
  rw [hf] at hh
  have hroom : F.next + (faceOf s.shape).slots ≤ F.ns := by
    rw [L.next, ← hf]
    exact L.room
  have hfree : ∀ j, F.next ≤ j → j < F.next + (faceOf s.shape).slots → ¬ Filled F j :=
    fun j a b => L.free j a (by rw [← L.next, hf]; exact b)
  have hSG : Sized G := (hearV_later hh).sized L.sized
  exact worth_of_left (courseAt s.at_ J s.p.first wit m ds c') s.shape hf s.p.lm s.p.first
    (siteData s (wit m.st.input) m.st.heard ds) rfl L.sized hroom hh hg hHd hP hLeft hok hpo
    (plan_sized hSG cn) (plan_later G cn)
    (plan_owed (leaves_owed (faceOf s.shape) L.sized hfree hh) cn)
    (plan_unpaid (Digits.heardWellMade s.shape L.sized hh hg).2.2.1 cn) s.p.first _ _ nu Kv st' w
    hfork hheard h0 hbit hkey (hD c c' hlend hc)

#print axioms ProofFile.Honest.K3.Law.Exchange.plan_later
#print axioms ProofFile.Honest.K3.Law.Exchange.plan_sized
#print axioms ProofFile.Honest.K3.Law.Exchange.plan_owed
#print axioms ProofFile.Honest.K3.Law.Exchange.plan_unpaid
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_site

end ProofFile.Honest.K3.Law.Exchange
